# Copyright 2026 SAP SE
#
# Licensed under the Apache License, Version 2.0 (the "License"); you may
# not use this file except in compliance with the License. You may obtain
# a copy of the License at
#
#      http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
# WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
# License for the specific language governing permissions and limitations
# under the License.
from eventlet import tpool
from dns import exception as dnsexception
from dns import zone as dnszone
from oslo_log import log as logging
import oslo_messaging as messaging
from oslo_utils import timeutils

from designate.central.service import Service
from designate.common import constants
from designate.common.decorators import lock
from designate.common.decorators import notification
from designate.common.decorators import rpc
import designate.conf
from designate import dnsutils
from designate import exceptions
from designate import heartbeat_emitter
from designate import objects
from designate import policy
from designate.storage import transaction
from designate.storage import transaction_shallow_copy


CONF = designate.conf.CONF
LOG = logging.getLogger(__name__)

_UNSET = object()


class ServiceSAP(Service):
    """SAP-specific central service behavior layered on upstream Service."""

    RPC_API_VERSION = '6.12'
    target = messaging.Target(version=RPC_API_VERSION)

    def _policy_target(self, *, project_id=_UNSET, domain_id=_UNSET, **extra):
        """Build a policy target dict, honoring policy.enforce_new_defaults().

        The principal identity key is remapped for new RBAC defaults:
        project_id -> RBAC_PROJECT_ID (else 'tenant_id'),
        domain_id  -> RBAC_DOMAIN_ID  (else 'domain_id').
        Any ``extra`` keys are passed through unchanged. Callers pass
        exactly one of project_id / domain_id.
        """
        target = dict(extra)
        new_defaults = policy.enforce_new_defaults()
        if project_id is not _UNSET:
            key = constants.RBAC_PROJECT_ID if new_defaults else 'tenant_id'
            target[key] = project_id
        if domain_id is not _UNSET:
            key = constants.RBAC_DOMAIN_ID if new_defaults else 'domain_id'
            target[key] = domain_id
        return target

    def __init__(self):
        super().__init__()
        self._sap_owns_heartbeat = not hasattr(self, 'heartbeat')
        if self._sap_owns_heartbeat:
            self.heartbeat = heartbeat_emitter.get_heartbeat_emitter(
                self.service_name, rpc_api=self)

    def start(self):
        super().start()
        if self._sap_owns_heartbeat:
            self.heartbeat.start()

    def stop(self, graceful=True):
        if self._sap_owns_heartbeat:
            self.heartbeat.stop()
        super().stop(graceful)

    def _check_zone_ownership_conflicts(self, context, zone):
        """
        Ensures zone.name does not collide - as an exact duplicate, a
        subzone, or a superzone - with a zone owned by a different
        tenant, regardless of which pool that zone lives in.

        This closes the CVE-2026-71193 cross-pool bypass: the exact
        duplicate DB constraint (name, deleted, pool_id) and the
        _is_subzone / _is_superzone checks were all scoped to a single
        pool, so scheduling a zone into a different pool skirted every
        cross-tenant ownership check.

        A single tenant may still own the same or an overlapping zone
        name across multiple pools (e.g. split-horizon deployments).
        Cross-tenant collisions are rejected unless the operator has
        explicitly opted in via the same policies the pool-scoped
        create_zone flow already honours (create_sub_zone_other_project
        for subzones, create_super_zone for superzones). There is no
        opt-in for an exact-name cross-tenant duplicate.
        """
        elevated = context.elevated(all_tenants=True)
        labels = zone.name.split('.')

        # Exact-name duplicate owned by another tenant, in any pool.
        for existing in self.storage.find_zones(elevated, {'name': zone.name}):
            if existing.tenant_id != zone.tenant_id:
                raise exceptions.DuplicateZone(
                    'Zone already exists, owned by a different tenant')

        # This zone would be a subzone of a zone owned by another
        # tenant, in any pool. Stop at the first (nearest) ancestor
        # match, same as _is_subzone.
        for i in range(1, len(labels)):
            name = '.'.join(labels[i:])
            ancestors = self.storage.find_zones(elevated, {'name': name})
            if not ancestors:
                continue
            for ancestor in ancestors:
                if ancestor.tenant_id != zone.tenant_id:
                    # Honour the same policy override the pool-scoped
                    # subzone path uses before rejecting.
                    if not policy.check('create_sub_zone_other_project',
                                        context, do_raise=False):
                        raise exceptions.IllegalChildZone(
                            'Unable to create subzone in another tenants '
                            'zone')
            break

        # This zone would be a superzone of a zone owned by another
        # tenant, in any pool.
        search_term = "%%.%(name)s" % {"name": zone.name}
        for subzone in self.storage.find_zones(
                elevated, {'name': search_term}):
            if subzone.tenant_id != zone.tenant_id:
                # Honour the same policy override the pool-scoped
                # superzone path uses before rejecting.
                if not policy.check('create_super_zone', context,
                                    do_raise=False):
                    raise exceptions.IllegalParentZone(
                        'Unable to create zone because another tenant owns '
                        'a subzone of the zone')

    def _add_ns(self, context, zone, ns_record, increment_serial=True):
        # Get NS recordset
        # If the zone doesn't have an NS recordset yet, create one
        try:
            recordset = self.find_recordset(
                context,
                criterion={
                    'zone_id': zone['id'],
                    'name': zone['name'],
                    'type': 'NS'
                }
            )
        except exceptions.RecordSetNotFound:
            self._create_ns(context, zone, [ns_record])
            return

        # Add new record to recordset based on the new nameserver
        recordset.records.append(
            objects.Record(data=ns_record, managed=True)
        )

        # Intentional: delayed notify is tied to increment_serial so
        # callers that skip the serial bump also skip the notification.
        self._update_recordset_in_storage(
            context, zone, recordset,
            increment_serial=increment_serial,
            set_delayed_notify=increment_serial)

    def _delete_ns(self, context, zone, ns_record, increment_serial=True):
        recordset = self.find_recordset(
            context,
            criterion={
                'zone_id': zone['id'],
                'name': zone['name'],
                'type': 'NS'
            }
        )

        for record in list(recordset.records):
            if record.data == ns_record:
                recordset.records.remove(record)

        # Intentional: delayed notify is tied to increment_serial so
        # callers that skip the serial bump also skip the notification.
        self._update_recordset_in_storage(
            context, zone, recordset,
            increment_serial=increment_serial,
            set_delayed_notify=increment_serial)

    def _enforce_record_quota(self, context, zone, recordset):
        # Quotas don't apply to managed records.
        if recordset.managed:
            return

        # Ensure the records per zone quota is OK
        zone_criterion = {
            'zone_id': zone.id,
            'managed': False,  # only include non-managed records
        }

        zone_records = self.storage.count_records(context, zone_criterion)

        recordset_criterion = {
            'recordset_id': recordset.id,
            'managed': False,  # only include non-managed records
        }
        recordset_records = self.storage.count_records(
            context, recordset_criterion)

        # We need to check the current number of zones + the
        # changes that add, so lets get +/- from our recordset
        # records based on the action
        adjusted_zone_records = (
            zone_records - recordset_records + len(recordset.records))

        # Only enforce quota for non-catalog zones:
        if zone.type != constants.ZONE_CATALOG:
            self.quota.limit_check(context, zone.tenant_id,
                                   zone_records=adjusted_zone_records)

            # Ensure the records per recordset quota is OK
            self.quota.limit_check(context, zone.tenant_id,
                                   recordset_records=len(recordset.records))

    def _generate_record_serial(self, zone, increment_serial):
        if not increment_serial:
            return zone.serial
        else:
            return zone.serial + 1

    @rpc.expected_exceptions()
    @transaction
    @lock.synchronized_zone()
    def increment_zone_serial(self, context, zone):
        created_ts = zone.created_at.timestamp()
        now_ts = timeutils.utcnow_ts()
        if created_ts < zone.serial < now_ts:
            zone.serial = self.storage.increment_serial(
                context, zone.id, int(now_ts))
        else:
            zone.serial = self.storage.increment_serial(
                context, zone.id, zone.serial + 1
            )
        self._update_soa(context, zone)
        return zone.serial

    @rpc.expected_exceptions()
    @notification.notify_type('dns.domain.create')
    @notification.notify_type('dns.zone.create')
    @lock.synchronized_zone(new_zone=True)
    def create_zone(self, context, zone):
        """Create zone: perform checks and then call _create_zone()
        """

        # Default to creating in the current users tenant
        zone.tenant_id = zone.tenant_id or context.project_id

        target = self._policy_target(
            project_id=zone.tenant_id, zone_name=zone.name)

        self._enforce_catalog_zone_policy(context, zone)

        self._is_valid_project_id(zone.tenant_id)

        # Ensure the tenant has enough quota to continue
        self._enforce_zone_quota(context, zone.tenant_id)

        # Ensure the zone name is valid
        self._is_valid_zone_name(context, zone.name)

        # Ensure TTL is above the minimum
        self._is_valid_ttl(context, zone.ttl)

        # Ensure this zone name does not collide with another tenant's
        # zone, regardless of which pool either zone lives in
        self._check_zone_ownership_conflicts(context, zone)

        # Get a pool id
        zone.pool_id = self.scheduler.schedule_zone(context, zone)

        # Get Domain name to handle IAAS domains differently
        if context.project_domain_name:
            domain_name = context.project_domain_name.lower()
        else:
            domain_name = ''

        # Handle sub-zones appropriately
        parent_zone = self._is_subzone(
            context, zone.name, zone.pool_id)
        if parent_zone:
            parent_zone_shared = self.find_shared_zones(
                context.elevated(all_tenants=True),
                criterion={
                    "zone_id": parent_zone.id,
                    "target_project_id": zone.tenant_id,
                },
                limit=1
            )

            if parent_zone.tenant_id == zone.tenant_id or parent_zone_shared:
                # Record the Parent Zone ID
                zone.parent_zone_id = parent_zone.id

                # Do subzone policy check instead of regular create_zone
                if domain_name.startswith('iaas'):
                    # Special case - IAAS Keystone Domains
                    policy.check('create_iaas_zone', context, target)
                else:
                    # All other Keystone Domains apply default rule
                    policy.check('create_sub_zone', context, target)

            elif not policy.check('create_sub_zone_other_project', context,
                                  do_raise=False):
                raise exceptions.IllegalChildZone('Unable to create '
                                                  'subzone in another '
                                                  'tenants zone')
        else:
            # If not subzone, regular policy check applies
            if domain_name.startswith('iaas'):
                # Special case - IAAS Keystone Domains
                policy.check('create_iaas_zone', context, target)
            else:
                # All other Keystone Domains apply default rule
                policy.check('create_zone', context, target)

        # Handle super-zones appropriately
        subzones = self._is_superzone(context, zone.name, zone.pool_id)
        msg = ('Unable to create zone because another tenant owns a subzone '
               'of the zone')
        if subzones:
            LOG.debug("Zone '%s' is a superzone.", zone.name)
            for subzone in subzones:
                if subzone.tenant_id != zone.tenant_id:
                    # raise unless explicitly allowed by the policy:
                    if not policy.check('create_super_zone', context,
                                        do_raise=False):
                        raise exceptions.IllegalParentZone(msg)

        # If this succeeds, subzone parent IDs will be updated
        # after zone is created

        # NOTE(kiall): Fetch the servers before creating the zone, this way
        #              we can prevent zone creation if no servers are
        #              configured.

        pool_ns_records = self._get_pool_ns_records(context, zone.pool_id)
        if len(pool_ns_records) == 0:
            LOG.critical('No nameservers configured. Please create at least '
                         'one nameserver')
            raise exceptions.NoServersConfigured()

        # End of pre-flight checks, create zone
        return self._create_zone(context, zone, subzones)

    @rpc.expected_exceptions()
    def find_zones(self, context, criterion=None, marker=None, limit=None,
                   sort_key=None, sort_dir=None):
        """List existing zones including the ones flagged for deletion.
        """
        target = self._policy_target(project_id=context.project_id)

        policy.check('find_zones', context, target)

        if criterion is None:
            criterion = {}

        # we forbid to look for catalog zones and hide those by default
        if 'type' not in criterion.keys():
            criterion['type'] = '!CATALOG'
        elif criterion.get('type') == 'CATALOG':
            if not context.is_admin:
                msg = 'This operation is not allowed for non-admins.'
                raise exceptions.Forbidden(msg)

        return self.storage.find_zones(context, criterion, marker, limit,
                                       sort_key, sort_dir)

    @rpc.expected_exceptions()
    @notification.notify_type('dns.domain.update')
    @notification.notify_type('dns.zone.update')
    @lock.synchronized_zone()
    def update_zone(self, context, zone, increment_serial=True):
        """Update zone. Perform checks and then call _update_zone()

        :returns: updated zone
        """
        target = self._policy_target(
            project_id=zone.obj_get_original_value('tenant_id'),
            zone_id=zone.obj_get_original_value('id'),
            zone_name=zone.obj_get_original_value('name'))

        policy.check('update_zone', context, target)
        self._enforce_catalog_zone_policy(context, zone)

        changes = zone.obj_get_changes()
        # Ensure immutable fields are not changed
        if 'tenant_id' in changes:
            # TODO(kiall): Moving between tenants should be allowed, but the
            #              current code will not take into account that
            #              RecordSets and Records must also be moved.
            raise exceptions.BadRequest('Moving a zone between tenants is '
                                        'not allowed')

        if 'name' in changes:
            raise exceptions.BadRequest('Renaming a zone is not allowed')

        if "serial" in changes:
            self._update_soa(context, zone)

        # Ensure TTL is above the minimum
        ttl = changes.get('ttl')
        self._is_valid_ttl(context, ttl)

        return self._update_zone(context, zone, increment_serial, changes)

    @rpc.expected_exceptions()
    @notification.notify_type('dns.domain.update')
    @notification.notify_type('dns.zone.update')
    def pool_move_zone(self, context, zone_id, target_pool_id=None):
        """Move zone. Perform checks and then create zone in destination pool

        :returns: moved zone
        """
        target = self._policy_target(
            project_id=context.project_id, zone_id=zone_id)

        policy.check('pool_move_zone', context, target)

        # Get the destination pool
        zone = self.storage.get_zone(context, zone_id)
        orig_pool_id = zone.pool_id

        if target_pool_id is None:
            target_pool_id = self.scheduler.schedule_zone(context, zone)
            if target_pool_id == orig_pool_id:
                raise exceptions.BadRequest('No valid pool selected')
            # Update the orignal zone with new pool_id
            zone.pool_id = target_pool_id

        # Need elevated context to get the pool
        elevated_context = context.elevated(all_tenants=True)
        try:
            self.storage.get_pool(elevated_context, target_pool_id)
        except exceptions.PoolNotFound:
            raise exceptions.BadRequest('Target pool does not exist')

        target_pool_ns_records = self._get_pool_ns_records(context,
                                                           target_pool_id)
        if len(target_pool_ns_records) == 0:
            LOG.critical('No nameservers configured. Please create at least '
                         'one nameserver on target pool')
            raise exceptions.NoServersConfigured()

        orig_pool_ns_records = self._get_pool_ns_records(context,
                                                         orig_pool_id)

        target_ns = {n.hostname for n in target_pool_ns_records}
        orig_ns = {n.hostname for n in orig_pool_ns_records}
        create_ns = target_ns.difference(orig_ns)
        delete_ns = orig_ns.difference(target_ns)

        # Update target NS servers for the zone without triggering serial
        # increments or delayed notifications; the pool move handles the
        # zone update itself at the end of this method.
        for ns_record in create_ns:
            self._add_ns(elevated_context, zone, ns_record,
                         increment_serial=False)

        # Then handle the ns_records to delete
        for ns_record in delete_ns:
            self._delete_ns(elevated_context, zone, ns_record,
                            increment_serial=False)

        LOG.info("Moving zone '%(zone)s' to pool '%(pool)s'",
                 {'zone': zone.name, 'pool': target_pool_id})
        zone.pool_id = target_pool_id
        zone = self._update_zone_in_storage(
                context, zone, increment_serial=False)

        zone.refresh = self._generate_soa_refresh_interval()
        zone.action = constants.UPDATE
        zone.status = constants.PENDING
        self.worker_api.update_zone(context, zone)

        return zone

    @rpc.expected_exceptions()
    @notification.notify_type('dns.recordset.create')
    def create_recordset(self, context, zone_id, recordset,
                         increment_serial=True):
        zone = self.storage.get_zone(context, zone_id,
                                     apply_tenant_criteria=False)

        self._enforce_catalog_zone_policy(context, zone)

        # Note this call must follow the get_zone call to maintain API response
        # code behavior.
        zone_shared = self._check_zone_share_permission(context, zone)

        # Don't allow updates to zones that are being deleted
        if zone.action == 'DELETE':
            raise exceptions.BadRequest('Can not update a deleting zone')

        target = self._policy_target(
            project_id=zone.tenant_id,
            zone_id=zone_id,
            zone_name=zone.name,
            zone_type=zone.type,
            zone_shared=zone_shared,
            recordset_name=recordset.name)

        policy.check('create_%s_recordset' % recordset.type, context, target)

        # Override the context to be all_tenants here as we have already
        # passed the RBAC check for this call and context checks in lower
        # layers will fail for shared zones.
        # TODO(johnsom) Remove once context checking is removed from the lower
        #               code layers.
        context = context.elevated(all_tenants=True)

        recordset, zone = self._create_recordset_in_storage(
            context, zone, recordset, increment_serial=increment_serial
        )

        recordset.zone_name = zone.name
        recordset.obj_reset_changes(['zone_name'])

        return recordset

    @transaction_shallow_copy
    def _create_recordset_in_storage(self, context, zone, recordset,
                                     increment_serial=True):
        # Ensure the tenant has enough quota to continue
        self._enforce_recordset_quota(context, zone)
        self._validate_recordset(context, zone, recordset)

        if recordset.obj_attr_is_set('records') and recordset.records:
            # Ensure the tenant has enough zone record quotas to
            # create new records
            self._enforce_record_quota(context, zone, recordset)

            for record in recordset.records:
                record.action = 'CREATE'
                record.status = 'PENDING'
                record.serial = self._generate_record_serial(
                    zone, increment_serial
                )

        new_recordset = self.storage.create_recordset(context, zone.id,
                                                      recordset)
        if recordset.records and increment_serial:
            # update the zone's status and increment the serial
            zone = self._update_zone_in_storage(
                context, zone, increment_serial
            )

        # Return the zone too in case it was updated
        return new_recordset, zone

    @rpc.expected_exceptions()
    @notification.notify_type('dns.recordset.update')
    def update_recordset(self, context, recordset, increment_serial=True):
        zone_id = recordset.obj_get_original_value('zone_id')
        changes = recordset.obj_get_changes()

        # Ensure immutable fields are not changed
        if 'tenant_id' in changes:
            raise exceptions.BadRequest('Moving a recordset between tenants '
                                        'is not allowed')

        if 'zone_id' in changes or 'zone_name' in changes:
            raise exceptions.BadRequest('Moving a recordset between zones '
                                        'is not allowed')

        if 'type' in changes:
            raise exceptions.BadRequest('Changing a recordsets type is not '
                                        'allowed')

        zone = self.storage.get_zone(context, zone_id,
                                     apply_tenant_criteria=False)

        self._enforce_catalog_zone_policy(context, zone)

        # Note this call must follow the get_zone call to maintain API response
        # code behavior.
        zone_shared = self._check_zone_share_permission(context, zone)

        # Don't allow updates to zones that are being deleted
        if zone.action == 'DELETE':
            raise exceptions.BadRequest('Can not update a deleting zone')

        # TODO(johnsom) This should account for all-projects context
        # it passes today due to ADMIN
        target = self._policy_target(
            project_id=zone.tenant_id,
            recordset_id=recordset.obj_get_original_value('id'),
            recordset_project_id=recordset.obj_get_original_value('tenant_id'),
            zone_id=recordset.obj_get_original_value('zone_id'),
            zone_name=zone.name,
            zone_shared=zone_shared,
            zone_type=zone.type)

        recordset_type = recordset.obj_get_original_value('type')
        policy.check('update_%s_recordset' % recordset_type, context, target)

        if recordset.managed and not context.edit_managed_records:
            raise exceptions.BadRequest('Managed records may not be updated')

        # Override the context to be all_tenants here as we have already
        # passed the RBAC check for this call and context checks in lower
        # layers will fail for shared zones.
        # TODO(johnsom) Remove once context checking is removed from the lower
        #               code layers.
        context = context.elevated(all_tenants=True)

        recordset, zone = self._update_recordset_in_storage(
            context, zone, recordset, increment_serial=increment_serial)

        return recordset

    @rpc.expected_exceptions()
    @notification.notify_type('dns.recordset.delete')
    def delete_recordset(self, context, zone_id, recordset_id,
                         increment_serial=True):
        # apply_tenant_criteria=False here as we will gate this delete
        # with the RBAC rules below. This allows the zone owner to delete
        # all of the recordsets of the zone.
        recordset = self.storage.find_recordset(
            context,
            {"id": recordset_id, "zone_id": zone_id},
            apply_tenant_criteria=False
        )
        zone = self.storage.get_zone(context, zone_id,
                                     apply_tenant_criteria=False)

        self._enforce_catalog_zone_policy(context, zone)

        # Don't allow updates to zones that are being deleted
        if zone.action == 'DELETE':
            raise exceptions.BadRequest('Can not update a deleting zone')

        # TODO(johnsom) should handle all_projects
        target = self._policy_target(
            project_id=zone.tenant_id,
            zone_id=zone_id,
            zone_name=zone.name,
            zone_type=zone.type,
            recordset_id=recordset.id,
            recordset_project_id=recordset.tenant_id)

        policy.check('delete_%s_recordset' % recordset.type, context, target)

        if recordset.managed and not context.edit_managed_records:
            raise exceptions.BadRequest('Managed records may not be deleted')

        # Override the context to be all_tenants here as we have already
        # passed the RBAC check for this call.
        # TODO(johnsom) Remove once context checking is removed from the lower
        #               code layers.
        context = context.elevated(all_tenants=True)

        recordset, zone = self._delete_recordset_in_storage(
            context, zone, recordset, increment_serial=increment_serial)

        recordset.zone_name = zone.name
        recordset.obj_reset_changes(['zone_name'])

        return recordset

    @rpc.expected_exceptions()
    def find_record(self, context, criterion=None):
        target = {'tenant_id': context.project_id}
        policy.check('find_record', context, target)

        return self.storage.find_record(context, criterion)

    @rpc.expected_exceptions()
    @notification.notify_type('dns.record.update')
    @lock.synchronized_zone()
    def update_record(self, context, record, increment_serial=True):
        zone_id = record.obj_get_original_value('zone_id')

        zone = self.storage.get_zone(context, zone_id)

        # Don't allow updates to zones that are being deleted
        if zone.action == 'DELETE':
            raise exceptions.BadRequest('Can not update a deleting zone')

        recordset_id = record.obj_get_original_value('recordset_id')
        recordset = self.storage.get_recordset(context, recordset_id)

        changes = record.obj_get_changes()

        # Ensure immutable fields are not changed
        if 'tenant_id' in changes:
            raise exceptions.BadRequest('Moving a recordset between tenants '
                                        'is not allowed')

        if 'zone_id' in changes:
            raise exceptions.BadRequest('Moving a recordset between zones '
                                        'is not allowed')

        if 'recordset_id' in changes:
            raise exceptions.BadRequest('Moving a recordset between '
                                        'recordsets is not allowed')

        target = {
            'zone_id': record.obj_get_original_value('zone_id'),
            'zone_name': zone.name,
            'zone_type': zone.type,
            'zone_shared': zone.shared,
            'recordset_id': record.obj_get_original_value('recordset_id'),
            'recordset_name': recordset.name,
            'record_id': record.obj_get_original_value('id'),
            'tenant_id': zone.tenant_id
        }

        policy.check('update_record', context, target)

        if recordset.managed and not context.edit_managed_records:
            raise exceptions.BadRequest('Managed records may not be updated')

        record, zone = self._update_record_in_storage(
            context, zone, record, increment_serial=increment_serial)

        self.zone_api.update_zone(context, zone)

        return record

    @transaction
    def _update_record_in_storage(self, context, zone, record,
                                  increment_serial=True):

        if increment_serial:
            # update the zone's status and increment the serial
            zone = self._update_zone_in_storage(
                context, zone, increment_serial)

        record.action = 'UPDATE'
        record.status = 'PENDING'
        record.serial = zone.serial

        # Update the record
        record = self.storage.update_record(context, record)

        return (record, zone)

    @rpc.expected_exceptions()
    @notification.notify_type('dns.record.delete')
    @lock.synchronized_zone()
    def delete_record(self, context, zone_id, recordset_id, record_id,
                      increment_serial=True):
        zone = self.storage.get_zone(context, zone_id)

        # Don't allow updates to zones that are being deleted
        if zone.action == 'DELETE':
            raise exceptions.BadRequest('Can not update a deleting zone')

        recordset = self.storage.get_recordset(context, recordset_id)
        record = self.storage.get_record(context, record_id)

        # Ensure the zone_id matches the record's zone_id
        if zone.id != record.zone_id:
            raise exceptions.RecordNotFound()

        # Ensure the recordset_id matches the record's recordset_id
        if recordset.id != record.recordset_id:
            raise exceptions.RecordNotFound()

        target = {
            'zone_id': zone_id,
            'zone_name': zone.name,
            'zone_type': zone.type,
            'zone_shared': zone.shared,
            'recordset_id': recordset_id,
            'recordset_name': recordset.name,
            'record_id': record.id,
            'tenant_id': zone.tenant_id
        }

        policy.check('delete_record', context, target)

        if recordset.managed and not context.edit_managed_records:
            raise exceptions.BadRequest('Managed records may not be deleted')

        record, zone = self._delete_record_in_storage(
            context, zone, record, increment_serial=increment_serial)

        self.zone_api.update_zone(context, zone)

        return record

    @transaction
    def _delete_record_in_storage(self, context, zone, record,
                                  increment_serial=True):

        if increment_serial:
            # update the zone's status and increment the serial
            zone = self._update_zone_in_storage(
                context, zone, increment_serial)

        record.action = 'DELETE'
        record.status = 'PENDING'
        record.serial = zone.serial

        record = self.storage.update_record(context, record)

        return (record, zone)

    @rpc.expected_exceptions()
    @notification.notify_type('dns.pool.create')
    @transaction
    def create_pool(self, context, pool):
        # Verify that there is a tenant_id
        if pool.tenant_id is None:
            pool.tenant_id = context.project_id
        if not pool.domain_id:
            pool.domain_id = context.project_domain_id

        if (not context.is_admin and
                pool.domain_id is not None and
                context.project_domain_id != pool.domain_id):
            raise exceptions.Forbidden(
                "It's not allowed to create pools in other domain"
            )

        policy.check('create_pool', context)
        created_pool = self.storage.create_pool(context, pool)
        return created_pool

    @rpc.expected_exceptions()
    def get_pool(self, context, pool_id):
        pool = self.storage.get_pool(context, pool_id)
        pool_shared = False
        if (not context.is_admin and
                context.project_domain_id and
                pool.domain_id is not None and
                context.project_domain_id != pool.domain_id):
            pool_shared = self.storage.is_pool_shared_with_domain(
                pool_id, context.project_domain_id)
            if not pool_shared:
                raise exceptions.SharedPoolNotFound(
                    "Pool isn't allowed for domain %r: %r" %
                    (context.project_domain_id, pool))
        target = {
            'pool_id': pool_id,
            'pool_name': pool.name,
            'pool_shared': pool_shared,
            constants.RBAC_DOMAIN_ID: pool.domain_id
        }
        policy.check('get_pool', context, target)
        return pool

    @rpc.expected_exceptions()
    @notification.notify_type('dns.zone_transfer_request.create')
    @transaction
    def create_zone_transfer_request(self, context, zone_transfer_request):

        # get zone
        zone = self.get_zone(context, zone_transfer_request.zone_id)

        self._enforce_catalog_zone_policy(context, zone)

        # Don't allow transfers for zones that are being deleted
        if zone.action == 'DELETE':
            raise exceptions.BadRequest('Can not transfer a deleting zone')

        target = self._policy_target(project_id=zone.tenant_id)

        # Handle sub-zones appropriately
        parent_zone = self._is_subzone(context, zone.name, zone.pool_id)

        if parent_zone:
            # Do subzone policy check instead of regular zone_transfer
            policy.check('create_sub_zone_transfer_request', context, target)
        else:
            # If not subzone, regular policy check applies
            policy.check('create_zone_transfer_request', context, target)

        zone_transfer_request.key = self._transfer_key_generator()

        if zone_transfer_request.tenant_id is None:
            zone_transfer_request.tenant_id = context.project_id

        self._is_valid_project_id(zone_transfer_request.tenant_id)

        created_zone_transfer_request = (
            self.storage.create_zone_transfer_request(
                context, zone_transfer_request))

        return created_zone_transfer_request

    @rpc.expected_exceptions()
    @notification.notify_type('dns.zone_import.create')
    def create_zone_import(self, context, request_body,
                           pool_id='', force=False):
        target = self._policy_target(project_id=context.project_id)

        if force:
            policy.check('create_force_zone_import', context, target)
        else:
            policy.check('create_zone_import', context, target)

        self._is_valid_project_id(context.project_id)
        values = {
            'status': 'PENDING',
            'message': None,
            'zone_id': None,
            'tenant_id': context.project_id,
            'task_type': 'IMPORT'
        }
        zone_import = objects.ZoneImport(**values)

        created_zone_import = self.storage.create_zone_import(context,
                                                              zone_import)

        self.tg.add_thread(self._import_zone, context, created_zone_import,
                           request_body, pool_id=pool_id, force=force)

        return created_zone_import

    @rpc.expected_exceptions()
    def _import_zone(self, context, zone_import, request_body, pool_id='',
                     force=False):

        def _force_import(existing_rrsets, new_rrsets):
            """
            if record exist in new and old then update
            if record exist in new and not in old then create
            if record not exist in new and exist in old then delete from old
            """
            for rrset in existing_rrsets:
                recordset_id = existing_rrsets[rrset].id
                if rrset not in new_rrsets:
                    LOG.debug(f"Deleting recordset {recordset_id}"
                              f" for zone {zone_object.id}")
                    self.delete_recordset(context, zone_object.id,
                                          recordset_id)
                if rrset in new_rrsets:
                    new_rrsets[rrset].id = recordset_id
                    new_rrsets[rrset].zone_id = zone_object.id
                    new_rrsets[rrset].tenant_id = zone_object.tenant_id
                    LOG.debug(f"Updating recordset {rrset} for zone {rrset}")
                    self.storage.update_recordset(context, new_rrsets[rrset])
                    new_rrsets.pop(rrset)
            for rrset in new_rrsets:
                if rrset not in existing_rrsets:
                    LOG.debug(f"Creating recordset {new_rrsets[rrset]}"
                              f" for zone {zone_object.id}")
                    self.create_recordset(context, zone_object.id,
                                          new_rrsets[rrset])

        def _import(self, context, zone_import, request_body, pool_id=''):
            # Dnspython needs a str instead of a unicode object
            zone = None
            try:
                dnspython_zone = dnszone.from_text(
                    request_body,
                    # Don't relativize, or we end up with '@' record names.
                    relativize=False,
                    # Don't check origin, we allow missing NS records
                    # (missing SOA records are taken care of in _create_zone).
                    check_origin=False)
                zone = dnsutils.from_dnspython_zone(dnspython_zone)
                zone.type = 'PRIMARY'

                # Set pool id attribute if it was specified as request header:
                if pool_id:
                    attr = objects.ZoneAttributeList.from_list([
                        {"key": "pool_id",
                         "value": pool_id}])

                    # We can set attributes freely as there are no attributes
                    # in zone import request body since it is text/dns
                    zone.__setattr__('attributes', attr)

                target = self._policy_target(project_id=context.project_id)

                #checks = {"MX": False, "NS": False}
                for rrset in list(zone.recordsets):
                    if rrset.type == 'SOA':
                        zone.recordsets.remove(rrset)
                    # subdomain NS records should be kept
                    elif rrset.type == 'NS' and rrset.name == zone.name:
                        zone.recordsets.remove(rrset)
                    #TODO: fix the check for MX and NS record types
                    #if rrset.type in ["MX", "NS"] and not checks[rrset.type]:
                    #    LOG.debug(f"Checking {rrset.type} policy during zone import")
                    #    check = policy.check(f'create_{rrset.type}_recordset',
                    #                         context, target, do_raise=False)
                    #    if not check:
                    #        zone_import.status = 'ERROR'
                    #        zone_import.message = f'Failed to create Record' \
                    #                              f' {rrset.name} - Forbidden'
                    #        break
                    #    else:
                    #        checks[rrset.type] = True
            except dnszone.UnknownOrigin:
                zone_import.message = ('The $ORIGIN statement is required and'
                                      ' must be the first statement in the'
                                      ' zonefile.')
                zone_import.status = 'ERROR'
            except dnsexception.SyntaxError:
                zone_import.message = 'Malformed zonefile.'
                zone_import.status = 'ERROR'
            except exceptions.BadRequest:
                zone_import.message = 'An SOA record is required.'
                zone_import.status = 'ERROR'
            except Exception as e:
                LOG.exception('An undefined error occurred during zone import')
                msg = 'An undefined error occurred. %s'\
                      % str(e)[:130]
                zone_import.message = msg
                zone_import.status = 'ERROR'

            return zone, zone_import

        # Execute the import in a real Python thread
        zone, zone_import = tpool.execute(_import, self, context,
            zone_import, request_body, pool_id=pool_id)

        # If the zone import was valid, create the zone
        if zone_import.status != 'ERROR':
            target = self._policy_target(project_id=context.project_id)

            try:
                if force:
                    try:
                        zone_object = self.storage.find_zone(
                            context,
                            {'name': zone.name}
                        )
                    except exceptions.ZoneNotFound:
                        if policy.check('create_zone_import', context,
                                        target, do_raise=False):
                            zone = self.create_zone(context, zone)
                        else:
                            zone_import.status = 'ERROR'
                            zone_import.message = 'Failed to create zone' \
                                                  ' - Forbidden'
                            self.update_zone_import(context.elevated(),
                                                    zone_import)
                            raise exceptions.Forbidden
                    else:
                        criterion = {'zone_id': zone_object.id}
                        rrsets = self.storage.find_recordsets(context,
                                                              criterion)
                        existing_rrsets = dict()
                        for rrset in rrsets:
                            if rrset.type == 'SOA':
                                continue
                            if rrset.type == 'NS' and rrset.name == zone.name:
                                continue
                            existing_rrsets[
                                f"{rrset.name}_{rrset.type}"] = rrset
                        new_rrsets = {
                            f"{rrset.name}_{rrset.type}": rrset for rrset
                            in zone.recordsets
                        }
                        _force_import(existing_rrsets, new_rrsets)
                        zone_import.zone_id = zone_object.id
                else:
                    if policy.check('create_zone_import', context,
                                    target, do_raise=False):
                        zone = self.create_zone(context, zone)
                    else:
                        zone_import.status = 'ERROR'
                        zone_import.message = 'Failed to create zone' \
                                              ' - Forbidden'
                        self.update_zone_import(context.elevated(),
                                                zone_import)
                        raise exceptions.Forbidden

                zone_import.status = 'COMPLETE'
                zone_import.zone_id = zone.id
                zone_import.message = (
                    f'{zone.name} imported'
                )

            except exceptions.DuplicateZone:
                zone_import.status = 'ERROR'
                zone_import.message = 'Duplicate zone.'
            except exceptions.InvalidTTL as e:
                zone_import.status = 'ERROR'
                zone_import.message = str(e)
            except exceptions.Forbidden:
                zone_import.status = 'ERROR'
                zone_import.message = 'Failed to create zone' \
                                      ' - Forbidden'
            except exceptions.OverQuota:
                zone_import.status = 'ERROR'
                zone_import.message = 'Quota exceeded during zone import.'
            except Exception as e:
                LOG.exception(
                    'An undefined error occurred during zone import creation'
                )
                msg = 'An undefined error occurred. %s'\
                      % str(e)[:130]
                if isinstance(e.__context__, exceptions.DuplicateZone):
                    msg = 'Duplicate zone.'
                zone_import.message = msg
                zone_import.status = 'ERROR'

        self.update_zone_import(context.elevated(), zone_import)

    @rpc.expected_exceptions()
    def delete_service_status(self, context, service_status):
        policy.check('delete_service_status', context)

        criterion = {
            "service_name": service_status.service_name,
            "hostname": service_status.hostname
        }

        if service_status.obj_attr_is_set('id'):
            criterion["id"] = service_status.id
        try:
            db_status = self.storage.find_service_status(
                context, criterion)
            db_status.update(dict(service_status))

            return self.storage.delete_service_status(context, db_status)
        except exceptions.ServiceStatusNotFound:
            LOG.warning(
                "Deleting service status entry for %(service_name)s "
                "at %(hostname)s",
                {
                    'service_name': service_status.service_name,
                    'hostname': service_status.hostname
                }
            )

    @rpc.expected_exceptions()
    @notification.notify_type('dns.pool.share')
    @transaction
    def share_pool(self, context, pool_id, shared_pool):
        # Ensure that pool exists and get the pool owner
        elevated_context = context.elevated(all_tenants=True)
        pool = self.storage.get_pool(elevated_context, pool_id)
        domain_id = pool.domain_id
        if not domain_id:
            raise exceptions.PoolWithoutDomainId(
                f"Pool {pool_id} doesn't have domain_id "
                f"Specify domain_id in pools.yaml.")
        target = self._policy_target(domain_id=domain_id)

        policy.check('share_pool', context, target)
        shared_pool['domain_id'] = pool.domain_id
        shared_pool['pool_id'] = pool_id

        shared_pool = self.storage.share_pool(context, shared_pool)

        return shared_pool

    @rpc.expected_exceptions()
    @notification.notify_type('dns.pool.unshare')
    @transaction
    def unshare_pool(self, context, pool_id, pool_share_id):
        # Ensure the share exists and get the share owner
        shared_pool = self.get_shared_pool(context, pool_id, pool_share_id)

        target = self._policy_target(domain_id=shared_pool.domain_id)

        policy.check('unshare_pool', context, target)

        shared_pool = self.storage.unshare_pool(
            context, pool_id, pool_share_id
        )

        return shared_pool

    @rpc.expected_exceptions()
    def find_shared_pools(self, context, criterion=None, marker=None,
                          limit=None, sort_key=None, sort_dir=None):
        # By default we will let any valid token through as the filter
        # criteria below will limit the scope of the results.
        policy.check('find_pool_shares', context)

        if not context.all_tenants:
            target_domain = (criterion or {}).get('target_domain_id')
            if target_domain and target_domain != context.project_domain_id:
                target = self._policy_target(domain_id=target_domain)
                policy.check('find_domain_pool_share', context, target)

        shared_pools = self.storage.find_shared_pools(
            context, criterion, marker, limit, sort_key, sort_dir
        )

        return shared_pools

    @rpc.expected_exceptions()
    def get_shared_pool(self, context, pool_id, pool_share_id):
        # Ensure that share exists and get the share owner
        pool_share = self.storage.get_shared_pool(
            context, pool_id, pool_share_id)

        target = self._policy_target(domain_id=pool_share.domain_id)

        policy.check('get_pool_share', context, target)

        return pool_share

