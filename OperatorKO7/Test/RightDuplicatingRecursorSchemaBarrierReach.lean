import OperatorKO7.Meta.RightDuplicatingRecursorSchemaBarrier

namespace RightDuplicatingRecursorSchemaBarrierReach

open OperatorKO7
open OperatorKO7.Trace
open OperatorKO7.StepDuplicating
open OperatorKO7.Meta.Recursor.CircularIdentity
open OperatorKO7.Meta.Recursor.PayloadGrowthBlindness
open OperatorKO7.Meta.RDRSRecursiveFamilyBoundary
open OperatorKO7.Meta.RightDuplicatingRecursorSchemaBarrier

-- Force elaboration of every public declaration in the Phase B module.

#check @schemaToRecursiveFamily
#check @IsOutsideBoundaryFor
#check @right_duplicating_recursor_schema_unconditional
#check @schema_orbit_indistinguishable_from_circular_reference
#check @RightDuplicatingRecursorSchemaBarrierCatalog
#check @RightDuplicatingRecursorSchemaBarrierCatalog.schemas
#check @RightDuplicatingRecursorSchemaBarrierCatalog.barrier_witness
#check @RightDuplicatingRecursorSchemaBarrierCatalog.size
#check @RightDuplicatingRecursorSchemaBarrierCatalog.member_isOutsideBoundary
#check @emptyRightDuplicatingRecursorSchemaBarrierCatalog
#check @rightDuplicatingRecursorSchemaBarrierCatalogOfList
#check @emptyRightDuplicatingRecursorSchemaBarrierCatalog_size
#check @rightDuplicatingRecursorSchemaBarrierCatalogOfList_size

-- Smoke instantiations.
example : RightDuplicatingRecursorSchemaBarrierCatalog :=
  emptyRightDuplicatingRecursorSchemaBarrierCatalog

example : RightDuplicatingRecursorSchemaBarrierCatalog :=
  rightDuplicatingRecursorSchemaBarrierCatalogOfList []

-- The headline UNCONDITIONAL theorem is reachable as a value.
example : ∀ S : RightDuplicatingRecursorSchema, IsOutsideBoundaryFor S :=
  right_duplicating_recursor_schema_unconditional

-- The empty catalog has size 0.
example : emptyRightDuplicatingRecursorSchemaBarrierCatalog.size = 0 :=
  emptyRightDuplicatingRecursorSchemaBarrierCatalog_size

end RightDuplicatingRecursorSchemaBarrierReach
