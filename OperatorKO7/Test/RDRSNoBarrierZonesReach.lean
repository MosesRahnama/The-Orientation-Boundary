import OperatorKO7.Meta.RDRSNoBarrierZones

/-!
# Reach tests for the RDRS T6 no-barrier layer.
-/

namespace OperatorKO7.RDRSNoBarrierZones

#check rdrs_type_computability_no_barrier_zones_closed
#check typeComputabilityRows_complete
#check rowStatus_terminal
#check simple_typed_direct_barrier_survives

theorem reach_marker :
    TypeComputabilityNoBarrierZonesClosed :=
  rdrs_type_computability_no_barrier_zones_closed

theorem reach_row_count :
    typeComputabilityRows.length = 20 :=
  typeComputabilityRows_length

theorem reach_bc_minus_typing_layer :
    rowReason .bellantoniCookMinus = .typingLayerBarrier :=
  bc_minus_row_reason

theorem reach_lfpl_typing_layer :
    rowReason .lfpl = .typingLayerBarrier :=
  lfpl_row_reason

theorem reach_ramified_typing_layer :
    rowReason .ramifiedRecursion = .typingLayerBarrier :=
  ramified_recursion_row_reason

end OperatorKO7.RDRSNoBarrierZones
