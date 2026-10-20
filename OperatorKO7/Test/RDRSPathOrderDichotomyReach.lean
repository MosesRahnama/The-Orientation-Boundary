import OperatorKO7.Meta.RDRSPathOrderDichotomy

/-!
# Reach tests for `Meta/RDRSPathOrderDichotomy.lean`

Smoke checks for the T2 finite path-order classification marker and its
supporting theorem surfaces.
-/

namespace OperatorKO7.RDRSPathOrderDichotomy

#check @pathOrderAtlasRows
#check @pathOrderAtlasRows_length
#check @pathOrderAtlasRows_nodup
#check @pathOrderAtlasRows_complete

#check @pathOrderClassifications
#check @pathOrderClassifications_families
#check @pathOrderClassifications_length
#check @pathOrderClassification_status_matches

#check @KBOBarrierVariant
#check @kboBarrierVariant_status
#check @kboBarrierVariant_no_symbolic_orientation

#check @SubtermCoefficientKBOHypotheses
#check @subtermCoefficientKBOHypotheses_not_from_weighted_counts
#print axioms subtermCoefficientKBOHypotheses_not_from_weighted_counts
#check @subtermCoefficientKBO_no_weighted_orientation
#print axioms subtermCoefficientKBO_no_weighted_orientation
#check @subtermCoefficientKBO_carrier_blocked
#print axioms subtermCoefficientKBO_carrier_blocked
#check @subtermCoefficientKBO_barrier
#print axioms subtermCoefficientKBO_barrier

#check @HeadPrecedencePathOrder
#check @HeadPrecedenceHypotheses
#check @HeadPrecedenceRouteAvailable
#check @headPrecedencePathOrder_conditional_escape
#check @mpo_good_precedence_orients_step
#check @mpo_bad_precedence_blocks_global_orientation

#check @ACRPOCase
#check @acRPO_shared_row_status
#check @RPOPermutationHypotheses
#check @rpoModuloPermutation_conditional_escape

#check @POPStarVariant
#check @POPStarSafeArgumentHypotheses
#check @popStarFamily_safe_duplication_barrier

#check @OrdinalCichonCaveat
#check @simpleTerminationOrderType_conditional_barrier
#check @cichonSlowGrowing_conditional_escape
#check @cichon_principle_not_universal

#check @PathOrderLayerClosed
#check @rdrs_path_order_layer_closed

end OperatorKO7.RDRSPathOrderDichotomy
