import OperatorKO7.Meta.DistinctionBoundary.DPChannelInstance

/-!
# Reach and axiom gate for DPChannelInstance (Roadmap 09, F2)

Pins every public declaration of
`Meta/DistinctionBoundary/DPChannelInstance.lean`. Each `#check` is paired
with `#print axioms`.
-/

set_option autoImplicit false

open OperatorKO7.Meta.DistinctionBoundary.DPChannelInstance

-- Induced extraction
#check @OperatorKO7.Meta.DistinctionBoundary.DPChannelInstance.extractRecSuccDP
#print axioms OperatorKO7.Meta.DistinctionBoundary.DPChannelInstance.extractRecSuccDP
#check @OperatorKO7.Meta.DistinctionBoundary.DPChannelInstance.extractRecSuccDP_certified
#print axioms OperatorKO7.Meta.DistinctionBoundary.DPChannelInstance.extractRecSuccDP_certified
#check @OperatorKO7.Meta.DistinctionBoundary.DPChannelInstance.step_ne_extracted
#print axioms OperatorKO7.Meta.DistinctionBoundary.DPChannelInstance.step_ne_extracted

-- Encoding of the R_rec_succ reduct
#check @OperatorKO7.Meta.DistinctionBoundary.DPChannelInstance.encodeFrame
#print axioms OperatorKO7.Meta.DistinctionBoundary.DPChannelInstance.encodeFrame
#check @OperatorKO7.Meta.DistinctionBoundary.DPChannelInstance.encodeActive
#print axioms OperatorKO7.Meta.DistinctionBoundary.DPChannelInstance.encodeActive
#check @OperatorKO7.Meta.DistinctionBoundary.DPChannelInstance.encodedTerm
#print axioms OperatorKO7.Meta.DistinctionBoundary.DPChannelInstance.encodedTerm
#check @OperatorKO7.Meta.DistinctionBoundary.DPChannelInstance.encodedTerm_frame
#print axioms OperatorKO7.Meta.DistinctionBoundary.DPChannelInstance.encodedTerm_frame
#check @OperatorKO7.Meta.DistinctionBoundary.DPChannelInstance.encodedTerm_active
#print axioms OperatorKO7.Meta.DistinctionBoundary.DPChannelInstance.encodedTerm_active

-- Channel and crown
#check @OperatorKO7.Meta.DistinctionBoundary.DPChannelInstance.actualDPChannel
#print axioms OperatorKO7.Meta.DistinctionBoundary.DPChannelInstance.actualDPChannel
#check @OperatorKO7.Meta.DistinctionBoundary.DPChannelInstance.decodeActive
#print axioms OperatorKO7.Meta.DistinctionBoundary.DPChannelInstance.decodeActive
#check @OperatorKO7.Meta.DistinctionBoundary.DPChannelInstance.actualDPChannel_decodes_isActive
#print axioms OperatorKO7.Meta.DistinctionBoundary.DPChannelInstance.actualDPChannel_decodes_isActive
#check @OperatorKO7.Meta.DistinctionBoundary.DPChannelInstance.actual_dp_license_is_exogenous_separator
#print axioms OperatorKO7.Meta.DistinctionBoundary.DPChannelInstance.actual_dp_license_is_exogenous_separator
#check @OperatorKO7.Meta.DistinctionBoundary.DPChannelInstance.actual_dp_license_not_value_factored
#print axioms OperatorKO7.Meta.DistinctionBoundary.DPChannelInstance.actual_dp_license_not_value_factored

-- R5 encoded instance b = s = n = void
#check @OperatorKO7.Meta.DistinctionBoundary.DPChannelInstance.r5_frame_not_selected
#print axioms OperatorKO7.Meta.DistinctionBoundary.DPChannelInstance.r5_frame_not_selected
#check @OperatorKO7.Meta.DistinctionBoundary.DPChannelInstance.r5_active_selected
#print axioms OperatorKO7.Meta.DistinctionBoundary.DPChannelInstance.r5_active_selected
#check @OperatorKO7.Meta.DistinctionBoundary.DPChannelInstance.r5_crown
#print axioms OperatorKO7.Meta.DistinctionBoundary.DPChannelInstance.r5_crown
