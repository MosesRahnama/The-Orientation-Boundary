import OperatorKO7.Meta.Recursor.RaryDuplicator

/-! Reach gate for the quantitative laws of Operational Inexpressibility. -/

set_option autoImplicit false

namespace OperatorKO7.Test.QuantLawsReach

open OperatorKO7.Meta.Recursor.SchemaTraceKernel
open OperatorKO7.Meta.Recursor.TraceInvariants
open OperatorKO7.Meta.Recursor.TraceAction
open OperatorKO7.Meta.Recursor.GaugeCost
open OperatorKO7.Meta.Recursor.RaryDuplicator

#check @orbit_step
#check @orbit_unique_redex
#check @orbit_terminal_normal
#check @wsize_closed_form
#check @countG_closed_form
#check @countPay_closed_form
#check @ctr_closed_form

#check @L1_exact_length
#check @L1_length_unique
#check @L1_payload_blind
#check @L2_mass_rate
#check @L2_terminal_drop
#check @L5_crossover_holds
#check @L5_crossover_minimal
#check @L5_fraction
#check @L6_step_budget
#check @L6_offset
#check @L7_sufficient_statistic
#check @L7_sufficient_statistic_unique
#check @L11_orbit_injective
#check @L11_carrier_dimension

#check @L3_action_syntactic
#check @L3_action_closed
#check @L3_action_bridge
#check @L3_second_quadratic_invariant
#check @L4_partition_identity
#check @L4_fraction_envelope
#check @L4_manuscript_con
#check @L4_dominance_ratio

#check @L8_bitcost_exact
#check @L8_bitcost_lower
#check @L8_projection_comparison
#check @L9_decode_correct
#check @L9_terminal_injective
#check @L9_zero_depth_payload_absent
#check @L9_zero_bit_confession

#check @L10_trace_law_r
#check @L10_runtime_r_blind
#check @L10_runtime_unique
#check @L10_con_r_closed
#check @L10_scaling_envelope
#check @L10_gauge_r
#check @Architectural.L10_architectural_r

example :
    wsize 2 2 1 1 1 (orbitState (.base 0) (.pay 1) 3 0) = 9 := by decide
example :
    wsize 2 2 1 1 1 (orbitState (.base 0) (.pay 1) 3 1) = 11 := by decide
example :
    wsize 2 2 1 1 1 (orbitState (.base 0) (.pay 1) 3 2) = 13 := by decide
example :
    wsize 2 2 1 1 1 (orbitState (.base 0) (.pay 1) 3 3) = 15 := by decide
example :
    wsize 2 2 1 1 1 (orbitState (.base 0) (.pay 1) 3 4) = 11 := by decide
example : traceAction 3 3 6 = 48 := by decide
example : conMassCell 3 3 = 18 := by decide
example :
    3 * (2 * traceAction 3 3 6) =
      4 * (2 * conMassCell 3 3) + 2 * 3 * 4 * 6 := by decide
example : conMassPayManuscript 3 2 = 20 := by decide
example : istar 3 6 3 = 3 := by decide
example : bitCost 1 3 = 3 := by decide
example : bitCost 2 3 = 15 := by decide
example :
    decodeRecord (orbitState (.base 2) (.pay 7) 3 4) = some (2, 7, 3) := by decide
example : conMassR 3 2 2 = 32 := by decide

#print axioms orbit_step
#print axioms orbit_unique_redex
#print axioms orbit_terminal_normal
#print axioms wsize_closed_form
#print axioms countG_closed_form
#print axioms countPay_closed_form
#print axioms ctr_closed_form
#print axioms L1_exact_length
#print axioms L1_length_unique
#print axioms L1_payload_blind
#print axioms L2_mass_rate
#print axioms L2_terminal_drop
#print axioms L5_crossover_holds
#print axioms L5_crossover_minimal
#print axioms L5_fraction
#print axioms L6_step_budget
#print axioms L6_offset
#print axioms L7_sufficient_statistic
#print axioms L7_sufficient_statistic_unique
#print axioms L11_orbit_injective
#print axioms L11_carrier_dimension
#print axioms L3_action_syntactic
#print axioms L3_action_closed
#print axioms L3_action_bridge
#print axioms L3_second_quadratic_invariant
#print axioms L4_partition_identity
#print axioms L4_fraction_envelope
#print axioms L4_manuscript_con
#print axioms L4_dominance_ratio
#print axioms L8_bitcost_exact
#print axioms L8_bitcost_lower
#print axioms L8_projection_comparison
#print axioms L9_decode_correct
#print axioms L9_terminal_injective
#print axioms L9_zero_depth_payload_absent
#print axioms L9_zero_bit_confession
#print axioms L10_trace_law_r
#print axioms L10_runtime_r_blind
#print axioms L10_runtime_unique
#print axioms L10_con_r_closed
#print axioms L10_scaling_envelope
#print axioms L10_gauge_r
#print axioms Architectural.L10_architectural_r

end OperatorKO7.Test.QuantLawsReach
