import OperatorKO7.Meta.Recursor.TraceConservation

/-!
Reach check for `Meta/Recursor/TraceConservation.lean`: every public declaration is
elaborated and its axiom inventory printed.
-/

set_option autoImplicit false

namespace OperatorKO7.Test.TraceConservationReach

open OperatorKO7.Meta.Recursor.TraceConservation

#check @affineCoordinate
#check @ConservedAlong
#check @affineCoordinate_step
#check @conservedAlong_iff
#check @conservedAlong_iff_zeroDepth_or_balance
#check @ctrWraps_conserved
#check @payMinusWraps_conserved
#check @ctrWraps_value
#check @payMinusWraps_value
#check @conserved_decomposition
#check @basis_independent
#check @ctr_not_conserved
#check @pay_not_conserved

#print axioms affineCoordinate
#print axioms ConservedAlong
#print axioms affineCoordinate_step
#print axioms conservedAlong_iff
#print axioms conservedAlong_iff_zeroDepth_or_balance
#print axioms ctrWraps_conserved
#print axioms payMinusWraps_conserved
#print axioms ctrWraps_value
#print axioms payMinusWraps_value
#print axioms conserved_decomposition
#print axioms basis_independent
#print axioms ctr_not_conserved
#print axioms pay_not_conserved

/-! ## Full affine coefficients and their trace observations -/

#check @fullAffineCoordinate
#print axioms fullAffineCoordinate
#check @FullAffineConservedAlong
#print axioms FullAffineConservedAlong
#check @FullAffineConservedEverywhere
#print axioms FullAffineConservedEverywhere
#check @fullAffineCoordinate_step
#print axioms fullAffineCoordinate_step
#check @fullAffineConservedAlong_iff_linear
#print axioms fullAffineConservedAlong_iff_linear
#check @fullAffineConservedAlong_iff
#print axioms fullAffineConservedAlong_iff
#check @fullAffineConservedEverywhere_iff
#print axioms fullAffineConservedEverywhere_iff
#check @fullAffineCoordinate_normalForm
#print axioms fullAffineCoordinate_normalForm
#check @fullAffine_conservation_parameterization
#print axioms fullAffine_conservation_parameterization
#check @TraceEquivalent
#print axioms TraceEquivalent
#check @traceEquivalent_iff
#print axioms traceEquivalent_iff
#check @traceEquivalent_iff_offsetShift
#print axioms traceEquivalent_iff_offsetShift
#check @fullAffine_observation_parameterization
#print axioms fullAffine_observation_parameterization
#check @fullAffine_conserved_observation_parameterization
#print axioms fullAffine_conserved_observation_parameterization
#check @conserved_trace_equivalence_iff
#print axioms conserved_trace_equivalence_iff
#check @nonzero_coefficient_zero_reading
#print axioms nonzero_coefficient_zero_reading
#check @constantOffset_conserved
#print axioms constantOffset_conserved
#check @constantOffset_value
#print axioms constantOffset_value
#check @offset_cannot_conserve_counter
#print axioms offset_cannot_conserve_counter

example (a b c d : Int) (k : Nat) :
    FullAffineConservedAlong a b c d k ↔ k = 0 ∨ a = b + c :=
  fullAffineConservedAlong_iff a b c d k

example (a b c d a' b' c' d' : Int) :
    TraceEquivalent a b c d a' b' c' d' ↔
      ∃ z : Int, a' = a ∧ b' = b + z ∧ c' = c - z ∧ d' = d - z :=
  traceEquivalent_iff_offsetShift a b c d a' b' c' d'

example : fullAffineCoordinate 0 1 (-1) (-1) 4 2 = 0 :=
  nonzero_coefficient_zero_reading.2 4 2

example : FullAffineConservedAlong 1 0 0 7 0 :=
  (fullAffineConservedAlong_iff 1 0 0 7 0).2 (Or.inl rfl)

example : ¬ FullAffineConservedAlong 1 0 0 7 4 :=
  offset_cannot_conserve_counter 7 (by decide)

end OperatorKO7.Test.TraceConservationReach
