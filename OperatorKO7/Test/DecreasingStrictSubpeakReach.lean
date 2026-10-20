import OperatorKO7.Meta.UniqueNormalization.DecreasingStrictSubpeak

/-!
# Reach and axiom gate for the route-R2 strict subpeak decrease

Pins every explicit public declaration of
`OperatorKO7/Meta/UniqueNormalization/DecreasingStrictSubpeak.lean`, together
with the constructor and projections of `InductiveLocalJoin`, and reports the
axiom closure of each. Baseline axioms only.
-/

open OperatorKO7.Meta.UniqueNormalization

#check @OperatorKO7.Meta.UniqueNormalization.belowPart
#check @OperatorKO7.Meta.UniqueNormalization.belowPart_add_removeBelow
#check @OperatorKO7.Meta.UniqueNormalization.removeBelow_lexMax_eq_zero_of_allBelow
#check @OperatorKO7.Meta.UniqueNormalization.lexMax_low_append_peak_low
#check @OperatorKO7.Meta.UniqueNormalization.allBelowEither_low_append
#check @OperatorKO7.Meta.UniqueNormalization.allBelowEither_low_peak_low_of_peak_lt
#check @OperatorKO7.Meta.UniqueNormalization.allBelow_b_of_not_below
#check @OperatorKO7.Meta.UniqueNormalization.strict_subpeak_of_allBelowEither
#check @OperatorKO7.Meta.UniqueNormalization.strict_subpeak_of_surviving_peak
#check @OperatorKO7.Meta.UniqueNormalization.local_left_subpeak_strict
#check @OperatorKO7.Meta.UniqueNormalization.local_right_subpeak_strict
#check @OperatorKO7.Meta.UniqueNormalization.InductiveLocalJoin
#check @OperatorKO7.Meta.UniqueNormalization.InductiveLocalJoin.mk
#check @OperatorKO7.Meta.UniqueNormalization.InductiveLocalJoin.toMeasuredJoin
#check @OperatorKO7.Meta.UniqueNormalization.InductiveLocalJoin.leftStrict
#check @OperatorKO7.Meta.UniqueNormalization.InductiveLocalJoin.rightStrict
#check @OperatorKO7.Meta.UniqueNormalization.LocalPeak.inductiveLocalJoin_of_decreasing

#print axioms OperatorKO7.Meta.UniqueNormalization.belowPart
#print axioms OperatorKO7.Meta.UniqueNormalization.belowPart_add_removeBelow
#print axioms OperatorKO7.Meta.UniqueNormalization.removeBelow_lexMax_eq_zero_of_allBelow
#print axioms OperatorKO7.Meta.UniqueNormalization.lexMax_low_append_peak_low
#print axioms OperatorKO7.Meta.UniqueNormalization.allBelowEither_low_append
#print axioms OperatorKO7.Meta.UniqueNormalization.allBelowEither_low_peak_low_of_peak_lt
#print axioms OperatorKO7.Meta.UniqueNormalization.allBelow_b_of_not_below
#print axioms OperatorKO7.Meta.UniqueNormalization.strict_subpeak_of_allBelowEither
#print axioms OperatorKO7.Meta.UniqueNormalization.strict_subpeak_of_surviving_peak
#print axioms OperatorKO7.Meta.UniqueNormalization.local_left_subpeak_strict
#print axioms OperatorKO7.Meta.UniqueNormalization.local_right_subpeak_strict
#print axioms OperatorKO7.Meta.UniqueNormalization.InductiveLocalJoin
#print axioms OperatorKO7.Meta.UniqueNormalization.InductiveLocalJoin.mk
#print axioms OperatorKO7.Meta.UniqueNormalization.InductiveLocalJoin.toMeasuredJoin
#print axioms OperatorKO7.Meta.UniqueNormalization.InductiveLocalJoin.leftStrict
#print axioms OperatorKO7.Meta.UniqueNormalization.InductiveLocalJoin.rightStrict
#print axioms OperatorKO7.Meta.UniqueNormalization.LocalPeak.inductiveLocalJoin_of_decreasing
