import OperatorKO7.Meta.UniqueNormalization.DecreasingDiagrams

set_option autoImplicit false

open OperatorKO7.Meta.UniqueNormalization

#check @MeasuredJoin.mirror
#check @MeasuredJoin.of_left_refl
#check @MeasuredJoin.of_right_refl
#check @peakMeasureLt_restore_right_suffix
#check @allPeaksMeasured
#check @UnlabelledConfluent
#check @allLocalPeaksDecreasing_confluent

#print axioms OperatorKO7.Meta.UniqueNormalization.MeasuredJoin.mirror
#print axioms OperatorKO7.Meta.UniqueNormalization.MeasuredJoin.of_left_refl
#print axioms OperatorKO7.Meta.UniqueNormalization.MeasuredJoin.of_right_refl
#print axioms OperatorKO7.Meta.UniqueNormalization.peakMeasureLt_restore_right_suffix
#print axioms OperatorKO7.Meta.UniqueNormalization.allPeaksMeasured
#print axioms OperatorKO7.Meta.UniqueNormalization.UnlabelledConfluent
#print axioms OperatorKO7.Meta.UniqueNormalization.allLocalPeaksDecreasing_confluent
