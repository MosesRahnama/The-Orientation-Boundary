import OperatorKO7.Meta.UniqueNormalization.GlobalUNFailure

set_option autoImplicit false

open OperatorKO7.Meta.UniqueNormalization.GlobalFailure

#check @GlobalUNFailure
#check @GlobalUNFailure.mk
#check @GlobalUNFailure.left
#check @GlobalUNFailure.right
#check @GlobalUNFailure.leftNormal
#check @GlobalUNFailure.rightNormal
#check @GlobalUNFailure.convertible
#check @GlobalUNFailure.distinct
#check @GlobalUNFailure.not_UNconv
#check @GlobalUNFailure.exists_data
#check @not_UNconv_iff_exists_distinct_convertible_normalForms
#check @not_UNconv_iff_nonempty_globalUNFailure
#check @UNconv_iff_no_globalUNFailure
#check @no_globalUNFailure_of_UNconv
#check ko7DiagonalFailure
#check ko7_not_UNconv_via_globalFailure
#check ko7_globalFailure_nonempty
#check ko7_not_UNconv_iff_failureObject

#print axioms GlobalUNFailure
#print axioms GlobalUNFailure.mk
#print axioms GlobalUNFailure.left
#print axioms GlobalUNFailure.right
#print axioms GlobalUNFailure.leftNormal
#print axioms GlobalUNFailure.rightNormal
#print axioms GlobalUNFailure.convertible
#print axioms GlobalUNFailure.distinct
#print axioms GlobalUNFailure.not_UNconv
#print axioms GlobalUNFailure.exists_data
#print axioms not_UNconv_iff_exists_distinct_convertible_normalForms
#print axioms not_UNconv_iff_nonempty_globalUNFailure
#print axioms UNconv_iff_no_globalUNFailure
#print axioms no_globalUNFailure_of_UNconv
#print axioms ko7DiagonalFailure
#print axioms ko7_not_UNconv_via_globalFailure
#print axioms ko7_globalFailure_nonempty
#print axioms ko7_not_UNconv_iff_failureObject
