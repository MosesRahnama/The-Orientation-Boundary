import OperatorKO7.Meta.UniqueNormalization.Section7FinalInterface

set_option autoImplicit false

open OperatorKO7.Meta.UniqueNormalization
open OperatorKO7.Meta.Rewriting

/-! Reach file for the closeout interface. Every public declaration of
`Section7FinalInterface.lean` is checked, and every theorem's axiom footprint is
printed. The interface declares the missing theorem; these checks confirm the
chain from the missing theorem to the final conclusion elaborates and stays
inside the approved axiom baseline. -/

#check @FiniteCarrierDownTransitive
#check @Section7TranslationDownOnTrans
#check @Section7FiniteTargetedModels
#check @down_transitive_of_finiteCarrierDownTransitive
#check @finiteCarrierDownTransitive_of_finiteTargetedModels
#check @Section7TranslationDownOnTrans.of_finiteTargetedModels
#check @htrans_of_section7TranslationDownOnTrans
#check @UNconv_of_section7TranslationDownOnTrans
#check @UNred_of_section7TranslationDownOnTrans
#check @UNconv_of_section7FiniteTargetedModels
#check @downOn_threeFold_iff_transitive

#print axioms FiniteCarrierDownTransitive
#print axioms Section7TranslationDownOnTrans
#print axioms Section7FiniteTargetedModels
#print axioms down_transitive_of_finiteCarrierDownTransitive
#print axioms finiteCarrierDownTransitive_of_finiteTargetedModels
#print axioms Section7TranslationDownOnTrans.of_finiteTargetedModels
#print axioms htrans_of_section7TranslationDownOnTrans
#print axioms UNconv_of_section7TranslationDownOnTrans
#print axioms UNred_of_section7TranslationDownOnTrans
#print axioms UNconv_of_section7FiniteTargetedModels
#print axioms downOn_threeFold_iff_transitive

/-! ## The consumed steps of the chain, pinned -/

#check @Coalgebra
#check @DownOn
#check @Down
#check @Down.trans_of_finite_coalgebras
#check @conv_eq_down
#check @constructorCompatible_conv_of_down_trans
#check @down_transitive_of_finite_complete_targeted_root_models
#check @UNconv_of_section7
#check @UNred_of_section7

#print axioms Down.trans_of_finite_coalgebras
#print axioms conv_eq_down
#print axioms constructorCompatible_conv_of_down_trans
#print axioms down_transitive_of_finite_complete_targeted_root_models
#print axioms UNconv_of_section7
#print axioms UNred_of_section7
