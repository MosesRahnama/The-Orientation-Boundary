import OperatorKO7.Meta.NormalizationBoundary.ErasureFiber

/-!
# Reach and axiom gate: `Meta/NormalizationBoundary/ErasureFiber.lean`

Every explicit public declaration of the owned module carries a paired `#check`
and `#print axioms` here, so the source-to-reach and reach-to-axiom differences
are both empty (LASOT Gate Q24, section 18.2).

This gate carries no mathematical content of its own.  It is evidence that each
declaration exists with the stated type and that its axiom closure lies inside
the baseline whitelist, and it is separate evidence from the theorem being the
intended one.
-/

open OperatorKO7.Meta.NormalizationBoundary.ErasureFiber

#check @deltaPow
#print axioms deltaPow

#check @deltaHeight
#print axioms deltaHeight

#check @deltaHeight_deltaPow
#print axioms deltaHeight_deltaPow

#check @deltaPow_injective
#print axioms deltaPow_injective

#check @integrate_delta_injective
#print axioms integrate_delta_injective

#check @erasedHistory
#print axioms erasedHistory

#check @erasedHistory_normalForm
#print axioms erasedHistory_normalForm

#check @erasedHistory_injective
#print axioms erasedHistory_injective

#check @ErasedFiber
#print axioms ErasedFiber

#check @erasedPoint
#print axioms erasedPoint

#check @erasedPoint_injective
#print axioms erasedPoint_injective

#check @erasedFiberInfinite
#print axioms erasedFiberInfinite

#check @no_finite_token_separates_erased_history
#print axioms no_finite_token_separates_erased_history
#check @no_finite_type_token_separates_erased_history
#print axioms no_finite_type_token_separates_erased_history
#check @exact_erasure_token_carrier_infinite
#print axioms exact_erasure_token_carrier_infinite

#check @normalForm_void
#print axioms normalForm_void

#check @normalForm_delta_void
#print axioms normalForm_delta_void

#check @normalForm_not_constant
#print axioms normalForm_not_constant

#check @normalization_redex_is_not_recursor_redex
#print axioms normalization_redex_is_not_recursor_redex

#check @normalization_redex_is_not_eqW_diagonal
#print axioms normalization_redex_is_not_eqW_diagonal

#check @normalization_erasure_is_unbounded
#print axioms normalization_erasure_is_unbounded
