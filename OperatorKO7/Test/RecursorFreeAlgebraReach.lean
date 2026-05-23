import OperatorKO7.Meta.Recursor.RecursorFreeAlgebra
import OperatorKO7.Meta.Recursor.DPConfessionLicenseUnconditional

/-!
Lane R reach test: confirms the theorem names resolve
through the Lean type-check level. Mirrors the shape used by every
other `Test/*Reach.lean` file in the OperatorKO7 tree.
-/

open OperatorKO7.Meta.Recursor.RecursorFreeAlgebra
open OperatorKO7.Meta.Recursor.DPConfessionLicenseUnconditional

#check @RecursorTerm.fold
#check @RecursorTerm.fold_isSigmaHomomorphism
#check @IsSigmaHomomorphism
#check @SigmaAlgebra
#check @RecursorFreeAlgebra.substitution_invariance
#check @DpCollapseToVoidSigma
#check @RecursorTerm.fold_DpCollapseToVoidSigma_eq_dpCollapseToVoid
#check @FactorsThroughCollapse
#check @factorsThroughCollapse_of_constantSigmaHomomorphism
#check @factorsThroughCollapse_no_distinguishing
#check @witnessLeft
#check @witnessRight
#check @witnessLeft_ne_witnessRight
#check @RecRConstantInThird
#check @dp_projection_not_in_recursor_signature_unconditional
#check @dp_projection_not_in_recursor_signature_corollary
#check @recursor_orbit_mass_indistinguishable_of_direct_measure_normalization
#check @recursor_termination_provable_iff_external_DP_license_accepted_unconditional
#check @recursor_orbit_mass_indistinguishable_unconditional_anchor
#check @commercial_claim_status_unconditional_anchor
