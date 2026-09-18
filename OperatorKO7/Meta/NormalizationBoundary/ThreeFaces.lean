import OperatorKO7.Meta.NormalizationBoundary.ErasureFiber
import OperatorKO7.Meta.NormalizationBoundary.NormalizationLicense

set_option autoImplicit false

/-!
# Three faces of one substitution-invariance root

`Meta/DistinctionBoundary/SharedRoot.lean` proves that the orientation-axis and
confluence-axis non-derivabilities are two inhabitants of one abstract
`SubstitutionInvariantObstruction`, under the headline
`two_nonderivabilities_share_one_root`.  `NormalizationLicense.lean` then builds
a third inhabitant, `normalizationObstruction`, without extending that headline,
so the shared-root surface understates what the development already carries.
This module closes that gap.

Two things are proved here.

* `three_faces_share_one_root` extends the two-face headline to three: each axis
  supplies an inhabitant whose collapse identifies a genuinely distinct witness
  pair that its external license separates.

* `normalization_face_is_not_constant_collapse` records what the third face adds
  rather than repeats.  Both existing collapses are constant maps: the
  distinction collapse `evalSigma · · void` is constant by `evalSigma_void`, and
  the orientation collapse `dpCollapseToVoid` is `fun _ => void` by definition.
  The normalization collapse is not constant (`ErasureFiber.normalForm_not_constant`).
  The abstraction is therefore strictly wider than the constant-collapse pattern
  that produced its first two inhabitants, which is what makes it a genuine
  abstraction rather than a restatement of "a constant map identifies
  everything".

The three external licenses remain different predicates: Boolean disequality on
the confluence axis, the dependency-pair counter projection on the orientation
axis, and the history token here.  The unification is at the
substitution-invariance level only, exactly as `SharedRoot.lean` states for the
first two.

Relation: metatheoretic; statements about signature-homomorphic evaluators and
about the collapse map `normalForm`.  Not `Step`, not `SafeStep`, not any
contextual closure, and not a termination, confluence, or normalization theorem
about the kernel relation.
Closure: not applicable.
Strategy: not applicable.
Property: shared-root instance count and collapse classification.
Trust: kernel-only; allowed axioms only.
-/

namespace OperatorKO7.Meta.NormalizationBoundary.ThreeFaces

universe u

open OperatorKO7 Trace
open OperatorKO7.Meta.NormalizationBoundary.AntiNormalizationMap
open OperatorKO7.Meta.NormalizationBoundary.NormalizationLicense
open OperatorKO7.Meta.NormalizationBoundary.ErasureFiber
open OperatorKO7.Meta.DistinctionBoundary.SharedRoot
open OperatorKO7.Meta.SafeStep.SigmaFreeAlgebra
open OperatorKO7.Meta.Recursor.RecursorFreeAlgebra
open OperatorKO7.Meta.Recursor.DPConfessionLicense

/-! ## The two existing collapses are constant -/

/-- The distinction-axis collapse is constant. -/
theorem distinction_collapse_constant (t : SigmaTerm) :
    distinctionObstruction.collapse t = SigmaTerm.void :=
  evalSigma_void t t

/-- The orientation-axis collapse is constant. -/
theorem orientation_collapse_constant (t : RecursorTerm) :
    orientationObstruction.collapse t = RecursorTerm.void := rfl

/-- **The third face is not a constant-collapse instance.**

Proves: constancy of the two existing collapses together with non-constancy of
the normalization collapse.
Does not prove: that the three external licenses are the same predicate; they
are not.
Trust: kernel-only. -/
theorem normalization_face_is_not_constant_collapse :
    (∀ t : SigmaTerm, distinctionObstruction.collapse t = SigmaTerm.void)
      ∧ (∀ t : RecursorTerm, orientationObstruction.collapse t = RecursorTerm.void)
      ∧ ¬ ∃ c : Trace, ∀ t : Trace, normalizationObstruction.collapse t = c :=
  ⟨distinction_collapse_constant, orientation_collapse_constant,
    normalForm_not_constant⟩

/-! ## Licensed recovery is exact -/

/-- **The history token is exact.**  Distinct histories produce distinct
licensed recoveries, so the external token carries precisely the distinction the
collapse destroyed.

Proves: `Function.Injective licensedRecover`.
Trust: kernel-only. -/
theorem licensedRecover_injective : Function.Injective licensedRecover :=
  integrate_delta_injective

/-! ## The headline -/

/-- **`three_faces_share_one_root`.**  The extension of
`two_nonderivabilities_share_one_root` to the normalization axis.

Each of the three axes supplies an inhabitant of the one abstract
`SubstitutionInvariantObstruction`, and for each the collapse identifies a
genuinely distinct witness pair that the external license separates.  The fourth
conjunct records what the third face adds: its collapse is not constant, whereas
the two existing collapses are, so the third instance is not a relabelling of
the pattern that produced the first two.

**Proves:** the collapse-blind / license-sighted core for all three instances,
together with the constant-versus-non-constant separation.
**Does not prove:** that the three external licenses agree.  They do not.  It
also proves no SN, confluence, or normalization statement about the kernel
relation.
**Relation:** metatheoretic; see the module header.
**Trust:** kernel-only. -/
theorem three_faces_share_one_root :
    (distinctionObstruction.collapse distinctionObstruction.a
        = distinctionObstruction.collapse distinctionObstruction.b
      ∧ distinctionObstruction.license distinctionObstruction.a
        ≠ distinctionObstruction.license distinctionObstruction.b)
    ∧ (orientationObstruction.collapse orientationObstruction.a
        = orientationObstruction.collapse orientationObstruction.b
      ∧ orientationObstruction.license orientationObstruction.a
        ≠ orientationObstruction.license orientationObstruction.b)
    ∧ (normalizationObstruction.collapse normalizationObstruction.a
        = normalizationObstruction.collapse normalizationObstruction.b
      ∧ normalizationObstruction.license normalizationObstruction.a
        ≠ normalizationObstruction.license normalizationObstruction.b)
    ∧ ¬ ∃ c : Trace, ∀ t : Trace, normalizationObstruction.collapse t = c :=
  ⟨distinctionObstruction.collapse_blind_license_sighted,
   orientationObstruction.collapse_blind_license_sighted,
   normalizationObstruction.collapse_blind_license_sighted,
   normalForm_not_constant⟩

/-- **The normalization face, with its cost law.**  The irreversibility face of
`NormalizationLicense.lean` together with the two quantitative facts of
`ErasureFiber.lean`: the erased fiber is infinite, and no finite token separates
it.

Proves: the conjunction of the four irreversibility clauses with fiber
infinitude and the finite-token impossibility.
Trust: kernel-only. -/
theorem normalization_face_has_unbounded_erasure :
    IrreversibilityFace
      ∧ Infinite ErasedFiber
      ∧ (∀ (k : Nat) (tok : ErasedFiber → Fin k), ¬ Function.Injective tok) :=
  ⟨normalization_boundary_is_irreversibility_face, erasedFiberInfinite,
    no_finite_token_separates_erased_history⟩

/-- The normalization face requires an infinite carrier for every injective recovery token, not
merely for tokens presented as `Fin k`. -/
theorem normalization_face_exact_token_is_infinite
    {Token : Type u} (tok : ErasedFiber → Token) (hinj : Function.Injective tok) :
    Infinite Token :=
  exact_erasure_token_carrier_infinite tok hinj

#print axioms distinction_collapse_constant
#print axioms orientation_collapse_constant
#print axioms normalization_face_is_not_constant_collapse
#print axioms licensedRecover_injective
#print axioms three_faces_share_one_root
#print axioms normalization_face_has_unbounded_erasure
#print axioms normalization_face_exact_token_is_infinite

end OperatorKO7.Meta.NormalizationBoundary.ThreeFaces
