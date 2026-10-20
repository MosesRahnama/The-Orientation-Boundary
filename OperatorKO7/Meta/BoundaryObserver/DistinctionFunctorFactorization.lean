import OperatorKO7.Meta.SafeStep.DynamicalBoundaryFunctor
import OperatorKO7.Meta.LicensedBoundaryCalculus.Core.CanonicalBoundaryFactorization
import OperatorKO7.Meta.LicensedBoundaryCalculus.Transport.Strength

set_option autoImplicit false

/-!
# The distinction collapse map factored through its kernel

`thm:partial-factorization` of the source manuscript applied to the dynamical
distinction boundary functor of Informational Incompleteness (`thm:dyn-boundary-functor`, ledger
row 09-054). The functor `SafeStep.DynamicalBoundaryFunctor.step_distinction_dynamical_boundary_functor`
sends every trace to the boundary verdict and every kernel `Step` edge to an equality of verdicts.
As a licensed reduction morphism from the raw KO7 dynamics to the verdict carrier with equality as
its step, it factors as restriction, admitted edges, quotient by its kernel, bijection onto its
image, and inclusion (`canonical_boundary_factorization_universal_unconditional`). Its kernel
identifies every two traces: `void` and `delta void` are a merged pair of the verdict observer, the
nonfaithfulness `distinction_dynamical_functor_not_faithful`, and the kernel quotient is a single
class. The quotient dynamics and the image dynamics are isomorphic (one class with a loop, one
verdict with a loop), the exact case of `thm:exact-dynamic-transport` (iii).

Relation: the raw KO7 root relation `Step` (`ko7RawARS`); the verdict carrier with equality.
Trust: kernel-only; quotient equality uses `Quot.sound`. No `sorry`, `admit`, `axiom`,
`native_decide`.
-/

namespace OperatorKO7.Meta.BoundaryObserver.DistinctionFunctorFactorization

open OperatorKO7 Trace
open OperatorKO7.Meta.LicensedBoundaryCalculus
open OperatorKO7.Meta.LicensedBoundaryCalculus.PartialLicensedReductionMorphism
open OperatorKO7.Meta.SafeStep.DynamicalBoundaryFunctor
open OperatorKO7.Meta.SafeStep.BoundaryDuality

/-- The verdict carrier: boundary verdicts in `Trace`, with equality as the step relation, so a
source transition maps to an unchanged verdict. -/
def verdictARS : ARS where
  Carrier := Trace
  step := fun y y' => y = y'
  scope :=
    { location := .root
      closure := .oneStep
      admission := .full
      layer := .projected }

/-- The verdict of the distinction boundary functor at a trace. -/
noncomputable def distinctionVerdict (t : Trace) : Trace :=
  distinctionBoundaryOperator.apply (step_distinction_dynamical_boundary_functor.mapObj t)
    (step_distinction_dynamical_boundary_functor.mapObj_domain t)

/-- The distinction verdict is the collapse value `void` at every trace. -/
theorem distinctionVerdict_eq_void (t : Trace) : distinctionVerdict t = void := rfl

/-- The distinction boundary functor as a licensed reduction morphism of the raw KO7 dynamics into
the verdict carrier. -/
noncomputable def distinctionVerdictMorphism : LicensedReductionMorphism ko7RawARS verdictARS where
  admitted := Step
  admitted_sub_raw := fun h => h
  map := distinctionVerdict
  map_step := fun h => step_distinction_dynamical_boundary_functor.mapStep h

/-- The partial form of the morphism, with total domain. -/
noncomputable def distinctionPartial : PartialLicensedReductionMorphism ko7RawARS verdictARS :=
  distinctionVerdictMorphism.toPartial

/--
`thm:partial-factorization` at the distinction functor.

Proves: the canonical five-factor composite (domain restriction, admitted edges, quotient by the
kernel, bijection onto the image, inclusion) of the distinction morphism equals the morphism.
Scope: row 09-054. Trust: kernel-only.
-/
theorem distinction_canonical_factorization :
    distinctionPartial.canonicalComposite = distinctionPartial :=
  canonical_boundary_factorization_universal_unconditional _

/--
Proves: the kernel quotient of the distinction morphism identifies every two traces.
Scope: row 09-054. Trust: kernel-only, `Quot.sound`.
-/
theorem distinction_kernel_total (x y : DomainCarrier distinctionPartial) :
    distinctionPartial.kernelProjection x = distinctionPartial.kernelProjection y :=
  (kernelProjection_eq_iff distinctionPartial x y).mpr rfl

/--
Proves: `void` and `delta void` are distinct traces with one kernel class: the merged pair that
`distinction_dynamical_functor_not_faithful` exhibits lies in the kernel of the factorization.
Scope: row 09-054. Trust: kernel-only.
-/
theorem distinction_kernel_merges_void_deltaVoid :
    (void : Trace) ≠ delta void ∧
      distinctionPartial.kernelProjection ⟨void, trivial⟩ =
        distinctionPartial.kernelProjection ⟨delta void, trivial⟩ :=
  ⟨fun h => Trace.noConfusion h, distinction_kernel_total _ _⟩

/-- The kernel quotient of the distinction morphism is a single class. -/
theorem distinction_kernelQuotient_subsingleton :
    Subsingleton (KernelQuotient distinctionPartial) := by
  constructor
  intro a b
  induction a using Quotient.inductionOn with
  | _ x =>
    induction b using Quotient.inductionOn with
    | _ y => exact distinction_kernel_total x y

/-- The image of the distinction morphism is the single verdict `void`. -/
theorem distinction_image_eq :
    ∀ y : ImageCarrier distinctionPartial, y.val = void := by
  rintro ⟨y, ⟨x, rfl⟩⟩
  rfl

/--
Proves: the verdict map is not injective: the distinction functor is not faithful, and its kernel
is a nonempty boundary.
Scope: row 09-054. Trust: kernel-only.
-/
theorem distinctionVerdict_not_injective : ¬ Function.Injective distinctionVerdict := by
  intro h
  exact Trace.noConfusion (h (show distinctionVerdict void = distinctionVerdict (delta void) from rfl))

/--
`thm:exact-dynamic-transport` (iii) at the distinction morphism.

Proves: the bijection from the kernel quotient onto the image is an isomorphism of the quotient
dynamics (direct image of `Step`) with the image dynamics (equality of verdicts): both are one
point with a loop.
Scope: row 09-054. Trust: kernel-only, `Quot.sound`.
-/
noncomputable def distinctionQuotientImageIso :
    TransportStrength.ARSIsomorphism distinctionPartial.kernelQuotientARS
      distinctionPartial.imageARS where
  toEquiv := distinctionPartial.quotientImageEquiv
  step_iff := by
    intro q r
    constructor
    · intro _
      change (distinctionPartial.quotientImageEquiv q).val =
        (distinctionPartial.quotientImageEquiv r).val
      rw [distinction_image_eq, distinction_image_eq]
    · intro _
      have hq : q = distinctionPartial.kernelProjection ⟨eqW void void, trivial⟩ :=
        distinction_kernelQuotient_subsingleton.elim _ _
      have hr : r = distinctionPartial.kernelProjection ⟨void, trivial⟩ :=
        distinction_kernelQuotient_subsingleton.elim _ _
      change ∃ x y : DomainCarrier distinctionPartial,
        distinctionPartial.admitted x.val y.val ∧ distinctionPartial.kernelProjection x = q ∧
          distinctionPartial.kernelProjection y = r
      exact ⟨⟨eqW void void, trivial⟩, ⟨void, trivial⟩, Step.R_eq_refl void, hq.symm, hr.symm⟩

/-- The isomorphism's forward map is the canonical quotient-to-image map. -/
theorem distinctionQuotientImageIso_apply (q : KernelQuotient distinctionPartial) :
    distinctionQuotientImageIso.toEquiv q = distinctionPartial.quotientToImage q := rfl

end OperatorKO7.Meta.BoundaryObserver.DistinctionFunctorFactorization
