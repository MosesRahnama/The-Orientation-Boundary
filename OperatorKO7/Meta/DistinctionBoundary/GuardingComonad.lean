import OperatorKO7.Meta.DistinctionBoundary.SemanticsPreservingMaximality

set_option autoImplicit false

/-!
# The guarding comonad: SafeStep as a coreflective interior operator

Section 16 of the manuscript proves a finite axis-duality functor on obstruction and
license descriptors and records that the descriptor connection is degenerate, so the
descriptor maps are mutually inverse and carry only the identity monad. The genuine
comonad in the development lives on the lattice of kernel subrelations.

Define the guarding operator `guard R = SafeStep ∩ R`. It is an idempotent interior
operator, the order dual of a closure operator, hence an idempotent comonad on the
preorder of relations ordered by inclusion. Its counit is the deflationary inclusion
`guard R ⊆ R` (`guard_counit`), its comultiplication is `guard R ⊆ guard (guard R)`
(`guard_comultiplication`), its value at the full kernel relation `Step` is exactly
`SafeStep` (`guard_step_eq_safeStep`), its fixed points are exactly the subrelations
of `SafeStep` (`guard_fixed_iff_le_safeStep`), and that coreflection value is the
maximal semantics-preserving repair (`safeStep_is_maximal_semantics_preserving_repair`).
The operator strictly refines the kernel (`guard_strictly_refines_kernel`), so the
comonad is nontrivial.

This supplies the counit and comultiplication data whose absence the descriptor result
records, locating the genuine comonad on the guard rather than on the finite descriptors.

Audit notes (LASOT):
* Object: the operator `guard` on `Trace -> Trace -> Prop`.
* Property: deflationary, monotone, idempotent, an interior operator and idempotent
  comonad, with coreflection value `SafeStep` and fixed points the safe subrelations.
* No `sorry`, `admit`, `axiom`, `native_decide`, `bv_decide`, `@[csimp]`, `unsafe`,
  `partial`, or `opaque`.
-/

open OperatorKO7
open OperatorKO7.Trace
open MetaSN_KO7

namespace OperatorKO7.Meta.DistinctionBoundary.GuardingComonad

/-- The guarding operator: keep exactly the branches that are both safe and in `R`. -/
def guard (R : Trace -> Trace -> Prop) : Trace -> Trace -> Prop :=
  fun a b => SafeStep a b ∧ R a b

/-- Counit: guarding is deflationary, every guarded branch is a branch of `R`. -/
theorem guard_counit {R : Trace -> Trace -> Prop} {a b : Trace}
    (h : guard R a b) : R a b := h.2

/-- Every guarded branch is a safe branch. -/
theorem guard_le_safeStep {R : Trace -> Trace -> Prop} {a b : Trace}
    (h : guard R a b) : SafeStep a b := h.1

/-- Monotone in the guarded relation. -/
theorem guard_monotone {R R' : Trace -> Trace -> Prop}
    (hsub : ∀ a b, R a b -> R' a b) {a b : Trace}
    (h : guard R a b) : guard R' a b :=
  ⟨h.1, hsub a b h.2⟩

/-- Comultiplication: every guarded branch is a guarded guarded branch. -/
theorem guard_comultiplication {R : Trace -> Trace -> Prop} {a b : Trace}
    (h : guard R a b) : guard (guard R) a b := ⟨h.1, h⟩

/-- Idempotence as a biconditional. -/
theorem guard_idempotent (R : Trace -> Trace -> Prop) (a b : Trace) :
    guard (guard R) a b ↔ guard R a b :=
  ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, h⟩⟩

/-- The interior-operator interface on relations, the idempotent comonad on kernel
subrelations ordered by inclusion. -/
structure IdempotentInterior
    (G : (Trace -> Trace -> Prop) -> Trace -> Trace -> Prop) : Prop where
  deflationary : ∀ R a b, G R a b -> R a b
  monotone : ∀ R R', (∀ a b, R a b -> R' a b) -> ∀ a b, G R a b -> G R' a b
  idempotent : ∀ R a b, G (G R) a b ↔ G R a b

/-- `guard` is an idempotent interior operator, the comonad on kernel subrelations. -/
theorem guarding_is_idempotent_interior : IdempotentInterior guard where
  deflationary := fun _ _ _ h => h.2
  monotone := fun _ _ hsub _ _ h => ⟨h.1, hsub _ _ h.2⟩
  idempotent := guard_idempotent

/-- The coreflection value at the full kernel relation is exactly `SafeStep`. -/
theorem guard_step_eq_safeStep (a b : Trace) :
    guard Step a b ↔ SafeStep a b :=
  ⟨fun h => h.1, fun hs => ⟨hs, safeStep_to_step hs⟩⟩

/-- Fixed points of the comonad are exactly the subrelations of `SafeStep`. -/
theorem guard_fixed_iff_le_safeStep (R : Trace -> Trace -> Prop) :
    (∀ a b, guard R a b ↔ R a b) ↔ (∀ a b, R a b -> SafeStep a b) := by
  constructor
  · intro h a b hr
    exact ((h a b).mpr hr).1
  · intro hle a b
    exact ⟨fun h => h.2, fun hr => ⟨hle a b hr, hr⟩⟩

/-- The comonad is nontrivial: it strictly refines the kernel by refusing the
diagonal difference branch that `Step` admits. -/
theorem guard_strictly_refines_kernel :
    Step (eqW void void) (integrate (merge void void))
      ∧ ¬ guard Step (eqW void void) (integrate (merge void void)) :=
  ⟨Step.R_eq_diff void void,
    fun h => safeStep_semanticsPreservingSafeSubrel.eq_diff_diagonal_guard void h.1⟩

/-- Headline: the guarding comonad is an idempotent interior operator, its value at the
kernel relation is `SafeStep`, and that value is the maximal semantics-preserving
repair. -/
theorem guarding_comonad_value_is_maximal_repair :
    IdempotentInterior guard
      ∧ (∀ a b, guard Step a b ↔ SafeStep a b)
      ∧ SemanticsPreservingSafeSubrel SafeStep
      ∧ ∀ {R : Trace -> Trace -> Prop},
          SemanticsPreservingSafeSubrel R -> ∀ {a b}, R a b -> SafeStep a b :=
  ⟨guarding_is_idempotent_interior,
    guard_step_eq_safeStep,
    safeStep_semanticsPreservingSafeSubrel,
    fun H => semantics_preserving_subrel_subset_safestep H⟩

#print axioms guarding_is_idempotent_interior
#print axioms guard_step_eq_safeStep
#print axioms guard_fixed_iff_le_safeStep
#print axioms guard_strictly_refines_kernel
#print axioms guarding_comonad_value_is_maximal_repair

end OperatorKO7.Meta.DistinctionBoundary.GuardingComonad
