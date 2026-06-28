import OperatorKO7.Meta.EqW_Guard_Barrier

set_option autoImplicit false

/-!
# Semantics-preserving maximality of the SafeStep repair

This module implements the comparison-interface and SafeStep-maximality target from
`ROADMAP-04-comparison-interface-and-safestep-maximality.md`.

The result is intentionally scoped. Local confluence by itself forces away the
diagonal `eqW` difference branch once the reflexive collapse branch is retained.
The remaining `SafeStep` side conditions are payload-semantics guards
(`deltaFlag`, `kappaM`), so the maximality theorem is stated for `Step`
subrelations that preserve those side conditions and keep every `SafeStep`
branch. Under those obligations, the relation is exactly `SafeStep`.

Audit notes (LASOT):
* Relation: arbitrary binary relation `R : Trace -> Trace -> Prop`, assumed to be
  a subrelation of the full kernel `Step`.
* Property: diagonal-branch exclusion by local join, and exact maximality of the
  guarded `SafeStep` repair among semantics-preserving subrelations.
* No `sorry`, `admit`, `axiom`, `native_decide`, `bv_decide`, `@[csimp]`,
  `unsafe`, `partial`, or `opaque`.
-/

open OperatorKO7
open OperatorKO7.Trace
open MetaSN_DM
open MetaSN_KO7

namespace OperatorKO7.Meta.DistinctionBoundary

/-! ## Equality-mode comparison surface -/

/-- Equality comparison modes used by the manuscript comparison table. -/
inductive EqualityMode where
| relational
| typed
| structural
| guardedRewrite
| deleteRewrite
| quotientRewrite
| unguardedTotalizedRewrite
deriving DecidableEq, Repr

/-- The only listed mode that carries the diagonal fork is the internalized,
unguarded, totalized rewrite mode. -/
def EqualityMode.CanDiagonalFork : EqualityMode -> Prop
| .relational => False
| .typed => False
| .structural => False
| .guardedRewrite => False
| .deleteRewrite => False
| .quotientRewrite => False
| .unguardedTotalizedRewrite => True

/-- Classification of the comparison-mode table: diagonal forking is exactly the
unguarded totalized rewrite mode. -/
theorem equalityMode_canDiagonalFork_iff (m : EqualityMode) :
    EqualityMode.CanDiagonalFork m ↔ m = EqualityMode.unguardedTotalizedRewrite := by
  cases m <;> simp [EqualityMode.CanDiagonalFork]

/-! ## Ambient join facts for the `eqW` diagonal -/

/-- Local join at a fixed source, measured in the ambient full kernel closure. -/
def LocalJoinRel (R : Trace -> Trace -> Prop) (a : Trace) : Prop :=
  ∀ {b c}, R a b -> R a c -> ∃ d, StepStar b d ∧ StepStar c d

/-- `void` is a full-kernel normal form. -/
theorem normalForm_void : NormalForm void := by
  intro ex
  rcases ex with ⟨u, hu⟩
  cases hu

/-- The two diagonal `eqW` verdicts have no common full-kernel reduct. -/
theorem void_integrate_merge_self_not_joinable (a : Trace) :
    ¬ ∃ d, StepStar void d ∧ StepStar (integrate (merge a a)) d := by
  intro h
  rcases h with ⟨d, hv, hi⟩
  have hd_eq_void : d = void := (nf_no_stepstar_forward normalForm_void hv).symm
  have hd_eq_int : d = integrate (merge a a) :=
    (nf_no_stepstar_forward
      (OperatorKO7.Meta.EqW_Guard_Barrier.normalForm_integrate_merge_self a) hi).symm
  exact OperatorKO7.Meta.EqW_Guard_Barrier.void_ne_integrate_merge_self a
    (hd_eq_void.symm.trans hd_eq_int)

/-- If the reflexive diagonal branch is retained, local join forces the diagonal
difference branch away. -/
theorem confluence_forces_no_diagonal_diff
    {R : Trace -> Trace -> Prop} {a : Trace}
    (href : R (eqW a a) void)
    (hjoin : LocalJoinRel R (eqW a a)) :
    ¬ R (eqW a a) (integrate (merge a a)) := by
  intro hdiff
  rcases hjoin href hdiff with ⟨d, hv, hi⟩
  exact void_integrate_merge_self_not_joinable a ⟨d, hv, hi⟩

/-! ## Semantics-preserving subrelations and maximality -/

/-- The side conditions a full-kernel subrelation must satisfy to count as a
semantics-preserving repair of the safe retained route. Besides being a `Step`
subrelation and retaining all `SafeStep` branches, it respects every payload guard
that defines `SafeStep`, and it refuses diagonal difference verdicts. -/
structure SemanticsPreservingSafeSubrel (R : Trace -> Trace -> Prop) : Prop where
  /-- The repaired relation stays inside the full kernel relation. -/
  sub_step : ∀ {a b}, R a b -> Step a b
  /-- The repaired relation keeps every certified safe branch. -/
  keeps_safe : ∀ {a b}, SafeStep a b -> R a b
  /-- Payload guard for `merge void t -> t`. -/
  merge_void_left_guard : ∀ t, R (merge void t) t -> deltaFlag t = 0
  /-- Payload guard for `merge t void -> t`. -/
  merge_void_right_guard : ∀ t, R (merge t void) t -> deltaFlag t = 0
  /-- Payload delta guard for `merge t t -> t`. -/
  merge_cancel_delta_guard : ∀ t, R (merge t t) t -> deltaFlag t = 0
  /-- Payload multiset guard for `merge t t -> t`. -/
  merge_cancel_kappa_guard : ∀ t, R (merge t t) t -> kappaM t = 0
  /-- Payload guard for `recΔ b s void -> b`. -/
  rec_zero_guard : ∀ b s, R (recΔ b s void) b -> deltaFlag b = 0
  /-- Payload guard for `eqW a a -> void`. -/
  eq_refl_guard : ∀ a, R (eqW a a) void -> kappaM a = 0
  /-- Record-legality guard for diagonal difference verdicts. -/
  eq_diff_diagonal_guard : ∀ a, ¬ R (eqW a a) (integrate (merge a a))

/-- Every `SafeStep` branch is a full-kernel `Step` branch. -/
theorem safeStep_to_step {a b : Trace} (h : SafeStep a b) : Step a b := by
  cases h with
  | R_int_delta => exact Step.R_int_delta _
  | R_merge_void_left => exact Step.R_merge_void_left _
  | R_merge_void_right => exact Step.R_merge_void_right _
  | R_merge_cancel => exact Step.R_merge_cancel _
  | R_rec_zero => exact Step.R_rec_zero _ _
  | R_rec_succ => exact Step.R_rec_succ _ _ _
  | R_eq_refl => exact Step.R_eq_refl _
  | R_eq_diff => exact Step.R_eq_diff _ _

/-- `SafeStep` itself satisfies the semantics-preserving obligations. -/
theorem safeStep_semanticsPreservingSafeSubrel :
    SemanticsPreservingSafeSubrel SafeStep where
  sub_step := fun h => safeStep_to_step h
  keeps_safe := fun h => h
  merge_void_left_guard := by
    intro t h
    cases h with
    | R_merge_void_left _ hδ => exact hδ
    | R_merge_void_right _ _ => simp
    | R_merge_cancel _ _ _ => simp
  merge_void_right_guard := by
    intro t h
    cases h with
    | R_merge_void_left _ _ => simp
    | R_merge_void_right _ hδ => exact hδ
    | R_merge_cancel _ _ _ => simp
  merge_cancel_delta_guard := by
    intro t h
    cases h with
    | R_merge_void_left _ _ => simp
    | R_merge_void_right _ _ => simp
    | R_merge_cancel _ hδ _ => exact hδ
  merge_cancel_kappa_guard := by
    intro t h
    cases h with
    | R_merge_void_left _ _ => simp
    | R_merge_void_right _ _ => simp
    | R_merge_cancel _ _ h0 => exact h0
  rec_zero_guard := by
    intro b s h
    cases h with
    | R_rec_zero _ _ hδ => exact hδ
  eq_refl_guard := by
    intro a h
    cases h with
    | R_eq_refl _ h0 => exact h0
  eq_diff_diagonal_guard := by
    intro a h
    cases h with
    | R_eq_diff _ _ hne => exact hne rfl

/-- Any semantics-preserving full-kernel subrelation is contained in `SafeStep`. -/
theorem semantics_preserving_subrel_subset_safestep
    {R : Trace -> Trace -> Prop}
    (H : SemanticsPreservingSafeSubrel R) :
    ∀ {a b}, R a b -> SafeStep a b := by
  intro a b hr
  have hs : Step a b := H.sub_step hr
  cases hs with
  | R_int_delta =>
      exact SafeStep.R_int_delta _
  | R_merge_void_left =>
      exact SafeStep.R_merge_void_left _ (H.merge_void_left_guard _ hr)
  | R_merge_void_right =>
      exact SafeStep.R_merge_void_right _ (H.merge_void_right_guard _ hr)
  | R_merge_cancel =>
      exact SafeStep.R_merge_cancel _
        (H.merge_cancel_delta_guard _ hr)
        (H.merge_cancel_kappa_guard _ hr)
  | R_rec_zero =>
      exact SafeStep.R_rec_zero _ _ (H.rec_zero_guard _ _ hr)
  | R_rec_succ =>
      exact SafeStep.R_rec_succ _ _ _
  | R_eq_refl =>
      exact SafeStep.R_eq_refl _ (H.eq_refl_guard _ hr)
  | R_eq_diff x y =>
      by_cases h : x = y
      · subst y
        exact False.elim ((H.eq_diff_diagonal_guard x) hr)
      · exact SafeStep.R_eq_diff x y h

/-- Maximality as exact equality: any semantics-preserving repair relation that
keeps the safe branches has exactly the `SafeStep` branches. -/
theorem semantics_preserving_subrel_eq_safestep
    {R : Trace -> Trace -> Prop}
    (H : SemanticsPreservingSafeSubrel R) :
    ∀ {a b}, R a b ↔ SafeStep a b := by
  intro a b
  constructor
  · exact semantics_preserving_subrel_subset_safestep H
  · exact H.keeps_safe

/-- Packaged headline: `SafeStep` is inhabited as a semantics-preserving repair, and
every semantics-preserving repair relation is contained in `SafeStep`. -/
theorem safeStep_is_maximal_semantics_preserving_repair :
    SemanticsPreservingSafeSubrel SafeStep ∧
      ∀ {R : Trace -> Trace -> Prop},
        SemanticsPreservingSafeSubrel R ->
          ∀ {a b}, R a b -> SafeStep a b :=
  ⟨safeStep_semanticsPreservingSafeSubrel,
    fun H => semantics_preserving_subrel_subset_safestep H⟩

/-! ## Statement-adequacy checks and axiom inventory -/

section AuditChecks

#check @equalityMode_canDiagonalFork_iff
#check @confluence_forces_no_diagonal_diff
#check @safeStep_to_step
#check @safeStep_semanticsPreservingSafeSubrel
#check @semantics_preserving_subrel_subset_safestep
#check @semantics_preserving_subrel_eq_safestep
#check @safeStep_is_maximal_semantics_preserving_repair

#print axioms equalityMode_canDiagonalFork_iff
#print axioms confluence_forces_no_diagonal_diff
#print axioms safeStep_to_step
#print axioms safeStep_semanticsPreservingSafeSubrel
#print axioms semantics_preserving_subrel_subset_safestep
#print axioms semantics_preserving_subrel_eq_safestep
#print axioms safeStep_is_maximal_semantics_preserving_repair

end AuditChecks

end OperatorKO7.Meta.DistinctionBoundary
