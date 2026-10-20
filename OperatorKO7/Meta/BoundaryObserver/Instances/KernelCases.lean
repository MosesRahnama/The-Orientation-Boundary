import OperatorKO7.Kernel
import OperatorKO7.Meta.BoundaryObserver.KernelCases
import OperatorKO7.Meta.BoundaryObserver.NoReturn
import OperatorKO7.Meta.EqGuardedConfluence
import OperatorKO7.Meta.DistinctionBoundary.ContextualDiagonalScope
import OperatorKO7.Meta.DistinctionBoundary.RoleErasureInstance

set_option autoImplicit false

namespace OperatorKO7.Meta.BoundaryObserver.KernelCases

open OperatorKO7 Trace
open OperatorKO7.Meta.BoundaryObserver.MergedPair
open OperatorKO7.Meta.DistinctionBoundary.RoleErasureInstance
open OperatorKO7.Meta.DistinctionBoundary.ContextualDiagonalScope

/-! ## Proposition 7.2: the two rules as tests on a pair of occurrences -/

/-- Proposition 7.2: the reflexive rule fires at the root of `eqW a b` if and only if the two
arguments are equal. Relation: `Step`, root, one step. -/
theorem eqRefl_fires_iff (a b : Trace) : Step (eqW a b) void ↔ a = b := by
  constructor
  · intro h
    cases h
    rfl
  · intro h
    rw [h]
    exact Step.R_eq_refl b

/-- Proposition 7.2: the difference rule fires at the root of `eqW a b` for all arguments.
Relation: `Step`, root, one step. -/
theorem eqDiff_fires (a b : Trace) : Step (eqW a b) (integrate (merge a b)) :=
  Step.R_eq_diff a b

/-- The root reducts of `eqW a b`: the record of the pair, and `void` when the arguments are
equal. Relation: `Step`, root, one step. -/
theorem eqW_root_reducts (a b t : Trace) :
    Step (eqW a b) t ↔ (t = integrate (merge a b) ∨ (a = b ∧ t = void)) := by
  constructor
  · intro h
    cases h with
    | R_eq_refl => exact Or.inr ⟨rfl, rfl⟩
    | R_eq_diff => exact Or.inl rfl
  · rintro (h | ⟨hab, h⟩)
    · rw [h]
      exact Step.R_eq_diff a b
    · rw [h, hab]
      exact Step.R_eq_refl b

/-! ## Corollary 7.4: the term with one node -/

/-- The number of nodes of a term. -/
def nodes : Trace → ℕ
  | void => 1
  | delta t => nodes t + 1
  | integrate t => nodes t + 1
  | merge a b => nodes a + nodes b + 1
  | app a b => nodes a + nodes b + 1
  | recΔ b s n => nodes b + nodes s + nodes n + 1
  | eqW a b => nodes a + nodes b + 1

/-- Every term has at least one node. -/
theorem nodes_pos (t : Trace) : 1 ≤ nodes t := by
  cases t <;> simp only [nodes] <;> omega

/-- Corollary 7.4: `void` is the only term with one node, hence the term of least size. -/
theorem nodes_eq_one_iff (t : Trace) : nodes t = 1 ↔ t = void := by
  constructor
  · intro h
    cases t with
    | void => rfl
    | delta u =>
      have hu := nodes_pos u
      simp only [nodes] at h
      omega
    | integrate u =>
      have hu := nodes_pos u
      simp only [nodes] at h
      omega
    | merge a b =>
      have ha := nodes_pos a
      simp only [nodes] at h
      omega
    | app a b =>
      have ha := nodes_pos a
      simp only [nodes] at h
      omega
    | recΔ b s n =>
      have hb := nodes_pos b
      simp only [nodes] at h
      omega
    | eqW a b =>
      have ha := nodes_pos a
      simp only [nodes] at h
      omega
  · intro h
    rw [h]
    rfl

/-! ## Proposition 7.7 and Theorem 7.3(i): frames, reducts of `eqW void void` -/

/-- Proposition 7.7(ii): a frame that holds two copies reduces to the frame with one.
Relation: `StepCtxFull`, context, one step. -/
theorem frame_pair_to_frame (a : Trace) :
    MetaSN_KO7.StepCtxFull (integrate (merge a a)) (integrate a) :=
  MetaSN_KO7.StepCtxFull.integrate (MetaSN_KO7.StepCtxFull.root (Step.R_merge_cancel a))

/-- Proposition 7.7(ii): the empty frame is a normal form.
Relation: `StepCtxFull`, context, one step. -/
theorem empty_frame_normal (t : Trace) : ¬ MetaSN_KO7.StepCtxFull (integrate void) t := by
  intro h
  cases h with
  | root hs => cases hs
  | integrate h' => exact void_normal h'

/-- Proposition 7.7(ii): the empty frame differs from the blank. -/
theorem empty_frame_ne_blank : integrate void ≠ void :=
  fun h => Trace.noConfusion h

/-- The remark after Proposition 7.7: a frame around the empty frame is a normal form, so the
law of crossing of Spencer-Brown has no counterpart. Relation: `StepCtxFull`, one step. -/
theorem double_frame_normal (t : Trace) :
    ¬ MetaSN_KO7.StepCtxFull (integrate (integrate void)) t := by
  intro h
  cases h with
  | root hs => cases hs
  | integrate h' => exact empty_frame_normal _ h'

/-- The four terms `eqW void void`, `void`, `integrate (merge void void)`, `integrate void` are
closed under one step of rewriting inside terms. Relation: `StepCtxFull`, one step. -/
theorem eqW_void_void_ctx_step_closed {x y : Trace}
    (hx : x = eqW void void ∨ x = void ∨ x = integrate (merge void void) ∨ x = integrate void)
    (h : MetaSN_KO7.StepCtxFull x y) :
    y = eqW void void ∨ y = void ∨ y = integrate (merge void void) ∨ y = integrate void := by
  rcases hx with hx | hx | hx | hx
  · rw [hx] at h
    cases h with
    | root hs =>
      cases hs with
      | R_eq_refl => exact Or.inr (Or.inl rfl)
      | R_eq_diff => exact Or.inr (Or.inr (Or.inl rfl))
    | eqWL h' => exact absurd h' void_normal
    | eqWR h' => exact absurd h' void_normal
  · rw [hx] at h
    exact absurd h void_normal
  · rw [hx] at h
    cases h with
    | root hs => cases hs
    | integrate h' =>
      rw [merge_void_void_step h']
      exact Or.inr (Or.inr (Or.inr rfl))
  · rw [hx] at h
    exact absurd h (empty_frame_normal _)

/--
Theorem 7.3(i), reducts.

Proves: under rewriting inside terms, the terms reachable from `eqW void void` are that term,
`void`, `integrate (merge void void)` and `integrate void`.
Does not prove: the reducts of `eqW a a` for other terms `a`.
Relation: `MetaSN_KO7.StepCtxFull`; closure: context, reflexive-transitive; strategy: full.
Trust: kernel-only.
-/
theorem eqW_void_void_ctx_reducts (t : Trace) :
    Relation.ReflTransGen MetaSN_KO7.StepCtxFull (eqW void void) t ↔
      (t = eqW void void ∨ t = void ∨ t = integrate (merge void void) ∨ t = integrate void) := by
  constructor
  · intro h
    induction h with
    | refl => exact Or.inl rfl
    | tail _ hstep ih => exact eqW_void_void_ctx_step_closed ih hstep
  · rintro (h | h | h | h)
    · rw [h]
    · rw [h]
      exact Relation.ReflTransGen.single (MetaSN_KO7.StepCtxFull.root (Step.R_eq_refl void))
    · rw [h]
      exact Relation.ReflTransGen.single (MetaSN_KO7.StepCtxFull.root (Step.R_eq_diff void void))
    · rw [h]
      exact (Relation.ReflTransGen.single
        (MetaSN_KO7.StepCtxFull.root (Step.R_eq_diff void void))).tail (frame_pair_to_frame void)

/-- Proposition 7.7(iii) and Theorem 7.3(i): under rewriting inside terms, the normal forms of
`eqW void void` are the blank and the empty frame.
Relation: `MetaSN_KO7.StepCtxFull`; closure: context, reflexive-transitive. -/
theorem eqW_void_void_ctx_normal_forms (t : Trace) :
    (Relation.ReflTransGen MetaSN_KO7.StepCtxFull (eqW void void) t ∧
        ∀ u, ¬ MetaSN_KO7.StepCtxFull t u) ↔ (t = void ∨ t = integrate void) := by
  constructor
  · rintro ⟨hreach, hnf⟩
    rcases (eqW_void_void_ctx_reducts t).1 hreach with h | h | h | h
    · rw [h] at hnf
      exact absurd (MetaSN_KO7.StepCtxFull.root (Step.R_eq_refl void)) (hnf _)
    · exact Or.inl h
    · rw [h] at hnf
      exact absurd (frame_pair_to_frame void) (hnf _)
    · exact Or.inr h
  · rintro (h | h)
    · rw [h]
      exact ⟨(eqW_void_void_ctx_reducts _).2 (Or.inr (Or.inl rfl)), fun _ hu => void_normal hu⟩
    · rw [h]
      exact ⟨(eqW_void_void_ctx_reducts _).2 (Or.inr (Or.inr (Or.inr rfl))), empty_frame_normal⟩

/-- Proposition 7.7(i): under the guarded root relation, the difference rule produces the frame
of a pair only for distinct arguments. Relation: `EqGuardedStep`, root, one step. -/
theorem guarded_diff_only_distinct (a b : Trace)
    (h : OperatorKO7.EqGuardedConfluence.EqGuardedStep (eqW a b) (integrate (merge a b))) :
    a ≠ b := by
  cases h
  assumption

/-- Non-vacuity of `guarded_diff_only_distinct`: the guarded difference rule fires on the
distinct arguments `void` and `delta void`. -/
theorem guarded_diff_fires_on_distinct :
    OperatorKO7.EqGuardedConfluence.EqGuardedStep (eqW void (delta void))
      (integrate (merge void (delta void))) :=
  OperatorKO7.EqGuardedConfluence.EqGuardedStep.R_eq_diff void (delta void)
    (fun h => Trace.noConfusion h)

/-! ## Proposition 7.6: addresses in the unrolled recursor -/

/-- The numeral `delta^k void`. -/
def numeral : ℕ → Trace
  | 0 => void
  | k + 1 => delta (numeral k)

/-- `spine s i t`: the term `t` under `i` applications of `s`, each as the first argument. -/
def spine (s : Trace) : ℕ → Trace → Trace
  | 0, t => t
  | i + 1, t => app s (spine s i t)

/-- `descend n t`: the subterm reached from `t` by `n` descents into the second argument of an
application, when the path exists. -/
def descend : ℕ → Trace → Option Trace
  | 0, t => some t
  | n + 1, app _ u => descend n u
  | _ + 1, _ => none

/-- `frameCopy j t`: the first argument of the application reached by `j - 1` descents into
second arguments. This is the subterm at the position `2^(j-1)·1` of the manuscript. -/
def frameCopy (j : ℕ) (t : Trace) : Option Trace :=
  match descend (j - 1) t with
  | some (app s _) => some s
  | _ => none

/-- A step inside the term under a spine is a step of the whole term.
Relation: `StepCtxFull`, context, one step. -/
theorem spine_ctx_step (s : Trace) (i : ℕ) {t u : Trace} (h : MetaSN_KO7.StepCtxFull t u) :
    MetaSN_KO7.StepCtxFull (spine s i t) (spine s i u) := by
  induction i with
  | zero => exact h
  | succ i ih => exact MetaSN_KO7.StepCtxFull.appR ih

/-- An application below a spine is one more level of the spine. -/
theorem spine_app (s t : Trace) (i : ℕ) : spine s i (app s t) = spine s (i + 1) t := by
  induction i with
  | zero => rfl
  | succ i ih =>
    show app s (spine s i (app s t)) = app s (spine s (i + 1) t)
    rw [ih]

/--
Proposition 7.6, the unrolling.

Proves: from `recΔ b s (delta^k void)`, `i ≤ k` applications of the step rule, each at the redex
that the previous one created, give `i` applications of `s` around the redex
`recΔ b s (delta^(k-i) void)`.
Does not prove: that this is the only reduction sequence from the term.
Relation: `MetaSN_KO7.StepCtxFull`; closure: context, reflexive-transitive.
Trust: kernel-only.
-/
theorem unroll_steps (b s : Trace) (k i : ℕ) (h : i ≤ k) :
    Relation.ReflTransGen MetaSN_KO7.StepCtxFull (recΔ b s (numeral k))
      (spine s i (recΔ b s (numeral (k - i)))) := by
  induction i with
  | zero => exact Relation.ReflTransGen.refl
  | succ i ih =>
    have hi : i ≤ k := Nat.le_of_succ_le h
    have hk : k - i = (k - (i + 1)) + 1 := by omega
    refine (ih hi).tail ?_
    rw [hk, ← spine_app]
    exact spine_ctx_step s i (MetaSN_KO7.StepCtxFull.root (Step.R_rec_succ b s _))

/-- Descending `m` times through a spine of `m + r` levels leaves a spine of `r` levels. -/
theorem descend_spine_add (s t : Trace) (m r : ℕ) :
    descend m (spine s (m + r) t) = some (spine s r t) := by
  induction m with
  | zero =>
    rw [Nat.zero_add]
    simp only [descend]
  | succ m ih =>
    have hm : m + 1 + r = (m + r) + 1 := by omega
    rw [hm]
    show descend (m + 1) (app s (spine s (m + r) t)) = some (spine s r t)
    simp only [descend]
    exact ih

/-- Proposition 7.6: `i` descents through the unrolled term reach the term under the spine. -/
theorem descend_spine (s t : Trace) (i : ℕ) : descend i (spine s i t) = some t :=
  descend_spine_add s t i 0

/-- Proposition 7.6: in a term with `i` levels of spine, the copy of `s` written at step `j`
stands at the position reached by `j - 1` descents, for every `1 ≤ j ≤ i`. The position does not
depend on `i`, so a copy keeps its position under later steps. -/
theorem frameCopy_spine (s t : Trace) (i j : ℕ) (hj : 1 ≤ j) (hji : j ≤ i) :
    frameCopy j (spine s i t) = some s := by
  obtain ⟨m, hm⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  obtain ⟨r, hr⟩ : ∃ r, i = m + (r + 1) := ⟨i - m - 1, by omega⟩
  rw [hm, hr]
  unfold frameCopy
  rw [Nat.add_sub_cancel, descend_spine_add]
  rfl

/-! ## Theorem 8.1: the recursor as a model of the two clauses -/

/-- `O R s k`: the observation of `R` with step argument `s` and counter `k`,
`recΔ R s (delta^k void)`. -/
def O (R s : Trace) (k : ℕ) : Trace := recΔ R s (numeral k)

/-- Theorem 8.1(i): at counter zero the observation returns `R`. Relation: `Step`, root. -/
theorem O_zero (R s : Trace) : Step (O R s 0) R :=
  Step.R_rec_zero R s

/-- Theorem 8.1(ii): at a positive counter one pass removes one `delta`, writes one application,
and keeps the observation with the smaller counter. Relation: `Step`, root. -/
theorem O_succ (R s : Trace) (k : ℕ) : Step (O R s (k + 1)) (app s (O R s k)) :=
  Step.R_rec_succ R s (numeral k)

/-- Theorem 8.1(iii): `k` passes and the base rule lead from the observation with counter `k` to
`k` applications of `s` around `R`.
Relation: `MetaSN_KO7.StepCtxFull`; closure: context, reflexive-transitive. -/
theorem O_unroll (R s : Trace) (k : ℕ) :
    Relation.ReflTransGen MetaSN_KO7.StepCtxFull (O R s k) (spine s k R) := by
  have h := unroll_steps R s k k (Nat.le_refl k)
  rw [Nat.sub_self] at h
  exact h.tail (spine_ctx_step s k (MetaSN_KO7.StepCtxFull.root (Step.R_rec_zero R s)))

/-- Theorem 8.1(iv): the observer that reads `R` from the state `(R, k)` does not determine the
test "the counter is zero". -/
theorem counter_test_not_determined :
    ¬ Determines (fun p : Trace × ℕ => p.1) (fun p : Trace × ℕ => decide (p.2 = 0)) := by
  intro h
  have h01 : decide ((0 : ℕ) = 0) = decide ((1 : ℕ) = 0) := h (void, 0) (void, 1) rfl
  exact absurd h01 (by decide)

/-- Theorem 8.1(iv): the states "`R`, counter zero" and "`R`, counter one" are a merged pair of
the observer that reads `R`. -/
theorem counter_merged_pair (R : Trace) :
    IsMergedPair (fun p : Trace × ℕ => p.1) (R, 0) (R, 1) :=
  ⟨fun h => Nat.zero_ne_one (congrArg Prod.snd h), rfl⟩

/--
Theorem 8.1(iv), last sentence.

Proves: the test "the counter is zero" separates two states `(R, j)` and `(R, k)` of a run if and
only if one of the two counters is zero and the other is positive.
Does not prove: any statement about tests other than this one.
Relation: none. Trust: kernel-only.
-/
theorem observed_test_separates_iff (R : Trace) (j k : ℕ) :
    ((fun p : Trace × ℕ => decide (p.2 = 0)) (R, j) ≠
        (fun p : Trace × ℕ => decide (p.2 = 0)) (R, k)) ↔
      ((j = 0 ∧ k ≠ 0) ∨ (j ≠ 0 ∧ k = 0)) := by
  show decide (j = 0) ≠ decide (k = 0) ↔ _
  by_cases hj : j = 0 <;> by_cases hk : k = 0 <;> simp [hj, hk]

/-- Theorem 8.1(iv): on two states one pass apart, the test "the counter is zero" changes value
if and only if the earlier state has counter zero. The test therefore changes at one place of a
run, between the state one pass away from `R` and the state in which `R` is returned. -/
theorem observed_test_adjacent_iff (R : Trace) (k : ℕ) :
    ((fun p : Trace × ℕ => decide (p.2 = 0)) (R, k) ≠
        (fun p : Trace × ℕ => decide (p.2 = 0)) (R, k + 1)) ↔ k = 0 := by
  show decide (k = 0) ≠ decide (k + 1 = 0) ↔ _
  by_cases hk : k = 0 <;> simp [hk]

/-- Theorem 8.1(v): the two copies of the step argument written by the step rule, one under the
application and one inside the recursor, are a merged pair of the content observer. -/
theorem step_copies_merged_pair (s : Trace) :
    IsMergedPair (fun o : Occ Trace => o.1) (s, Role.frame) (s, Role.active) :=
  ⟨fun h => Role.noConfusion (congrArg Prod.snd h), rfl⟩

/-- The remark before Theorem 8.1: a relation with a step from a term to itself has an infinite
sequence, the constant one. -/
theorem self_step_infinite_seq (t : Trace) :
    ∃ f : ℕ → Trace, ∀ n, (fun a b : Trace => b = a) (f n) (f (n + 1)) :=
  ⟨fun _ => t, fun _ => rfl⟩

end OperatorKO7.Meta.BoundaryObserver.KernelCases
