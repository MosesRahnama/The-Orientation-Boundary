import OperatorKO7.Kernel
import OperatorKO7.Meta.SafeStep_Core

/-!
# SafeStepInterpreter: a verified executable one-step root-SafeStep reduct enumerator

This module provides the executable transition oracle for the guarded relation
`MetaSN_KO7.SafeStep` (defined in `OperatorKO7/Meta/SafeStep_Core.lean`).

`safeStepReducts : Trace → List Trace` is a total function that, by pattern match
on the head constructor and by deciding each rule guard, returns *exactly* the list
of one-step root `SafeStep` reducts of its input. When several rules fire on the
same term it collects all of them: e.g. at `merge void void` the three merge rules
(`R_merge_void_left`, `R_merge_void_right`, `R_merge_cancel`) all apply, so the list
carries one entry per firing rule.

The two correctness directions are proved against the inductive relation:

- `safeStepReducts_sound`     : `u ∈ safeStepReducts t → SafeStep t u`
- `safeStepReducts_complete`  : `SafeStep t u → u ∈ safeStepReducts t`

and combined into `safeStep_iff_mem_reducts`, from which a `Decidable (SafeStep t u)`
instance follows by transporting the `List`-membership decision procedure.

Relation: SafeStep
Property: one_step (root only)

Scope boundary: this is the *root* one-step `SafeStep` enumerator. It is NOT a
contextual enumerator and says nothing about `SafeStepStar` or full kernel `Step`.

This module reuses the `SafeStep` inductive and its guards verbatim. It does not
redefine `SafeStep`, redefine `deltaFlag`/`kappaM`, or re-prove any SafeStep metatheory.

No `sorry`, no `admit`, no added `axiom`, no `native_decide`/`bv_decide`,
no `@[csimp]`, no `unsafe`/`partial`/`opaque`.
-/

set_option autoImplicit false

open OperatorKO7 Trace
open MetaSN_DM (kappaM)

namespace MetaSN_KO7

/-!
## The enumerator

`safeStepReducts` pattern matches on the head constructor of the input `Trace`.
Each branch decides the guard(s) of every `SafeStep` rule whose left-hand side has
that head, and emits the corresponding reduct only when the guard holds.

Decidability used:
- `DecidableEq Trace` (from the `deriving` clause on `Trace`) for `a = b` guards;
- `deltaFlag t = 0` and `kappaM t = 0` are decidable equalities on `Nat` / `Multiset Nat`.

The `merge a b` branch is written generically (rather than via the syntactic
`merge void t` / `merge t void` patterns) so that all three merge rules are decided
uniformly and the completeness proof is a clean per-constructor case analysis.
-/

/-- Executable one-step root `SafeStep` reduct enumerator.

Returns exactly the list of `u` with a root `SafeStep t u`, one entry per firing rule.
Several rules may fire on the same term (e.g. all three merge rules at `merge void void`),
in which case every reduct is collected. -/
def safeStepReducts : Trace → List Trace
  | integrate (delta _t) => [void]
  | merge a b =>
      -- R_merge_void_left  : merge void b ⇒ b      (guard: deltaFlag b = 0)
      (if a = void ∧ deltaFlag b = 0 then [b] else []) ++
      -- R_merge_void_right : merge a void ⇒ a       (guard: deltaFlag a = 0)
      (if b = void ∧ deltaFlag a = 0 then [a] else []) ++
      -- R_merge_cancel     : merge a a ⇒ a          (guards: deltaFlag a = 0, kappaM a = 0)
      (if a = b ∧ deltaFlag a = 0 ∧ kappaM a = 0 then [a] else [])
  | recΔ b _s void =>
      -- R_rec_zero : recΔ b s void ⇒ b              (guard: deltaFlag b = 0)
      if deltaFlag b = 0 then [b] else []
  | recΔ b s (delta n) =>
      -- R_rec_succ : recΔ b s (delta n) ⇒ app s (recΔ b s n)   (unguarded)
      [app s (recΔ b s n)]
  | eqW a b =>
      -- R_eq_refl : eqW a a ⇒ void                  (guard: kappaM a = 0)
      (if a = b ∧ kappaM a = 0 then [void] else []) ++
      -- R_eq_diff : eqW a b ⇒ integrate (merge a b) (guard: a ≠ b)
      (if a ≠ b then [integrate (merge a b)] else [])
  | _ => []

/-!
## Soundness

Every member of `safeStepReducts t` is a genuine root `SafeStep t u`. The proof is a
case analysis on the head of `t`; in each branch the `if`-guards that admitted `u`
are exactly the hypotheses needed to apply the matching `SafeStep` constructor.
-/

/-- **Soundness.** Anything the enumerator emits is a real one-step root `SafeStep`. -/
theorem safeStepReducts_sound : ∀ t u : Trace, u ∈ safeStepReducts t → SafeStep t u := by
  intro t u hu
  -- Split on the head of `t` (via `cases`, which substitutes `t` into `hu`) to mirror
  -- the branch structure of `safeStepReducts`.
  cases t with
  | void => simp [safeStepReducts] at hu
  | delta t' => simp [safeStepReducts] at hu
  | integrate x =>
      cases x with
      | delta t' =>
          -- branch [void]; only reduct is `void` via R_int_delta.
          simp only [safeStepReducts, List.mem_singleton] at hu
          subst hu
          exact SafeStep.R_int_delta t'
      | void => simp [safeStepReducts] at hu
      | integrate y => simp [safeStepReducts] at hu
      | merge a b => simp [safeStepReducts] at hu
      | app a b => simp [safeStepReducts] at hu
      | recΔ a b c => simp [safeStepReducts] at hu
      | eqW a b => simp [safeStepReducts] at hu
  | merge a b =>
      -- Three independent guarded singletons concatenated.
      simp only [safeStepReducts, List.append_assoc, List.mem_append] at hu
      rcases hu with hL | hR | hC
      · -- R_merge_void_left : `subst hL` collapses the target into `u`.
        by_cases hg : a = void ∧ deltaFlag b = 0
        · rw [if_pos hg] at hL
          rw [List.mem_singleton] at hL
          subst hL
          obtain ⟨ha, hδ⟩ := hg
          subst ha
          exact SafeStep.R_merge_void_left u hδ
        · rw [if_neg hg] at hL; exact absurd hL (List.not_mem_nil)
      · -- R_merge_void_right : `subst hR` collapses the target into `u`.
        by_cases hg : b = void ∧ deltaFlag a = 0
        · rw [if_pos hg] at hR
          rw [List.mem_singleton] at hR
          subst hR
          obtain ⟨hb, hδ⟩ := hg
          subst hb
          exact SafeStep.R_merge_void_right u hδ
        · rw [if_neg hg] at hR; exact absurd hR (List.not_mem_nil)
      · -- R_merge_cancel : `subst hC` collapses the target into `u`.
        by_cases hg : a = b ∧ deltaFlag a = 0 ∧ kappaM a = 0
        · rw [if_pos hg] at hC
          rw [List.mem_singleton] at hC
          subst hC
          obtain ⟨hab, hδ, h0⟩ := hg
          subst hab
          exact SafeStep.R_merge_cancel u hδ h0
        · rw [if_neg hg] at hC; exact absurd hC (List.not_mem_nil)
  | app a b => simp [safeStepReducts] at hu
  | recΔ b s n =>
      cases n with
      | void =>
          -- R_rec_zero, guarded by deltaFlag b = 0.
          by_cases hδ : deltaFlag b = 0
          · rw [show safeStepReducts (recΔ b s void) = (if deltaFlag b = 0 then [b] else [])
                  from rfl, if_pos hδ, List.mem_singleton] at hu
            -- `hu : u = b`; substituting collapses the target into `u`.
            subst hu
            exact SafeStep.R_rec_zero u s hδ
          · rw [show safeStepReducts (recΔ b s void) = (if deltaFlag b = 0 then [b] else [])
                  from rfl, if_neg hδ] at hu
            exact absurd hu (List.not_mem_nil)
      | delta n' =>
          -- R_rec_succ, unguarded.
          simp only [safeStepReducts, List.mem_singleton] at hu
          subst hu
          exact SafeStep.R_rec_succ b s n'
      | integrate y => simp [safeStepReducts] at hu
      | merge a c => simp [safeStepReducts] at hu
      | app a c => simp [safeStepReducts] at hu
      | recΔ a c d => simp [safeStepReducts] at hu
      | eqW a c => simp [safeStepReducts] at hu
  | eqW a b =>
      -- Two guarded singletons: refl (a = b ∧ kappaM a = 0) and diff (a ≠ b).
      simp only [safeStepReducts, List.mem_append] at hu
      rcases hu with hRefl | hDiff
      · by_cases hg : a = b ∧ kappaM a = 0
        · rw [if_pos hg] at hRefl
          rw [List.mem_singleton] at hRefl
          subst hRefl
          obtain ⟨hab, h0⟩ := hg
          subst hab
          exact SafeStep.R_eq_refl a h0
        · rw [if_neg hg] at hRefl; exact absurd hRefl (List.not_mem_nil)
      · by_cases hne : a ≠ b
        · rw [if_pos hne] at hDiff
          rw [List.mem_singleton] at hDiff
          subst hDiff
          exact SafeStep.R_eq_diff a b hne
        · rw [if_neg hne] at hDiff; exact absurd hDiff (List.not_mem_nil)

/-!
## Completeness

Every inductive `SafeStep t u` is found by the enumerator. The proof is a case
analysis on the `SafeStep` constructor; each guarded constructor discharges its own
`if`-condition (`hδ`, `h0`, `hne`), so the corresponding singleton is selected and
membership follows. This is the load-bearing direction.
-/

/-- **Completeness.** Every one-step root `SafeStep` is enumerated. Covers all eight
constructors, including both guarded `eqW` rules. -/
theorem safeStepReducts_complete : ∀ t u : Trace, SafeStep t u → u ∈ safeStepReducts t := by
  intro t u h
  -- `cases` substitutes the relation indices, so in each branch the source/target are
  -- fixed and the rule's trace argument is identified with `u` (or `t'`/`a`/`b` where the
  -- target is a compound term). We therefore phrase each branch with the bound names that
  -- survive unification: see the `show` line of each case.
  cases h with
  | R_int_delta t' =>
      -- source `integrate (delta t')`, target `void`.
      show void ∈ safeStepReducts (integrate (delta t'))
      rw [show safeStepReducts (integrate (delta t')) = [void] from rfl]
      exact List.mem_singleton.mpr rfl
  | R_merge_void_left _ hδ =>
      -- source `merge void u`, target `u`; left guard holds (void = void, deltaFlag u = 0).
      show u ∈ safeStepReducts (merge void u)
      rw [show safeStepReducts (merge void u)
            = (if void = void ∧ deltaFlag u = 0 then [u] else []) ++
              (if u = void ∧ deltaFlag void = 0 then [void] else []) ++
              (if void = u ∧ deltaFlag void = 0 ∧ kappaM void = 0 then [void] else [])
          from rfl]
      rw [if_pos (⟨rfl, hδ⟩ : (void : Trace) = void ∧ deltaFlag u = 0)]
      apply List.mem_append_left
      apply List.mem_append_left
      exact List.mem_singleton.mpr rfl
  | R_merge_void_right _ hδ =>
      -- source `merge u void`, target `u`; right guard holds (void = void, deltaFlag u = 0).
      show u ∈ safeStepReducts (merge u void)
      rw [show safeStepReducts (merge u void)
            = (if u = void ∧ deltaFlag void = 0 then [void] else []) ++
              (if void = void ∧ deltaFlag u = 0 then [u] else []) ++
              (if u = void ∧ deltaFlag u = 0 ∧ kappaM u = 0 then [u] else [])
          from rfl]
      rw [if_pos (⟨rfl, hδ⟩ : (void : Trace) = void ∧ deltaFlag u = 0)]
      apply List.mem_append_left
      apply List.mem_append_right
      exact List.mem_singleton.mpr rfl
  | R_merge_cancel _ hδ h0 =>
      -- source `merge u u`, target `u`; cancel guard holds (u = u, deltaFlag, kappaM).
      show u ∈ safeStepReducts (merge u u)
      rw [show safeStepReducts (merge u u)
            = (if u = void ∧ deltaFlag u = 0 then [u] else []) ++
              (if u = void ∧ deltaFlag u = 0 then [u] else []) ++
              (if u = u ∧ deltaFlag u = 0 ∧ kappaM u = 0 then [u] else [])
          from rfl]
      rw [if_pos (⟨rfl, hδ, h0⟩ : u = u ∧ deltaFlag u = 0 ∧ kappaM u = 0)]
      apply List.mem_append_right
      exact List.mem_singleton.mpr rfl
  | R_rec_zero _ s hδ =>
      -- source `recΔ u s void`, target `u`; guard deltaFlag u = 0.
      show u ∈ safeStepReducts (recΔ u s void)
      rw [show safeStepReducts (recΔ u s void) = (if deltaFlag u = 0 then [u] else []) from rfl,
          if_pos hδ]
      exact List.mem_singleton.mpr rfl
  | R_rec_succ b s n =>
      -- source `recΔ b s (delta n)`, target `app s (recΔ b s n)`.
      show app s (recΔ b s n) ∈ safeStepReducts (recΔ b s (delta n))
      rw [show safeStepReducts (recΔ b s (delta n)) = [app s (recΔ b s n)] from rfl]
      exact List.mem_singleton.mpr rfl
  | R_eq_refl a h0 =>
      -- source `eqW a a`, target `void`; refl guard holds (a = a, kappaM a = 0).
      show void ∈ safeStepReducts (eqW a a)
      rw [show safeStepReducts (eqW a a)
            = (if a = a ∧ kappaM a = 0 then [void] else []) ++
              (if a ≠ a then [integrate (merge a a)] else [])
          from rfl]
      rw [if_pos (⟨rfl, h0⟩ : a = a ∧ kappaM a = 0)]
      apply List.mem_append_left
      exact List.mem_singleton.mpr rfl
  | R_eq_diff a b hne =>
      -- source `eqW a b`, target `integrate (merge a b)`; diff guard `a ≠ b`.
      show integrate (merge a b) ∈ safeStepReducts (eqW a b)
      rw [show safeStepReducts (eqW a b)
            = (if a = b ∧ kappaM a = 0 then [void] else []) ++
              (if a ≠ b then [integrate (merge a b)] else [])
          from rfl]
      rw [if_pos hne]
      apply List.mem_append_right
      exact List.mem_singleton.mpr rfl

/-!
## The bridge and the decision procedure
-/

/-- **Characterization.** Root `SafeStep` is exactly membership in the enumerated list. -/
theorem safeStep_iff_mem_reducts (t u : Trace) : SafeStep t u ↔ u ∈ safeStepReducts t :=
  ⟨safeStepReducts_complete t u, safeStepReducts_sound t u⟩

/-- `SafeStep t u` is decidable: transport the decidable `List` membership across the
characterization. No `native_decide`; the underlying decision is `List.decidableMem`
on a `DecidableEq Trace`. -/
instance decidableSafeStep (t u : Trace) : Decidable (SafeStep t u) :=
  decidable_of_iff _ (safeStep_iff_mem_reducts t u).symm

/-!
## Non-vacuity tied to the paper

At the diagonal `eqW void void`, the difference rule `R_eq_diff` is guard-blocked
(`void = void` refutes `a ≠ b`), so only the licensed reflexive reduct `void` remains.
Off the diagonal (`eqW void (delta void)`) the difference branch is live.
-/

/-- **Diagonal.** At `eqW void void` only the licensed reflexive reduct survives:
`R_eq_refl` fires (`kappaM void = 0`) giving `void`, while `R_eq_diff` is blocked
because `void = void`. Hence the reduct list is exactly `[void]`. -/
theorem safeStepReducts_diagonal : safeStepReducts (eqW void void) = [void] := by
  -- Evaluate the `eqW` branch: refl guard holds (`void = void`, `kappaM void = 0`),
  -- diff guard fails (`¬ void ≠ void`).
  have hrefl : (void : Trace) = void ∧ kappaM void = 0 := ⟨rfl, by simp [kappaM]⟩
  have hdiff : ¬ ((void : Trace) ≠ void) := by simp
  rw [show safeStepReducts (eqW void void)
        = (if (void : Trace) = void ∧ kappaM void = 0 then [void] else []) ++
          (if (void : Trace) ≠ void then [integrate (merge void void)] else [])
      from rfl,
      if_pos hrefl, if_neg hdiff, List.append_nil]

/-- **Off-diagonal witness.** At `eqW void (delta void)` the operands differ, so the
difference rule `R_eq_diff` is live and its reduct `integrate (merge void (delta void))`
is enumerated. -/
theorem safeStepReducts_offdiagonal_mem :
    integrate (merge void (delta void)) ∈ safeStepReducts (eqW void (delta void)) := by
  -- The diff guard `void ≠ delta void` holds, so the diff singleton is present.
  have hne : (void : Trace) ≠ delta void := by simp
  rw [show safeStepReducts (eqW void (delta void))
        = (if (void : Trace) = delta void ∧ kappaM void = 0 then [void] else []) ++
          (if (void : Trace) ≠ delta void then [integrate (merge void (delta void))] else [])
      from rfl,
      if_pos hne]
  apply List.mem_append_right
  exact List.mem_singleton.mpr rfl

/-- Companion existence form of the off-diagonal witness, stated directly on the
inductive relation via the characterization. -/
theorem safeStep_offdiagonal :
    SafeStep (eqW void (delta void)) (integrate (merge void (delta void))) :=
  (safeStep_iff_mem_reducts _ _).mpr safeStepReducts_offdiagonal_mem

end MetaSN_KO7

/-! ## Axiom audit (headline theorems) -/

#check @MetaSN_KO7.safeStepReducts
#check @MetaSN_KO7.safeStepReducts_sound
#check @MetaSN_KO7.safeStepReducts_complete
#check @MetaSN_KO7.safeStep_iff_mem_reducts
#check @MetaSN_KO7.decidableSafeStep
#check @MetaSN_KO7.safeStepReducts_diagonal
#check @MetaSN_KO7.safeStepReducts_offdiagonal_mem

#print axioms MetaSN_KO7.safeStepReducts_sound
#print axioms MetaSN_KO7.safeStepReducts_complete
#print axioms MetaSN_KO7.safeStep_iff_mem_reducts
#print axioms MetaSN_KO7.decidableSafeStep
#print axioms MetaSN_KO7.safeStepReducts_diagonal
#print axioms MetaSN_KO7.safeStepReducts_offdiagonal_mem
