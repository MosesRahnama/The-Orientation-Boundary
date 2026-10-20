import OperatorKO7.Kernel
import OperatorKO7.Meta.Confluence_Safe
import OperatorKO7.Meta.EqW_Guard_Barrier
import OperatorKO7.Meta.SafeStep.EqWVoidAnomaly
import OperatorKO7.Meta.SafeStep.DistinctionControls

set_option autoImplicit false

/-!
# Critical-pair completeness for the KO7 kernel root relation

This module proves that the `eqW` reflexive diagonal is the **unique** source of
root non-joinability in the full kernel relation `Step`.  It is the depth result
of the distinction (confluence) axis: not merely *that* `eqW void void` breaks
local confluence, but that it is the *only* root overlap that does.

## The eight root rules and their overlaps

`Step` (`OperatorKO7/Kernel.lean`) has eight unconditional root rules.  Two rules
form a **root critical pair** when their left-hand sides unify at the root (the
whole term is the redex).  Enumerating the left-hand side head symbols:

* `integrate (delta t)` — rule `R_int_delta`. Only one `integrate` root rule, so
  no overlap.
* `merge void t`, `merge t void`, `merge t t` — rules `R_merge_void_left`,
  `R_merge_void_right`, `R_merge_cancel`. These three coincide exactly at the
  common instance `merge void void`. Every reduct there is `void`, so the peak is
  **joinable** (`MetaSN_KO7.localJoinStep_merge_void_void` via `DistinctionControls`,
  re-exported here as `merge_void_void_joins`).
* `recΔ b s void`, `recΔ b s (delta n)` — rules `R_rec_zero`, `R_rec_succ`. Their
  scrutinees are the distinct constructors `void` and `delta n`, which do **not**
  unify: there is no root overlap. Recorded as `rec_rules_no_root_overlap`.
* `eqW a a`, `eqW a b` — rules `R_eq_refl`, `R_eq_diff`. These unify exactly on the
  reflexive diagonal `eqW c c`. There `R_eq_refl` gives `void` and `R_eq_diff` gives
  `integrate (merge c c)`; both are normal forms and they are distinct, so the peak
  is **not** joinable (`MetaSN_KO7.not_localJoinStep_eqW_refl` via
  `EqW_Guard_Barrier`).

So the only non-joinable root overlap is the `eqW` diagonal.  The headline
`eqW_void_void_is_the_unique_root_obstruction` packages this as an `iff`:
`¬ LocalJoinStep a ↔ a` is a reflexive `eqW`.

## Relation / property (LASOT)

* Relation: full kernel `Step` (closure `StepStar`) throughout. Every theorem names
  its relation in its docstring.
* Property: `local_confluence` (root joinability of a single source, and its
  negation), and the completeness `iff` characterizing the obstruction set.
* Trust: kernel-only. No `sorry`, `admit`, `axiom`, `native_decide`, `bv_decide`,
  `@[csimp]`, `unsafe`, `partial`, or `opaque`. `#print axioms` on each headline is a
  subset of `{propext, Classical.choice, Quot.sound}`.
* Reused, not re-proved: `MetaSN_KO7.LocalJoinStep`,
  `MetaSN_KO7.localJoinStep_merge_void_void` (from `DistinctionControls`),
  `MetaSN_KO7.not_localJoinStep_eqW_refl` and `not_localJoinStep_eqW_void_void`.
  The only new mathematics is the *positivity* direction: every non-`eqW`-diagonal
  source is root-joinable, proved by an exhaustive constructor analysis mirroring
  `MetaSN_KO7.localJoin_all_safe` but for the unguarded relation.
-/

open OperatorKO7 Trace

namespace OperatorKO7.Meta.DistinctionBoundary.CriticalPairCompleteness

/-! ## The obstruction predicate -/

/-- `IsEqWDiagonal a` holds when `a` is a reflexive equality test `eqW c c`. This is
the exact set of full-kernel root sources at which local confluence fails. -/
def IsEqWDiagonal (a : Trace) : Prop := ∃ c : Trace, a = eqW c c

/-- The canonical witness `eqW void void` is on the diagonal. -/
theorem eqW_void_void_isEqWDiagonal : IsEqWDiagonal (eqW void void) :=
  ⟨void, rfl⟩

/-! ## The benign merge diagonal joins (re-export of the `DistinctionControls` keystone) -/

/-- **Benign root overlap.** The three merge rules overlap only at `merge void void`,
and that peak is joinable: every reduct is `void`.

Relation: full kernel `Step` (closure `StepStar`). Property: `local_confluence`. -/
theorem merge_void_void_joins : MetaSN_KO7.LocalJoinStep (merge void void) :=
  OperatorKO7.Meta.SafeStep.DistinctionControls.localJoinStep_merge_void_void

/-! ## The rec rules do not overlap at the root

`R_rec_zero` fires at `recΔ b s void`; `R_rec_succ` fires at `recΔ b s (delta n)`.
The scrutinees `void` and `delta n` are distinct constructors, so no term is matched
by both rules: there is no root critical pair between them. We record this as the
impossibility of a shared redex. -/

/-- The two `recΔ` root rules never apply to the same source: their scrutinees are the
distinct constructors `void` and `delta _`. Hence they form no root critical pair.

Relation: full kernel `Step`. Property: structural (no shared redex). -/
theorem rec_rules_no_root_overlap (_b _s n : Trace) :
    ¬ (∃ x, x = (void : Trace) ∧ x = delta n) := by
  rintro ⟨x, rfl, h⟩
  cases h

/-! ## Positivity: every non-diagonal source is root-joinable

This is the new content. We show local joinability of `Step` at every source that is
*not* a reflexive `eqW`. The proof is an exhaustive constructor analysis. For all
non-`eqW`, non-merge-diagonal shapes the root reduct is unique (or there is no root
step), so joinability is immediate; the merge diagonal uses `merge_void_void_joins`;
the off-diagonal `eqW a b` (`a ≠ b`) admits only `R_eq_diff`. -/

/-- Helper: if every `Step` out of `a` lands on a single target `d`, then `a` is
root-joinable. -/
theorem localJoinStep_of_unique (a d : Trace)
    (h : ∀ {x}, Step a x → x = d) : MetaSN_KO7.LocalJoinStep a := by
  intro b c hb hc
  have hb' : b = d := h hb
  have hc' : c = d := h hc
  exact ⟨d, by simpa [hb'] using StepStar.refl d, by simpa [hc'] using StepStar.refl d⟩

/-- Helper: if there are no `Step`s out of `a`, then `a` is root-joinable vacuously. -/
theorem localJoinStep_of_none (a : Trace)
    (h : ∀ {x}, Step a x → False) : MetaSN_KO7.LocalJoinStep a := by
  intro b c hb _hc
  exact (h hb).elim

/-- **Positivity / completeness (negative direction sources).** Every full-kernel root
source that is not a reflexive `eqW` diagonal is locally joinable.

This is the exhaustive constructor analysis: `void`, `delta`, `app`, every
`integrate _`, every `recΔ _ _ _`, every `merge _ _` (diagonal via
`merge_void_void_joins`, off cases unique/none), and off-diagonal `eqW a b` all join;
the only excluded case is `a = eqW c c`.

Relation: full kernel `Step` (closure `StepStar`). Property: `local_confluence`. -/
theorem localJoinStep_of_not_diagonal (a : Trace) (hnd : ¬ IsEqWDiagonal a) :
    MetaSN_KO7.LocalJoinStep a := by
  cases a with
  | void =>
      exact localJoinStep_of_none void (fun h => by cases h)
  | delta t =>
      exact localJoinStep_of_none (delta t) (fun h => by cases h)
  | app x y =>
      exact localJoinStep_of_none (app x y) (fun h => by cases h)
  | integrate t =>
      cases t with
      | delta u =>
          refine localJoinStep_of_unique (integrate (delta u)) void ?_
          intro x hx; cases hx with | R_int_delta _ => rfl
      | void =>
          exact localJoinStep_of_none (integrate void) (fun h => by cases h)
      | integrate u =>
          exact localJoinStep_of_none (integrate (integrate u)) (fun h => by cases h)
      | merge x y =>
          exact localJoinStep_of_none (integrate (merge x y)) (fun h => by cases h)
      | app x y =>
          exact localJoinStep_of_none (integrate (app x y)) (fun h => by cases h)
      | recΔ b s n =>
          exact localJoinStep_of_none (integrate (recΔ b s n)) (fun h => by cases h)
      | eqW x y =>
          exact localJoinStep_of_none (integrate (eqW x y)) (fun h => by cases h)
  | recΔ b s n =>
      cases n with
      | void =>
          refine localJoinStep_of_unique (recΔ b s void) b ?_
          intro x hx; cases hx with | R_rec_zero _ _ => rfl
      | delta u =>
          refine localJoinStep_of_unique (recΔ b s (delta u)) (app s (recΔ b s u)) ?_
          intro x hx; cases hx with | R_rec_succ _ _ _ => rfl
      | integrate u =>
          exact localJoinStep_of_none (recΔ b s (integrate u)) (fun h => by cases h)
      | merge x y =>
          exact localJoinStep_of_none (recΔ b s (merge x y)) (fun h => by cases h)
      | app x y =>
          exact localJoinStep_of_none (recΔ b s (app x y)) (fun h => by cases h)
      | recΔ b' s' n' =>
          exact localJoinStep_of_none (recΔ b s (recΔ b' s' n')) (fun h => by cases h)
      | eqW x y =>
          exact localJoinStep_of_none (recΔ b s (eqW x y)) (fun h => by cases h)
  | merge x y =>
      by_cases hxv : x = void
      · subst hxv
        by_cases hyv : y = void
        · subst hyv; exact merge_void_void_joins
        · -- merge void y, y ≠ void: only R_merge_void_left can fire (cancel needs y = void).
          refine localJoinStep_of_unique (merge void y) y ?_
          intro z hz
          cases hz with
          | R_merge_void_left _ => rfl
          | R_merge_void_right _ => exact absurd rfl hyv
          | R_merge_cancel _ => exact absurd rfl hyv
      · by_cases hyv : y = void
        · subst hyv
          -- merge x void, x ≠ void: only R_merge_void_right can fire.
          refine localJoinStep_of_unique (merge x void) x ?_
          intro z hz
          cases hz with
          | R_merge_void_right _ => rfl
          | R_merge_void_left _ => exact absurd rfl hxv
          | R_merge_cancel _ => exact absurd rfl hxv
        · by_cases hxy : x = y
          · subst hxy
            -- merge x x, x ≠ void: only R_merge_cancel can fire.
            refine localJoinStep_of_unique (merge x x) x ?_
            intro z hz
            cases hz with
            | R_merge_cancel _ => rfl
            | R_merge_void_left _ => exact absurd rfl hxv
            | R_merge_void_right _ => exact absurd rfl hyv
          · -- neither void, x ≠ y: no merge rule fires.
            refine localJoinStep_of_none (merge x y) ?_
            intro z hz
            cases hz with
            | R_merge_void_left _ => exact hxv rfl
            | R_merge_void_right _ => exact hyv rfl
            | R_merge_cancel _ => exact hxy rfl
  | eqW x y =>
      by_cases hxy : x = y
      · subst hxy; exact absurd ⟨x, rfl⟩ hnd
      · -- off-diagonal eqW x y, x ≠ y: only R_eq_diff can fire.
        refine localJoinStep_of_unique (eqW x y) (integrate (merge x y)) ?_
        intro z hz
        cases hz with
        | R_eq_diff _ _ => rfl
        | R_eq_refl _ => exact absurd rfl hxy

/-! ## The obstruction direction: every diagonal source is non-joinable -/

/-- Every reflexive `eqW` diagonal source is **not** root-joinable: the `R_eq_refl` /
`R_eq_diff` overlap produces two distinct normal forms.  Re-export of
`MetaSN_KO7.not_localJoinStep_eqW_refl` (`EqW_Guard_Barrier`), lifted along the
diagonal predicate.

Relation: full kernel `Step` (closure `StepStar`). Property: `local_confluence`
(its negation). -/
theorem not_localJoinStep_of_diagonal (a : Trace) (hd : IsEqWDiagonal a) :
    ¬ MetaSN_KO7.LocalJoinStep a := by
  obtain ⟨c, rfl⟩ := hd
  exact MetaSN_KO7.not_localJoinStep_eqW_refl c

/-! ## Headline: critical-pair completeness -/

/-- **Critical-pair completeness of the KO7 kernel.**

A full-kernel root source `a` fails local confluence **iff** it is a reflexive
equality test `eqW c c`.  Equivalently: the `eqW` reflexive diagonal is exactly the
set of root confluence obstructions of `Step`; every other root overlap (the
`merge void void` triple coincidence) joins, and all remaining shapes have unique or
absent root reducts.

This is the completeness statement: the obstruction is not just *exhibited* at
`eqW void void`, it is *characterized* — there is no other root critical pair that
fails to join.

Relation: full kernel `Step` (closure `StepStar`). Property: `local_confluence`
characterization. -/
theorem eqW_diagonal_is_the_unique_root_obstruction (a : Trace) :
    ¬ MetaSN_KO7.LocalJoinStep a ↔ IsEqWDiagonal a := by
  constructor
  · intro hnj
    by_contra hnd
    exact hnj (localJoinStep_of_not_diagonal a hnd)
  · exact not_localJoinStep_of_diagonal a

/-- **Canonical-witness corollary.** Specializing the completeness characterization to
the minimal closed witness: `eqW void void` is non-joinable, and (by completeness) any
non-joinable root source is a reflexive `eqW`.  This is the precise sense in which
`eqW void void` is *the* confluence obstruction of KO7.

Relation: full kernel `Step`. Property: `local_confluence`. -/
theorem eqW_void_void_is_canonical_root_obstruction :
    ¬ MetaSN_KO7.LocalJoinStep (eqW void void)
      ∧ (∀ a, ¬ MetaSN_KO7.LocalJoinStep a → IsEqWDiagonal a) :=
  ⟨not_localJoinStep_of_diagonal (eqW void void) eqW_void_void_isEqWDiagonal,
   fun a => (eqW_diagonal_is_the_unique_root_obstruction a).mp⟩

/-! ## Axiom audit -/

#print axioms eqW_diagonal_is_the_unique_root_obstruction
#print axioms localJoinStep_of_not_diagonal
#print axioms not_localJoinStep_of_diagonal
#print axioms merge_void_void_joins
#print axioms eqW_void_void_is_canonical_root_obstruction

end OperatorKO7.Meta.DistinctionBoundary.CriticalPairCompleteness
