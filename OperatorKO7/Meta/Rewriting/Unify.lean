import OperatorKO7.Meta.Rewriting.Subst
import Mathlib.Data.Finset.Card

/-!
# First-order unification by Martelli-Montanari transformation

Roadmap source: `ROADMAP-01-generic-critical-pair-lemma.md`, sections 3
(unification specification, Martelli-Montanari, the lexicographic measure), 5,
and 8 (the termination risk). This is Wave 2A: the keystone unification
function delivered as data, with its totality and termination established.

## What this module delivers

`unify : Term sigma nu -> Term sigma nu -> Option (Subst sigma nu)` solves a
single equation by running a Martelli-Montanari transformation on a worklist of
equation pairs (`List (Term sigma nu × Term sigma nu)`). The four transformation
moves are:

- decompose: `app f as =?= app f bs` with matching arity becomes the worklist of
  argument pairs (a head-symbol or arity clash yields `none`);
- delete: `var x =?= var x` is discarded;
- orient and eliminate: `var x =?= t` (or the oriented `t =?= var x` with `t` an
  application) binds `x` to `t` once the occurs-check `occurs x t = false`
  passes (an occurring variable yields `none`), and `subst1 x t` is applied
  across the rest of the worklist.

The result is returned as real, idempotent substitution data: the eliminate move
composes the recursively computed solution with `subst1 x t`, building the
classic idempotent most-general unifier so the Wave-3 correctness theorems
(`UnifyCorrect.lean`) are provable about it.

## Termination

`solve` recurses on a worklist whose lexicographic measure is
`(card (wlVars W), wlSize W, W.length)` over `Nat ×ₗ Nat ×ₗ Nat`:

- the eliminate move strictly shrinks the variable-count component, by
  `Subst.FV_elim_strict_subset` lifted to the worklist (`wlVars_subst1`,
  `elim_card_lt`); the substitution may grow the symbol size, but the dominating
  first component falls;
- the decompose move keeps the variable set fixed and strictly shrinks the
  symbol-size component (`wlVars_zipPairs_append`, `wlSize_zipPairs_lt`);
- the delete move keeps the variable set within the previous one and strictly
  shrinks the length, so either the variable count falls or it ties and the
  size and length fall (`wlVars_tail_subset`, `wlSize_tail_lt`).

Every `decreasing_by` goal is discharged from these lemmas via `Prod.lex_def`.

Trust: kernel-only; baseline-only under `#print axioms` (a subset of
`{propext, Classical.choice, Quot.sound}`, from `Finset`/`DecidableEq` plumbing
only). No `sorry`, `axiom`, `native_decide`, `partial`, or `unsafe`.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.Rewriting

open Subst

universe u v

variable {sigma : Type u} {nu : Type v}

/-! ## Worklist measures -/

/-- The set of variables occurring anywhere in a worklist of equation pairs. -/
def wlVars [DecidableEq nu] (W : List (Term sigma nu × Term sigma nu)) : Finset nu :=
  W.foldr (fun p acc => Term.vars p.1 ∪ Term.vars p.2 ∪ acc) ∅

@[simp] theorem wlVars_nil [DecidableEq nu] :
    wlVars ([] : List (Term sigma nu × Term sigma nu)) = ∅ := rfl

@[simp] theorem wlVars_cons [DecidableEq nu] (p : Term sigma nu × Term sigma nu)
    (W : List (Term sigma nu × Term sigma nu)) :
    wlVars (p :: W) = Term.vars p.1 ∪ Term.vars p.2 ∪ wlVars W := rfl

/-- Membership in the worklist variable set is membership in some pair's
component variable set. -/
theorem mem_wlVars_iff [DecidableEq nu] {z : nu} {W : List (Term sigma nu × Term sigma nu)} :
    z ∈ wlVars W ↔ ∃ p ∈ W, z ∈ Term.vars p.1 ∨ z ∈ Term.vars p.2 := by
  induction W with
  | nil => simp
  | cons p W ih =>
      simp only [wlVars_cons, Finset.mem_union, List.mem_cons, ih]
      constructor
      · rintro ((h | h) | ⟨q, hq, hz⟩)
        exacts [⟨p, Or.inl rfl, Or.inl h⟩, ⟨p, Or.inl rfl, Or.inr h⟩, ⟨q, Or.inr hq, hz⟩]
      · rintro ⟨q, rfl | hq, hz | hz⟩
        exacts [Or.inl (Or.inl hz), Or.inl (Or.inr hz),
          Or.inr ⟨q, hq, Or.inl hz⟩, Or.inr ⟨q, hq, Or.inr hz⟩]

/-- The total symbol size of a worklist: the sum of the sizes of both components
of every pair. -/
def wlSize : List (Term sigma nu × Term sigma nu) → Nat
  | [] => 0
  | p :: W => Term.size p.1 + Term.size p.2 + wlSize W

@[simp] theorem wlSize_nil : wlSize ([] : List (Term sigma nu × Term sigma nu)) = 0 := rfl

@[simp] theorem wlSize_cons (p : Term sigma nu × Term sigma nu)
    (W : List (Term sigma nu × Term sigma nu)) :
    wlSize (p :: W) = Term.size p.1 + Term.size p.2 + wlSize W := rfl

theorem wlSize_append (W1 W2 : List (Term sigma nu × Term sigma nu)) :
    wlSize (W1 ++ W2) = wlSize W1 + wlSize W2 := by
  induction W1 with
  | nil => simp
  | cons p W ih => simp only [List.cons_append, wlSize_cons, ih]; omega

/-! ## Applying a single-point substitution across a worklist -/

/-- Apply `subst1 x t` to both components of every pair in a worklist. -/
def wlSubst1 [DecidableEq nu] (x : nu) (t : Term sigma nu)
    (W : List (Term sigma nu × Term sigma nu)) : List (Term sigma nu × Term sigma nu) :=
  W.map (fun p => (apply (subst1 x t) p.1, apply (subst1 x t) p.2))

/-- The eliminate move's variable-set bound, lifted from
`Subst.FV_elim_strict_subset` to a whole worklist: when `x` does not occur in
`t`, substituting `subst1 x t` removes `x` from the worklist variable set and
keeps the result within `(wlVars W).erase x` together with `vars t`. -/
theorem wlVars_subst1 [DecidableEq nu] (x : nu) (t : Term sigma nu) (hx : occurs x t = false)
    (W : List (Term sigma nu × Term sigma nu)) :
    x ∉ wlVars (wlSubst1 x t W) ∧
      wlVars (wlSubst1 x t W) ⊆ (wlVars W).erase x ∪ Term.vars t := by
  refine ⟨?_, ?_⟩
  · rw [mem_wlVars_iff]
    rintro ⟨q, hq, hz⟩
    simp only [wlSubst1, List.mem_map] at hq
    obtain ⟨p, _, rfl⟩ := hq
    rcases hz with hz | hz
    · exact (FV_elim_strict_subset x t hx p.1).1 hz
    · exact (FV_elim_strict_subset x t hx p.2).1 hz
  · intro z hz
    rw [mem_wlVars_iff] at hz
    obtain ⟨q, hq, hzc⟩ := hz
    simp only [wlSubst1, List.mem_map] at hq
    obtain ⟨p, hpW, rfl⟩ := hq
    have key : ∀ (w : Term sigma nu), (z ∈ Term.vars w → z ∈ wlVars W) →
        z ∈ Term.vars (apply (subst1 x t) w) → z ∈ (wlVars W).erase x ∪ Term.vars t := by
      intro w hwv hw
      have hsub := (FV_elim_strict_subset x t hx w).2 hw
      rw [Finset.mem_union] at hsub ⊢
      rcases hsub with hin | hin
      · left
        rw [Finset.mem_erase] at hin ⊢
        exact ⟨hin.1, hwv hin.2⟩
      · right; exact hin
    rcases hzc with hz | hz
    · exact key p.1 (fun h => mem_wlVars_iff.2 ⟨p, hpW, Or.inl h⟩) hz
    · exact key p.2 (fun h => mem_wlVars_iff.2 ⟨p, hpW, Or.inr h⟩) hz

/-- Eliminate-move strict decrease of the variable-count component. The "before"
worklist `(var x, t) :: rest` carries `x` in its variable set, while the "after"
worklist `wlSubst1 x t rest` does not, so the card strictly falls. The `var x`
appears as the first component, contributing `{x}` to the before-set. -/
theorem elim_card_lt [DecidableEq nu] (x : nu) (t : Term sigma nu) (hx : occurs x t = false)
    (rest : List (Term sigma nu × Term sigma nu)) :
    (wlVars (wlSubst1 x t rest)).card
      < (wlVars ((Term.var x, t) :: rest)).card := by
  obtain ⟨hxnot, hsub⟩ := wlVars_subst1 x t hx rest
  have hxbefore : x ∈ wlVars ((Term.var x, t) :: rest) := by
    rw [wlVars_cons, Term.vars_var]
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton_self x))
  have hsub' : wlVars (wlSubst1 x t rest) ⊆ wlVars ((Term.var x, t) :: rest) := by
    rw [wlVars_cons, Term.vars_var]
    refine hsub.trans (Finset.union_subset ?_ ?_)
    · intro z hz
      exact Finset.mem_union_right _ (Finset.mem_of_mem_erase hz)
    · intro z hz
      exact Finset.mem_union_left _ (Finset.mem_union_right _ hz)
  have hss : wlVars (wlSubst1 x t rest) ⊂ wlVars ((Term.var x, t) :: rest) := by
    rw [Finset.ssubset_iff_of_subset hsub']
    exact ⟨x, hxbefore, hxnot⟩
  exact Finset.card_lt_card hss

/-- The symmetric eliminate-move strict decrease, for the oriented case where the
variable is the second component: `(t, var x) :: rest`. -/
theorem elim_card_lt' [DecidableEq nu] (x : nu) (t : Term sigma nu) (hx : occurs x t = false)
    (rest : List (Term sigma nu × Term sigma nu)) :
    (wlVars (wlSubst1 x t rest)).card
      < (wlVars ((t, Term.var x) :: rest)).card := by
  obtain ⟨hxnot, hsub⟩ := wlVars_subst1 x t hx rest
  have hxbefore : x ∈ wlVars ((t, Term.var x) :: rest) := by
    rw [wlVars_cons, Term.vars_var]
    exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton_self x))
  have hsub' : wlVars (wlSubst1 x t rest) ⊆ wlVars ((t, Term.var x) :: rest) := by
    rw [wlVars_cons, Term.vars_var]
    refine hsub.trans (Finset.union_subset ?_ ?_)
    · intro z hz
      exact Finset.mem_union_right _ (Finset.mem_of_mem_erase hz)
    · intro z hz
      exact Finset.mem_union_left _ (Finset.mem_union_left _ hz)
  have hss : wlVars (wlSubst1 x t rest) ⊂ wlVars ((t, Term.var x) :: rest) := by
    rw [Finset.ssubset_iff_of_subset hsub']
    exact ⟨x, hxbefore, hxnot⟩
  exact Finset.card_lt_card hss

/-! ## Decompose-move measures -/

/-- Zip two argument lists into a worklist of pairs. Intended for equal-length
lists, where it pairs corresponding arguments; a length clash truncates (the
caller guards on equal length and fails otherwise). -/
def zipPairs : List (Term sigma nu) → List (Term sigma nu) →
    List (Term sigma nu × Term sigma nu)
  | [], _ => []
  | _, [] => []
  | a :: as, b :: bs => (a, b) :: zipPairs as bs

/-- Decompose keeps the variable set fixed: the variables of the argument-pair
worklist (followed by `rest`) match those of `(app f as, app f bs) :: rest`,
given equal arity. -/
theorem wlVars_zipPairs_append [DecidableEq nu] (f g : sigma)
    (as bs : List (Term sigma nu)) (rest : List (Term sigma nu × Term sigma nu))
    (hlen : as.length = bs.length) :
    wlVars (zipPairs as bs ++ rest)
      = wlVars ((Term.app f as, Term.app g bs) :: rest) := by
  rw [wlVars_cons, Term.vars_app, Term.vars_app]
  induction as generalizing bs with
  | nil =>
      cases bs with
      | nil => simp [zipPairs]
      | cons b bs => simp at hlen
  | cons a as ih =>
      cases bs with
      | nil => simp at hlen
      | cons b bs =>
          simp only [zipPairs, List.cons_append, wlVars_cons, Term.varsList_cons]
          rw [ih bs (by simpa using hlen)]
          ext z; simp only [Finset.mem_union]; tauto

/-- The symbol size of a zipped argument-pair worklist is the sum of the two
argument lists' sizes, given equal length. -/
theorem wlSize_zipPairs_eq (as bs : List (Term sigma nu)) (hlen : as.length = bs.length) :
    wlSize (zipPairs as bs) = Term.sizeList as + Term.sizeList bs := by
  induction as generalizing bs with
  | nil =>
      cases bs with
      | nil => rfl
      | cons b bs => simp at hlen
  | cons a as ih =>
      cases bs with
      | nil => simp at hlen
      | cons b bs =>
          simp only [zipPairs, wlSize_cons, Term.sizeList_cons]
          rw [ih bs (by simpa using hlen)]; omega

/-- Decompose strictly shrinks the symbol-size component: stripping the two
matched `app` wrappers removes `2` from the total size. -/
theorem wlSize_zipPairs_lt (f g : sigma)
    (as bs : List (Term sigma nu)) (rest : List (Term sigma nu × Term sigma nu))
    (hlen : as.length = bs.length) :
    wlSize (zipPairs as bs ++ rest)
      < wlSize ((Term.app f as, Term.app g bs) :: rest) := by
  rw [wlSize_append, wlSize_cons, Term.size_app, Term.size_app,
    wlSize_zipPairs_eq as bs hlen]
  omega

/-! ## Delete-move measures -/

/-- Delete keeps the variable set within the previous one: dropping the head pair
can only remove variables. -/
theorem wlVars_tail_subset [DecidableEq nu] (p : Term sigma nu × Term sigma nu)
    (rest : List (Term sigma nu × Term sigma nu)) :
    wlVars rest ⊆ wlVars (p :: rest) := by
  rw [wlVars_cons]
  exact Finset.subset_union_right

/-- Delete strictly shrinks the symbol size: the dropped pair has size at least
`2`, since each term has size at least `1`. -/
theorem wlSize_tail_lt (p : Term sigma nu × Term sigma nu)
    (rest : List (Term sigma nu × Term sigma nu)) :
    wlSize rest < wlSize (p :: rest) := by
  rw [wlSize_cons]
  have h1 := Term.one_le_size p.1
  have h2 := Term.one_le_size p.2
  omega

/-! ## The unifier -/

/-- Solve a worklist of equation pairs by Martelli-Montanari transformation,
returning an idempotent unifying substitution as data, or `none` on a clash or
occurs-check failure.

The recursion is on the worklist; termination is by the lexicographic measure
`(card (wlVars W), wlSize W, W.length)`. Each move provides the corresponding
strict decrease proved above. -/
def solve [DecidableEq sigma] [DecidableEq nu] :
    List (Term sigma nu × Term sigma nu) → Option (Subst sigma nu)
  | [] => some Subst.id
  | (Term.var x, Term.var y) :: rest =>
      if x = y then
        -- delete
        solve rest
      else
        -- eliminate x := var y (the occurs-check passes: a distinct variable)
        (solve (wlSubst1 x (Term.var y) rest)).map (fun s => s.comp (subst1 x (Term.var y)))
  | (Term.var x, Term.app g bs) :: rest =>
      -- eliminate x := app g bs, guarded by the occurs-check
      if occurs x (Term.app g bs) then
        none
      else
        (solve (wlSubst1 x (Term.app g bs) rest)).map
          (fun s => s.comp (subst1 x (Term.app g bs)))
  | (Term.app f as, Term.var y) :: rest =>
      -- orient, then eliminate y := app f as, guarded by the occurs-check
      if occurs y (Term.app f as) then
        none
      else
        (solve (wlSubst1 y (Term.app f as) rest)).map
          (fun s => s.comp (subst1 y (Term.app f as)))
  | (Term.app f as, Term.app g bs) :: rest =>
      -- decompose on matching head and arity; otherwise clash
      if f = g ∧ as.length = bs.length then
        solve (zipPairs as bs ++ rest)
      else
        none
  termination_by W => (wlVars W |>.card, wlSize W, W.length)
  decreasing_by
    -- Each of the five moves provides a strict lexicographic decrease of
    -- `(card (wlVars W), wlSize W, W.length)`.
    · -- delete `var x =?= var x`: dropping the head pair keeps the variable count
      -- within the previous one; if it ties, the strictly smaller symbol size
      -- settles the decrease.
      rw [Prod.lex_def]
      rcases lt_or_eq_of_le
          (Finset.card_le_card (wlVars_tail_subset (Term.var x, Term.var y) rest)) with h | h
      · exact Or.inl h
      · refine Or.inr ⟨h, ?_⟩
        rw [Prod.lex_def]
        exact Or.inl (wlSize_tail_lt (Term.var x, Term.var y) rest)
    · -- eliminate `var x := var y` with `x ≠ y`: the occurs-check passes and the
      -- variable count strictly drops.
      refine Prod.Lex.left _ _ ?_
      have hocc : occurs x (Term.var (sigma := sigma) y) = false := by
        simp only [occurs_var, decide_eq_false_iff_not]; exact ‹¬ x = y›
      exact elim_card_lt x (Term.var y) hocc rest
    · -- eliminate `var x := app g bs`: the occurs-check passes and the variable
      -- count strictly drops.
      refine Prod.Lex.left _ _ ?_
      exact elim_card_lt x (Term.app g bs) (by simpa using ‹¬ occurs x (Term.app g bs) = true›) rest
    · -- eliminate (orient) `app f as := var y`: the occurs-check passes and the
      -- variable count strictly drops.
      refine Prod.Lex.left _ _ ?_
      exact elim_card_lt' y (Term.app f as)
        (by simpa using ‹¬ occurs y (Term.app f as) = true›) rest
    · -- decompose: the variable count ties and the symbol size strictly drops.
      obtain ⟨_, hlen⟩ := ‹f = g ∧ as.length = bs.length›
      rw [Prod.lex_def]
      refine Or.inr ⟨?_, ?_⟩
      · rw [wlVars_zipPairs_append f g as bs rest hlen]
      · rw [Prod.lex_def]
        exact Or.inl (wlSize_zipPairs_lt f g as bs rest hlen)

/-- Unify two terms: return an idempotent most-general unifier as data when one
exists, or `none` on a clash or occurs-check failure. Implemented by solving the
singleton worklist `[(s, t)]`. -/
def unify [DecidableEq sigma] [DecidableEq nu]
    (s t : Term sigma nu) : Option (Subst sigma nu) :=
  solve [(s, t)]

/-! ## Non-vacuity battery

These decidable, named lemmas confirm the engine computes genuine bindings, fails
on clashes, and binds variables under a function symbol. They use the concrete
signature `sigma = nu = Nat` and reduce through the equation lemmas for `solve`
(the well-founded recursion unfolds under `simp [unify, solve, ...]`). -/

/-- A variable unifies with any term whose occurs-check passes, here the constant
`app 0 []`; the result is a substitution (`isSome`). -/
theorem unify_var_const_isSome :
    (unify (sigma := Nat) (nu := Nat) (Term.var 0) (Term.app 0 [])).isSome = true := by
  simp [unify, solve, wlSubst1]

/-- Two distinct nullary applications (constants) do not unify. -/
theorem unify_distinct_consts_none :
    unify (sigma := Nat) (nu := Nat) (Term.app 0 []) (Term.app 1 []) = none := by
  simp [unify, solve]

/-- Unifying `f x` with `f c` binds `x` to the constant `c`. The returned
substitution sends the variable `0` to `app 1 []`. -/
theorem unify_app_var_binds :
    (unify (sigma := Nat) (nu := Nat)
        (Term.app 0 [Term.var 0]) (Term.app 0 [Term.app 1 []])).map
      (fun s => s 0) = some (Term.app 1 []) := by
  simp [unify, solve, zipPairs, wlSubst1, Subst.comp, subst1]

/-- The same unifier leaves an unrelated variable untouched (a minimal binding):
variable `5` maps to itself. -/
theorem unify_app_var_fixes_other :
    (unify (sigma := Nat) (nu := Nat)
        (Term.app 0 [Term.var 0]) (Term.app 0 [Term.app 1 []])).map
      (fun s => s 5) = some (Term.var 5) := by
  simp [unify, solve, zipPairs, wlSubst1, Subst.comp, Subst.id, subst1]

/-- A nullary head against a non-nullary head of the same symbol is an arity
clash and does not unify. -/
theorem unify_arity_clash_none :
    unify (sigma := Nat) (nu := Nat)
      (Term.app 0 []) (Term.app 0 [Term.var 0]) = none := by
  simp [unify, solve]

/-- The occurs-check blocks the cyclic equation `x =?= f x`. -/
theorem unify_occurs_check_none :
    unify (sigma := Nat) (nu := Nat)
      (Term.var 0) (Term.app 0 [Term.var 0]) = none := by
  simp [unify, solve, occurs]

end OperatorKO7.Meta.Rewriting

/-! ## Axiom audit -/

#print axioms OperatorKO7.Meta.Rewriting.unify
#print axioms OperatorKO7.Meta.Rewriting.solve
#print axioms OperatorKO7.Meta.Rewriting.unify_var_const_isSome
#print axioms OperatorKO7.Meta.Rewriting.unify_distinct_consts_none
#print axioms OperatorKO7.Meta.Rewriting.unify_app_var_binds
#print axioms OperatorKO7.Meta.Rewriting.unify_app_var_fixes_other
#print axioms OperatorKO7.Meta.Rewriting.unify_arity_clash_none
#print axioms OperatorKO7.Meta.Rewriting.unify_occurs_check_none
