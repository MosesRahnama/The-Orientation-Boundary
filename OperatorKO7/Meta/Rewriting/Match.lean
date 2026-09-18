import OperatorKO7.Meta.Rewriting.Subst

/-!
# One-sided matching for the generic rewriting library

Roadmap source: `ROADMAP-01-generic-critical-pair-lemma.md`, sections 4 and 5
(`Meta/Rewriting/Match.lean`, "matchAgainst : Term -> Term -> Option Subst +
soundness, a degenerate unify"). Wave 2B of the rewriting foundation.

Matching is the one-sided specialization of unification: a *pattern* `l`, whose
variables are open for instantiation, is matched against a *target* `t`, which is
treated as fixed. A successful match returns a substitution `s` with
`s.apply l = t`. This is the substitution-instance recognizer that the
critical-pair construction uses to detect when one rule's left-hand side embeds in
another's.

The matcher is structural on the pattern, threading a partial-binding accumulator
`PartialMap` (a finite association list from variables to terms):

- a pattern variable `x` binds to the corresponding subterm of `t`; if `x` is
  already bound, the existing binding must coincide with `t` (a repeated pattern
  variable matches consistently, and a conflict reports `none`);
- `app f as` matches `app f bs` argument-wise, succeeding only on a shared head
  symbol and shared arity, threading the accumulator left to right;
- a variable pattern matched against any target binds that variable; an
  application pattern matched against a variable target reports `none`.

On success the accumulated partial map is closed into a total `Subst` (variables
outside the map are sent to themselves), and `matchAgainst_sound` certifies that
this substitution reproduces the target: `matchAgainst l t = some s -> s.apply l = t`.

Trust: kernel-only; baseline-only under `#print axioms` (subset of
`{propext, Classical.choice, Quot.sound}`). Any `Classical.choice`/`propext`
dependence is from `Finset`/`DecidableEq` plumbing inherited through `Term`.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.Rewriting

open Subst (apply applyList)

universe u v

variable {sigma : Type u} {nu : Type v}

/-! ## Partial bindings -/

/-- A partial binding accumulator: a finite association list from variables to the
terms they are tentatively bound to. The matcher threads one of these through the
pattern, growing it as fresh pattern variables are encountered. -/
abbrev PartialMap (sigma : Type u) (nu : Type v) := List (nu × Term sigma nu)

namespace PartialMap

variable [DecidableEq nu]

/-- Look up the current binding of a variable in the accumulator, returning the
first matching entry if one is present. -/
def find? (m : PartialMap sigma nu) (x : nu) : Option (Term sigma nu) :=
  (List.find? (fun p => p.1 = x) m).map Prod.snd

/-- Close a partial binding map into a total substitution: a variable found in the
map is sent to its recorded term, and every other variable is sent to itself. -/
def toSubst (m : PartialMap sigma nu) : Subst sigma nu :=
  fun x => (find? m x).getD (.var x)

@[simp] theorem find?_nil (x : nu) :
    find? ([] : PartialMap sigma nu) x = none := rfl

theorem find?_cons (p : nu × Term sigma nu) (m : PartialMap sigma nu) (x : nu) :
    find? (p :: m) x = if p.1 = x then some p.2 else find? m x := by
  simp only [find?, List.find?_cons]
  by_cases hp : p.1 = x
  · simp [hp]
  · simp [hp]

/-- A successful lookup of `x` forces the closed substitution to send `x` to the
looked-up term. This is the bridge from the accumulator to `toSubst`. -/
theorem toSubst_apply_var_of_find? {m : PartialMap sigma nu} {x : nu}
    {t : Term sigma nu} (h : find? m x = some t) :
    toSubst m x = t := by
  simp [toSubst, h]

/-- A failed lookup distinguishes the variable from a freshly prepended head: if `x`
is absent from `m` but present after prepending `(y, t)`, then `x = y`. The
contrapositive form used below: a successful lookup in `m` survives the prepend of a
head whose key is itself absent from `m`. -/
theorem find?_cons_of_find?_of_head_fresh {m : PartialMap sigma nu}
    {y : nu} {t : Term sigma nu} {x : nu} {b : Term sigma nu}
    (hfresh : find? m y = none) (h : find? m x = some b) :
    find? ((y, t) :: m) x = some b := by
  rw [find?_cons]
  by_cases hyx : y = x
  · -- `x = y` would make the `m`-lookup of `x` both `none` and `some b`
    subst hyx
    rw [h] at hfresh
    exact absurd hfresh (by simp)
  · simpa [hyx] using h

end PartialMap

/-! ## The matcher -/

mutual
/-- Match a pattern against a target while threading a partial-binding accumulator.

`matchAux l t m` attempts to extend `m` so that the closed substitution reproduces
`t` from `l`:

- a variable pattern binds to `t`; a binding already present for that variable must
  equal `t`, otherwise the match reports `none`;
- an application pattern matches a target with the same head symbol and arity,
  matching arguments left to right through `matchAuxList`; a mismatched head or arity
  reports `none`;
- an application pattern against a variable target reports `none`. -/
def matchAux [DecidableEq sigma] [DecidableEq nu] :
    Term sigma nu → Term sigma nu → PartialMap sigma nu → Option (PartialMap sigma nu)
  | .var x, t, m =>
      match PartialMap.find? m x with
      | some t' => if t' = t then some m else none
      | none => some ((x, t) :: m)
  | .app _ _, .var _, _ => none
  | .app f ls, .app g ts, m =>
      if f = g then matchAuxList ls ts m else none
/-- Argument-list companion of `matchAux`: match two argument lists position by
position, threading the accumulator, succeeding only when the lists have equal
length. -/
def matchAuxList [DecidableEq sigma] [DecidableEq nu] :
    List (Term sigma nu) → List (Term sigma nu) → PartialMap sigma nu →
      Option (PartialMap sigma nu)
  | [], [], m => some m
  | [], _ :: _, _ => none
  | _ :: _, [], _ => none
  | l :: ls, t :: ts, m =>
      match matchAux l t m with
      | some m' => matchAuxList ls ts m'
      | none => none
end

/-- Match a pattern `l` against a target `t`, returning a substitution `s` with
`s.apply l = t` when the pattern is a substitution instance of the target, and
`none` otherwise. One-sided: only the pattern's variables are instantiated; the
target is fixed. See `matchAgainst_sound`. -/
def matchAgainst [DecidableEq sigma] [DecidableEq nu]
    (l t : Term sigma nu) : Option (Subst sigma nu) :=
  (matchAux l t []).map PartialMap.toSubst

/-! ## Monotonicity of the accumulator

Every binding present in the input accumulator survives the match: a variable bound
to `b` on the way in is still bound to `b` on the way out. This lets the soundness
proof transport a binding established at an inner step out to the final accumulator. -/

/-- The argument-list driver for `matchAux_find?_mono`: bindings are preserved
through `matchAuxList`. Parameterized by the per-argument monotonicity statement
`ih`, so it inducts on the argument list independently of the pattern recursion. -/
theorem matchAuxList_find?_mono [DecidableEq sigma] [DecidableEq nu]
    {ls : List (Term sigma nu)}
    (ih : ∀ a ∈ ls, ∀ (t : Term sigma nu) (m m' : PartialMap sigma nu)
            (x : nu) (b : Term sigma nu),
            matchAux a t m = some m' → PartialMap.find? m x = some b →
              PartialMap.find? m' x = some b) :
    ∀ (ts : List (Term sigma nu)) (m m' : PartialMap sigma nu) (x : nu) (b : Term sigma nu),
      matchAuxList ls ts m = some m' → PartialMap.find? m x = some b →
        PartialMap.find? m' x = some b := by
  induction ls with
  | nil =>
      intro ts m m' x b hmatch hfind
      cases ts with
      | nil =>
          simp only [matchAuxList, Option.some.injEq] at hmatch
          subst hmatch; exact hfind
      | cons t ts => simp only [matchAuxList, reduceCtorEq] at hmatch
  | cons l ls ihls =>
      intro ts m m' x b hmatch hfind
      cases ts with
      | nil => simp only [matchAuxList, reduceCtorEq] at hmatch
      | cons t ts =>
          simp only [matchAuxList] at hmatch
          cases hstep : matchAux l t m with
          | some m1 =>
              rw [hstep] at hmatch
              have hmid := ih l (by simp) t m m1 x b hstep hfind
              exact ihls (fun a ha => ih a (by simp [ha])) ts m1 m' x b hmatch hmid
          | none => rw [hstep] at hmatch; simp only [reduceCtorEq] at hmatch

/-- Bindings are preserved by `matchAux`: a variable already bound to `b` stays bound
to `b` in the output accumulator. Proven by structural induction on the pattern,
reducing the application case to `matchAuxList_find?_mono`. -/
theorem matchAux_find?_mono [DecidableEq sigma] [DecidableEq nu] :
    ∀ (l t : Term sigma nu) (m m' : PartialMap sigma nu) (x : nu) (b : Term sigma nu),
      matchAux l t m = some m' → PartialMap.find? m x = some b →
        PartialMap.find? m' x = some b := by
  intro l
  induction l using Term.rec' with
  | hvar y =>
      intro t m m' x b hmatch hfind
      simp only [matchAux] at hmatch
      cases hy : PartialMap.find? m y with
      | some t' =>
          rw [hy] at hmatch
          by_cases ht : t' = t
          · simp only [ht, if_true, Option.some.injEq] at hmatch
            subst hmatch; exact hfind
          · simp only [ht, if_false, reduceCtorEq] at hmatch
      | none =>
          rw [hy] at hmatch
          simp only [Option.some.injEq] at hmatch
          subst hmatch
          exact PartialMap.find?_cons_of_find?_of_head_fresh hy hfind
  | happ f ls ih =>
      intro t m m' x b hmatch hfind
      cases t with
      | var z => simp only [matchAux, reduceCtorEq] at hmatch
      | app g ts =>
          simp only [matchAux] at hmatch
          by_cases hfg : f = g
          · simp only [hfg, if_true] at hmatch
            exact matchAuxList_find?_mono ih ts m m' x b hmatch hfind
          · simp only [hfg, if_false, reduceCtorEq] at hmatch

/-! ## All pattern variables become bound

After a successful match, every variable occurring in the pattern is bound in the
output accumulator. Combined with monotonicity, this makes the closed substitution
depend only on bindings the match actually fixed. -/

/-- The argument-list driver for `matchAux_vars_bound`: every variable occurring in
the pattern argument list is bound in the output accumulator. Parameterized by the
per-argument statement `ih`, so it inducts on the argument list independently. -/
theorem matchAuxList_vars_bound [DecidableEq sigma] [DecidableEq nu]
    {ls : List (Term sigma nu)}
    (ih : ∀ a ∈ ls, ∀ (t : Term sigma nu) (m m' : PartialMap sigma nu),
            matchAux a t m = some m' →
              ∀ x ∈ Term.vars a, ∃ b, PartialMap.find? m' x = some b) :
    ∀ (ts : List (Term sigma nu)) (m m' : PartialMap sigma nu),
      matchAuxList ls ts m = some m' →
        ∀ x ∈ Term.varsList ls, ∃ b, PartialMap.find? m' x = some b := by
  induction ls with
  | nil =>
      intro ts m m' _ x hx
      simp only [Term.varsList_nil, Finset.notMem_empty] at hx
  | cons l ls ihls =>
      intro ts m m' hmatch x hx
      cases ts with
      | nil => simp only [matchAuxList, reduceCtorEq] at hmatch
      | cons t ts =>
          simp only [matchAuxList] at hmatch
          cases hstep : matchAux l t m with
          | some m1 =>
              rw [hstep] at hmatch
              simp only [Term.varsList_cons, Finset.mem_union] at hx
              rcases hx with hx | hx
              · -- `x` is in the head; bound after the head match, lifted to `m'`
                obtain ⟨b, hb⟩ := ih l (by simp) t m m1 hstep x hx
                exact ⟨b, matchAuxList_find?_mono (fun a _ => matchAux_find?_mono a)
                  ts m1 m' x b hmatch hb⟩
              · -- `x` is in the tail; bound by the recursive call
                exact ihls (fun a ha => ih a (by simp [ha])) ts m1 m' hmatch x hx
          | none => rw [hstep] at hmatch; simp only [reduceCtorEq] at hmatch

/-- Every variable of the pattern is bound in the output accumulator after a
successful match. Proven by structural induction on the pattern, reducing the
application case to `matchAuxList_vars_bound`. -/
theorem matchAux_vars_bound [DecidableEq sigma] [DecidableEq nu] :
    ∀ (l t : Term sigma nu) (m m' : PartialMap sigma nu),
      matchAux l t m = some m' →
        ∀ x ∈ Term.vars l, ∃ b, PartialMap.find? m' x = some b := by
  intro l
  induction l using Term.rec' with
  | hvar y =>
      intro t m m' hmatch x hx
      simp only [Term.vars_var, Finset.mem_singleton] at hx
      subst hx
      simp only [matchAux] at hmatch
      cases hy : PartialMap.find? m x with
      | some t' =>
          rw [hy] at hmatch
          by_cases ht : t' = t
          · simp only [ht, if_true, Option.some.injEq] at hmatch
            subst hmatch; exact ⟨t', hy⟩
          · simp only [ht, if_false, reduceCtorEq] at hmatch
      | none =>
          rw [hy] at hmatch
          simp only [Option.some.injEq] at hmatch
          subst hmatch
          refine ⟨t, ?_⟩
          rw [PartialMap.find?_cons]; simp
  | happ f ls ih =>
      intro t m m' hmatch x hx
      cases t with
      | var z => simp only [matchAux, reduceCtorEq] at hmatch
      | app g ts =>
          simp only [matchAux] at hmatch
          by_cases hfg : f = g
          · simp only [hfg, if_true] at hmatch
            rw [Term.vars_app] at hx
            exact matchAuxList_vars_bound ih ts m m' hmatch x hx
          · simp only [hfg, if_false, reduceCtorEq] at hmatch

/-! ## Application depends only on the variables that occur -/

/-- Two substitutions that agree on every variable of a term produce the same
application. The pointwise-congruence principle for `apply`, proven by structural
induction on the term. -/
theorem apply_congr_of_eq_on_vars [DecidableEq nu] :
    ∀ (s s' : Subst sigma nu) (t : Term sigma nu),
      (∀ x ∈ Term.vars t, s x = s' x) → apply s t = apply s' t := by
  intro s s' t
  induction t using Term.rec' with
  | hvar x =>
      intro h
      rw [Subst.apply_var, Subst.apply_var]
      exact h x (by simp)
  | happ f args ih =>
      intro h
      rw [Subst.apply_app, Subst.apply_app, Subst.applyList_eq_map,
        Subst.applyList_eq_map]
      congr 1
      apply List.map_congr_left
      intro a ha
      apply ih a ha
      intro x hx
      apply h x
      rw [Term.vars_app, Term.mem_varsList_iff]
      exact ⟨a, ha, hx⟩

/-! ## Soundness -/

/-- The argument-list driver for `matchAux_sound_core`: a successful `matchAuxList`
produces an accumulator whose closed substitution maps the pattern argument list onto
the target argument list. The head image is promoted from the intermediate
accumulator to the final one through monotonicity and `apply_congr_of_eq_on_vars`.
Parameterized by the per-argument soundness statement `ih`. -/
theorem matchAuxList_sound_core [DecidableEq sigma] [DecidableEq nu]
    {ls : List (Term sigma nu)}
    (ih : ∀ a ∈ ls, ∀ (t : Term sigma nu) (m m' : PartialMap sigma nu),
            matchAux a t m = some m' → apply (PartialMap.toSubst m') a = t) :
    ∀ (ts : List (Term sigma nu)) (m m' : PartialMap sigma nu),
      matchAuxList ls ts m = some m' →
        ls.map (apply (PartialMap.toSubst m')) = ts := by
  induction ls with
  | nil =>
      intro ts m m' hmatch
      cases ts with
      | nil => simp
      | cons t ts => simp only [matchAuxList, reduceCtorEq] at hmatch
  | cons a as ihas =>
      intro ts m m' hmatch
      cases ts with
      | nil => simp only [matchAuxList, reduceCtorEq] at hmatch
      | cons t ts =>
          simp only [matchAuxList] at hmatch
          cases hstep : matchAux a t m with
          | some m1 =>
              rw [hstep] at hmatch
              -- head: `a` maps to `t` under the intermediate accumulator `m1`
              have hhead_m1 : apply (PartialMap.toSubst m1) a = t :=
                ih a (by simp) t m m1 hstep
              -- tail: the recursive call fixes the rest under the final `m'`
              have htail : as.map (apply (PartialMap.toSubst m')) = ts :=
                ihas (fun b hb => ih b (by simp [hb])) ts m1 m' hmatch
              -- promote the head image from `m1` to `m'`: they agree on `vars a`,
              -- since each such variable is bound in `m1` and survives into `m'`
              have hhead_m' : apply (PartialMap.toSubst m') a = t := by
                rw [← hhead_m1]
                apply apply_congr_of_eq_on_vars
                intro x hx
                obtain ⟨b, hb⟩ := matchAux_vars_bound a t m m1 hstep x hx
                have hb' : PartialMap.find? m' x = some b :=
                  matchAuxList_find?_mono (fun c _ => matchAux_find?_mono c)
                    ts m1 m' x b hmatch hb
                rw [PartialMap.toSubst_apply_var_of_find? hb,
                  PartialMap.toSubst_apply_var_of_find? hb']
              simp only [List.map_cons, hhead_m', htail]
          | none => rw [hstep] at hmatch; simp only [reduceCtorEq] at hmatch

/-- Soundness core: a successful `matchAux` produces an accumulator whose closed
substitution carries the pattern onto the target. Proven by structural induction on
the pattern, reducing the application case to `matchAuxList_sound_core`. -/
theorem matchAux_sound_core [DecidableEq sigma] [DecidableEq nu] :
    ∀ (l t : Term sigma nu) (m m' : PartialMap sigma nu),
      matchAux l t m = some m' → apply (PartialMap.toSubst m') l = t := by
  intro l
  induction l using Term.rec' with
  | hvar y =>
      intro t m m' hmatch
      simp only [matchAux] at hmatch
      cases hy : PartialMap.find? m y with
      | some t' =>
          rw [hy] at hmatch
          by_cases ht : t' = t
          · simp only [ht, if_true, Option.some.injEq] at hmatch
            subst hmatch
            rw [Subst.apply_var, PartialMap.toSubst_apply_var_of_find? hy, ht]
          · simp only [ht, if_false, reduceCtorEq] at hmatch
      | none =>
          rw [hy] at hmatch
          simp only [Option.some.injEq] at hmatch
          subst hmatch
          rw [Subst.apply_var]
          have hfind : PartialMap.find? ((y, t) :: m) y = some t := by
            rw [PartialMap.find?_cons]; simp
          rw [PartialMap.toSubst_apply_var_of_find? hfind]
  | happ f ls ih =>
      intro t m m' hmatch
      cases t with
      | var z => simp only [matchAux, reduceCtorEq] at hmatch
      | app g ts =>
          simp only [matchAux] at hmatch
          by_cases hfg : f = g
          · subst hfg
            simp only [if_true] at hmatch
            rw [Subst.apply_app, Subst.applyList_eq_map]
            congr 1
            exact matchAuxList_sound_core ih ts m m' hmatch
          · simp only [hfg, if_false, reduceCtorEq] at hmatch

/-- Soundness: a successful match returns a substitution that reproduces the target
from the pattern. The match-as-data obligation for the rewriting library. -/
theorem matchAgainst_sound [DecidableEq sigma] [DecidableEq nu]
    {l t : Term sigma nu} {s : Subst sigma nu}
    (h : matchAgainst l t = some s) : apply s l = t := by
  simp only [matchAgainst, Option.map_eq_some_iff] at h
  obtain ⟨m', hm', rfl⟩ := h
  exact matchAux_sound_core l t [] m' hm'

/-! ## Non-vacuity examples -/

section Examples

/-- A concrete two-symbol signature: a binary `f` and a constant `c`. -/
inductive Sym | f | c
deriving DecidableEq

open Term Subst

/-- The constant term `c`. -/
private def cTerm : Term Sym Nat := .app .c []
/-- The pattern `f(x, c)` with variable `x = 0`. -/
private def patFxc : Term Sym Nat := .app .f [.var 0, cTerm]
/-- The target `f(c, c)`. -/
private def tgtFcc : Term Sym Nat := .app .f [cTerm, cTerm]

/-- A successful match returns a substitution reproducing the target. The pattern
`f(x, c)` matches the target `f(c, c)` by binding `x` to `c`, and the returned
substitution carries the pattern onto the target. -/
example :
    ∃ s : Subst Sym Nat,
      matchAgainst patFxc tgtFcc = some s ∧ apply s patFxc = tgtFcc := by
  refine ⟨_, rfl, ?_⟩
  exact matchAgainst_sound (l := patFxc) (t := tgtFcc) rfl

/-- A head mismatch returns `none`: the constant pattern `c` cannot match the
application `f(c, c)` because the head symbols differ. -/
example : matchAgainst cTerm tgtFcc = (none : Option (Subst Sym Nat)) := rfl

/-- A non-linear pattern with conflicting subterms returns `none`: the pattern
`f(x, x)` cannot match `f(c, f(c, c))` because the single variable `x` is forced to
two different terms. -/
example :
    matchAgainst (.app .f [.var 0, .var 0] : Term Sym Nat)
      (.app .f [cTerm, .app .f [cTerm, cTerm]])
      = none := rfl

end Examples

end OperatorKO7.Meta.Rewriting

/-! ## Axiom audit -/

#print axioms OperatorKO7.Meta.Rewriting.matchAgainst
#print axioms OperatorKO7.Meta.Rewriting.matchAgainst_sound
