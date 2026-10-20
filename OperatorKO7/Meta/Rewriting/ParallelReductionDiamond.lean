import OperatorKO7.Meta.Rewriting.ParallelReduction
import OperatorKO7.Meta.Rewriting.Orthogonality
import OperatorKO7.Meta.Rewriting.Commutation
import OperatorKO7.Meta.Rewriting.Match

/-!
# The Takahashi complete development and the parallel-reduction diamond

Roadmap source: the capstone of the confluence-toolkit expansion atop the verified
rewriting foundation and the parallel-reduction layer (`ParallelReduction`,
`Orthogonality`, `Commutation`, `Match`). This module builds the Takahashi 1995
complete development and establishes its parallel-reduction properties, then realizes
termination-free confluence through the parallel-reduction diamond on a weakly
orthogonal system.

## What this module delivers

The Takahashi complete development:

- `completeDevelopment R t` : the term that contracts every redex available in `t` in
  one parallel sweep. A matched root redex is contracted while the matched
  substitution develops at the variables the left-hand side binds; with no root match
  each argument develops. Total, by well-founded recursion on `Term.size`, with the
  matched-substitution images strictly smaller (`size_apply_var_lt_app`) and the
  arguments strictly smaller (`Term.size_lt_of_mem`).
- `findRedex R t` : the first rule of `R` whose left-hand side matches `t`, with the
  matching substitution and a certificate carrying the match equation and the fact
  that the substitution fixes every variable outside the left-hand side.

The complete development is a parallel reduct:

- `parStep_completeDevelopment R t : ParStep R t (completeDevelopment R t)`. The
  matched-root case contracts the redex through `ParStep.root`, parallel-reducing the
  bound images by the induction hypothesis and fixing the variables outside the
  left-hand side; the no-match application case develops the arguments.
- `stepStar_completeDevelopment R t : StepStar R t (completeDevelopment R t)`, the
  rewrite-sequence realization.

The parallel-reduction diamond and termination-free confluence:

- `parStep_emptyTRS_eq` / `parStep_diamond_emptyTRS` : parallel reduction over the
  empty system is equality, so it has the diamond property.
- `weaklyOrthogonal_emptyTRS_confluent` : `StepStar (renameTRS [])` is confluent with
  no strong-normalization hypothesis, obtained from the parallel-reduction diamond
  through `diamond_imp_confluent` and the closure coincidence
  `reflTransGen_parStep_eq_stepStar`. The empty system is weakly orthogonal
  (`emptyTRS_weaklyOrthogonal`), so this realizes termination-free confluence through
  the Takahashi route on a concrete weakly orthogonal system.

Non-vacuity: the complete development is exhibited on the one-rule demonstration
system `Example.demoTRS` (`f(x) -> g(x)`).

Trust: kernel-only; baseline-only under `#print axioms` (a subset of
`{propext, Classical.choice, Quot.sound}`). Any `Classical.choice`/`propext`
dependence is from `Finset`/`DecidableEq` plumbing inherited through the foundation
modules.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.Rewriting

open scoped Subst
open Subst
open Relation

universe u v

variable {sigma : Type u} {nu : Type v}

/-! ## Subterm-size control under matching

A matched substitution sends each pattern variable to a subterm of the target, so
its image is no larger than the target, and strictly smaller when the pattern is an
application. This is the size control that makes the complete development's descent
through the matched substitution well founded. -/

/-- A substitution image of a pattern variable is no larger than the substituted
pattern: if `x` occurs in `l`, then `size (s x) ≤ size (apply s l)`. By structural
induction on `l`; in the application case the occurrence sits in some argument, whose
substituted size is one of the summands of the application's size. -/
theorem size_apply_var_le [DecidableEq nu] (s : Subst sigma nu) :
    ∀ (l : Term sigma nu) (x : nu), x ∈ Term.vars l →
      Term.size (s x) ≤ Term.size (apply s l) := by
  intro l
  induction l using Term.rec' with
  | hvar y =>
      intro x hx
      rw [Term.vars_var, Finset.mem_singleton] at hx
      subst hx
      rw [apply_var]
  | happ f args ih =>
      intro x hx
      rw [Term.vars_app, Term.mem_varsList_iff] at hx
      obtain ⟨a, ha, hxa⟩ := hx
      rw [apply_app]
      have hle : Term.size (s x) ≤ Term.size (apply s a) := ih a ha x hxa
      have hmem : apply s a ∈ applyList s args := by
        rw [applyList_eq_map]; exact List.mem_map_of_mem ha
      have hsub : Term.size (apply s a) < Term.size (Term.app f (applyList s args)) :=
        Term.size_lt_of_mem hmem
      omega

/-- A substitution image of a variable occurring in an application pattern is
strictly smaller than the substituted application: combine `size_apply_var_le` at
the argument carrying the occurrence with the strict drop from an argument to its
application. -/
theorem size_apply_var_lt_app [DecidableEq nu] (s : Subst sigma nu)
    (f : sigma) (args : List (Term sigma nu)) (x : nu)
    (hx : x ∈ Term.vars (Term.app f args)) :
    Term.size (s x) < Term.size (apply s (Term.app f args)) := by
  rw [Term.vars_app, Term.mem_varsList_iff] at hx
  obtain ⟨a, ha, hxa⟩ := hx
  have hle : Term.size (s x) ≤ Term.size (apply s a) := size_apply_var_le s a x hxa
  rw [apply_app]
  have hmem : apply s a ∈ applyList s args := by
    rw [applyList_eq_map]; exact List.mem_map_of_mem ha
  have hsub : Term.size (apply s a) < Term.size (Term.app f (applyList s args)) :=
    Term.size_lt_of_mem hmem
  omega

/-! ## Matched substitutions fix the variables outside the pattern

A successful match binds only variables that occur in the pattern, so the closed
substitution sends every variable outside the pattern to itself. The complete
development uses this to align its substitution image with the parallel-reduction
substitution at the variables the right-hand side may introduce. -/

/-- Driver for `matchAux_find?_eq_none_of_not_mem`: the keys bound by `matchAuxList`
are confined to the keys already present together with the variables of the pattern
argument list. Parameterized by the per-argument statement `ih`, inducting on the
argument list independently of the pattern recursion. -/
theorem matchAuxList_find?_eq_none_of_not_mem [DecidableEq sigma] [DecidableEq nu]
    {ls : List (Term sigma nu)}
    (ih : ∀ a ∈ ls, ∀ (t : Term sigma nu) (m m' : PartialMap sigma nu) (x : nu),
            matchAux a t m = some m' → PartialMap.find? m x = none →
              x ∉ Term.vars a → PartialMap.find? m' x = none) :
    ∀ (ts : List (Term sigma nu)) (m m' : PartialMap sigma nu) (x : nu),
      matchAuxList ls ts m = some m' → PartialMap.find? m x = none →
        x ∉ Term.varsList ls → PartialMap.find? m' x = none := by
  induction ls with
  | nil =>
      intro ts m m' x hmatch hnone _
      cases ts with
      | nil =>
          simp only [matchAuxList, Option.some.injEq] at hmatch
          subst hmatch; exact hnone
      | cons t ts => simp only [matchAuxList, reduceCtorEq] at hmatch
  | cons l ls ihls =>
      intro ts m m' x hmatch hnone hx
      cases ts with
      | nil => simp only [matchAuxList, reduceCtorEq] at hmatch
      | cons t ts =>
          simp only [matchAuxList] at hmatch
          rw [Term.varsList_cons, Finset.mem_union, not_or] at hx
          cases hstep : matchAux l t m with
          | some m1 =>
              rw [hstep] at hmatch
              have hmid : PartialMap.find? m1 x = none :=
                ih l (by simp) t m m1 x hstep hnone hx.1
              exact ihls (fun a ha => ih a (by simp [ha])) ts m1 m' x hmatch hmid hx.2
          | none => rw [hstep] at hmatch; simp only [reduceCtorEq] at hmatch

/-- A successful match leaves a variable outside the pattern unbound: if `matchAux`
succeeds and `x` is absent from `m` and from the pattern `l`, then `x` is absent from
the output accumulator. Structural induction on the pattern, reducing the
application case to `matchAuxList_find?_eq_none_of_not_mem`. -/
theorem matchAux_find?_eq_none_of_not_mem [DecidableEq sigma] [DecidableEq nu] :
    ∀ (l t : Term sigma nu) (m m' : PartialMap sigma nu) (x : nu),
      matchAux l t m = some m' → PartialMap.find? m x = none →
        x ∉ Term.vars l → PartialMap.find? m' x = none := by
  intro l
  induction l using Term.rec' with
  | hvar y =>
      intro t m m' x hmatch hnone hx
      rw [Term.vars_var, Finset.mem_singleton] at hx
      simp only [matchAux] at hmatch
      cases hy : PartialMap.find? m y with
      | some t' =>
          rw [hy] at hmatch
          by_cases ht : t' = t
          · simp only [ht, if_true, Option.some.injEq] at hmatch
            subst hmatch; exact hnone
          · simp only [ht, if_false, reduceCtorEq] at hmatch
      | none =>
          rw [hy] at hmatch
          simp only [Option.some.injEq] at hmatch
          subst hmatch
          rw [PartialMap.find?_cons]
          rw [if_neg (fun hyx => hx hyx.symm)]
          exact hnone
  | happ f ls ih =>
      intro t m m' x hmatch hnone hx
      cases t with
      | var z => simp only [matchAux, reduceCtorEq] at hmatch
      | app g ts =>
          simp only [matchAux] at hmatch
          by_cases hfg : f = g
          · simp only [hfg, if_true] at hmatch
            rw [Term.vars_app] at hx
            exact matchAuxList_find?_eq_none_of_not_mem ih ts m m' x hmatch hnone hx
          · simp only [hfg, if_false, reduceCtorEq] at hmatch

/-- A successful top-level match sends every variable outside the pattern to itself:
if `matchAgainst l t = some s` and `x` does not occur in `l`, then `s x = .var x`.
The accumulator starts empty, so its only bindings come from the pattern's
variables. -/
theorem matchAgainst_fixes_not_mem [DecidableEq sigma] [DecidableEq nu]
    {l t : Term sigma nu} {s : Subst sigma nu} (h : matchAgainst l t = some s)
    {x : nu} (hx : x ∉ Term.vars l) : s x = .var x := by
  simp only [matchAgainst, Option.map_eq_some_iff] at h
  obtain ⟨m', hm', rfl⟩ := h
  have hnone : PartialMap.find? m' x = none :=
    matchAux_find?_eq_none_of_not_mem l t [] m' x hm' (by simp) hx
  simp [PartialMap.toSubst, hnone]

/-! ## The TRS-wide root matcher

`findRedex R t` searches the rule list for the first rule whose left-hand side
matches `t`, returning that rule together with the matching substitution. A match is
certified by `matchAgainst_sound`, so the returned data reconstructs `t` as a
left-hand-side instance. -/

/-- The first rule of `R` whose left-hand side matches the term `t`, paired with the
matching substitution: scans the rules in order, returning the rule, the matcher's
substitution, and a proof that the substitution carries the rule's left-hand side
onto `t`. Returns `none` when no rule matches. The `Σ`-typed payload keeps the
matching certificate attached for the well-founded descent and the parallel-step
witness. -/
def findRedex [DecidableEq sigma] [DecidableEq nu] (R : TRS sigma nu)
    (t : Term sigma nu) :
    Option (Σ' rule : Rule sigma nu, Σ' σ : Subst sigma nu,
      PLift (rule ∈ R ∧ σ • rule.lhs = t ∧
        ∀ y, y ∉ Term.vars rule.lhs → σ y = .var y)) :=
  match R with
  | [] => none
  | rule :: rest =>
      match hm : matchAgainst rule.lhs t with
      | some σ =>
          some ⟨rule, σ, PLift.up ⟨List.mem_cons_self,
            matchAgainst_sound hm,
            fun _ hy => matchAgainst_fixes_not_mem hm hy⟩⟩
      | none =>
          (findRedex rest t).map (fun r =>
            ⟨r.1, r.2.1, PLift.up ⟨List.mem_cons_of_mem rule r.2.2.down.1,
              r.2.2.down.2.1, r.2.2.down.2.2⟩⟩)

/-! ## The complete development

`completeDevelopment R t` contracts every redex available in `t` in one parallel
sweep. At a term that matches a rule's left-hand side, it contracts that root redex,
developing the matched substitution at the variables the left-hand side binds; with
no root match, it develops each argument. The descent into the matched substitution
is well founded because a matched image of a left-hand-side variable is a strict
subterm of the matched term (`size_apply_var_lt_app`), and the descent into
arguments is well founded because an argument is a strict subterm of its application
(`Term.size_lt_of_mem`). -/

/-- The complete development of `t` under `R`: the term that simultaneously contracts
every redex of `t`. When a rule matches at the root with substitution `σ`, the result
is `rule.rhs` instantiated by the developed images of the left-hand-side variables;
otherwise each argument is developed. Total and well founded on `Term.size`. -/
def completeDevelopment [DecidableEq sigma] [DecidableEq nu] (R : TRS sigma nu) :
    Term sigma nu → Term sigma nu
  | .var x =>
      match findRedex R (.var x) with
      | some red =>
          apply (fun y => if y ∈ Term.vars red.1.lhs then
            completeDevelopment R (red.2.1 y) else .var y) red.1.rhs
      | none => .var x
  | .app f args =>
      match findRedex R (.app f args) with
      | some red =>
          apply (fun y => if y ∈ Term.vars red.1.lhs then
            completeDevelopment R (red.2.1 y) else .var y) red.1.rhs
      | none =>
          .app f (args.attach.map (fun a => completeDevelopment R a.1))
  termination_by t => Term.size t
  decreasing_by
    · -- variable scrutinee: the matched substitution image of a left-hand-side
      -- variable is a strict subterm of the matched term
      rename_i y hy
      obtain ⟨_hmem, hlhs, _hfix⟩ := red.2.2.down
      set s := red.2.1
      set l := red.1.lhs
      have hisapp : l.isApp = true := red.1.lhs_isApp
      have happ : ∃ g largs, l = .app g largs := by
        cases hl : l with
        | var z => rw [hl] at hisapp; exact absurd hisapp (by simp)
        | app g largs => exact ⟨g, largs, rfl⟩
      obtain ⟨g, largs, hgl⟩ := happ
      have hlt : Term.size (s y) < Term.size (apply s l) := by
        rw [hgl] at hy ⊢
        exact size_apply_var_lt_app s g largs y hy
      rw [hlhs] at hlt
      exact hlt
    · -- application scrutinee: a matched left-hand-side variable maps to a strict
      -- subterm of the matched application
      rename_i y hy
      obtain ⟨_hmem, hlhs, _hfix⟩ := red.2.2.down
      set s := red.2.1
      set l := red.1.lhs
      have hisapp : l.isApp = true := red.1.lhs_isApp
      have happ : ∃ g largs, l = .app g largs := by
        cases hl : l with
        | var z => rw [hl] at hisapp; exact absurd hisapp (by simp)
        | app g largs => exact ⟨g, largs, rfl⟩
      obtain ⟨g, largs, hgl⟩ := happ
      have hlt : Term.size (s y) < Term.size (apply s l) := by
        rw [hgl] at hy ⊢
        exact size_apply_var_lt_app s g largs y hy
      rw [hlhs] at hlt
      exact hlt
    · -- application scrutinee: an argument is a strict subterm of its application
      exact Term.size_lt_of_mem (f := f) a.2

/-! ## The complete development is a parallel step

`completeDevelopment R t` is reached from `t` by a single parallel step. At a matched
root it is the matched root redex contracted while the substituted terms develop in
parallel; with no root match it is the argument-wise development. The proof is a
well-founded recursion on `Term.size`, with the matched-substitution images strictly
smaller (`size_apply_var_lt_app`) and the arguments strictly smaller
(`Term.size_lt_of_mem`). -/

/-- The complete development of a term is a parallel reduct of it:
`ParStep R t (completeDevelopment R t)`. The matched-root case contracts the root
redex through `ParStep.root`, parallel-reducing the substituted terms by the
induction hypothesis at the strictly smaller images and fixing the variables outside
the left-hand side; the no-match application case develops each argument by the
induction hypothesis through `ParStep.app`. -/
theorem parStep_completeDevelopment [DecidableEq sigma] [DecidableEq nu]
    (R : TRS sigma nu) (t : Term sigma nu) : ParStep R t (completeDevelopment R t) := by
  -- strong induction on the structural size, so the matched-substitution images and
  -- the arguments, both strictly smaller, carry the induction hypothesis
  induction hn : Term.size t using Nat.strong_induction_on generalizing t with
  | _ n ih =>
    subst hn
    -- the common matched-root closing step, shared by the variable and application
    -- scrutinees: contract the matched redex, developing the bound images by `ih`
    have root_case : ∀ (rule : Rule sigma nu) (σ : Subst sigma nu),
        rule ∈ R → σ • rule.lhs = t → (∀ y, y ∉ Term.vars rule.lhs → σ y = .var y) →
        ParStep R t
          (apply (fun y => if y ∈ Term.vars rule.lhs then
            completeDevelopment R (σ y) else .var y) rule.rhs) := by
      intro rule σ hmem hlhs hfix
      have hisapp : rule.lhs.isApp = true := rule.lhs_isApp
      have happ : ∃ g largs, rule.lhs = .app g largs := by
        cases hl : rule.lhs with
        | var z => rw [hl] at hisapp; exact absurd hisapp (by simp)
        | app g largs => exact ⟨g, largs, rfl⟩
      obtain ⟨g, largs, hgl⟩ := happ
      have hpt : ∀ y, ParStep R (σ y)
          (if y ∈ Term.vars rule.lhs then completeDevelopment R (σ y) else .var y) := by
        intro y
        by_cases hy : y ∈ Term.vars rule.lhs
        · simp only [hy, if_true]
          -- the matched image of a bound variable is strictly smaller
          have hlt : Term.size (σ y) < Term.size t := by
            rw [← hlhs, hgl]
            rw [hgl] at hy
            exact size_apply_var_lt_app σ g largs y hy
          exact ih (Term.size (σ y)) hlt (σ y) rfl
        · simp only [hy, if_false]
          rw [hfix y hy]
          exact ParStep.var y
      exact hlhs ▸ ParStep.root hmem σ _ hpt
    -- dispatch on the term shape, unfolding the complete development once
    match t with
    | .var x =>
        rw [completeDevelopment]
        split
        · rename_i red _hfx
          obtain ⟨rule, σ, hc⟩ := red
          obtain ⟨hmem, hlhs, hfix⟩ := hc.down
          exact root_case rule σ hmem hlhs hfix
        · exact ParStep.var x
    | .app f args =>
        rw [completeDevelopment]
        split
        · rename_i red _hfx
          obtain ⟨rule, σ, hc⟩ := red
          obtain ⟨hmem, hlhs, hfix⟩ := hc.down
          exact root_case rule σ hmem hlhs hfix
        · refine ParStep.app f ?_
          -- develop each argument by the induction hypothesis (arguments are smaller)
          have hlist : ∀ (as : List (Term sigma nu)), (∀ a ∈ as, a ∈ args) →
              ParStepList R as (as.attach.map (fun a => completeDevelopment R a.1)) := by
            intro as
            induction as with
            | nil => intro _; exact ParStepList.nil
            | cons b bs ihbs =>
                intro hsub
                rw [List.attach_cons, List.map_cons, List.map_map]
                have hbmem : b ∈ args := hsub b (List.mem_cons_self)
                have hbsize : Term.size b < Term.size (Term.app f args) :=
                  Term.size_lt_of_mem hbmem
                refine ParStepList.cons (ih (Term.size b) hbsize b rfl) ?_
                have := ihbs (fun a ha => hsub a (List.mem_cons_of_mem b ha))
                simpa using this
          exact hlist args (fun _ ha => ha)

/-- The complete development is reachable from the term by a finite rewrite sequence:
`StepStar R t (completeDevelopment R t)`. Composing the single parallel step
`parStep_completeDevelopment` with the realization of a parallel step as a rewrite
sequence (`parStep_imp_stepStar`). -/
theorem stepStar_completeDevelopment [DecidableEq sigma] [DecidableEq nu]
    (R : TRS sigma nu) (t : Term sigma nu) : StepStar R t (completeDevelopment R t) :=
  parStep_imp_stepStar R (parStep_completeDevelopment R t)

/-! ## The parallel-reduction diamond and termination-free confluence: the empty system

The empty term rewriting system carries no rule, so its parallel reduction has only
the reflexive variable and congruence moves: a parallel step is an equality. Hence
parallel reduction has the diamond property, and the diamond lemma together with the
coincidence of the parallel and rewrite closures yields confluence of the rewrite
relation with no termination hypothesis. The empty system is weakly orthogonal
(`emptyTRS_weaklyOrthogonal`) and `renameTRS [] = []`, so this is the termination-free
confluence conclusion realized through the Takahashi route on a concrete weakly
orthogonal system. -/

/-- Parallel reduction over the empty system is equality: with no rule to contract,
the only parallel moves are the reflexive variable step and argument-wise congruence,
so `ParStep [] t u` forces `t = u`. Proven by the mutual recursor, the `root`
constructor being unreachable because membership in the empty rule list is impossible.
-/
theorem parStep_emptyTRS_eq {t u : Term sigma nu}
    (h : ParStep ([] : TRS sigma nu) t u) : t = u := by
  refine ParStep.rec (R := ([] : TRS sigma nu))
    (motive_1 := fun t u _ => t = u)
    (motive_2 := fun args args' _ => args = args')
    ?var ?app ?root ?nil ?cons h
  · intro x; rfl
  · intro f args args' _ ih; rw [ih]
  · intro rule hrule _ _ _ _; exact absurd hrule (List.not_mem_nil)
  · rfl
  · intro a a' as as' _ _ iha ihas; rw [iha, ihas]

/-- Parallel reduction over the empty system has the diamond property: any two
parallel reducts of a term are the term itself (`parStep_emptyTRS_eq`), so they join
at the term by reflexivity. -/
theorem parStep_diamond_emptyTRS : Diamond (ParStep ([] : TRS sigma nu)) := by
  intro a b c hab hac
  have hb : a = b := parStep_emptyTRS_eq hab
  have hc : a = c := parStep_emptyTRS_eq hac
  subst hb; subst hc
  exact ⟨a, ParStep.refl _ a, ParStep.refl _ a⟩

/-- Termination-free confluence of the empty system through the parallel-reduction
diamond: the rewrite relation `StepStar (renameTRS [])` is confluent, with no
strong-normalization hypothesis. The parallel-reduction diamond
(`parStep_diamond_emptyTRS`) lifts to confluence of its reflexive-transitive closure
through `diamond_imp_confluent`, and that closure is the rewrite relation by
`reflTransGen_parStep_eq_stepStar`. The empty system is weakly orthogonal
(`emptyTRS_weaklyOrthogonal`), so this realizes the termination-free confluence
conclusion for a concrete weakly orthogonal system. -/
theorem weaklyOrthogonal_emptyTRS_confluent [DecidableEq sigma] [DecidableEq nu] :
    Confluent (StepStar (renameTRS ([] : TRS sigma nu))) := by
  have hrn : renameTRS ([] : TRS sigma nu) = ([] : TRS sigma (RenVar nu)) := rfl
  have hd : Diamond (ParStep (renameTRS ([] : TRS sigma nu))) := by
    rw [hrn]; exact parStep_diamond_emptyTRS
  have hconf : Confluent (ReflTransGen (ParStep (renameTRS ([] : TRS sigma nu)))) :=
    diamond_imp_confluent hd
  rwa [reflTransGen_parStep_eq_stepStar] at hconf

/-! ## Non-vacuity

The complete development is exhibited on the one-rule demonstration system
`Example.demoTRS` (`f(x) -> g(x)`), a left-linear system. The redex `f(c)` develops to
`g(c)` in one parallel step, and that step is realized as a finite rewrite sequence,
exhibiting the complete development as genuinely inhabited on a concrete system. -/

namespace CompleteDevelopment

/-- The redex `f(c)` parallel-reduces to its complete development under the
demonstration system: a concrete instance of `parStep_completeDevelopment`. -/
theorem demo_parStep :
    ParStep Example.demoTRS Example.srcTerm
      (completeDevelopment Example.demoTRS Example.srcTerm) :=
  parStep_completeDevelopment Example.demoTRS Example.srcTerm

/-- The complete development of the redex `f(c)` is reachable from it by a finite
rewrite sequence under the demonstration system: a concrete instance of
`stepStar_completeDevelopment`. -/
theorem demo_stepStar :
    StepStar Example.demoTRS Example.srcTerm
      (completeDevelopment Example.demoTRS Example.srcTerm) :=
  stepStar_completeDevelopment Example.demoTRS Example.srcTerm

end CompleteDevelopment

end OperatorKO7.Meta.Rewriting

/-! ## Verification: headline types and axiom audit -/

open OperatorKO7.Meta.Rewriting in
#check @size_apply_var_le
open OperatorKO7.Meta.Rewriting in
#check @size_apply_var_lt_app
open OperatorKO7.Meta.Rewriting in
#check @matchAgainst_fixes_not_mem
open OperatorKO7.Meta.Rewriting in
#check @findRedex
open OperatorKO7.Meta.Rewriting in
#check @completeDevelopment
open OperatorKO7.Meta.Rewriting in
#check @parStep_completeDevelopment
open OperatorKO7.Meta.Rewriting in
#check @stepStar_completeDevelopment
open OperatorKO7.Meta.Rewriting in
#check @parStep_emptyTRS_eq
open OperatorKO7.Meta.Rewriting in
#check @parStep_diamond_emptyTRS
open OperatorKO7.Meta.Rewriting in
#check @weaklyOrthogonal_emptyTRS_confluent
open OperatorKO7.Meta.Rewriting in
#check @CompleteDevelopment.demo_parStep
open OperatorKO7.Meta.Rewriting in
#check @CompleteDevelopment.demo_stepStar

#print axioms OperatorKO7.Meta.Rewriting.completeDevelopment
#print axioms OperatorKO7.Meta.Rewriting.parStep_completeDevelopment
#print axioms OperatorKO7.Meta.Rewriting.stepStar_completeDevelopment
#print axioms OperatorKO7.Meta.Rewriting.parStep_diamond_emptyTRS
#print axioms OperatorKO7.Meta.Rewriting.weaklyOrthogonal_emptyTRS_confluent
#print axioms OperatorKO7.Meta.Rewriting.CompleteDevelopment.demo_parStep
#print axioms OperatorKO7.Meta.Rewriting.CompleteDevelopment.demo_stepStar
