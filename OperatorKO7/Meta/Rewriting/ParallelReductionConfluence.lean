import OperatorKO7.Meta.Rewriting.ParallelReductionDiamond
import OperatorKO7.Meta.Rewriting.CriticalPairComplete

/-!
# The Takahashi triangle and termination-free confluence of orthogonal systems

Roadmap source: the capstone of the confluence-toolkit expansion atop the verified
rewriting foundation and the parallel-reduction layer. This module establishes the
Takahashi 1995 triangle for orthogonal first-order term rewriting systems: every
parallel reduct of a term parallel-reduces to that term's complete development. The
triangle gives the parallel-reduction diamond, and the diamond lifts to confluence of
the rewrite relation with no strong-normalization hypothesis.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.Rewriting

open scoped Subst
open Subst
open Relation

universe u v

variable {sigma : Type u} {nu : Type v}

/-! ## Matching is complete for substitution instances

The matcher recognizes every substitution instance: when a substitution `s` carries a
pattern `l` onto a target `t`, the matcher applied to `l` and `t` succeeds, returning
an accumulator consistent with `s`. The accumulator-consistency invariant
(`PartialMap.AgreesWith`) threads the partial bindings through the structural
recursion: a binding already recorded agrees with `s`, and the recursion only extends
the accumulator with bindings `s` already satisfies. -/

/-- A substitution `s` agrees with a partial accumulator `m` when every binding
recorded in `m` is the value `s` assigns: `find? m x = some b → s x = b`. The matcher
preserves this agreement, so a successful match returns an accumulator whose closed
substitution coincides with `s` on the pattern's variables. -/
def PartialMap.AgreesWith [DecidableEq nu] (s : Subst sigma nu) (m : PartialMap sigma nu) :
    Prop :=
  ∀ x b, PartialMap.find? m x = some b → s x = b

/-- Prepending a binding `s` already satisfies preserves agreement. -/
theorem PartialMap.agreesWith_cons [DecidableEq nu] {s : Subst sigma nu}
    {m : PartialMap sigma nu} {x : nu} {t : Term sigma nu}
    (hm : PartialMap.AgreesWith s m) (hxt : s x = t) :
    PartialMap.AgreesWith s ((x, t) :: m) := by
  intro y b hy
  rw [PartialMap.find?_cons] at hy
  by_cases hxy : x = y
  · subst hxy; simp only [if_true, Option.some.injEq] at hy
    rw [hxt, hy]
  · simp only [if_neg hxy] at hy
    exact hm y b hy

/-- The argument-list driver for `matchAux_complete`: when a substitution `s` carries
a pattern argument list `ls` onto a target list `ts` (position-wise) and agrees with
the input accumulator, `matchAuxList` succeeds with an accumulator still agreeing with
`s`. Parameterized by the per-argument completeness statement `ih`, inducting on the
argument list independently of the pattern recursion. -/
theorem matchAuxList_complete [DecidableEq sigma] [DecidableEq nu]
    {ls : List (Term sigma nu)}
    (ih : ∀ a ∈ ls, ∀ (t : Term sigma nu) (m : PartialMap sigma nu) (s : Subst sigma nu),
            apply s a = t → PartialMap.AgreesWith s m →
              ∃ m', matchAux a t m = some m' ∧ PartialMap.AgreesWith s m') :
    ∀ (ts : List (Term sigma nu)) (m : PartialMap sigma nu) (s : Subst sigma nu),
      ls.map (apply s) = ts → PartialMap.AgreesWith s m →
        ∃ m', matchAuxList ls ts m = some m' ∧ PartialMap.AgreesWith s m' := by
  induction ls with
  | nil =>
      intro ts m s hmap hm
      cases ts with
      | nil => exact ⟨m, rfl, hm⟩
      | cons t ts => simp only [List.map_nil] at hmap; exact absurd hmap.symm (by simp)
  | cons l ls ihls =>
      intro ts m s hmap hm
      cases ts with
      | nil => simp only [List.map_cons] at hmap; exact absurd hmap (by simp)
      | cons t ts =>
          simp only [List.map_cons, List.cons.injEq] at hmap
          obtain ⟨hhead, htail⟩ := hmap
          obtain ⟨m1, hm1, hag1⟩ := ih l (by simp) t m s hhead hm
          obtain ⟨m', hm', hag'⟩ :=
            ihls (fun a ha => ih a (by simp [ha])) ts m1 s htail hag1
          refine ⟨m', ?_, hag'⟩
          simp only [matchAuxList, hm1, hm']

/-- Completeness of `matchAux`: if `s` carries the pattern `l` onto the target `t` and
agrees with the input accumulator `m`, then `matchAux l t m` succeeds with an
accumulator still agreeing with `s`. Structural induction on the pattern, reducing the
application case to `matchAuxList_complete`. -/
theorem matchAux_complete [DecidableEq sigma] [DecidableEq nu] :
    ∀ (l t : Term sigma nu) (m : PartialMap sigma nu) (s : Subst sigma nu),
      apply s l = t → PartialMap.AgreesWith s m →
        ∃ m', matchAux l t m = some m' ∧ PartialMap.AgreesWith s m' := by
  intro l
  induction l using Term.rec' with
  | hvar y =>
      intro t m s hmap hm
      rw [apply_var] at hmap
      simp only [matchAux]
      cases hy : PartialMap.find? m y with
      | some t' =>
          -- `s y = t'` by agreement, and `s y = t`, so `t' = t`
          have hsy : s y = t' := hm y t' hy
          have ht' : t' = t := by rw [← hsy, hmap]
          refine ⟨m, ?_, hm⟩
          simp [ht']
      | none =>
          refine ⟨(y, t) :: m, rfl, ?_⟩
          exact PartialMap.agreesWith_cons hm hmap
  | happ f ls ih =>
      intro t m s hmap hm
      cases t with
      | var z =>
          rw [apply_app] at hmap; exact absurd hmap (by simp)
      | app g ts =>
          rw [apply_app] at hmap
          -- the heads agree and the argument lists agree
          have hfg : f = g := by injection hmap
          have htsapp : applyList s ls = ts := by injection hmap
          subst hfg
          simp only [matchAux, if_true]
          have hmap' : ls.map (apply s) = ts := by rw [← applyList_eq_map]; exact htsapp
          exact matchAuxList_complete ih ts m s hmap' hm

/-- Completeness of `matchAgainst`: a substitution instance is recognized. If
`apply s l = t`, then `matchAgainst l t` succeeds. The empty accumulator agrees with
every substitution, so `matchAux_complete` applies at the top level. -/
theorem matchAgainst_complete [DecidableEq sigma] [DecidableEq nu]
    {l t : Term sigma nu} {s : Subst sigma nu} (h : apply s l = t) :
    (matchAgainst l t).isSome = true := by
  obtain ⟨m', hm', _⟩ := matchAux_complete l t [] s h (by intro x b hx; simp at hx)
  simp [matchAgainst, hm']

/-! ## The root matcher finds every root redex

`completeDevelopment` selects its root contraction through `findRedex`, which scans the
rule list with the syntactic matcher. Matching completeness shows the matcher never
misses a substitution instance, so when a term is a root rule-instance, `findRedex`
returns a rule. Contrapositively, a `none` from `findRedex` certifies that the term is
not a root redex of any rule, the fact that closes the no-root-redex case of the
triangle. -/

/-- `findRedex` succeeds on any root redex instance: if some rule of `R` has a
left-hand side carried onto `t` by a substitution, then `findRedex R t` returns some
rule. Scans the rules; the matching rule is recognized by `matchAgainst_complete`, and
earlier rules either match (also success) or are skipped. -/
theorem findRedex_isSome_of_rootStep [DecidableEq sigma] [DecidableEq nu]
    {R : TRS sigma nu} {t : Term sigma nu}
    (h : ∃ rule ∈ R, ∃ σ : Subst sigma nu, σ • rule.lhs = t) :
    (findRedex R t).isSome = true := by
  obtain ⟨rule, hrule, σ, hσ⟩ := h
  induction R with
  | nil => exact absurd hrule List.not_mem_nil
  | cons r rest ih =>
      rw [findRedex]
      split
      · -- the first rule matches: `findRedex` returns `some`
        simp
      · -- the first rule does not match (its matcher returned `none`)
        rename_i hm
        simp only [Option.isSome_map]
        rcases List.mem_cons.1 hrule with hr | hr
        · -- the matching rule is `r` itself, contradicting `hm`
          subst hr
          have := matchAgainst_complete hσ
          rw [hm] at this; exact absurd this (by simp)
        · exact ih hr

/-- A term with no root redex has no contraction at the root: if `findRedex R t = none`
then there is no rule of `R` and substitution presenting `t` as that rule's left-hand
side instance. The contrapositive of `findRedex_isSome_of_rootStep`. -/
theorem not_rootStep_of_findRedex_none [DecidableEq sigma] [DecidableEq nu]
    {R : TRS sigma nu} {t : Term sigma nu} (h : findRedex R t = none) :
    ¬ ∃ rule ∈ R, ∃ σ : Subst sigma nu, σ • rule.lhs = t := by
  intro hroot
  have := findRedex_isSome_of_rootStep hroot
  rw [h] at this; exact absurd this (by simp)

/-! ## Inversion of parallel reduction

The shape of a parallel step is determined by its source. A variable parallel-reduces
only to itself. A parallel step out of an application either develops the arguments
through `ParStepList`, or contracts a root rule-instance. These inversions drive the
case analysis in the triangle. -/

/-- An application is never a substitution instance of a variable... rather, a rule
instance is always an application: `σ • rule.lhs` is an application because the
left-hand side is. -/
theorem apply_lhs_isApp {R : TRS sigma nu} {rule : Rule sigma nu} (_hrule : rule ∈ R)
    (σ : Subst sigma nu) : (σ • rule.lhs).isApp = true := by
  have happ : rule.lhs.isApp = true := rule.lhs_isApp
  cases hl : rule.lhs with
  | var z => rw [hl] at happ; simp at happ
  | app g largs => rw [apply_app]; rfl

/-- A parallel step out of a variable lands on the same variable: a rule never matches
a variable at the root (its left-hand side is an application), so the only available
move is the reflexive variable step. The inversion goes through the mutual recursor
with the source pinned to `.var x`, since the `root` index `σ • rule.lhs` does not
directly unify with a variable. -/
theorem parStep_var_inv {R : TRS sigma nu} {x : nu} {u : Term sigma nu}
    (h : ParStep R (.var x) u) : u = .var x := by
  refine ParStep.rec (R := R)
    (motive_1 := fun t u _ => ∀ y : nu, t = .var y → u = .var y)
    (motive_2 := fun _ _ _ => True)
    ?var ?app ?root trivial (fun _ _ _ _ => trivial) h x rfl
  · intro z y hz; exact hz
  · intro f args args' _ _ y hy; exact absurd hy (by simp)
  · intro rule hrule σ σ' _ _ y hy
    -- `σ • rule.lhs = var y` contradicts `apply_lhs_isApp`
    have := apply_lhs_isApp (R := R) hrule σ
    rw [hy] at this; simp at this

/-! ## Weak orthogonality forces root reducts to coincide

Two root contractions of one source are a root overlap of the two rules. After the
rules are renamed apart, the shared source presents both renamed left-hand sides as a
common instance at the root position, so `criticalPairs_complete` exhibits the two
reducts as a residual instance of an emitted critical pair. Under weak orthogonality
that pair is trivial: its two components coincide, so the two root reducts are equal.
The bridge from a renamed-rule instance to a recombined-substitution instance is
`apply_rename_congr`. -/

/-! ## Renaming commutes with substitution, and is injective

Renaming a substituted term equals substituting (by a relabeled substitution) into the
renamed term, and an injective relabeling is injective on terms. Together these carry a
substitution-instance equation over the original carrier up to the renamed carrier and
back, the bridge that lifts the renamed-carrier root-overlap equality to the original
system. -/

/-- Renaming commutes with substitution along a relabeled substitution: if
`τ (g x) = rename g (σ x)` for every variable `x`, then
`rename g (σ • t) = τ • rename g t`. Structural induction on `t`; at a variable both
sides are `rename g (σ x)`. -/
theorem rename_apply_comm {nu' : Type v} (σ : Subst sigma nu) (τ : Subst sigma nu')
    (g : nu → nu') (hpt : ∀ x, τ (g x) = Term.rename g (σ x)) :
    ∀ (t : Term sigma nu), Term.rename g (apply σ t) = apply τ (Term.rename g t) := by
  intro t
  induction t using Term.rec' with
  | hvar x => rw [apply_var, Term.rename_var, apply_var]; exact (hpt x).symm
  | happ f args ih =>
      rw [apply_app, Term.rename_app, Term.rename_app, apply_app,
        Term.renameList_eq_map, Term.renameList_eq_map, applyList_eq_map,
        applyList_eq_map, List.map_map, List.map_map]
      congr 1
      exact List.map_congr_left ih

/-- An injective relabeling induces an injective renaming on terms: if `g` is injective
and `rename g a = rename g b`, then `a = b`. Structural induction on `a` with case
analysis on `b`. -/
theorem rename_injective {nu' : Type v} {g : nu → nu'} (hg : Function.Injective g) :
    ∀ (a b : Term sigma nu), Term.rename g a = Term.rename g b → a = b := by
  intro a
  induction a using Term.rec' with
  | hvar x =>
      intro b hb
      cases b with
      | var y =>
          rw [Term.rename_var, Term.rename_var, Term.var.injEq] at hb
          rw [hg hb]
      | app h bs => rw [Term.rename_var, Term.rename_app] at hb; exact absurd hb (by simp)
  | happ f args ih =>
      intro b hb
      cases b with
      | var y => rw [Term.rename_app, Term.rename_var] at hb; exact absurd hb (by simp)
      | app h bs =>
          rw [Term.rename_app, Term.rename_app] at hb
          have hfh : f = h := by injection hb
          have hargs : Term.renameList g args = Term.renameList g bs := by injection hb
          subst hfh
          rw [Term.renameList_eq_map, Term.renameList_eq_map] at hargs
          have hlist : args = bs := by
            clear hb
            induction args generalizing bs with
            | nil => cases bs with
                | nil => rfl
                | cons c cs => simp at hargs
            | cons a as iha =>
                cases bs with
                | nil => simp at hargs
                | cons c cs =>
                    rw [List.map_cons, List.map_cons, List.cons.injEq] at hargs
                    rw [List.cons.injEq]
                    refine ⟨ih a (by simp) c hargs.1, ?_⟩
                    exact iha (fun x hx => ih x (by simp [hx])) cs hargs.2
          rw [hlist]

/-- Under weak orthogonality, two root contractions of one source over the renamed
carrier produce the same reduct. Two rules `r1, r2 ∈ R`, renamed apart through `g1` and
`g2` into `RenVar nu` and contracted at the root by substitutions `σ1, σ2` to a common
source `σ1 • rename g1 r1.lhs = σ2 • rename g2 r2.lhs`, have equal reducts
`σ1 • rename g1 r1.rhs = σ2 • rename g2 r2.rhs`. The combined substitution
`ν = Sum.elim (σ1 ∘ g1) (σ2 ∘ g2)` presents the canonical apart copies as a common
instance at the root, so `criticalPairs_complete` names the emitted critical pair;
weak orthogonality makes that pair trivial, so the two residual instances coincide.
The structure mirrors `joinable_rootOverlap_of_cp_joinable`, concluding equality. -/
theorem weaklyOrthogonal_rootOverlap_eq [DecidableEq sigma] [DecidableEq nu]
    {R : TRS sigma nu} (hwo : weaklyOrthogonal R)
    {r1 r2 : Rule sigma nu} (hr1 : r1 ∈ R) (hr2 : r2 ∈ R)
    (g1 g2 : nu → RenVar nu) {σ1 σ2 : Subst sigma (RenVar nu)}
    (hs : σ1 • Term.rename g1 r1.lhs = σ2 • Term.rename g2 r2.lhs) :
    σ1 • Term.rename g1 r1.rhs = σ2 • Term.rename g2 r2.rhs := by
  -- the combined substitution feeding both apart copies their original assignment
  set ν : Subst sigma (RenVar nu) :=
    Sum.elim (fun x => σ1 (g1 x)) (fun y => σ2 (g2 y)) with hν
  have hνl : ∀ x, ν (Sum.inl x) = σ1 (g1 x) := fun _ => rfl
  have hνr : ∀ y, ν (Sum.inr y) = σ2 (g2 y) := fun _ => rfl
  -- recombine the canonical apart copies into the shared instance
  have hsrc1 : ν • Term.rename (renL nu) r1.lhs = σ1 • Term.rename g1 r1.lhs :=
    apply_rename_congr ν σ1 (renL nu) g1 (fun x => hνl x) r1.lhs
  have hsrc2 : ν • Term.rename (renR nu) r2.lhs = σ2 • Term.rename g2 r2.lhs :=
    apply_rename_congr ν σ2 (renR nu) g2 (fun y => hνr y) r2.lhs
  have hrhs1 : ν • Term.rename (renL nu) r1.rhs = σ1 • Term.rename g1 r1.rhs :=
    apply_rename_congr ν σ1 (renL nu) g1 (fun x => hνl x) r1.rhs
  have hrhs2 : ν • Term.rename (renR nu) r2.rhs = σ2 • Term.rename g2 r2.rhs :=
    apply_rename_congr ν σ2 (renR nu) g2 (fun y => hνr y) r2.rhs
  -- the overlap at the root: the subterm there is the whole inl-renamed left-hand side
  have hsub : Term.subtermAt (renameRule (renL nu) r1).lhs [] =
      some (renameRule (renL nu) r1).lhs := Term.subtermAt_nil _
  -- common-instance hypothesis at the root position
  have hcommon : ν • (renameRule (renL nu) r1).lhs = ν • (renameRule (renR nu) r2).lhs := by
    rw [renameRule_lhs, renameRule_lhs, hsrc1, hsrc2]; exact hs
  -- completeness names the emitted pair and the residual substitution
  obtain ⟨c1, c2, hmem, ρ, hc1, hc2⟩ :=
    criticalPairs_complete hr1 hr2 (nil_mem_nonVarPositions_renameRule (renL nu) r1) hsub hcommon
  -- weak orthogonality: the emitted pair is trivial, so the residual instances agree
  have htriv : c1 = c2 := hwo.2 (c1, c2) hmem
  rw [renameRule_rhs] at hc1
  rw [Term.replaceAt_nil, renameRule_rhs] at hc2
  rw [← hrhs1, ← hrhs2, hc1, hc2, htriv]

/-- Under weak orthogonality, two root contractions of one source in the original
system produce the same reduct: if `rule1, rule2 ∈ R` and
`σ1 • rule1.lhs = σ2 • rule2.lhs`, then `σ1 • rule1.rhs = σ2 • rule2.rhs`. The equation
is relabeled into the renamed carrier through `renL`, where the renamed-carrier
overlap equality `weaklyOrthogonal_rootOverlap_eq` applies, and `renL`-injectivity of
`rename` carries the conclusion back. This is the root-overlap reconciliation that
closes the matched-root cases of the triangle. -/
theorem weaklyOrthogonal_root_reducts_eq [DecidableEq sigma] [DecidableEq nu]
    {R : TRS sigma nu} (hwo : weaklyOrthogonal R)
    {rule1 rule2 : Rule sigma nu} (h1 : rule1 ∈ R) (h2 : rule2 ∈ R)
    {σ1 σ2 : Subst sigma nu} (hs : σ1 • rule1.lhs = σ2 • rule2.lhs) :
    σ1 • rule1.rhs = σ2 • rule2.rhs := by
  -- relabeled substitutions over `RenVar nu`, agreeing with `σi` along `renL`
  set τ1 : Subst sigma (RenVar nu) :=
    Sum.elim (fun x => Term.rename (renL nu) (σ1 x)) (fun y => .var (Sum.inr y)) with hτ1
  set τ2 : Subst sigma (RenVar nu) :=
    Sum.elim (fun x => Term.rename (renL nu) (σ2 x)) (fun y => .var (Sum.inr y)) with hτ2
  have hτ1l : ∀ x, τ1 (renL nu x) = Term.rename (renL nu) (σ1 x) := fun _ => rfl
  have hτ2l : ∀ x, τ2 (renL nu x) = Term.rename (renL nu) (σ2 x) := fun _ => rfl
  -- the relabeled source equation over `RenVar nu`
  have hsren : τ1 • Term.rename (renL nu) rule1.lhs = τ2 • Term.rename (renL nu) rule2.lhs := by
    rw [← rename_apply_comm σ1 τ1 (renL nu) hτ1l, ← rename_apply_comm σ2 τ2 (renL nu) hτ2l, hs]
  -- renamed-carrier overlap equality with both rules relabeled through `renL`
  have hrhsren : τ1 • Term.rename (renL nu) rule1.rhs = τ2 • Term.rename (renL nu) rule2.rhs :=
    weaklyOrthogonal_rootOverlap_eq hwo h1 h2 (renL nu) (renL nu) hsren
  -- descend through `renL`-injectivity of `rename`
  rw [← rename_apply_comm σ1 τ1 (renL nu) hτ1l, ← rename_apply_comm σ2 τ2 (renL nu) hτ2l] at hrhsren
  exact rename_injective (g := renL nu) Sum.inl_injective _ _ hrhsren

/-! ## Shallow left-hand sides

A left-hand side is shallow when its only non-variable position is the root: it is an
application all of whose arguments are variables, `f(x1, ..., xn)`. A system with
shallow left-hand sides has no proper function position in any rule, so no rule can
overlap another below the root; the only critical overlaps are at the root, where weak
orthogonality reconciles them. The demonstration rule `f(x) -> g(x)` is shallow. -/

/-- A left-hand side pattern is shallow when its only non-variable position is the root:
every proper position carries a variable, so the pattern is `f(x1, ..., xn)`. -/
def shallowLhs [DecidableEq sigma] [DecidableEq nu] (rule : Rule sigma nu) : Prop :=
  nonVarPositions rule.lhs = [[]]

/-- A term rewriting system is shallow when every rule's left-hand side is shallow:
each left-hand side is a function symbol applied to variables. With shallow left-hand
sides the only overlaps are at the root, which weak orthogonality controls. -/
def shallow [DecidableEq sigma] [DecidableEq nu] (R : TRS sigma nu) : Prop :=
  ∀ rule ∈ R, shallowLhs rule

/-- The arguments of a shallow application are all variables: if
`nonVarPositions (app f args) = [[]]` then no argument is an application. The
non-variable positions list off the root would otherwise carry an `i :: _` entry from
that argument. -/
theorem args_all_var_of_shallow [DecidableEq sigma] [DecidableEq nu]
    {f : sigma} {args : List (Term sigma nu)}
    (h : nonVarPositions (Term.app f args) = [[]]) :
    ∀ a ∈ args, ∃ x, a = .var x := by
  rw [nonVarPositions_app, List.cons.injEq] at h
  have hempty : nonVarPositionsList args 0 = [] := h.2
  -- a non-variable argument contributes a non-empty sublist
  intro a ha
  cases a with
  | var x => exact ⟨x, rfl⟩
  | app g bs =>
      exfalso
      -- the argument `app g bs` at its index contributes `[]` mapped, hence a member
      have hkey : ∀ (l : List (Term sigma nu)) (base : Nat),
          (∃ b ∈ l, b.isApp = true) → nonVarPositionsList l base ≠ [] := by
        intro l
        induction l with
        | nil => rintro base ⟨b, hb, _⟩; simp at hb
        | cons c cs ih =>
            intro base hex
            rw [nonVarPositionsList]
            rcases hex with ⟨b, hb, hbapp⟩
            rw [List.mem_cons] at hb
            rcases hb with rfl | hb
            · -- the application head contributes its root position
              cases hc : b with
              | var y => rw [hc] at hbapp; simp at hbapp
              | app g' bs' =>
                  intro hcontra
                  rw [nonVarPositions_app] at hcontra
                  simp at hcontra
            · -- a later application contributes through the tail
              intro hcontra
              rw [List.append_eq_nil_iff] at hcontra
              exact ih (base + 1) ⟨b, hb, hbapp⟩ hcontra.2
      exact hkey args 0 ⟨.app g bs, ha, by simp⟩ hempty

/-- From a position-wise parallel reduction of the substituted variables of a shallow,
left-linear pattern, recover a parallel-reduced substitution. Given a duplicate-free
variable list `xs` and `ParStepList R (xs.map σ) args'`, there is a substitution `σ'`
with `xs.map σ' = args'`, fixing every variable outside `xs`, and with
`ParStep R (σ x) (σ' x)` for each `x ∈ xs`. Built by recursion on the paired lists;
the duplicate-freedom keeps the head assignment from clashing with the tail. -/
theorem exists_parStep_subst_of_parStepList [DecidableEq nu] {R : TRS sigma nu}
    {σ : Subst sigma nu} :
    ∀ (xs : List nu) (args' : List (Term sigma nu)), xs.Nodup →
      ParStepList R (xs.map σ) args' →
        ∃ σ' : Subst sigma nu, xs.map σ' = args' ∧
          (∀ y, y ∉ xs → σ' y = .var y) ∧ (∀ x ∈ xs, ParStep R (σ x) (σ' x)) := by
  intro xs
  induction xs with
  | nil =>
      intro args' _ hpl
      -- the empty pattern: the reduced list is empty, identity works
      rw [List.map_nil] at hpl
      cases hpl
      exact ⟨fun y => .var y, by simp, fun _ _ => rfl, fun x hx => absurd hx (by simp)⟩
  | cons x xs ih =>
      intro args' hnd hpl
      rw [List.map_cons] at hpl
      cases args' with
      | nil => cases hpl
      | cons a' args'2 =>
          cases hpl with
          | cons hhead htail =>
              obtain ⟨hxnd, hxsnd⟩ := List.nodup_cons.1 hnd
              obtain ⟨σ', hmap, hfix, hpt⟩ := ih args'2 hxsnd htail
              -- override the recursive substitution at the head variable `x`
              refine ⟨fun y => if y = x then a' else σ' y, ?_, ?_, ?_⟩
              · -- the mapped list reproduces `a' :: args'2`
                rw [List.map_cons]
                simp only [↓reduceIte]
                congr 1
                -- the tail: `x ∉ xs`, so the override does not affect tail entries
                rw [← hmap]
                apply List.map_congr_left
                intro y hy
                have hyx : y ≠ x := by rintro rfl; exact hxnd hy
                simp [hyx]
              · -- fixes variables outside `x :: xs`
                intro y hy
                rw [List.mem_cons, not_or] at hy
                simp only [if_neg hy.1]
                exact hfix y hy.2
              · -- pointwise parallel reduction on `x :: xs`
                intro z hz
                rw [List.mem_cons] at hz
                rcases hz with rfl | hz
                · simp only [↓reduceIte]; exact hhead
                · have hzx : z ≠ x := by rintro rfl; exact hxnd hz
                  simp only [if_neg hzx]; exact hpt z hz

/-- Inversion of a parallel step out of an application: either the step develops the
arguments through `ParStepList`, leaving the head fixed, or it contracts a root
rule-instance. The two summands are the `app` and `root` constructors; the inversion
goes through the mutual recursor with the source pinned, since the `root` index
`σ • rule.lhs` does not directly unify with `app f args`. -/
theorem parStep_app_inv {R : TRS sigma nu} {f : sigma} {args : List (Term sigma nu)}
    {u : Term sigma nu} (h : ParStep R (.app f args) u) :
    (∃ args', u = .app f args' ∧ ParStepList R args args') ∨
      (∃ rule : Rule sigma nu, rule ∈ R ∧ ∃ σ σ' : Subst sigma nu,
        (.app f args : Term sigma nu) = σ • rule.lhs ∧ u = σ' • rule.rhs ∧
        ∀ x, ParStep R (σ x) (σ' x)) := by
  refine ParStep.rec (R := R)
    (motive_1 := fun t u _ => ∀ (g : sigma) (as : List (Term sigma nu)), t = .app g as →
      (∃ as', u = .app g as' ∧ ParStepList R as as') ∨
        (∃ rule : Rule sigma nu, rule ∈ R ∧ ∃ σ σ' : Subst sigma nu,
          (.app g as : Term sigma nu) = σ • rule.lhs ∧ u = σ' • rule.rhs ∧
          ∀ x, ParStep R (σ x) (σ' x)))
    (motive_2 := fun _ _ _ => True)
    ?var ?app ?root trivial (fun _ _ _ _ => trivial) h f args rfl
  · -- variable source: cannot equal an application
    intro x g as hx; exact absurd hx (by simp)
  · -- application source: the developing case
    intro g args0 args0' hlist _ g' as has
    rw [Term.app.injEq] at has
    obtain ⟨hgg, haa⟩ := has
    subst hgg; subst haa
    exact Or.inl ⟨args0', rfl, hlist⟩
  · -- root source: the contracting case
    intro rule hrule σ σ' hpt _ g as has
    exact Or.inr ⟨rule, hrule, σ, σ', has.symm, rfl, hpt⟩

/-! ## The complete development of a shallow root redex

When `completeDevelopment` contracts a shallow root redex `σ • rule.lhs = app f args`,
the contracted substitution develops every argument: the result of instantiating
`rule.lhs` by the developed images is `app f` applied to the developed arguments. This
identifies the development of a shallow redex independently of which matching rule was
selected, the fact that lets two root contractions of one source be reconciled. -/

/-- A root matcher never fires on a variable: a rule's left-hand side is an application,
so `matchAgainst rule.lhs (.var x) = none` for every rule, and `findRedex R (.var x)`
returns `none`. Hence the complete development of a variable is the variable. -/
theorem findRedex_var_eq_none [DecidableEq sigma] [DecidableEq nu]
    (R : TRS sigma nu) (x : nu) : findRedex R (.var x) = none := by
  induction R with
  | nil => rfl
  | cons r rest ih =>
      have hm : matchAgainst r.lhs (.var x) = none := by
        -- the pattern is an application, so it cannot match a variable target
        have happ : r.lhs.isApp = true := r.lhs_isApp
        cases hl : r.lhs with
        | var z => rw [hl] at happ; simp at happ
        | app g largs => simp [matchAgainst, matchAux]
      rw [findRedex]
      split
      · -- the matcher cannot return `some` on a variable
        rename_i τ hsome
        rw [hm] at hsome; exact absurd hsome (by simp)
      · rw [ih]; rfl

/-- Instantiating a shallow left-hand side by the developed substitution develops the
arguments: if `nonVarPositions rule.lhs = [[]]` and `σ • rule.lhs = .app f args`, then
`apply (fun y => if y ∈ Term.vars rule.lhs then completeDevelopment R (σ y) else g y)
rule.lhs = .app f (args.map (completeDevelopment R))` for any fallback `g`. The shallow
left-hand side `f(x1,...,xn)` has all pattern variables at depth one, so each developed
image lands on the development of the matching argument. -/
theorem dev_apply_shallow_lhs [DecidableEq sigma] [DecidableEq nu]
    (R : TRS sigma nu) {rule : Rule sigma nu} (hsh : shallowLhs rule)
    {σ : Subst sigma nu} {f : sigma} {args : List (Term sigma nu)}
    (heq : σ • rule.lhs = .app f args) (g : Subst sigma nu) :
    apply (fun y => if y ∈ Term.vars rule.lhs then completeDevelopment R (σ y) else g y)
        rule.lhs
      = .app f (args.map (completeDevelopment R)) := by
  -- the shallow left-hand side is `f` applied to variables
  have happ : rule.lhs.isApp = true := rule.lhs_isApp
  cases hl : rule.lhs with
  | var z => rw [hl] at happ; simp at happ
  | app f0 largs =>
      -- every argument of the pattern is a variable
      have hvars : ∀ a ∈ largs, ∃ x, a = .var x := by
        apply args_all_var_of_shallow (f := f0)
        rw [← hl]; exact hsh
      -- the head and arguments of the instance
      rw [hl, apply_app] at heq
      rw [Term.app.injEq] at heq
      obtain ⟨hf, hargs⟩ := heq
      subst hf
      -- set the developed substitution
      set ρ : Subst sigma nu :=
        (fun y => if y ∈ Term.vars (Term.app f0 largs) then completeDevelopment R (σ y) else g y)
        with hρ
      rw [apply_app, applyList_eq_map]
      congr 1
      -- rewrite `args` as the substituted pattern, then compare position-wise
      rw [← hargs, applyList_eq_map, List.map_map]
      apply List.map_congr_left
      intro a ha
      obtain ⟨x, rfl⟩ := hvars a ha
      simp only [Function.comp_apply, apply_var]
      have hxmem : x ∈ Term.vars (Term.app f0 largs) := by
        rw [Term.vars_app, Term.mem_varsList_iff]; exact ⟨.var x, ha, by simp⟩
      rw [hρ]; simp only [if_pos hxmem]

/-! ## The Takahashi triangle for shallow weakly orthogonal systems

Every parallel reduct parallel-reduces to the complete development. The proof is a
strong induction on the term's size, inverting the parallel step. A variable reduces
only to itself, matching its own development. At a term carrying a root redex, the
reduct either developed the arguments, in which case the matched substitution is
recovered by the shallow decomposition `exists_parStep_subst_of_parStepList` and the
root redex is contracted with the developed images supplied by the induction
hypothesis; or it contracted a root redex of a possibly different rule, in which case
the two contractions reconcile through `weaklyOrthogonal_root_reducts_eq` after both are
identified with the development of the shared arguments by `dev_apply_shallow_lhs`. At a
term with no root redex the reduct develops the arguments, closed argument-wise by the
induction hypothesis. -/

/-- A list of variable terms is the variable-image of a list of variables: if every
entry of `largs` is a variable, then `largs = xs.map Term.var` for some `xs`. Recovers
the underlying variable list of a shallow left-hand side's arguments. -/
theorem exists_var_list_of_all_var {largs : List (Term sigma nu)}
    (h : ∀ a ∈ largs, ∃ x, a = .var x) : ∃ xs : List nu, largs = xs.map .var := by
  induction largs with
  | nil => exact ⟨[], rfl⟩
  | cons a as ih =>
      obtain ⟨x, rfl⟩ := h a (by simp)
      obtain ⟨xs, rfl⟩ := ih (fun b hb => h b (by simp [hb]))
      exact ⟨x :: xs, by simp⟩

/-- Applying a substitution across a list of variable terms reads off the substitution:
`applyList σ (xs.map var) = xs.map σ`. -/
theorem applyList_map_var (σ : Subst sigma nu) (xs : List nu) :
    applyList σ (xs.map (Term.var (sigma := sigma))) = xs.map σ := by
  rw [applyList_eq_map, List.map_map]; rfl

/-- The variable-occurrence list of a shallow pattern is its variable list:
`varOccs (app f (xs.map var)) = xs`. So a linear shallow pattern has a duplicate-free
variable list. -/
theorem varOccs_app_var_eq {f : sigma} (xs : List nu) :
    Term.varOccs (Term.app f (xs.map (Term.var (sigma := sigma)))) = xs := by
  rw [Term.varOccs_app]
  induction xs with
  | nil => rfl
  | cons a as ih => rw [List.map_cons, Term.varOccsList_cons, Term.varOccs_var, ih]; rfl

/-- The variables of a shallow left-hand side are exactly the entries of its variable
list: `y ∈ vars (app f (xs.map var)) ↔ y ∈ xs`. -/
theorem mem_vars_app_var_iff [DecidableEq nu] {f : sigma} {xs : List nu} {y : nu} :
    y ∈ Term.vars (Term.app f (xs.map (Term.var (sigma := sigma)))) ↔ y ∈ xs := by
  rw [Term.vars_app, Term.mem_varsList_iff]
  constructor
  · rintro ⟨a, ha, hya⟩
    rw [List.mem_map] at ha
    obtain ⟨x, hx, rfl⟩ := ha
    rw [Term.vars_var, Finset.mem_singleton] at hya
    exact hya ▸ hx
  · intro hy
    exact ⟨.var y, List.mem_map_of_mem hy, by simp⟩

/-- The argument-wise development reconciliation: given the per-argument triangle
property and a position-wise parallel reduction `ParStepList R args args'`, the reduced
arguments `args'` parallel-reduce position-wise to the developed arguments. The list
companion of the no-root-redex case, proven by induction on `args'` against the
sub-list witness so the per-argument hypothesis applies to each entry. -/
theorem parStepList_develop [DecidableEq sigma] [DecidableEq nu] {R : TRS sigma nu}
    {whole : List (Term sigma nu)}
    (hdev : ∀ a ∈ whole, ∀ w, ParStep R a w → ParStep R w (completeDevelopment R a)) :
    ∀ {args args' : List (Term sigma nu)}, (∀ a ∈ args, a ∈ whole) →
      ParStepList R args args' →
        ParStepList R args' (args.attach.map (fun a => completeDevelopment R a.1)) := by
  intro args
  induction args with
  | nil =>
      intro args' _ hpl
      cases hpl
      simpa using ParStepList.nil
  | cons a as ih =>
      intro args' hsub hpl
      cases hpl with
      | cons hhead htail =>
          rename_i a' as'
          rw [List.attach_cons, List.map_cons, List.map_map]
          have hamem : a ∈ whole := hsub a (List.mem_cons_self)
          refine ParStepList.cons (hdev a hamem a' hhead) ?_
          have := ih (fun b hb => hsub b (List.mem_cons_of_mem a hb)) htail
          simpa using this

/-- The Takahashi triangle: for a shallow weakly orthogonal system, every parallel
reduct of a term parallel-reduces to that term's complete development,
`ParStep R u (completeDevelopment R t)`. Strong induction on `Term.size t` with the
matched-substitution images strictly smaller (`size_apply_var_lt_app`) and the arguments
strictly smaller (`Term.size_lt_of_mem`). The matched-root cases use
`weaklyOrthogonal_root_reducts_eq` to reconcile a root contraction with the development,
and the shallow structure (`dev_apply_shallow_lhs`, `exists_parStep_subst_of_parStepList`)
to align the substitution instances. -/
theorem parStep_triangle [DecidableEq sigma] [DecidableEq nu] {R : TRS sigma nu}
    (hwo : weaklyOrthogonal R) (hsh : shallow R) :
    ∀ {t u : Term sigma nu}, ParStep R t u → ParStep R u (completeDevelopment R t) := by
  intro t
  induction hn : Term.size t using Nat.strong_induction_on generalizing t with
  | _ n ih =>
    subst hn
    intro u h
    match t with
    | .var x =>
        -- a parallel step out of a variable lands on the variable itself
        rw [parStep_var_inv h, completeDevelopment, findRedex_var_eq_none]
        exact ParStep.var x
    | .app f args =>
        rcases parStep_app_inv h with ⟨args', rfl, hlist⟩ | ⟨rule2, hrule2, σ2, σ2', hsrc2, rfl, hpt2⟩
        · -- the reduct developed the arguments: split on whether a root redex matches
          rw [completeDevelopment]
          split
          · -- a root redex matches; recover the matched substitution by decomposition
            rename_i red hfind
            obtain ⟨rule, σ, hc⟩ := red
            obtain ⟨hmem, hlhs, hfix⟩ := hc.down
            show ParStep R (Term.app f args')
              (apply (fun y => if y ∈ Term.vars rule.lhs then completeDevelopment R (σ y) else .var y)
                rule.rhs)
            set ρ : Subst sigma nu :=
              (fun y => if y ∈ Term.vars rule.lhs then completeDevelopment R (σ y) else .var y)
              with hρ
            -- the shallow left-hand side is `app f0 largs` with `largs` all variables
            have hshrule : shallowLhs rule := hsh rule hmem
            have happ : rule.lhs.isApp = true := rule.lhs_isApp
            obtain ⟨f0, largs, hl⟩ : ∃ f0 largs, rule.lhs = .app f0 largs := by
              cases hcl : rule.lhs with
              | var z => rw [hcl] at happ; simp at happ
              | app f0 largs => exact ⟨f0, largs, rfl⟩
            have hvars : ∀ a ∈ largs, ∃ x, a = .var x := by
              apply args_all_var_of_shallow (f := f0); rw [← hl]; exact hshrule
            obtain ⟨xs, hxs⟩ := exists_var_list_of_all_var hvars
            -- the matched instance fixes the head and the (substituted) arguments
            have hinst : σ • rule.lhs = .app f0 (xs.map σ) := by
              rw [hl, hxs, apply_app, applyList_map_var]
            rw [hlhs, Term.app.injEq] at hinst
            obtain ⟨hf0, hargseq⟩ := hinst
            -- left-linearity gives the variable list duplicate-free
            have hnd : xs.Nodup := by
              have hlin : Term.linear rule.lhs := (hwo.1) rule hmem
              rw [hl, hxs, Term.linear, varOccs_app_var_eq] at hlin; exact hlin
            -- the position-wise reduction of the substituted variables
            have hpl : ParStepList R (xs.map σ) args' := by rw [← hargseq]; exact hlist
            obtain ⟨σ', hmap, hfix', hpt'⟩ := exists_parStep_subst_of_parStepList xs args' hnd hpl
            -- `app f args' = σ' • rule.lhs`
            have hinst' : σ' • rule.lhs = .app f args' := by
              have h1 : σ' • rule.lhs = .app f0 args' := by
                rw [hl, hxs, apply_app, applyList_map_var, hmap]
              rw [h1, hf0]
            -- contract the root redex with the developed substitution `ρ`
            rw [← hinst']
            refine ParStep.root hmem σ' ρ (fun y => ?_)
            by_cases hy : y ∈ Term.vars rule.lhs
            · -- pattern variable: develop via the induction hypothesis at smaller size
              rw [hρ]; simp only [if_pos hy]
              have hyxs : y ∈ xs := by rw [hl, hxs] at hy; exact mem_vars_app_var_iff.1 hy
              have hstep : ParStep R (σ y) (σ' y) := hpt' y hyxs
              -- the matched image is a strict subterm of the redex
              have hlt : Term.size (σ y) < Term.size (Term.app f args) := by
                have hlt0 := size_apply_var_lt_app σ f0 largs y (by rw [← hl]; exact hy)
                rwa [← hl, hlhs] at hlt0
              exact ih (Term.size (σ y)) hlt rfl hstep
            · -- non-pattern variable: both sides are `y`
              rw [hρ]; simp only [if_neg hy]
              have hyxs : y ∉ xs := by rw [hl, hxs] at hy; exact fun hcc => hy (mem_vars_app_var_iff.2 hcc)
              rw [hfix' y hyxs]; exact ParStep.var y
          · -- no root redex: develop the arguments through the induction hypothesis
            rename_i hfind
            refine ParStep.app f ?_
            refine parStepList_develop (whole := args) ?_ (fun a ha => ha) hlist
            -- the per-argument triangle: each argument is strictly smaller
            intro a ha w hpar
            exact ih (Term.size a) (Term.size_lt_of_mem ha) rfl hpar
        · -- the reduct contracted a root redex of `rule2`
          rw [completeDevelopment]
          split
          · -- the development also contracts a root redex `rule`
            rename_i red hfind
            obtain ⟨rule, σ, hc⟩ := red
            obtain ⟨hmem, hlhs, hfix⟩ := hc.down
            show ParStep R (σ2' • rule2.rhs)
              (apply (fun y => if y ∈ Term.vars rule.lhs then completeDevelopment R (σ y) else .var y)
                rule.rhs)
            -- the developed substitution for the reduct's rule `rule2`
            set δ : Subst sigma nu :=
              (fun y => if y ∈ Term.vars rule2.lhs then completeDevelopment R (σ2 y) else σ2' y)
              with hδ
            -- `rule2.lhs` is an application, so each pattern image is strictly smaller
            have happ2 : rule2.lhs.isApp = true := rule2.lhs_isApp
            obtain ⟨f2, l2, hl2⟩ : ∃ f2 l2, rule2.lhs = .app f2 l2 := by
              cases hcl : rule2.lhs with
              | var z => rw [hcl] at happ2; simp at happ2
              | app f2 l2 => exact ⟨f2, l2, rfl⟩
            -- step 1: the reduct parallel-reduces to the development via `parStep_subst`
            have hstep1 : ParStep R (σ2' • rule2.rhs) (δ • rule2.rhs) := by
              refine parStep_subst R (fun x => ?_) (ParStep.refl R rule2.rhs)
              by_cases hx : x ∈ Term.vars rule2.lhs
              · rw [hδ]; simp only [if_pos hx]
                -- `ParStep (σ2 x) (σ2' x)` and triangle-IH at the smaller image
                have hlt : Term.size (σ2 x) < Term.size (Term.app f args) := by
                  have hlt0 := size_apply_var_lt_app σ2 f2 l2 x (by rw [← hl2]; exact hx)
                  rwa [← hl2, ← hsrc2] at hlt0
                exact ih (Term.size (σ2 x)) hlt rfl (hpt2 x)
              · rw [hδ]; simp only [if_neg hx]; exact ParStep.refl R (σ2' x)
            -- step 2: the two developments coincide, both equal to the shared development
            have hdev2 : δ • rule2.lhs = .app f (args.map (completeDevelopment R)) :=
              dev_apply_shallow_lhs R (hsh rule2 hrule2) hsrc2.symm σ2'
            have hdevr : apply (fun y => if y ∈ Term.vars rule.lhs then completeDevelopment R (σ y)
                  else .var y) rule.lhs = .app f (args.map (completeDevelopment R)) :=
              dev_apply_shallow_lhs R (hsh rule hmem) hlhs (fun y => .var y)
            have hlhseq : δ • rule2.lhs
                = apply (fun y => if y ∈ Term.vars rule.lhs then completeDevelopment R (σ y)
                    else .var y) rule.lhs := by rw [hdev2, hdevr]
            -- weak orthogonality forces the two root reducts to coincide
            have hrhseq : δ • rule2.rhs
                = apply (fun y => if y ∈ Term.vars rule.lhs then completeDevelopment R (σ y)
                    else .var y) rule.rhs :=
              weaklyOrthogonal_root_reducts_eq hwo hrule2 hmem hlhseq
            rw [← hrhseq]; exact hstep1
          · -- no root redex: contradicts the existing root contraction of `rule2`
            rename_i hfind
            exact absurd ⟨rule2, hrule2, σ2, hsrc2.symm⟩ (not_rootStep_of_findRedex_none hfind)

/-! ## The parallel-reduction diamond and termination-free confluence

The triangle gives the diamond: any two parallel reducts of a term both
parallel-reduce to its complete development. The diamond lifts to confluence of the
reflexive-transitive closure of parallel reduction, which coincides with the rewrite
relation, so the rewrite relation is confluent with no strong-normalization
hypothesis. -/

/-- The parallel-reduction diamond for a shallow weakly orthogonal system: any two
parallel reducts `u1, u2` of a term `t` are completed by a one-step parallel valley,
both parallel-reducing to the complete development `completeDevelopment R t`. The two
legs are instances of the Takahashi triangle `parStep_triangle`. -/
theorem parStep_diamond [DecidableEq sigma] [DecidableEq nu] {R : TRS sigma nu}
    (hwo : weaklyOrthogonal R) (hsh : shallow R) : Diamond (ParStep R) := by
  intro t u1 u2 h1 h2
  exact ⟨completeDevelopment R t, parStep_triangle hwo hsh h1, parStep_triangle hwo hsh h2⟩

/-- Termination-free confluence of parallel reduction for a shallow weakly orthogonal
system: the reflexive-transitive closure of `ParStep R` is confluent, with no
strong-normalization hypothesis. The parallel-reduction diamond `parStep_diamond` lifts
to confluence of its closure through `diamond_imp_confluent`. -/
theorem weaklyOrthogonal_shallow_imp_confluent [DecidableEq sigma] [DecidableEq nu]
    {R : TRS sigma nu} (hwo : weaklyOrthogonal R) (hsh : shallow R) :
    Confluent (ReflTransGen (ParStep R)) :=
  diamond_imp_confluent (parStep_diamond hwo hsh)

/-- Termination-free confluence of the rewrite relation for a shallow weakly orthogonal
system: `StepStar R` is confluent, with no strong-normalization hypothesis. The
parallel-reduction diamond lifts to confluence of the closure of `ParStep R`
(`weaklyOrthogonal_shallow_imp_confluent`), and that closure is the rewrite relation by
`reflTransGen_parStep_eq_stepStar`. This realizes confluence through the Takahashi route
on the original system, with no termination assumption. -/
theorem weaklyOrthogonal_shallow_stepStar_confluent [DecidableEq sigma] [DecidableEq nu]
    {R : TRS sigma nu} (hwo : weaklyOrthogonal R) (hsh : shallow R) :
    Confluent (StepStar R) := by
  have hconf := weaklyOrthogonal_shallow_imp_confluent hwo hsh
  rwa [reflTransGen_parStep_eq_stepStar] at hconf

/-! ## Non-vacuity

The demonstration system `Example.demoTRS` (`f(x) -> g(x)`) is a non-empty shallow
weakly orthogonal system: its single left-hand side `f(x)` is linear and shallow, and
its only critical pair is the trivial root self-overlap. The termination-free
confluence conclusion applies to it, exhibiting the result on a concrete non-empty
system. -/

namespace WeaklyOrthogonalShallow

/-- The demonstration left-hand side `f(x)` is shallow: its only non-variable position
is the root. -/
theorem demo_shallowLhs : shallowLhs Example.demoRule := by
  show nonVarPositions Example.demoRule.lhs = [[]]
  decide

/-- The demonstration system is shallow: its single rule has a shallow left-hand side. -/
theorem demo_shallow : shallow Example.demoTRS := by
  intro rule hrule
  rw [Example.demoTRS, List.mem_singleton] at hrule
  subst hrule; exact demo_shallowLhs

/-- The demonstration system is weakly orthogonal: it is left-linear and its only
critical pair is the trivial root self-overlap, whose two components coincide. -/
theorem demo_weaklyOrthogonal : weaklyOrthogonal Example.demoTRS := by
  constructor
  · -- left-linear: the single left-hand side `f(x)` has a duplicate-free variable list
    intro rule hrule
    rw [Example.demoTRS, List.mem_singleton] at hrule
    subst hrule
    show (Term.varOccs Example.demoRule.lhs).Nodup
    decide
  · -- every critical pair is trivial: the only overlap is the root self-overlap
    intro p hp
    have hcp : criticalPairs Example.demoTRS
        = [((.app 1 [.var (Sum.inr 0)] : Term Nat (RenVar Nat)), .app 1 [.var (Sum.inr 0)])] := by
      simp [criticalPairs, Example.demoTRS, Example.demoRule, Example.lhsTerm, Example.rhsTerm,
        overlapPairs, renameRule, Term.rename, Term.renameList, nonVarPositions,
        nonVarPositionsList, overlapAt, Term.subtermAt, unify, solve, zipPairs, wlSubst1,
        Term.replaceAt, Subst.apply, Subst.applyList, Subst.id, subst1]
    rw [hcp, List.mem_singleton] at hp
    subst hp; rfl

/-- Termination-free confluence applied to the non-empty demonstration system:
`StepStar Example.demoTRS` is confluent, with no strong-normalization hypothesis. The
system `f(x) -> g(x)` is shallow and weakly orthogonal, so the Takahashi route applies,
exhibiting termination-free confluence on a concrete non-empty system. -/
theorem demo_stepStar_confluent : Confluent (StepStar Example.demoTRS) :=
  weaklyOrthogonal_shallow_stepStar_confluent demo_weaklyOrthogonal demo_shallow

end WeaklyOrthogonalShallow

end OperatorKO7.Meta.Rewriting

/-! ## Verification: headline types and axiom audit -/

open OperatorKO7.Meta.Rewriting in
#check @matchAgainst_complete
open OperatorKO7.Meta.Rewriting in
#check @findRedex_isSome_of_rootStep
open OperatorKO7.Meta.Rewriting in
#check @weaklyOrthogonal_root_reducts_eq
open OperatorKO7.Meta.Rewriting in
#check @parStep_app_inv
open OperatorKO7.Meta.Rewriting in
#check @parStep_triangle
open OperatorKO7.Meta.Rewriting in
#check @parStep_diamond
open OperatorKO7.Meta.Rewriting in
#check @weaklyOrthogonal_shallow_imp_confluent
open OperatorKO7.Meta.Rewriting in
#check @weaklyOrthogonal_shallow_stepStar_confluent
open OperatorKO7.Meta.Rewriting in
#check @WeaklyOrthogonalShallow.demo_weaklyOrthogonal
open OperatorKO7.Meta.Rewriting in
#check @WeaklyOrthogonalShallow.demo_shallow
open OperatorKO7.Meta.Rewriting in
#check @WeaklyOrthogonalShallow.demo_stepStar_confluent

#print axioms OperatorKO7.Meta.Rewriting.weaklyOrthogonal_root_reducts_eq
#print axioms OperatorKO7.Meta.Rewriting.parStep_triangle
#print axioms OperatorKO7.Meta.Rewriting.parStep_diamond
#print axioms OperatorKO7.Meta.Rewriting.weaklyOrthogonal_shallow_imp_confluent
#print axioms OperatorKO7.Meta.Rewriting.weaklyOrthogonal_shallow_stepStar_confluent
#print axioms OperatorKO7.Meta.Rewriting.WeaklyOrthogonalShallow.demo_weaklyOrthogonal
#print axioms OperatorKO7.Meta.Rewriting.WeaklyOrthogonalShallow.demo_stepStar_confluent
