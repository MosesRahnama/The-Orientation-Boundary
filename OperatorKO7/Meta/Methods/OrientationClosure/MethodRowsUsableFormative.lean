import OperatorKO7.Meta.Methods.OrientationClosure.ProcessorSemantics
import OperatorKO7.Meta.Methods.DependencyPairTypedRows
import Mathlib.Tactic

/-!
# Rows `usableRulesMinimality` and `formativeRules` (orientation closeout, P5 group)

Two rows of the method universe are stated and proved here.

`usableRulesMinimality` generates the usable rules of a dependency-pair problem over the generic
first-order library: the rules whose defined root symbols are reachable, recursively over the
dependency graph, from the defined symbols occurring in the right-hand sides of the pairs. The row
proves closure of the generated set under its own computation, leastness of the generated set among
closed rule sets containing the seed rules, and the chain-class finiteness transport from the
generated rules to the original problem for calls whose defined subterm roots are usable.

`formativeRules` generates the formative rule and pair catalog of the KO7 dependency-pair problem
from the actual eight-schema source and proves reduction sufficiency, closure, and exactness of the
generated catalog for the actual pair relation.

Pinned primary definitions. Usable rules: the formulation of N. Hirokawa and A. Middeldorp,
*Tyrolean termination tool: techniques and features*, Information and Computation 205(4), 2007,
realized in the package by `RDRSCoverageEvidenceLedger.ko7GeneratedUsableRules` (2026).
Formative rules: C. Fuhs and C. Kop,
*First-Order Formative Rules*, RTA-TLCA 2014, LNCS 8560:240-256, Springer, 2014, Section 3, realized
in the package by `DependencyPairTypedRows.FormativePair` (2026).

Trust: kernel-only; baseline axioms only; Mathlib and existing `OperatorKO7` modules only.
-/

set_option autoImplicit false

namespace OperatorKO7.Methods.OrientationClosure.MethodRowsUsableFormative

open OperatorKO7.Meta.Rewriting
open OperatorKO7.Methods.OrientationClosure.DependencyPairSoundness
open OperatorKO7.Methods.OrientationClosure.ProcessorSemantics
open OperatorKO7.Trace
open OperatorKO7.MetaDependencyPairs
open OperatorKO7.Methods.DependencyPairTypedRows

/-! ## Shared free-schema carriers -/

/-- First-order terms over the free symbols. -/
abbrev FTerm : Type := Term FreeSym Nat

/-- Calls over the free symbols. -/
abbrev FCall : Type := Call FreeSym Nat

/-- Dependency-pair problems over the free symbols. -/
abbrev FProblem : Type := FCall → FCall → Prop

/-- Rules over the free symbols. -/
abbrev FRule : Type := Rule FreeSym Nat

/-- Rewrite systems over the free symbols. -/
abbrev FTRS : Type := TRS FreeSym Nat

/-- The dependency-pair problem of the free recursor is finite. -/
theorem free_finiteDP : FiniteDP freeRecursorTRS (dpPairs freeRecursorTRS) :=
  Subrelation.wf (fun {_ _} h => (chainP_dpPairs_iff freeRecursorTRS _ _).1 h)
    (minChain_wf_of_subtermCriterion freeRecursorTRS_subtermCriterion)

/-- The source call of the dependency pair of the free recursor. -/
def dpSource : FCall := (.recur, [.var 0, .var 1, .app .succ [.var 2]])

/-- The target call of the dependency pair of the free recursor. -/
def dpTarget : FCall := (.recur, [.var 0, .var 1, .var 2])

/-- The recursive call of the successor rule is a subterm of its right-hand side. -/
theorem succRule_rhs_recur :
    IsSubterm (.app FreeSym.recur [.var 0, .var 1, .var 2] : FTerm) succRule.rhs := by
  show IsSubterm _ (Term.app FreeSym.wrap
    [Term.var 1, Term.app FreeSym.recur [Term.var 0, Term.var 1, Term.var 2]])
  exact IsSubterm.arg FreeSym.wrap _ (by simp) (IsSubterm.refl _)

/-- The extracted pair of the free recursor edge. -/
theorem free_dpPair : dpPairs freeRecursorTRS dpSource dpTarget :=
  ⟨succRule, by simp [freeRecursorTRS], Subst.id, by simp [dpSource, succRule, Subst.id],
    [.var 0, .var 1, .var 2], succRule_rhs_recur, (freeRecursorTRS_defined_iff _).2 rfl,
    by simp [dpTarget, Subst.id]⟩

/-! ## Subterm and substitution lemmas for the generator -/

/-- Subterm is transitive. -/
theorem isSubterm_trans {w u t : FTerm} (h1 : IsSubterm w u) (h2 : IsSubterm u t) :
    IsSubterm w t := by
  induction h2 generalizing w with
  | refl => exact h1
  | arg f args hmem hsub ih => exact .arg f args hmem (ih h1)

/-- A subterm of an application is the application itself or a subterm of one of its arguments. -/
theorem isSubterm_app_decompose {w t : FTerm} (h : IsSubterm w t) {f : FreeSym}
    {args : List FTerm} (ht : t = .app f args) :
    w = .app f args ∨ ∃ a ∈ args, IsSubterm w a := by
  induction h generalizing f args with
  | refl => exact Or.inl ht
  | arg g gargs hmem hsub _ =>
    simp only [Term.app.injEq] at ht
    obtain ⟨rfl, rfl⟩ := ht
    exact Or.inr ⟨_, hmem, hsub⟩

/-- The image of a variable of a term is a subterm of the substituted term. -/
theorem IsSubterm_subst_var {σ : Subst FreeSym Nat} {t : FTerm} {x : Nat}
    (hx : x ∈ Term.vars t) : IsSubterm (σ x) (Subst.apply σ t) := by
  induction t using Term.rec' with
  | hvar y =>
    simp only [Term.vars_var, Finset.mem_singleton] at hx
    subst hx
    exact IsSubterm.refl _
  | happ f args ih =>
    rw [Term.vars_app, Term.mem_varsList_iff] at hx
    obtain ⟨a, ha, hxa⟩ := hx
    rw [Subst.apply_app, Subst.applyList_eq_map]
    exact IsSubterm.arg f _ (List.mem_map_of_mem ha) (ih a ha hxa)

/-! ## Usable-rule generation over the free signature -/

/-- The root symbol of a rule's left-hand side, if the left-hand side is an application. -/
def ruleRoot (r : FRule) : Option FreeSym :=
  match r.lhs with
  | .var _ => none
  | .app f _ => some f

/-- A rule whose left-hand side is headed by `f` has `ruleRoot` equal to `f`. -/
theorem ruleRoot_of_lhs_app {r : FRule} {f : FreeSym}
    (h : ∃ args : List FTerm, r.lhs = .app f args) : ruleRoot r = some f := by
  obtain ⟨args, hl⟩ := h
  unfold ruleRoot
  rw [hl]

/-- `g` occurs as the root symbol of an application subterm of `t`. -/
def occursRoot (g : FreeSym) (t : FTerm) : Prop :=
  ∃ args : List FTerm, IsSubterm (.app g args) t

/-- Every application subterm of a substitution instance either comes from the skeleton or lies in
a substitution image. -/
theorem occursRoot_subst {σ : Subst FreeSym Nat} {t : FTerm} {g : FreeSym}
    (h : occursRoot g (Subst.apply σ t)) :
    (∃ args : List FTerm, IsSubterm (.app g args) t) ∨
      ∃ x : Nat, x ∈ Term.vars t ∧ occursRoot g (σ x) := by
  induction t using Term.rec' with
  | hvar x => exact Or.inr ⟨x, by simp, h⟩
  | happ f args ih =>
    obtain ⟨targs, htargs⟩ := h
    rcases isSubterm_app_decompose htargs (Subst.apply_app σ f args) with heq | ⟨a, ha, hsub⟩
    · simp only [Term.app.injEq] at heq
      obtain ⟨rfl, -⟩ := heq
      exact Or.inl ⟨args, IsSubterm.refl _⟩
    · rw [Subst.applyList_eq_map, List.mem_map] at ha
      obtain ⟨l, hl, rfl⟩ := ha
      rcases ih l hl ⟨targs, hsub⟩ with ⟨sargs, hs⟩ | ⟨x, hx, hocc⟩
      · exact Or.inl ⟨sargs, isSubterm_trans hs (.arg f args hl (.refl l))⟩
      · exact Or.inr ⟨x, by
          rw [Term.vars_app, Term.mem_varsList_iff]
          exact ⟨l, hl, hx⟩, hocc⟩

/-- The seed symbols: the defined symbols occurring in the pair targets. -/
def pairTargetRoot (R : FTRS) (P : FProblem) (g : FreeSym) : Prop :=
  ∃ c d : FCall, P c d ∧ IsDefined R g ∧ occursRoot g (.app d.1 d.2)

/-- The least symbol set closed under the call relation of `R` from the pair-target roots. -/
inductive UsableSym (R : FTRS) (P : FProblem) : FreeSym → Prop
  | seed {g : FreeSym} : pairTargetRoot R P g → UsableSym R P g
  | step {r : FRule} {f g : FreeSym} (hr : r ∈ R) (hrf : ruleRoot r = some f)
      (hf : UsableSym R P f) (hg : occursRoot g r.rhs) (hdef : IsDefined R g) :
      UsableSym R P g

/-- A rule is generated when it belongs to `R` and its root symbol is usable. -/
def IsUsableRule (R : FTRS) (P : FProblem) (r : FRule) : Prop :=
  r ∈ R ∧ ∃ f : FreeSym, ruleRoot r = some f ∧ UsableSym R P f

/-- The seed-rooted rules: every rule of `R` whose root symbol is a pair-target root. -/
def SeedRules (R : FTRS) (P : FProblem) (T : FRule → Prop) : Prop :=
  ∀ r : FRule, r ∈ R → (∃ f : FreeSym, ruleRoot r = some f ∧ pairTargetRoot R P f) → T r

/-- Closure of a rule set under the call relation of `R`. -/
def RuleSetClosed (R : FTRS) (T : FRule → Prop) : Prop :=
  ∀ r : FRule, T r → ∀ g : FreeSym, occursRoot g r.rhs → IsDefined R g →
    ∀ q : FRule, q ∈ R → ruleRoot q = some g → T q

/-- Every rule whose root symbol is usable is generated, by induction on usability. -/
theorem usableSym_rule_mem {R : FTRS} {P : FProblem} {T : FRule → Prop}
    (hseed : SeedRules R P T) (hclosed : RuleSetClosed R T) :
    ∀ {f : FreeSym}, UsableSym R P f → ∀ q : FRule, q ∈ R → ruleRoot q = some f → T q := by
  intro f hf
  induction hf with
  | seed hseedf => intro q hq hroot; exact hseed q hq ⟨_, hroot, hseedf⟩
  | step hr hrf hf' hg hdef ih =>
    intro q hq hroot
    exact hclosed _ (ih _ hr hrf) _ hg hdef q hq hroot

/-- The generated set is the least closed rule set containing the seed rules. -/
theorem usableRules_least (R : FTRS) (P : FProblem) :
    ∀ T : FRule → Prop, SeedRules R P T → RuleSetClosed R T →
      ∀ r : FRule, IsUsableRule R P r → T r := by
  intro T hseed hclosed r hr
  obtain ⟨hrR, f, hroot, hf⟩ := hr
  exact usableSym_rule_mem hseed hclosed hf r hrR hroot

/-- The generated set is closed under its own computation. -/
theorem usableRules_closed (R : FTRS) (P : FProblem) :
    RuleSetClosed R (IsUsableRule R P) := by
  intro r hr g hg hdef q hq hroot
  obtain ⟨hrR, f, hrf, hf⟩ := hr
  exact ⟨hq, g, hroot, UsableSym.step hrR hrf hf hg hdef⟩

/-! ## Rootedness, usable rewriting, and the chain hypothesis -/

/-- Every defined application subterm root of `t` is a usable symbol. -/
def UsableRooted (R : FTRS) (P : FProblem) (t : FTerm) : Prop :=
  ∀ {g : FreeSym} {args : List FTerm}, IsSubterm (.app g args) t → IsDefined R g → UsableSym R P g

/-- A rewrite step using only generated rules. -/
inductive UsableStep (R : FTRS) (P : FProblem) : FTerm → FTerm → Prop
  | root {r : FRule} {σ : Subst FreeSym Nat} (hr : IsUsableRule R P r) :
      UsableStep R P (Subst.apply σ r.lhs) (Subst.apply σ r.rhs)
  | arg (f : FreeSym) (pre post : List FTerm) {a b : FTerm} :
      UsableStep R P a b → UsableStep R P (.app f (pre ++ a :: post)) (.app f (pre ++ b :: post))

/-- Argument lists related by one usable rewrite step. -/
def UsableArgStep (R : FTRS) (P : FProblem) (xs ys : List FTerm) : Prop :=
  ∃ pre post : List FTerm, ∃ a b : FTerm,
    xs = pre ++ a :: post ∧ ys = pre ++ b :: post ∧ UsableStep R P a b

/-- A call all of whose arguments are usable-rooted. -/
def CallUsableRooted (R : FTRS) (P : FProblem) (c : FCall) : Prop :=
  ∀ a ∈ c.2, UsableRooted R P a

/-- The minimal chain relation of the pair problem read over the generated usable rules. -/
def UsableChainP (R : FTRS) (P : FProblem) (c d : FCall) : Prop :=
  (∀ a ∈ c.2, SN R a) ∧ (∀ a ∈ d.2, SN R a) ∧
    ∃ xs : List FTerm, Relation.ReflTransGen (UsableArgStep R P) c.2 xs ∧ P (c.1, xs) d

/-- An application is usable-rooted exactly when its root is usable and every argument is. -/
theorem usableRooted_app {R : FTRS} {P : FProblem} {f : FreeSym} {args : List FTerm} :
    UsableRooted R P (.app f args) ↔
      (IsDefined R f → UsableSym R P f) ∧ ∀ a ∈ args, UsableRooted R P a := by
  constructor
  · intro h
    refine ⟨fun hdef => h (IsSubterm.refl _) hdef, ?_⟩
    intro a ha
    intro g targs hsub hdef
    exact h (.arg f args ha hsub) hdef
  · rintro ⟨hf, hall⟩ g targs hsub hdef
    rcases isSubterm_app_decompose hsub rfl with heq | ⟨a, ha, hwa⟩
    · simp only [Term.app.injEq] at heq
      obtain ⟨rfl, -⟩ := heq
      exact hf hdef
    · exact hall a ha hwa hdef

/-- Usable-rootedness is inherited by subterms. -/
theorem usableRooted_of_subterm {R : FTRS} {P : FProblem} {u t : FTerm}
    (h : UsableRooted R P t) (hsub : IsSubterm u t) : UsableRooted R P u := by
  intro g targs hw hdef
  exact h (isSubterm_trans hw hsub) hdef

/-- A rewrite step from a usable-rooted term uses only generated rules and stays usable-rooted. -/
theorem usableStep_of_step {R : FTRS} {P : FProblem}
    (hvars : ∀ r ∈ R, Term.vars r.rhs ⊆ Term.vars r.lhs) :
    ∀ {u v : FTerm}, OperatorKO7.Meta.Rewriting.Step R u v → UsableRooted R P u →
      UsableStep R P u v ∧ UsableRooted R P v := by
  intro u v h
  induction h with
  | root hroot =>
    intro hu
    obtain ⟨rule, hrule, σ, hl, hr⟩ := hroot
    subst hl
    subst hr
    obtain ⟨f, largs, hf⟩ := lhs_eq_app rule
    have hrootf : ruleRoot rule = some f := ruleRoot_of_lhs_app ⟨largs, hf⟩
    have hsym : UsableSym R P f := by
      have hsub : IsSubterm (.app f (Subst.applyList σ largs)) (Subst.apply σ rule.lhs) := by
        rw [hf, Subst.apply_app]
        exact IsSubterm.refl _
      exact hu hsub ⟨rule, hrule, largs, hf⟩
    refine ⟨UsableStep.root ⟨hrule, f, hrootf, hsym⟩, ?_⟩
    intro g targs hsub hgdef
    rcases occursRoot_subst (σ := σ) ⟨targs, hsub⟩ with ⟨sargs, hs⟩ | ⟨x, hx, hocc⟩
    · exact UsableSym.step hrule hrootf hsym ⟨sargs, hs⟩ hgdef
    · obtain ⟨targs', htargs'⟩ := hocc
      have hxL : x ∈ Term.vars rule.lhs := hvars rule hrule hx
      have hsubx : IsSubterm (σ x) (Subst.apply σ rule.lhs) := IsSubterm_subst_var hxL
      exact hu (isSubterm_trans htargs' hsubx) hgdef
  | arg f pre post hab ih =>
    intro hu
    have hall := (usableRooted_app.mp hu).2
    obtain ⟨habU, hbU⟩ := ih (hall _ (List.mem_append.mpr (Or.inr List.mem_cons_self)))
    refine ⟨UsableStep.arg f pre post habU, ?_⟩
    refine (usableRooted_app).2 ⟨?_, ?_⟩
    · intro hfdef
      exact hu (IsSubterm.refl _) hfdef
    · intro x hx
      simp only [List.mem_append, List.mem_cons] at hx
      rcases hx with hx | rfl | hx
      · exact hall x (by simp only [List.mem_append, List.mem_cons]; exact Or.inl hx)
      · exact hbU
      · exact hall x (by simp only [List.mem_append, List.mem_cons]; exact Or.inr (Or.inr hx))

/-- A generated-rule step is an original step. -/
theorem step_of_usableStep {R : FTRS} {P : FProblem} {a b : FTerm}
    (h : UsableStep R P a b) : OperatorKO7.Meta.Rewriting.Step R a b := by
  induction h with
  | root hr => exact OperatorKO7.Meta.Rewriting.Step.root ⟨_, hr.1, _, rfl, rfl⟩
  | arg f pre post hab ih => exact OperatorKO7.Meta.Rewriting.Step.arg f pre post ih

/-- Argument rewriting inside the generated rules is argument rewriting. -/
theorem argStep_of_usableArgStep {R : FTRS} {P : FProblem} {xs ys : List FTerm}
    (h : UsableArgStep R P xs ys) : ArgStep R xs ys := by
  obtain ⟨pre, post, a, b, rfl, rfl, hab⟩ := h
  exact ⟨pre, post, a, b, rfl, rfl, step_of_usableStep hab⟩

/-- One original argument step from usable-rooted arguments lands in usable-rooted arguments. -/
theorem argStep_usableRooted {R : FTRS} {P : FProblem}
    (hvars : ∀ r ∈ R, Term.vars r.rhs ⊆ Term.vars r.lhs) {xs ys : List FTerm}
    (hxs : ∀ a ∈ xs, UsableRooted R P a) (h : ArgStep R xs ys) :
    ∀ a ∈ ys, UsableRooted R P a := by
  obtain ⟨pre, post, a, b, rfl, rfl, hab⟩ := h
  intro c hc
  simp only [List.mem_append, List.mem_cons] at hc
  rcases hc with hc | rfl | hc
  · exact hxs c (by simp only [List.mem_append, List.mem_cons]; exact Or.inl hc)
  · exact (usableStep_of_step hvars hab (hxs a (by simp))).2
  · exact hxs c (by simp only [List.mem_append, List.mem_cons]; exact Or.inr (Or.inr hc))

/-- One original argument step from usable-rooted arguments uses only generated rules. -/
theorem usableArgStep_of_argStep {R : FTRS} {P : FProblem}
    (hvars : ∀ r ∈ R, Term.vars r.rhs ⊆ Term.vars r.lhs) {xs ys : List FTerm}
    (hxs : ∀ a ∈ xs, UsableRooted R P a) (h : ArgStep R xs ys) : UsableArgStep R P xs ys := by
  obtain ⟨pre, post, a, b, rfl, rfl, hab⟩ := h
  exact ⟨pre, post, a, b, rfl, rfl, (usableStep_of_step hvars hab (hxs a (by simp))).1⟩

/-- The reach replays inside the generated rules and keeps every visited argument usable-rooted. -/
theorem usableReach_and_rooted {R : FTRS} {P : FProblem}
    (hvars : ∀ r ∈ R, Term.vars r.rhs ⊆ Term.vars r.lhs) :
    ∀ {xs ys : List FTerm}, Relation.ReflTransGen (ArgStep R) xs ys →
      (∀ a ∈ xs, UsableRooted R P a) →
        Relation.ReflTransGen (UsableArgStep R P) xs ys ∧ ∀ a ∈ ys, UsableRooted R P a := by
  intro xs ys h
  induction h with
  | refl => intro hxs; exact ⟨.refl, hxs⟩
  | tail hreach hstep ih =>
    intro hxs
    obtain ⟨hreachU, hmid⟩ := ih hxs
    exact ⟨hreachU.tail (usableArgStep_of_argStep hvars hmid hstep),
      argStep_usableRooted hvars hmid hstep⟩

/-- Every original reach from usable-rooted arguments replays inside the generated rules. -/
theorem usableReach_of_reach {R : FTRS} {P : FProblem}
    (hvars : ∀ r ∈ R, Term.vars r.rhs ⊆ Term.vars r.lhs) {xs ys : List FTerm}
    (h : Relation.ReflTransGen (ArgStep R) xs ys) (hxs : ∀ a ∈ xs, UsableRooted R P a) :
    Relation.ReflTransGen (UsableArgStep R P) xs ys :=
  (usableReach_and_rooted hvars h hxs).1

/-- The generated chain relation is a subrelation of the original one. -/
theorem chainReach_of_usableReach {R : FTRS} {P : FProblem} :
    ∀ {xs ys : List FTerm}, Relation.ReflTransGen (UsableArgStep R P) xs ys →
      Relation.ReflTransGen (ArgStep R) xs ys := by
  intro xs ys h
  induction h with
  | refl => exact .refl
  | tail hr hstep ih => exact ih.tail (argStep_of_usableArgStep hstep)

/-- The chain hypothesis: on usable-rooted calls the original chain relation is the generated one. -/
theorem usableChainP_of_chainP {R : FTRS} {P : FProblem}
    (hvars : ∀ r ∈ R, Term.vars r.rhs ⊆ Term.vars r.lhs) {c d : FCall}
    (hc : CallUsableRooted R P c) (h : ChainP R P c d) : UsableChainP R P c d := by
  obtain ⟨hcSN, hdSN, xs, hreach, hpd⟩ := h
  exact ⟨hcSN, hdSN, xs, usableReach_of_reach hvars hreach hc, hpd⟩

/-- The generated chain relation is a subrelation of the original one. -/
theorem usableChainP_to_chainP {R : FTRS} {P : FProblem} {c d : FCall}
    (h : UsableChainP R P c d) : ChainP R P c d := by
  obtain ⟨hcSN, hdSN, xs, hreach, hpd⟩ := h
  exact ⟨hcSN, hdSN, xs, chainReach_of_usableReach hreach, hpd⟩

/-! ## Row `usableRulesMinimality` -/

/-- Native data of `usableRulesMinimality`: the rewrite system and the dependency-pair problem.
The usable rules are generated from the data, not stored in it. -/
structure usableRulesMinimalityData where
  /-- The rewrite system. -/
  R : FTRS
  /-- The dependency-pair problem. -/
  P : FProblem

/-- Set-indexed closure of a candidate usable rule set. -/
def usableRulesClosedSet (M : usableRulesMinimalityData) (T : FRule → Prop) : Prop :=
  RuleSetClosed M.R T

/-- The generated usable rule set is closed under its own computation. -/
def usableRulesClosed (M : usableRulesMinimalityData) : Prop :=
  RuleSetClosed M.R (IsUsableRule M.R M.P)

/-- The generated usable rule set is the least closed set containing the seed rules. -/
def usableRulesLeast (M : usableRulesMinimalityData) : Prop :=
  ∀ T : FRule → Prop, SeedRules M.R M.P T → RuleSetClosed M.R T →
    ∀ r : FRule, IsUsableRule M.R M.P r → T r

/-- Laws of `usableRulesMinimality`, pinned to the usable rules of N. Hirokawa and
A. Middeldorp, *Tyrolean termination tool: techniques and features*, Information and Computation
205(4), 2007: for a term `t` and system `R` with `R_f` the rules of root
`f`, `U(R,t) = union over f in Fun(t) of (R_f union union over l->r in R_f of U(R,r))`; the package
realization is `RDRSCoverageEvidenceLedger.ko7GeneratedUsableRules` (2026). An admissible problem is
a dependency-pair problem, `P` a subrelation of `dpPairs R`, whose rules satisfy the variable
condition `vars rhs <= vars lhs`. -/
def usableRulesMinimalityLaws (M : usableRulesMinimalityData) : Prop :=
  (∀ {c d : FCall}, M.P c d → dpPairs M.R c d) ∧
    (∀ r ∈ M.R, Term.vars r.rhs ⊆ Term.vars r.lhs)

/-- The method's own acceptance: the generated set is closed, is the least closed set containing
the seed rules, and the chain problem read over the generated rules is finite. Adapter: the free
two-rule system `freeRecursorTRS` with its extracted pair relation `dpPairs freeRecursorTRS`; the
generated rules of the extracted pair are those reachable through `recur`, and they retain the
duplicating rule. -/
def usableRulesMinimalityAccepts (M : usableRulesMinimalityData) : Prop :=
  usableRulesClosed M ∧ usableRulesLeast M ∧ WellFounded (fun d c => UsableChainP M.R M.P c d)

/-- The chain-class finiteness statement the soundness theorem yields: the original chain relation
is finite on the calls all of whose defined subterm roots are usable. -/
def UsableFragmentTerminates (M : usableRulesMinimalityData) : Prop :=
  WellFounded (fun d c : FCall => ChainP M.R M.P c d ∧ CallUsableRooted M.R M.P c)

/-- Verdict: fragment escape. The method accepts the free two-rule system and the yield is
finiteness of the original chain relation on the usable-rooted chain class; the omitted transport
for calls that are not usable-rooted is named in `usableRulesMinimality_scope`. -/
def usableRulesMinimalityResult (M : usableRulesMinimalityData) : Prop :=
  usableRulesMinimalityAccepts M ∧ UsableFragmentTerminates M

/-- The chain hypothesis: finiteness of the problem over the generated usable rules implies
finiteness of the original problem on the usable-rooted chain class. -/
theorem usableRulesMinimality_sound :
    ∀ M, usableRulesMinimalityLaws M → usableRulesMinimalityAccepts M →
      usableRulesMinimalityResult M := by
  intro M hL hA
  exact ⟨hA, Subrelation.wf (fun {d c} hcd => usableChainP_of_chainP hL.2 hcd.2 hcd.1) hA.2.2⟩

/-- The witness problem: the free two-rule system and its extracted pairs. -/
def usableRulesMinimalityWitness : usableRulesMinimalityData where
  R := freeRecursorTRS
  P := dpPairs freeRecursorTRS

theorem usableRulesMinimalityWitness_laws : usableRulesMinimalityLaws usableRulesMinimalityWitness :=
  ⟨fun h => h, freeRecursorTRS_vars⟩

theorem usableRulesMinimalityWitness_accepts :
    usableRulesMinimalityAccepts usableRulesMinimalityWitness := by
  refine ⟨usableRules_closed _ _, usableRules_least _ _, ?_⟩
  exact Subrelation.wf (fun {_ _} h => usableChainP_to_chainP h) free_finiteDP

theorem usableRulesMinimalityWitness_result : usableRulesMinimalityResult usableRulesMinimalityWitness :=
  usableRulesMinimality_sound _ usableRulesMinimalityWitness_laws
    usableRulesMinimalityWitness_accepts

/-- The seed symbol of the free recursor pair problem is the recursor itself. -/
theorem free_seed_recur : pairTargetRoot freeRecursorTRS (dpPairs freeRecursorTRS) FreeSym.recur :=
  ⟨dpSource, dpTarget, free_dpPair, (freeRecursorTRS_defined_iff _).2 rfl,
    ⟨[.var 0, .var 1, .var 2], IsSubterm.refl _⟩⟩

/-- The only usable symbol of the free recursor pair problem is the recursor. -/
theorem free_usableSym_iff (g : FreeSym) :
    UsableSym freeRecursorTRS (dpPairs freeRecursorTRS) g ↔ g = FreeSym.recur := by
  constructor
  · intro h
    induction h with
    | seed hseed =>
      obtain ⟨c, d, hpd, hdef, hocc⟩ := hseed
      exact (freeRecursorTRS_defined_iff _).1 hdef
    | step hr hrf hf hg hdef => exact (freeRecursorTRS_defined_iff _).1 hdef
  · rintro rfl
    exact UsableSym.seed free_seed_recur

/-- The recursive base rule is generated by the closure step of the recursive call. -/
theorem free_zeroRule_usable :
    IsUsableRule freeRecursorTRS (dpPairs freeRecursorTRS) zeroRule :=
  ⟨by simp [freeRecursorTRS], FreeSym.recur, ruleRoot_of_lhs_app ⟨_, rfl⟩,
    UsableSym.seed free_seed_recur⟩

/-- The duplicating rule is retained in the generated set. -/
theorem free_succRule_usable :
    IsUsableRule freeRecursorTRS (dpPairs freeRecursorTRS) succRule :=
  ⟨by simp [freeRecursorTRS], FreeSym.recur, ruleRoot_of_lhs_app ⟨_, rfl⟩,
    UsableSym.seed free_seed_recur⟩

/-- The recursive call of the successor rule has the usable root. -/
theorem recur_occursRoot_succRule_rhs : occursRoot FreeSym.recur succRule.rhs :=
  ⟨[.var 0, .var 1, .var 2], succRule_rhs_recur⟩

/-- **Feature.** The generator recurses over the dependency graph of the free recursor: the
recursive rule's right-hand side calls `recur`, so the closure step generates the recursive base
rule `zeroRule`; the generated symbol set is the fixed point `{recur}`; and the generated rule set
is closed and is the least closed set containing the seed rules. This is the feature of the
`usableRulesMinimalityWitness` data. -/
theorem usableRulesMinimalityWitness_feature :
    (∀ g : FreeSym, UsableSym freeRecursorTRS (dpPairs freeRecursorTRS) g ↔ g = FreeSym.recur) ∧
    IsUsableRule freeRecursorTRS (dpPairs freeRecursorTRS) zeroRule ∧
    IsUsableRule freeRecursorTRS (dpPairs freeRecursorTRS) succRule ∧
    occursRoot FreeSym.recur succRule.rhs ∧
    usableRulesClosed usableRulesMinimalityWitness ∧
    usableRulesLeast usableRulesMinimalityWitness :=
  ⟨free_usableSym_iff, free_zeroRule_usable, free_succRule_usable, recur_occursRoot_succRule_rhs,
    usableRules_closed _ _, usableRules_least _ _⟩

/-! ### Control system for the dropped-minimality control -/

/-- Control rule 1: the recursor rule that seeds the usable set. -/
def loopRecRule : FRule where
  lhs := .app .recur [.var 0, .var 1, .var 2]
  rhs := .app .recur [.var 0, .var 1, .var 2]
  lhs_isApp := rfl

/-- Control rule 2: a recursor rule whose right-hand side calls the wrapper. -/
def wrapCallRule : FRule where
  lhs := .app .recur [.var 0, .var 1, .var 2]
  rhs := .app .wrap [.var 0, .var 1]
  lhs_isApp := rfl

/-- Control rule 3: the wrapper rule, reachable only through rule 2's right-hand side. -/
def wrapReturnRule : FRule where
  lhs := .app .wrap [.var 0, .var 1]
  rhs := .var 0
  lhs_isApp := rfl

/-- The two-level control system. -/
def usableControlR : FTRS := [loopRecRule, wrapCallRule, wrapReturnRule]

/-- Control pair source. -/
def usableControlSource : FCall := (.recur, [.var 0, .var 1, .var 2])

/-- Control pair target. -/
def usableControlTarget : FCall := (.recur, [.var 0, .var 1, .var 2])

/-- The control pair relation: the single self-pair of the recursor rule. -/
def usableControlP : FProblem := fun c d => c = usableControlSource ∧ d = usableControlTarget

theorem ruleRoot_wrapReturnRule : ruleRoot wrapReturnRule = some FreeSym.wrap :=
  ruleRoot_of_lhs_app ⟨_, rfl⟩

/-- The control seed symbol. -/
theorem control_seed : pairTargetRoot usableControlR usableControlP FreeSym.recur :=
  ⟨usableControlSource, usableControlTarget, ⟨rfl, rfl⟩,
    ⟨loopRecRule, by simp [usableControlR], [.var 0, .var 1, .var 2], rfl⟩,
    ⟨[.var 0, .var 1, .var 2], IsSubterm.refl _⟩⟩

/-- The recursor is usable in the control system. -/
theorem control_recur_usable : UsableSym usableControlR usableControlP FreeSym.recur :=
  UsableSym.seed control_seed

/-- The wrapper becomes usable through rule 2's right-hand side. -/
theorem control_wrap_usable : UsableSym usableControlR usableControlP FreeSym.wrap :=
  UsableSym.step (r := wrapCallRule) (f := FreeSym.recur) (g := FreeSym.wrap)
    (by simp [usableControlR]) rfl control_recur_usable ⟨[.var 0, .var 1], IsSubterm.refl _⟩
    ⟨wrapReturnRule, by simp [usableControlR], [.var 0, .var 1], rfl⟩

/-- The wrapper rule is generated although its root is not a pair-target root. -/
theorem control_wrapReturn_usable :
    IsUsableRule usableControlR usableControlP wrapReturnRule :=
  ⟨by simp [usableControlR], FreeSym.wrap, ruleRoot_wrapReturnRule, control_wrap_usable⟩

/-- The wrapper does not occur in the control pair target. -/
theorem not_occursRoot_wrap_recur_vars :
    ¬ occursRoot FreeSym.wrap (.app FreeSym.recur [.var 0, .var 1, .var 2] : FTerm) := by
  rintro ⟨args, h⟩
  rcases isSubterm_app_decompose h rfl with heq | ⟨a, ha, hsub⟩
  · have h1 : FreeSym.wrap = FreeSym.recur := by
      have hh := heq
      simp only [Term.app.injEq] at hh
      exact hh.1
    exact absurd h1 (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl <;> exact not_isSubterm_app_var hsub

/-- **Control 1.** Deleting the recursive base rule from the generated set breaks closure: the
recursive rule's right-hand side still calls `recur`, and the base rule of `recur` is missing. -/
theorem usableRulesMinimality_missingBase_breaks_closure :
    ¬ usableRulesClosedSet usableRulesMinimalityWitness
      (fun r => IsUsableRule usableRulesMinimalityWitness.R usableRulesMinimalityWitness.P r
        ∧ r ≠ zeroRule) := by
  intro hclosed
  have hsucc : IsUsableRule usableRulesMinimalityWitness.R usableRulesMinimalityWitness.P succRule :=
    free_succRule_usable
  have hne : succRule ≠ zeroRule := by
    intro heq
    have h2 : (succRule.rhs : FTerm) = zeroRule.rhs := congrArg (fun r : FRule => r.rhs) heq
    simp only [succRule, zeroRule] at h2
    cases h2
  have hmem : (fun r => IsUsableRule usableRulesMinimalityWitness.R usableRulesMinimalityWitness.P r
      ∧ r ≠ zeroRule) succRule := ⟨hsucc, hne⟩
  have hz := hclosed succRule hmem FreeSym.recur recur_occursRoot_succRule_rhs
    ((freeRecursorTRS_defined_iff FreeSym.recur).2 rfl)
    zeroRule (by simp [usableRulesMinimalityWitness, freeRecursorTRS])
    (ruleRoot_of_lhs_app (r := zeroRule) ⟨_, rfl⟩)
  exact hz.2 rfl

/-- **Control 2.** Dropping the minimality (closure) condition from the leastness theorem breaks
the theorem: on the two-level control system the seed-rooted rules form a set that contains every
seed rule and omits the generated wrapper rule. -/
theorem usableRulesMinimality_droppedLeastness_breaks_theorem :
    ¬ (∀ T : FRule → Prop, SeedRules usableControlR usableControlP T →
        ∀ r : FRule, IsUsableRule usableControlR usableControlP r → T r) := by
  intro hleast
  have hrt := hleast
    (fun r => r ∈ usableControlR ∧ ∃ f : FreeSym, ruleRoot r = some f ∧
      pairTargetRoot usableControlR usableControlP f)
    (fun r hr hseed => ⟨hr, hseed⟩)
    wrapReturnRule control_wrapReturn_usable
  obtain ⟨-, f, hroot, c, d, hpd, -, hocc⟩ := hrt
  have hf : FreeSym.wrap = f := by
    have hh := hroot
    rw [ruleRoot_wrapReturnRule] at hh
    exact Option.some.inj hh
  subst hf
  obtain ⟨-, hd⟩ := hpd
  subst hd
  exact not_occursRoot_wrap_recur_vars (by simpa [usableControlTarget] using hocc)

/-- **Mutation.** Removing the recursive base rule from the generated set breaks closure, and
dropping the minimality (closure) condition from the leastness theorem breaks the theorem on the
two-level control system. -/
theorem usableRulesMinimality_mutation :
    (¬ usableRulesClosedSet usableRulesMinimalityWitness
      (fun r => IsUsableRule usableRulesMinimalityWitness.R usableRulesMinimalityWitness.P r
        ∧ r ≠ zeroRule)) ∧
    (¬ (∀ T : FRule → Prop, SeedRules usableControlR usableControlP T →
        ∀ r : FRule, IsUsableRule usableControlR usableControlP r → T r)) :=
  ⟨usableRulesMinimality_missingBase_breaks_closure,
    usableRulesMinimality_droppedLeastness_breaks_theorem⟩

/-- The scope wall of the fragment: the transport from finiteness of the generated usable-rules
problem to finiteness of the original dependency-pair problem for calls that are not usable-rooted
(the general minimal-chain usable-rules soundness theorem) is not claimed. -/
def usableRulesMinimality_scope : Prop :=
  ∀ M : usableRulesMinimalityData,
    WellFounded (fun d c : FCall => UsableChainP M.R M.P c d) → FiniteDP M.R M.P

/-! ## Row `formativeRules` -/

/-- Native data of `formativeRules`: the selector of the formative rule catalog and the selector of
the formative pair catalog, read against the fixed actual source `Step` of the KO7 kernel. -/
structure formativeRulesData where
  /-- Selector of the formative rules of the actual source. -/
  selectsRule : KO7RootRuleTag → Bool
  /-- Selector of the formative pairs of the actual pair problem. -/
  selectsPair : FormativePairTag → Bool

/-- The generated formative rule catalog: the selected instances of the actual source schemas. -/
def FormativeRuleCatalog (M : formativeRulesData) (a b : Trace) : Prop :=
  ∃ tag : KO7RootRuleTag, M.selectsRule tag = true ∧ KO7RuleInstance tag a b

/-- The generated formative pair catalog: the selected tagged pairs. -/
def FormativePairCatalog (M : formativeRulesData) (a b : Trace) : Prop :=
  ∃ tag : FormativePairTag, M.selectsPair tag = true ∧ FormativePair tag a b

/-- Reduction sufficiency: every actual dependency pair is generated by a selected source rule
instance. -/
def formativeRulesSufficient (M : formativeRulesData) : Prop :=
  ∀ {a b : Trace}, DPPair a b →
    ∃ (tag : KO7RootRuleTag) (u : Trace), M.selectsRule tag = true ∧ KO7RuleInstance tag a u

/-- Closure of the generation: whenever the formative rule is selected, every pair it forms is in
the selected pair catalog. -/
def formativeRulesClosed (M : formativeRulesData) : Prop :=
  M.selectsRule .recSucc = true →
    ∀ b s n : Trace, ∃ tag : FormativePairTag, M.selectsPair tag = true ∧
      FormativePair tag (recΔ b s (delta n)) (recΔ b s n)

/-- Laws of `formativeRules`, pinned to C. Fuhs and C. Kop, *First-Order Formative Rules*,
RTA-TLCA 2014, LNCS 8560:240-256, Springer, 2014, Section 3 (the first-order definition of
formative rules, dual to the usable rules), and to the package primary definition
`DependencyPairTypedRows.FormativePair` (2026), whose single tag `.recSucc` is formed by the KO7
rule schema `KO7RuleInstance.recSucc` of the eight-schema source. Admissibility: the selector
retains `.recSucc` in both catalogs. -/
def formativeRulesLaws (M : formativeRulesData) : Prop :=
  M.selectsRule .recSucc = true ∧ M.selectsPair .recSucc = true

/-- The method's own acceptance: the generation is closed and sufficient and the generated pair
catalog is exact for the actual pair relation, `FormativePairCatalog M a b <-> DPPair a b`.
Adapter: the KO7 kernel `Step` relation, whose eight schemas are listed by `KO7RuleInstance` and
whose only pair-forming schema is `.recSucc`. -/
def formativeRulesAccepts (M : formativeRulesData) : Prop :=
  formativeRulesClosed M ∧ formativeRulesSufficient M ∧
    (∀ a b : Trace, FormativePairCatalog M a b ↔ DPPair a b)

/-- Verdict: escape. The generated catalog is exact, its reverse is well founded, and the original
pair problem is finite. -/
def formativeRulesResult (M : formativeRulesData) : Prop :=
  formativeRulesAccepts M ∧
    WellFounded (fun y x : Trace => FormativePairCatalog M x y) ∧
    WellFounded (fun y x : Trace => DPPair x y)

/-- A lawful selector covers every actual pair by a selected rule instance. -/
theorem formativeRules_sufficient_of_laws (M : formativeRulesData)
    (hL : formativeRulesLaws M) : formativeRulesSufficient M := by
  intro a b h
  cases h with
  | rec_succ base payload counter =>
    exact ⟨.recSucc, .app payload (recΔ base payload counter), hL.1,
      KO7RuleInstance.recSucc base payload counter⟩

/-- A lawful selector forms every pair of the retained rule. -/
theorem formativeRules_closed_of_laws (M : formativeRulesData)
    (hL : formativeRulesLaws M) : formativeRulesClosed M := by
  intro _
  intro b s n
  exact ⟨.recSucc, hL.2, FormativePair.recSucc b s n⟩

/-- The soundness theorem of the formative catalog: a lawful selector that accepts the free
duplicating rule yields an exact and well-founded catalog and finiteness of the original pair
problem. -/
theorem formativeRules_sound :
    ∀ M, formativeRulesLaws M → formativeRulesAccepts M → formativeRulesResult M := by
  intro M _ hA
  refine ⟨hA, ?_, ?_⟩
  · exact Subrelation.wf (fun {a b} h => (hA.2.2 b a).mp h) wf_DPPairRev
  · simpa using wf_DPPairRev

/-- The witness selector: retain the formative rule and the formative pair tag. -/
def formativeRulesWitness : formativeRulesData where
  selectsRule := fun tag => tag == .recSucc
  selectsPair := fun _ => true

theorem formativeRulesWitness_laws : formativeRulesLaws formativeRulesWitness := by
  refine ⟨?_, rfl⟩
  decide

theorem formativeRulesWitness_accepts : formativeRulesAccepts formativeRulesWitness := by
  refine ⟨?_, ?_, ?_⟩
  · intro _
    intro b s n
    exact ⟨.recSucc, rfl, FormativePair.recSucc b s n⟩
  · intro a b h
    cases h with
    | rec_succ base payload counter =>
      exact ⟨.recSucc, .app payload (recΔ base payload counter), rfl,
        KO7RuleInstance.recSucc base payload counter⟩
  · intro a b
    constructor
    · rintro ⟨tag, -, hfp⟩
      cases hfp with
      | recSucc base payload counter => exact DPPair.rec_succ base payload counter
    · intro h
      cases h with
      | rec_succ base payload counter =>
        exact ⟨.recSucc, rfl, FormativePair.recSucc base payload counter⟩

theorem formativeRulesWitness_result : formativeRulesResult formativeRulesWitness :=
  formativeRules_sound _ formativeRulesWitness_laws formativeRulesWitness_accepts

/-- **Feature.** The catalog is generated from the actual eight-schema source: every kernel step is
a schema instance, the `.recSucc` instance forms exactly the pair the catalog carries, and the
generated catalog is sufficient and closed. -/
theorem formativeRulesWitness_feature :
    (∀ {a b : Trace}, OperatorKO7.Step a b ↔ ∃ tag : KO7RootRuleTag, KO7RuleInstance tag a b) ∧
    (∀ b s n : Trace,
      FormativeRuleCatalog formativeRulesWitness (.recΔ b s (delta n)) (.app s (.recΔ b s n)) ∧
      FormativePairCatalog formativeRulesWitness (.recΔ b s (delta n)) (.recΔ b s n)) ∧
    (∀ {a b : Trace}, DPPair a b → FormativePairCatalog formativeRulesWitness a b) ∧
    formativeRulesSufficient formativeRulesWitness ∧
    formativeRulesClosed formativeRulesWitness := by
  refine ⟨step_iff_KO7RuleInstance, ?_, ?_, ?_, ?_⟩
  · intro b s n
    exact ⟨⟨.recSucc, rfl, KO7RuleInstance.recSucc b s n⟩,
      ⟨.recSucc, rfl, FormativePair.recSucc b s n⟩⟩
  · intro a b h
    exact (formativeRulesWitness_accepts.2.2 a b).mpr h
  · exact formativeRules_sufficient_of_laws formativeRulesWitness formativeRulesWitness_laws
  · exact formativeRules_closed_of_laws formativeRulesWitness formativeRulesWitness_laws

/-- The false selector: omit every rule and every pair. -/
def blindFormativeSelector : formativeRulesData where
  selectsRule := fun _ => false
  selectsPair := fun _ => false

/-- **Mutation.** The false selector omits the necessary rule: it violates the laws, loses
exactness against the actual pair relation, and leaves the actual duplicating pair ungenerated. -/
theorem formativeRules_mutation :
    (¬ formativeRulesLaws blindFormativeSelector) ∧
    (¬ formativeRulesAccepts blindFormativeSelector) ∧
    (∃ a b : Trace, DPPair a b ∧ ¬ FormativePairCatalog blindFormativeSelector a b) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    exact Bool.false_ne_true h.1
  · intro h
    have hp : FormativePairCatalog blindFormativeSelector (recΔ void void (delta void))
        (recΔ void void void) :=
      (h.2.2 (recΔ void void (delta void)) (recΔ void void void)).mpr
        (DPPair.rec_succ void void void)
    obtain ⟨tag, hsel, -⟩ := hp
    exact Bool.false_ne_true hsel
  · refine ⟨recΔ void void (delta void), recΔ void void void, DPPair.rec_succ void void void, ?_⟩
    rintro ⟨tag, hsel, -⟩
    exact Bool.false_ne_true hsel

end OperatorKO7.Methods.OrientationClosure.MethodRowsUsableFormative
