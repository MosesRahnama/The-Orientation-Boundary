import OperatorKO7.Meta.UniqueNormalization.SemiEquationalConfluence
import OperatorKO7.Meta.UniqueNormalization.CommonGeneralisation

/-!
# The right-hand-side variable condition at the hub reconstruction step

Campaign: `COMMAND-CENTER/design/RESEARCH-ROADMAP.md`, package DC-3 of the Distinction
certificate closeout. Source assessment: `Distinction_Boundary/notes/closeout-assessment.md`,
Agent 3 correction.

Two results.

1. **Bare fresh right-hand-side variables.** Over an arbitrary signature and variable type, a
rule `l → y` whose right-hand side is a variable `y` absent from `l` contracts every instance of
`l` to every term (`fresh_rhs_root_universal`), so every pair of terms is convertible
(`fresh_rhs_conversion_universal`). `FreshRhs` in `CommonGeneralisation.lean` is the one-rule
instance already recorded there.

2. **The unrestricted reconstruction statement is false.** An assessment proposed deleting the
right-hand-side variable condition from the reconstruction step H3.3: every feasible overlap of
the hub linearization would yield an omega-unifier of the original patterns, or else a forbidden
omega-overlap of the original system. The system

  `d → z`,  `F(x, x) → a`,  `F(a, b) → b`

(symbol codes `F = 1`, `a = 2`, `b = 3`, `d = 4`; `z` is the variable `1`, absent from `d`) is
non-omega-overlapping (`reconstruction_nonOmegaOverlapping`) and violates only the variable
condition (`reconstruction_not_rhsDetermined`). Its conversion relates `a` and `b` through `d`,
so the hub rule `F(x, 2) → a` with condition `x ~ 2` overlaps `F(a, b) → b` feasibly at the root
(`reconstruction_hub_feasible`), while the original patterns are not omega-unifiable
(`reconstruction_patterns_not_omegaUnifiable`) and no forbidden source overlap exists
(`reconstruction_forbidden_overlap_absent`). Both alternatives fail
(`unrestricted_reconstruction_false`). The fixture lies outside Klop's class; the restricted
statement `RestrictedReconstructOrForbid` is stated here and remains unproved.

Proves: the two generic fresh-variable theorems and the refutation of the unrestricted statement.
Does not prove: the restricted reconstruction statement, or `NoFeasibleOverlap` for any system in
Klop's class.
Relation: `rootStep`, `Step` and `conv` of the source system; `CStep` of `linHub` with its own
conversion `cconv` as the condition oracle, related to `conv` by `cconv_iff_conv`.
Closure: root step, and conversion.
Strategy: full rewriting.
Trust: kernel checked; no `sorry`, `admit`, `axiom`, `native_decide`, `partial`, `unsafe` or
`opaque`. `Classical.choice` enters through the substitution update at an arbitrary variable
type. Axiom footprints are printed by the paired reach file.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniqueNormalization.FreshVariableBoundary

open OperatorKO7.Meta.Rewriting
open OperatorKO7.Meta.UniqueNormalization

universe u v

/-! ## Bare fresh right-hand-side variables -/

section Generic

variable {sigma : Type u} {nu : Type v}

/-- Two substitutions agreeing on every variable occurring in `t` agree on `t`. -/
theorem apply_eq_of_varOccurs_agree {a b : Subst sigma nu} :
    ∀ t : Term sigma nu, (∀ x, VarOccurs x t → a x = b x) →
      Subst.apply a t = Subst.apply b t := by
  intro t
  induction t using Term.rec' with
  | hvar x => intro h; exact h x VarOccurs.here
  | happ f args ih =>
      intro h
      simp only [Subst.apply_app, Subst.applyList_eq_map]
      congr 1
      exact List.map_congr_left (fun c hc => ih c hc (fun x hx => h x (VarOccurs.arg hc hx)))

open Classical in
/-- The substitution `s` updated at the single variable `y` to the term `t`. -/
noncomputable def updateAt (s : Subst sigma nu) (y : nu) (t : Term sigma nu) : Subst sigma nu :=
  fun x => if x = y then t else s x

/-- The update sends `y` to `t`. -/
theorem updateAt_same (s : Subst sigma nu) (y : nu) (t : Term sigma nu) :
    updateAt s y t y = t := by
  unfold updateAt
  rw [if_pos rfl]

/-- The update fixes every other variable. -/
theorem updateAt_ne (s : Subst sigma nu) {x y : nu} (t : Term sigma nu) (h : x ≠ y) :
    updateAt s y t x = s x := by
  unfold updateAt
  rw [if_neg h]

/-- The root-universality specification for bare fresh right-hand-side variables. -/
def FreshRootGoal (sigma : Type u) (nu : Type v) : Prop :=
  ∀ (R : TRS sigma nu) (rule : Rule sigma nu), rule ∈ R →
    ∀ y, rule.rhs = Term.var y → ¬ VarOccurs y rule.lhs →
      ∀ (s : Subst sigma nu) (t : Term sigma nu),
        rootStep R (Subst.apply s rule.lhs) t

/-- **A bare fresh right-hand-side variable contracts every instance to every term.** Update the
matching substitution only at the fresh variable: the instance of the left-hand side is unchanged,
and the updated rule instance has right-hand side `t`.

Relation: `rootStep R`. Property: one step. -/
theorem fresh_rhs_root_universal : FreshRootGoal sigma nu := by
  intro R rule hr y hy hfresh s t
  refine ⟨rule, hr, updateAt s y t, ?_, ?_⟩
  · apply apply_eq_of_varOccurs_agree
    intro x hx
    have hxy : x ≠ y := fun h => hfresh (h ▸ hx)
    exact (updateAt_ne s t hxy).symm
  · rw [hy, Subst.apply_var, updateAt_same]

/-- **Every pair of terms converts.** One instance of the left-hand side contracts to both terms,
and the two root steps are joined backward and forward.

Relation: `conv R`. Closure: conversion. -/
theorem fresh_rhs_conversion_universal {R : TRS sigma nu} {rule : Rule sigma nu} (hr : rule ∈ R)
    {y : nu} (hy : rule.rhs = Term.var y) (hfresh : ¬ VarOccurs y rule.lhs)
    (t₁ t₂ : Term sigma nu) : conv R t₁ t₂ := by
  have h₁ := fresh_rhs_root_universal R rule hr y hy hfresh (fun _ => t₁) t₁
  have h₂ := fresh_rhs_root_universal R rule hr y hy hfresh (fun _ => t₁) t₂
  exact conv.trans (conv.symm (conv.of_step (Step.root h₁))) (conv.of_step (Step.root h₂))

end Generic

/-- A variable occurs in a variable exactly when the two are equal. -/
theorem varOccurs_var_iff {sigma : Type u} {nu : Type v} {x y : nu} :
    VarOccurs x (Term.var y : Term sigma nu) ↔ x = y := by
  constructor
  · rintro ⟨⟩
    rfl
  · rintro rfl
    exact VarOccurs.here

/-- **The generic theorem at `FreshRhs`**: every pair of terms converts in `F(x) → y`. -/
theorem freshRhs_conversion_universal (t₁ t₂ : Term Nat Nat) : conv FreshRhs.trs t₁ t₂ :=
  fresh_rhs_conversion_universal (List.Mem.head _) (y := 1) rfl
    (by
      intro h
      rcases h.app_inv with ⟨a, ha, hx⟩
      simp only [List.mem_singleton] at ha
      subst ha
      exact absurd (varOccurs_var_iff.1 hx) (by decide)) t₁ t₂

/-! ## Forbidden source overlaps and the two reconstruction statements -/

/-- A forbidden omega-overlap of a source system: a non-variable subterm of one left-hand side
omega-unifies with a left-hand side, outside the identical-rule root exception. -/
def ForbiddenSourceOverlap {sigma : Type u} {nu : Type v} (R : TRS sigma nu) : Prop :=
  ∃ r₁ ∈ R, ∃ r₂ ∈ R, ∃ q : Term sigma nu, Subterm q r₁.lhs ∧ q.isApp = true ∧
    OmegaUnifiable q r₂.lhs ∧ ¬ (r₁ = r₂ ∧ q = r₁.lhs)

/-- A forbidden source overlap exists exactly when the system is omega-overlapping. -/
theorem forbiddenSourceOverlap_iff_not_nonOmegaOverlapping {sigma : Type u} {nu : Type v}
    (R : TRS sigma nu) : ForbiddenSourceOverlap R ↔ ¬ NonOmegaOverlapping R := by
  constructor
  · rintro ⟨r₁, h₁, r₂, h₂, q, hq, happ, hu, hbad⟩ hno
    exact hbad (hno r₁ h₁ r₂ h₂ q hq happ hu)
  · intro hn
    by_contra hnone
    apply hn
    intro r₁ h₁ r₂ h₂ q hq happ hu
    by_contra hbad
    exact hnone ⟨r₁, h₁, r₂, h₂, q, hq, happ, hu, hbad⟩

/-- **The reconstruction-or-forbid statement with the right-hand-side condition deleted.** For
every non-omega-overlapping system and every overlap of two hub rules at a non-variable subterm
`q` of the first split left-hand side, with both independent substitutions and every condition of
both rules discharged by the conversion of the hub linearization: the collapsed subterm (the
original subterm at that position) omega-unifies with the second original left-hand side, or the
source system has a forbidden omega-overlap. -/
def UnrestrictedReconstructOrForbid : Prop :=
  ∀ R : TRS Nat Nat, NonOmegaOverlapping R →
    ∀ rule₁ ∈ R, ∀ rule₂ ∈ R, ∀ q : Term Nat Nat,
      Subterm q (hubCRule rule₁).lhs → q.isApp = true →
      ∀ σ₁ σ₂ : Subst Nat Nat, Subst.apply σ₁ q = Subst.apply σ₂ (hubCRule rule₂).lhs →
        (∀ p ∈ (hubCRule rule₁).conds,
          cconv (linHub R) (Subst.apply σ₁ p.1) (Subst.apply σ₁ p.2)) →
        (∀ p ∈ (hubCRule rule₂).conds,
          cconv (linHub R) (Subst.apply σ₂ p.1) (Subst.apply σ₂ p.2)) →
        OmegaUnifiable (Term.mapVar (hubCollapse (ruleFreshBase rule₁)) q) rule₂.lhs ∨
          ForbiddenSourceOverlap R

/-- **The restricted statement (H3.3 with the condition restored).** The same conclusion under
the additional variable condition of the source system. This module neither proves nor refutes
it; it is the unproved reconstruction target. -/
def RestrictedReconstructOrForbid : Prop :=
  ∀ R : TRS Nat Nat, NonOmegaOverlapping R →
    (∀ rule ∈ R, ∀ x, VarOccurs x rule.rhs → VarOccurs x rule.lhs) →
    ∀ rule₁ ∈ R, ∀ rule₂ ∈ R, ∀ q : Term Nat Nat,
      Subterm q (hubCRule rule₁).lhs → q.isApp = true →
      ∀ σ₁ σ₂ : Subst Nat Nat, Subst.apply σ₁ q = Subst.apply σ₂ (hubCRule rule₂).lhs →
        (∀ p ∈ (hubCRule rule₁).conds,
          cconv (linHub R) (Subst.apply σ₁ p.1) (Subst.apply σ₁ p.2)) →
        (∀ p ∈ (hubCRule rule₂).conds,
          cconv (linHub R) (Subst.apply σ₂ p.1) (Subst.apply σ₂ p.2)) →
        OmegaUnifiable (Term.mapVar (hubCollapse (ruleFreshBase rule₁)) q) rule₂.lhs ∨
          ForbiddenSourceOverlap R

/-- The unrestricted statement implies the restricted one; the converse is the content of the
refutation below. -/
theorem restricted_of_unrestricted (h : UnrestrictedReconstructOrForbid) :
    RestrictedReconstructOrForbid :=
  fun R hno _ => h R hno

/-! ## The fixture `d → z`, `F(x, x) → a`, `F(a, b) → b` -/

/-- `d → z`: the constant `d = 4` rewrites to the variable `1`. -/
def ruleD : Rule Nat Nat := ⟨.app 4 [], .var 1, rfl⟩

/-- `F(x, x) → a`, with `F = 1` and `a = 2`. -/
def ruleFxx : Rule Nat Nat := ⟨.app 1 [.var 0, .var 0], .app 2 [], rfl⟩

/-- `F(a, b) → b`, with `b = 3`. -/
def ruleFab : Rule Nat Nat := ⟨.app 1 [.app 2 [], .app 3 []], .app 3 [], rfl⟩

/-- The three rules. -/
def reconstruction_rules : TRS Nat Nat := [ruleD, ruleFxx, ruleFab]

/-- The non-variable subterms of the left-hand sides. -/
theorem reconstruction_lhs_subterm_cases {r : Rule Nat Nat} (hr : r ∈ reconstruction_rules)
    {q : Term Nat Nat} (hq : Subterm q r.lhs) (happ : q.isApp = true) :
    q = r.lhs ∨ q = .app 2 [] ∨ q = .app 3 [] := by
  simp only [reconstruction_rules, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact Or.inl (ClassExamples.flat_app_subterm_eq (by simp) hq happ)
  · exact Or.inl (ClassExamples.flat_app_subterm_eq
      (fun a ha => ⟨0, by simpa using ha⟩) hq happ)
  · change Subterm q (.app 1 [.app 2 [], .app 3 []]) at hq
    cases hq with
    | refl => exact Or.inl rfl
    | arg ha hsa =>
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl
        · cases hsa with
          | refl => exact Or.inr (Or.inl rfl)
          | arg hb _ => simp at hb
        · cases hsa with
          | refl => exact Or.inr (Or.inr rfl)
          | arg hb _ => simp at hb

/-- **The two `F` patterns are not omega-unifiable**: the shared variable would relate `a` to `b`. -/
theorem reconstruction_patterns_not_omegaUnifiable :
    ¬ OmegaUnifiable ruleFxx.lhs ruleFab.lhs := by
  rintro ⟨E, hE, hst⟩
  simp only [ruleFxx, ruleFab, leftCopy, rightCopy, Term.mapVar_app, Term.mapVarList_cons,
    Term.mapVarList_nil, Term.mapVar_var] at hst
  obtain ⟨-, hargs⟩ := hE.decomp hst
  simp only [List.forall₂_cons] at hargs
  obtain ⟨h1, h2, -⟩ := hargs
  exact absurd (hE.decomp (hE.trans' (hE.symm' h1) h2)).1 (by decide)

/-- The same pair in the other order. -/
theorem reconstruction_patterns_not_omegaUnifiable_symm :
    ¬ OmegaUnifiable ruleFab.lhs ruleFxx.lhs := by
  rintro ⟨E, hE, hst⟩
  simp only [ruleFxx, ruleFab, leftCopy, rightCopy, Term.mapVar_app, Term.mapVarList_cons,
    Term.mapVarList_nil, Term.mapVar_var] at hst
  obtain ⟨-, hargs⟩ := hE.decomp hst
  simp only [List.forall₂_cons] at hargs
  obtain ⟨h1, h2, -⟩ := hargs
  exact absurd (hE.decomp (hE.trans' h1 (hE.symm' h2))).1 (by decide)

/-- **The fixture is non-omega-overlapping.** Every rule pair and every non-variable subterm is
enumerated; the only same-head root pair is refuted by `a ≠ b`. -/
theorem reconstruction_nonOmegaOverlapping : NonOmegaOverlapping reconstruction_rules := by
  intro r₁ h₁ r₂ h₂ q hq happ hu
  have h₁' := h₁
  have h₂' := h₂
  simp only [reconstruction_rules, List.mem_cons, List.not_mem_nil, or_false] at h₁' h₂'
  rcases reconstruction_lhs_subterm_cases h₁ hq happ with hroot | h | h
  · subst hroot
    rcases h₁' with rfl | rfl | rfl <;> rcases h₂' with rfl | rfl | rfl
    all_goals first
      | exact ⟨rfl, rfl⟩
      | exact absurd (ClassExamples.omega_head_eq hu) (by decide)
      | exact absurd hu reconstruction_patterns_not_omegaUnifiable
      | exact absurd hu reconstruction_patterns_not_omegaUnifiable_symm
  · subst h
    exfalso
    rcases h₂' with rfl | rfl | rfl <;>
      exact absurd (ClassExamples.omega_head_eq hu) (by decide)
  · subst h
    exfalso
    rcases h₂' with rfl | rfl | rfl <;>
      exact absurd (ClassExamples.omega_head_eq hu) (by decide)

/-- **The only failing class condition is the variable condition.** -/
theorem reconstruction_not_rhsDetermined : ¬ TRS.RhsDetermined reconstruction_rules := by
  intro h
  have hd := h ruleD (List.Mem.head _) (fun _ => .app 2 []) (fun _ => .app 3 []) rfl
  simp [ruleD] at hd

/-- The occurrence form of the variable condition also fails, at `d → z`. -/
theorem reconstruction_violates_variable_condition :
    ¬ (∀ rule ∈ reconstruction_rules, ∀ x, VarOccurs x rule.rhs → VarOccurs x rule.lhs) := by
  intro h
  have hocc := h ruleD (List.Mem.head _) 1 VarOccurs.here
  change VarOccurs 1 (Term.app 4 []) at hocc
  rcases hocc.app_inv with ⟨a, ha, -⟩
  simp at ha

/-- `d` rewrites to every term. -/
theorem reconstruction_step_d (t : Term Nat Nat) : Step reconstruction_rules (.app 4 []) t :=
  Step.root ⟨ruleD, List.Mem.head _, fun _ => t, rfl, rfl⟩

/-- `a` and `b` are convertible through `d`. -/
theorem reconstruction_a_conv_b : conv reconstruction_rules (.app 2 []) (.app 3 []) :=
  conv.trans (conv.symm (conv.of_step (reconstruction_step_d _)))
    (conv.of_step (reconstruction_step_d _))

/-- The constants `a` and `b` are normal forms. -/
theorem reconstruction_const_normalForm {c : Nat} (hc : c = 2 ∨ c = 3) :
    NormalForm reconstruction_rules (.app c []) := by
  intro w hstep
  rcases Step.app_inv hstep with hroot | ⟨pre, post, x, y, hargs, -, -⟩
  · obtain ⟨rule, hmem, σ, hs, -⟩ := hroot
    simp only [reconstruction_rules, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl <;> rcases hc with rfl | rfl <;>
      simp [ruleD, ruleFxx, ruleFab] at hs
  · exact absurd hargs.symm (by simp)

/-- **The fixture fails unique normal forms**: `a` and `b` are distinct convertible normal forms. -/
theorem reconstruction_not_UNconv : ¬ UNconv reconstruction_rules := by
  intro h
  have hab := h _ _ (reconstruction_const_normalForm (Or.inl rfl))
    (reconstruction_const_normalForm (Or.inr rfl)) reconstruction_a_conv_b
  simp at hab

/-- The fixture's conversion is universal, by the generic fresh-variable theorem. -/
theorem reconstruction_conversion_universal (t₁ t₂ : Term Nat Nat) :
    conv reconstruction_rules t₁ t₂ :=
  fresh_rhs_conversion_universal (List.Mem.head _) (rule := ruleD) (y := 1) rfl
    (by
      intro h
      rcases h.app_inv with ⟨a, ha, -⟩
      simp at ha) t₁ t₂

/-! ## The hub linearization of the fixture -/

/-- The hub image of `d → z`. -/
def hubD : CRule Nat Nat := ⟨.app 4 [], .var 1, [], rfl⟩

/-- The hub image of `F(x, x) → a`: the second occurrence becomes the fresh variable `2`, with the
condition `x ~ 2`. -/
def hubFxx : CRule Nat Nat := ⟨.app 1 [.var 0, .var 2], .app 2 [], [(.var 0, .var 2)], rfl⟩

/-- The hub image of `F(a, b) → b`. -/
def hubFab : CRule Nat Nat := ⟨.app 1 [.app 2 [], .app 3 []], .app 3 [], [], rfl⟩

/-- The fresh base of `d → z` is `2`, above the right-hand side variable. -/
theorem ruleFreshBase_ruleD : ruleFreshBase ruleD = 2 := by
  simp [ruleFreshBase, ruleD, maxNatList, Term.varOccurrences]

/-- The fresh base of `F(x, x) → a` is `1`. -/
theorem ruleFreshBase_ruleFxx : ruleFreshBase ruleFxx = 1 := by
  simp [ruleFreshBase, ruleFxx, maxNatList, Term.varOccurrences]

/-- The fresh base of `F(a, b) → b` is `1`. -/
theorem ruleFreshBase_ruleFab : ruleFreshBase ruleFab = 1 := by
  simp [ruleFreshBase, ruleFab, maxNatList, Term.varOccurrences]

/-- Two conditional rules with equal left-hand sides, right-hand sides and condition lists are
equal. -/
theorem crule_ext {r s : CRule Nat Nat} (hl : r.lhs = s.lhs) (hr : r.rhs = s.rhs)
    (hc : r.conds = s.conds) : r = s := by
  cases r
  cases s
  cases hl
  cases hr
  cases hc
  rfl

/-- The hub transform of `d → z`. -/
theorem hubCRule_ruleD : hubCRule ruleD = hubD := by
  apply crule_ext
  · rw [hubCRule_lhs, ruleFreshBase_ruleD]
    simp [ruleD, hubD, hubSplitTerm, hubSplitTermAux, hubSplitListAux]
  · rfl
  · rw [hubCRule_conds, ruleFreshBase_ruleD]
    simp [ruleD, hubD, hubSplitConditions, hubSplitTermAux, hubSplitListAux]

/-- The hub transform of `F(x, x) → a`. -/
theorem hubCRule_ruleFxx : hubCRule ruleFxx = hubFxx := by
  apply crule_ext
  · rw [hubCRule_lhs, ruleFreshBase_ruleFxx]
    simp [ruleFxx, hubFxx, hubSplitTerm, hubSplitTermAux, hubSplitListAux, hubFresh, Nat.pair]
  · rfl
  · rw [hubCRule_conds, ruleFreshBase_ruleFxx]
    simp [ruleFxx, hubFxx, hubSplitConditions, hubSplitTermAux, hubSplitListAux, hubFresh,
      Nat.pair]

/-- The hub transform of `F(a, b) → b`. -/
theorem hubCRule_ruleFab : hubCRule ruleFab = hubFab := by
  apply crule_ext
  · rw [hubCRule_lhs, ruleFreshBase_ruleFab]
    simp [ruleFab, hubFab, hubSplitTerm, hubSplitTermAux, hubSplitListAux]
  · rfl
  · rw [hubCRule_conds, ruleFreshBase_ruleFab]
    simp [ruleFab, hubFab, hubSplitConditions, hubSplitTermAux, hubSplitListAux]

/-- **The actual hub linearization of the fixture.** -/
theorem reconstruction_hub_rules_eq :
    linHub reconstruction_rules = [hubD, hubFxx, hubFab] := by
  simp [linHub, reconstruction_rules, hubCRule_ruleD, hubCRule_ruleFxx, hubCRule_ruleFab]

/-- The substitution of the feasible overlap: `x ↦ a`, and `a`'s partner `2 ↦ b`. -/
def overlapSubst : Subst Nat Nat := fun v => if v = 0 then .app 2 [] else .app 3 []

/-- **The feasible overlap data at the actual hub transform.** The split left-hand side `F(x, 2)`
and `F(a, b)` have a common instance, the condition `x ~ 2` instantiates to `a ~ b`, which the
conversion of `linHub` discharges through `cconv_iff_conv`, and the second rule has no condition.
The two hub rules are different. -/
theorem reconstruction_feasible_data :
    Subst.apply overlapSubst (hubCRule ruleFxx).lhs =
        Subst.apply Subst.id (hubCRule ruleFab).lhs ∧
      (∀ p ∈ (hubCRule ruleFxx).conds, cconv (linHub reconstruction_rules)
        (Subst.apply overlapSubst p.1) (Subst.apply overlapSubst p.2)) ∧
      (∀ p ∈ (hubCRule ruleFab).conds, cconv (linHub reconstruction_rules)
        (Subst.apply Subst.id p.1) (Subst.apply Subst.id p.2)) ∧
      hubCRule ruleFxx ≠ hubCRule ruleFab := by
  rw [hubCRule_ruleFxx, hubCRule_ruleFab]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [hubFxx, hubFab, overlapSubst]
  · intro p hp
    simp only [hubFxx, List.mem_singleton] at hp
    subst hp
    have hab := (cconv_iff_conv (isLinearization_linHub reconstruction_rules) _ _).2
      reconstruction_a_conv_b
    simpa [overlapSubst] using hab
  · intro p hp
    simp [hubFab] at hp
  · intro h
    have hr := congrArg CRule.rhs h
    simp [hubFxx, hubFab] at hr

/-- Membership of the hub image of `F(x, x) → a`. -/
theorem hubCRule_ruleFxx_mem : hubCRule ruleFxx ∈ linHub reconstruction_rules :=
  List.mem_map_of_mem (List.Mem.tail _ (List.Mem.head _))

/-- Membership of the hub image of `F(a, b) → b`. -/
theorem hubCRule_ruleFab_mem : hubCRule ruleFab ∈ linHub reconstruction_rules :=
  List.mem_map_of_mem (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

/-- **The hub linearization has a feasible overlap**, so it fails `NoFeasibleOverlap` for its own
conversion. -/
theorem reconstruction_hub_feasible :
    ¬ NoFeasibleOverlap (linHub reconstruction_rules) (cconv (linHub reconstruction_rules)) := by
  intro hno
  obtain ⟨heq, hc₁, hc₂, hne⟩ := reconstruction_feasible_data
  exact hne (hno _ hubCRule_ruleFxx_mem _ hubCRule_ruleFab_mem _ (Subterm.refl _)
    (hubSplitTerm_isApp _ ruleFxx.lhs_isApp) _ _ heq hc₁ hc₂).1

/-- **No forbidden source overlap exists**, by source non-omega-overlap. -/
theorem reconstruction_forbidden_overlap_absent :
    ¬ ForbiddenSourceOverlap reconstruction_rules :=
  fun h => (forbiddenSourceOverlap_iff_not_nonOmegaOverlapping _).1 h
    reconstruction_nonOmegaOverlapping

/-- **The unrestricted reconstruction statement is false.** At the fixture the feasible hub
overlap exists, the collapsed subterm is the original pattern `F(x, x)`, which does not
omega-unify with `F(a, b)`, and no forbidden source overlap exists. -/
theorem unrestricted_reconstruction_false : ¬ UnrestrictedReconstructOrForbid := by
  intro H
  obtain ⟨heq, hc₁, hc₂, -⟩ := reconstruction_feasible_data
  rcases H reconstruction_rules reconstruction_nonOmegaOverlapping ruleFxx
      (List.Mem.tail _ (List.Mem.head _)) ruleFab (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
      _ (Subterm.refl _) (hubSplitTerm_isApp _ ruleFxx.lhs_isApp) _ _ heq hc₁ hc₂ with hω | hbad
  · rw [hubCRule_lhs, hubSplitRuleLhs_collapse] at hω
    exact reconstruction_patterns_not_omegaUnifiable hω
  · exact reconstruction_forbidden_overlap_absent hbad

/-- **The packaged counterexample.** Feasible transformed overlap, both proposed alternatives
false, source non-omega-overlap satisfied, the variable condition violated, and unique normal
forms failing. -/
theorem reconstruction_counterexample_package :
    ¬ NoFeasibleOverlap (linHub reconstruction_rules) (cconv (linHub reconstruction_rules)) ∧
      ¬ OmegaUnifiable ruleFxx.lhs ruleFab.lhs ∧
      ¬ ForbiddenSourceOverlap reconstruction_rules ∧
      NonOmegaOverlapping reconstruction_rules ∧
      ¬ TRS.RhsDetermined reconstruction_rules ∧
      ¬ UNconv reconstruction_rules ∧
      ¬ UnrestrictedReconstructOrForbid :=
  ⟨reconstruction_hub_feasible, reconstruction_patterns_not_omegaUnifiable,
    reconstruction_forbidden_overlap_absent, reconstruction_nonOmegaOverlapping,
    reconstruction_not_rhsDetermined, reconstruction_not_UNconv, unrestricted_reconstruction_false⟩

end OperatorKO7.Meta.UniqueNormalization.FreshVariableBoundary
