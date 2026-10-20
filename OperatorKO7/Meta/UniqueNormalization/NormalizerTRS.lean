import OperatorKO7.Meta.UniqueNormalization.ConservativePolicies
import OperatorKO7.Meta.UniqueNormalization.NormalFormSaturation
import OperatorKO7.Meta.Rewriting.Rewrite

/-!
# Contexts, substitutions and semantic rule admission

The concrete carrier is the existing first-order Term sigma nu syntax.
Rule instances use the existing Step relation, including every substitution
and every finite application context. Variable preservation is an additional
condition because the existing Rule structure permits fresh right-side variables.

-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniqueNormalization.Normalization

open OperatorKO7.Meta.Rewriting

universe u v w

variable {X : Type w} {R : X → X → Prop} {n : X → X}

def OperationClosed (R : X → X → Prop) (c : X → X) : Prop :=
  ∀ ⦃x y⦄, R x y → R (c x) (c y)

/-- Closure of the maximal realization has exactly two requirements: preservation
of the normalizer kernel and reflection of its fixed-point set. -/
theorem maxRel_operation_closed_iff (c : X → X) :
    OperationClosed (MaxRel n) c ↔
      (∀ x y, n x = n y → n (c x) = n (c y)) ∧
      (∀ x, c x = n (c x) → x = n x) := by
  classical
  constructor
  · intro hc
    constructor
    · intro x y hxy
      by_cases hx : x = n x
      · by_cases hy : y = n y
        · have heq : x = y := hx.trans (hxy.trans hy.symm)
          exact congrArg (fun a => n (c a)) heq
        · exact (hc ⟨hy, hxy.symm⟩).2.symm
      · exact (hc ⟨hx, hxy⟩).2
    · intro x hx
      apply Classical.byContradiction
      intro hnx
      exact (hc (show MaxRel n x x from ⟨hnx, rfl⟩)).1 hx
  · rintro ⟨hk, hf⟩ x y hxy
    exact ⟨fun hx => hxy.1 (hf x hx), hk x y hxy.2⟩

/-- A step-preserving operation preserves the maximal realization of a globally
reachable normalizer. Its redex preservation supplies fixed-point reflection. -/
theorem maxRel_operation_closed (h : Realizes R n) (c : X → X)
    (hc : OperationClosed R c) : OperationClosed (MaxRel n) c := by
  apply (maxRel_operation_closed_iff c).mpr
  constructor
  · intro x y hxy
    apply h.conv_iff.mp
    exact conv_map c (fun {_ _} hab => .rel _ _ (hc hab)) (h.conv_iff.mpr hxy)
  · intro x hx
    apply (h.nf_iff x).mp
    intro y hxy
    exact (h.nf_iff (c x)).mpr hx (c y) (hc hxy)

/-- A restricted carrier needs its own closure premise on the operation.
Taking P to be Normalizes R records the qualification for the normalizable core. -/
theorem operation_closed_on_restriction (P : X → Prop) (c : X → X)
    (hp : ∀ x, P x → P (c x)) (hc : OperationClosed R c) :
    OperationClosed (fun x y : {x : X // P x} => R x.1 y.1)
      (fun x => ⟨c x.1, hp x.1 x.2⟩) := by
  intro x y hxy
  exact hc hxy

section Terms

variable {sigma : Type u} {nu : Type v}

/-- The full finite one-hole context grammar for the existing term syntax. -/
inductive TermContext (sigma : Type u) (nu : Type v)
  | hole : TermContext sigma nu
  | arg (f : sigma) (pre post : List (Term sigma nu))
      (inner : TermContext sigma nu) : TermContext sigma nu

def TermContext.plug : TermContext sigma nu → Term sigma nu → Term sigma nu
  | .hole, t => t
  | .arg f pre post C, t => .app f (pre ++ C.plug t :: post)

theorem termContext_step (T : TRS sigma nu) (C : TermContext sigma nu)
    {s t : Term sigma nu} (h : Step T s t) : Step T (C.plug s) (C.plug t) := by
  induction C with
  | hole => exact h
  | arg f pre post C ih => exact Step.arg f pre post ih

/-- Substitution closure is proved for the actual rewrite constructors. -/
theorem rewriting_step_subst (T : TRS sigma nu) (σ : Subst sigma nu)
    {s t : Term sigma nu} (h : Step T s t) :
    Step T (Subst.apply σ s) (Subst.apply σ t) := by
  induction h with
  | root hroot =>
      obtain ⟨rule, hrule, τ, rfl, rfl⟩ := hroot
      exact Step.root ⟨rule, hrule, Subst.comp σ τ,
        (Subst.apply_comp σ τ rule.lhs).symm,
        (Subst.apply_comp σ τ rule.rhs).symm⟩
  | arg f pre post h ih =>
      simpa only [Subst.apply_app, Subst.applyList_eq_map,
        List.map_append, List.map_cons] using
        Step.arg f (pre.map (Subst.apply σ)) (post.map (Subst.apply σ)) ih

theorem maxRel_context {T : TRS sigma nu} {n : Term sigma nu → Term sigma nu}
    (h : Realizes (Step T) n) (C : TermContext sigma nu) :
    OperationClosed (MaxRel n) C.plug :=
  maxRel_operation_closed h C.plug (fun {_ _} hp => termContext_step T C hp)

theorem maxRel_substitution {T : TRS sigma nu} {n : Term sigma nu → Term sigma nu}
    (h : Realizes (Step T) n) (σ : Subst sigma nu) :
    OperationClosed (MaxRel n) (Subst.apply σ) :=
  maxRel_operation_closed h (Subst.apply σ)
    (fun {_ _} hp => rewriting_step_subst T σ hp)

/-- Normalization commutes with substitution after normalization on the outside.
The substituted normal form need not itself be normal. -/
theorem normalized_substitution {T : TRS sigma nu} {n : Term sigma nu → Term sigma nu}
    (h : Realizes (Step T) n) (σ : Subst sigma nu) (t : Term sigma nu) :
    n (Subst.apply σ (n t)) = n (Subst.apply σ t) := by
  have hp : Star (Step T) (Subst.apply σ t) (Subst.apply σ (n t)) :=
    star_map (Subst.apply σ) (fun {_ _} hs => rewriting_step_subst T σ hs) (h.reaches t)
  exact (star_invariant n (fun {_ _} hs => h.step_invariant hs) hp).symm

section VariableConditions

variable [DecidableEq nu]

/-- The ordinary syntactic variable condition on an individual step. -/
def NoFreshVars (s t : Term sigma nu) : Prop := Term.vars t ⊆ Term.vars s

def RuleNoFreshVars (r : Rule sigma nu) : Prop := NoFreshVars r.lhs r.rhs

theorem noFreshVars_substitution (σ : Subst sigma nu) {s t : Term sigma nu}
    (h : NoFreshVars s t) : NoFreshVars (Subst.apply σ s) (Subst.apply σ t) := by
  intro z hz
  obtain ⟨y, hy, hzy⟩ := (Subst.mem_vars_apply_iff σ t z).mp hz
  exact (Subst.mem_vars_apply_iff σ s z).mpr ⟨y, h hy, hzy⟩

theorem noFreshVars_arg (f : sigma) (pre post : List (Term sigma nu))
    {s t : Term sigma nu} (h : NoFreshVars s t) :
    NoFreshVars (.app f (pre ++ s :: post)) (.app f (pre ++ t :: post)) := by
  intro z hz
  change z ∈ Term.varsList (pre ++ t :: post) at hz
  change z ∈ Term.varsList (pre ++ s :: post)
  obtain ⟨a, ha, hza⟩ := Term.mem_varsList_iff.mp hz
  apply Term.mem_varsList_iff.mpr
  rcases List.mem_append.mp ha with hpre | hrest
  · exact ⟨a, List.mem_append.mpr (Or.inl hpre), hza⟩
  · rcases List.mem_cons.mp hrest with heq | hpost
    · subst a
      exact ⟨s, List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))), h hza⟩
    · exact ⟨a, List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr hpost))), hza⟩

theorem noFreshVars_context (C : TermContext sigma nu) {s t : Term sigma nu}
    (h : NoFreshVars s t) : NoFreshVars (C.plug s) (C.plug t) := by
  induction C with
  | hole => exact h
  | arg f pre post C ih => exact noFreshVars_arg f pre post ih

/-- The full rewrite relation preserves variables when every actual rule does. -/
theorem noFreshVars_step (T : TRS sigma nu)
    (hT : ∀ r, r ∈ T → RuleNoFreshVars r) : Subrel (Step T) NoFreshVars := by
  intro s t h
  induction h with
  | root hr =>
      obtain ⟨rule, hmem, σ, rfl, rfl⟩ := hr
      exact noFreshVars_substitution σ (hT rule hmem)
  | arg f pre post h ih => exact noFreshVars_arg f pre post ih

def VarMaxRel (n : Term sigma nu → Term sigma nu) (s t : Term sigma nu) : Prop :=
  MaxRel n s t ∧ NoFreshVars s t

theorem step_subrel_varMaxRel {T : TRS sigma nu} {n : Term sigma nu → Term sigma nu}
    (h : Realizes (Step T) n) (hT : ∀ r, r ∈ T → RuleNoFreshVars r) :
    Subrel (Step T) (VarMaxRel n) :=
  fun {_ _} hp => ⟨h.subrel_maxRel hp, noFreshVars_step T hT hp⟩

/-- An ordinary realizing TRS witnesses reachability inside the maximal
variable-preserving semantic relation. No finite rule presentation is asserted. -/
theorem varMaxRel_realizes {T : TRS sigma nu} {n : Term sigma nu → Term sigma nu}
    (h : Realizes (Step T) n) (hT : ∀ r, r ∈ T → RuleNoFreshVars r) :
    Realizes (VarMaxRel n) n := by
  apply realizes_of_subrel_maxRel (fun {_ _} hp => hp.1)
  intro t
  exact star_mono (step_subrel_varMaxRel h hT) (h.reaches t)

theorem varMaxRel_greatest {S : Term sigma nu → Term sigma nu → Prop}
    {n : Term sigma nu → Term sigma nu} (h : Realizes S n)
    (hv : Subrel S NoFreshVars) : Subrel S (VarMaxRel n) :=
  fun {_ _} hp => ⟨h.subrel_maxRel hp, hv hp⟩

theorem varMaxRel_context {T : TRS sigma nu} {n : Term sigma nu → Term sigma nu}
    (h : Realizes (Step T) n) (C : TermContext sigma nu) :
    OperationClosed (VarMaxRel n) C.plug :=
  fun {_ _} hp => ⟨maxRel_context h C hp.1, noFreshVars_context C hp.2⟩

theorem varMaxRel_substitution {T : TRS sigma nu} {n : Term sigma nu → Term sigma nu}
    (h : Realizes (Step T) n) (σ : Subst sigma nu) :
    OperationClosed (VarMaxRel n) (Subst.apply σ) :=
  fun {_ _} hp => ⟨maxRel_substitution h σ hp.1, noFreshVars_substitution σ hp.2⟩

end VariableConditions

/-- Each candidate means its entire singleton-TRS relation, not a finite sample. -/
def RuleInstance (r : Rule sigma nu) : Term sigma nu → Term sigma nu → Prop := Step [r]

theorem rewriting_step_mono {T U : TRS sigma nu}
    (hTU : ∀ r, r ∈ T → r ∈ U) : Subrel (Step T) (Step U) := by
  intro s t hp
  induction hp with
  | root hr =>
      obtain ⟨r, hm, σ, hs, ht⟩ := hr
      exact Step.root ⟨r, hTU r hm, σ, hs, ht⟩
  | arg f pre post h ih => exact Step.arg f pre post ih

theorem rewriting_rule_self (T : TRS sigma nu) {r : Rule sigma nu} (hr : r ∈ T) :
    Step T r.lhs r.rhs :=
  Step.root ⟨r, hr, Subst.id, (Subst.id_apply r.lhs).symm, (Subst.id_apply r.rhs).symm⟩

theorem ruleInstance_self (r : Rule sigma nu) : RuleInstance r r.lhs r.rhs :=
  rewriting_rule_self [r] (List.mem_singleton.mpr rfl)

/-- Every actual rewrite step belongs to one full rule-instance relation. -/
theorem rewriting_step_iff_ruleUnion (T : TRS sigma nu) (s t : Term sigma nu) :
    Step T s t ↔ RuleUnion RuleInstance (fun r => r ∈ T) s t := by
  constructor
  · intro hp
    induction hp with
    | root hr =>
        obtain ⟨r, hm, σ, hs, ht⟩ := hr
        exact ⟨r, hm, Step.root ⟨r, List.mem_singleton.mpr rfl, σ, hs, ht⟩⟩
    | arg f pre post h ih =>
        obtain ⟨r, hr, hp⟩ := ih
        exact ⟨r, hr, Step.arg f pre post hp⟩
  · rintro ⟨r, hr, hp⟩
    apply rewriting_step_mono (T := [r]) (U := T) (fun q hq => ?_) hp
    have hqr : q = r := List.mem_singleton.mp hq
    exact hqr.symm ▸ hr

/-- Closure alone characterizes containment of every substitution and context
instance of a rule in an arbitrary semantic relation. -/
theorem ruleInstance_subrel_iff_of_closed
    (S : Term sigma nu → Term sigma nu → Prop)
    (hc : ∀ C : TermContext sigma nu, OperationClosed S C.plug)
    (hs : ∀ σ : Subst sigma nu, OperationClosed S (Subst.apply σ))
    (r : Rule sigma nu) :
    Subrel (RuleInstance r) S ↔ S r.lhs r.rhs := by
  constructor
  · intro hsub
    exact hsub (ruleInstance_self r)
  · intro hside s t hp
    induction hp with
    | root hr =>
        obtain ⟨q, hq, σ, rfl, rfl⟩ := hr
        have hqr : q = r := List.mem_singleton.mp hq
        subst q
        exact hs σ hside
    | arg f pre post hp ih =>
        exact hc (.arg f pre post .hole) ih

/-- Full normalizer-safe rule admission requires only closure of MaxRel. -/
theorem ruleInstance_safe_iff_of_closed {n : Term sigma nu → Term sigma nu}
    (hc : ∀ C : TermContext sigma nu, OperationClosed (MaxRel n) C.plug)
    (hs : ∀ σ : Subst sigma nu, OperationClosed (MaxRel n) (Subst.apply σ))
    (r : Rule sigma nu) :
    Subrel (RuleInstance r) (MaxRel n) ↔ MaxRel n r.lhs r.rhs :=
  ruleInstance_subrel_iff_of_closed (MaxRel n) hc hs r

/-- An existing globally realizing TRS supplies the two closure premises. -/
theorem ruleInstance_safe_iff {T : TRS sigma nu} {n : Term sigma nu → Term sigma nu}
    (h : Realizes (Step T) n) (r : Rule sigma nu) :
    Subrel (RuleInstance r) (MaxRel n) ↔ MaxRel n r.lhs r.rhs :=
  ruleInstance_safe_iff_of_closed (maxRel_context h) (maxRel_substitution h) r

theorem trs_rule_side_safety {T : TRS sigma nu} {n : Term sigma nu → Term sigma nu}
    (h : Realizes (Step T) n) (U : TRS sigma nu) :
    Subrel (Step U) (MaxRel n) ↔ ∀ r, r ∈ U → MaxRel n r.lhs r.rhs := by
  constructor
  · intro hs r hr
    exact hs (rewriting_rule_self U hr)
  · intro hs s t hp
    obtain ⟨r, hr, hrt⟩ := (rewriting_step_iff_ruleUnion U s t).mp hp
    exact (ruleInstance_safe_iff h r).mpr (hs r hr) hrt

/-- The abstract cut theorem is connected to the existing TRS constructors. -/
theorem trs_realizes_iff_rule_cuts (T : TRS sigma nu) (n : Term sigma nu → Term sigma nu) :
    Realizes (Step T) n ↔
      (∀ r, r ∈ T → SafeRule RuleInstance n r) ∧
        HitsRuleCuts RuleInstance n (fun r => r ∈ T) := by
  have heq : Step T = RuleUnion RuleInstance (fun r => r ∈ T) := by
    funext s t
    exact propext (rewriting_step_iff_ruleUnion T s t)
  rw [heq]
  exact rule_family_realizes_iff RuleInstance (fun r => r ∈ T)

/-- Retaining a realizing base leaves only the displayed-side admission tests
for an extension. Deletion and replacement still require the cut constraints. -/
theorem trs_extension_realizes_iff {T : TRS sigma nu} {n : Term sigma nu → Term sigma nu}
    (h : Realizes (Step T) n) (U : TRS sigma nu) :
    Realizes (Step (T ++ U)) n ↔ ∀ r, r ∈ U → MaxRel n r.lhs r.rhs := by
  constructor
  · intro he r hr
    exact he.subrel_maxRel (rewriting_rule_self (T ++ U)
      (List.mem_append.mpr (Or.inr hr)))
  · intro hu
    apply realizes_of_subrel_maxRel
    · apply (trs_rule_side_safety h (T ++ U)).mpr
      intro r hr
      rcases List.mem_append.mp hr with ht | hu'
      · exact h.subrel_maxRel (rewriting_rule_self T ht)
      · exact hu r hu'
    · intro t
      exact star_mono (rewriting_step_mono
        (fun r hr => List.mem_append.mpr (Or.inl hr))) (h.reaches t)

section ExecutableAdmission

variable [DecidableEq sigma] [DecidableEq nu]

/-- This Boolean test uses only the supplied normalizer and decidable term equality. -/
def ruleAdmission (n : Term sigma nu → Term sigma nu) (r : Rule sigma nu) : Bool :=
  decide (r.lhs ≠ n r.lhs ∧ n r.lhs = n r.rhs)

theorem ruleAdmission_spec_of_closed {n : Term sigma nu → Term sigma nu}
    (hc : ∀ C : TermContext sigma nu, OperationClosed (MaxRel n) C.plug)
    (hs : ∀ σ : Subst sigma nu, OperationClosed (MaxRel n) (Subst.apply σ))
    (r : Rule sigma nu) :
    ruleAdmission n r = true ↔ Subrel (RuleInstance r) (MaxRel n) := by
  simpa only [ruleAdmission, decide_eq_true_eq, MaxRel] using
    (ruleInstance_safe_iff_of_closed hc hs r).symm

theorem ruleAdmission_spec {T : TRS sigma nu} {n : Term sigma nu → Term sigma nu}
    (h : Realizes (Step T) n) (r : Rule sigma nu) :
    ruleAdmission n r = true ↔ Subrel (RuleInstance r) (MaxRel n) :=
  ruleAdmission_spec_of_closed (maxRel_context h) (maxRel_substitution h) r

def admittedRules (n : Term sigma nu → Term sigma nu) (candidates : TRS sigma nu) :
    TRS sigma nu := candidates.filter (ruleAdmission n)

theorem mem_admittedRules {T : TRS sigma nu} {n : Term sigma nu → Term sigma nu}
    (h : Realizes (Step T) n) (candidates : TRS sigma nu) (r : Rule sigma nu) :
    r ∈ admittedRules n candidates ↔
      r ∈ candidates ∧ Subrel (RuleInstance r) (MaxRel n) := by
  constructor
  · intro hr
    obtain ⟨hm, ht⟩ := List.mem_filter.mp hr
    exact ⟨hm, (ruleAdmission_spec h r).mp ht⟩
  · rintro ⟨hm, hs⟩
    exact List.mem_filter.mpr ⟨hm, (ruleAdmission_spec h r).mpr hs⟩

theorem admittedRules_extension_realizes {T : TRS sigma nu}
    {n : Term sigma nu → Term sigma nu} (h : Realizes (Step T) n)
    (candidates : TRS sigma nu) : Realizes (Step (T ++ admittedRules n candidates)) n := by
  apply (trs_extension_realizes_iff h _).mpr
  intro r hr
  exact (ruleInstance_safe_iff h r).mp ((mem_admittedRules h candidates r).mp hr).2

end ExecutableAdmission

end Terms

namespace FreshVariableControl

/-- The ordinary erasing rule f(x) -> c. -/
def erasingRule : Rule Nat Nat where
  lhs := .app 0 [.var 0]
  rhs := .app 1 []
  lhs_isApp := rfl

def erasingTRS : TRS Nat Nat := [erasingRule]
def groundSource : Term Nat Nat := .app 0 [.app 1 []]
def openTarget : Term Nat Nat := .app 0 [.var 1]
def commonResult : Term Nat Nat := .app 1 []

theorem erasingRule_noFreshVars : RuleNoFreshVars erasingRule := by
  simp [RuleNoFreshVars, NoFreshVars, erasingRule]

theorem erasingTRS_noFreshVars : Subrel (Step erasingTRS) NoFreshVars := by
  apply noFreshVars_step
  intro r hr
  have heq : r = erasingRule := List.mem_singleton.mp hr
  exact heq.symm ▸ erasingRule_noFreshVars

theorem groundSource_step : Step erasingTRS groundSource commonResult :=
  Step.root ⟨erasingRule, List.mem_singleton.mpr rfl,
    (fun _ => .app 1 []), rfl, rfl⟩

theorem openTarget_step : Step erasingTRS openTarget commonResult :=
  Step.root ⟨erasingRule, List.mem_singleton.mpr rfl,
    (fun _ => .var 1), rfl, rfl⟩

/-- Saturation adds f(c) -> f(y), despite the original TRS preserving variables. -/
theorem saturation_fresh_variable :
    Saturate (Step erasingTRS) groundSource openTarget ∧
      ¬ NoFreshVars groundSource openTarget := by
  refine ⟨⟨fun hn => hn commonResult groundSource_step, ?_⟩, ?_⟩
  · exact conv_of_join ⟨commonResult, .single groundSource_step, .single openTarget_step⟩
  · simp [NoFreshVars, groundSource, openTarget]

theorem saturation_not_variable_preserving :
    ¬ Subrel (Saturate (Step erasingTRS)) NoFreshVars :=
  fun h => saturation_fresh_variable.2 (h saturation_fresh_variable.1)

/-- No ordinary TRS on this syntax has exactly the saturated step relation. -/
theorem saturation_no_ordinary_presentation :
    ¬ ∃ T : TRS Nat Nat, (∀ r, r ∈ T → RuleNoFreshVars r) ∧
      (∀ s t, Step T s t ↔ Saturate (Step erasingTRS) s t) := by
  rintro ⟨T, hT, heq⟩
  have hs : Step T groundSource openTarget :=
    (heq groundSource openTarget).mpr saturation_fresh_variable.1
  exact saturation_fresh_variable.2 (noFreshVars_step T hT hs)

end FreshVariableControl

end OperatorKO7.Meta.UniqueNormalization.Normalization
