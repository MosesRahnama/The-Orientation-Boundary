import OperatorKO7.Meta.UniqueNormalization.Section7TightClosure

/-!
# A terminating self-grey parent with an unsound equality

The sole rule is d(x) → c(d(x)); p and q are distinct variables.
The six-node parent has edges dp → cdp → cdq and dq → cdq.
Its constructor edge uses its own equality, while every actual DownOn clause
preserves Term.vars. This refutes raw self-grey soundness, not the full Klop theorem.
Relation: rootStep, Grey, EqvOn, DownOn. Closure: the actual relativized invariant.
Strategy: root-only rule instances; finite parent paths. External trust: none.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniqueNormalization.Section7SelfGreyCountermodel

open OperatorKO7.Meta.Rewriting

abbrev T := Term (Unit ⊕ Unit) Bool
abbrev p : T := .var false
abbrev q : T := .var true
abbrev d (t : T) : T := .app (.inr ()) [t]
abbrev c (t : T) : T := .app (.inl ()) [t]
abbrev dp : T := d p
abbrev dq : T := d q
abbrev cdp : T := c dp
abbrev cdq : T := c dq

def rule : Rule (Unit ⊕ Unit) Bool where
  lhs := dp
  rhs := cdp
  lhs_isApp := rfl

def rules : TRS (Unit ⊕ Unit) Bool := [rule]
def terms : List T := coalgebraOf [cdp, cdq]

theorem terms_eq : terms = [cdp, dp, p, cdq, dq, q] := rfl

theorem terms_coalgebra : Coalgebra terms := coalgebra_coalgebraOf _

theorem terms_length : terms.length = 6 := rfl

theorem terms_nodup : terms.Nodup := by decide

theorem mem_terms (t : T) :
    t ∈ terms ↔ t = p ∨ t = q ∨ t = dp ∨ t = dq ∨ t = cdp ∨ t = cdq := by
  simp [terms_eq, or_assoc, or_left_comm, or_comm]

theorem p_ne_q : p ≠ q := by decide

theorem cdp_ne_cdq : cdp ≠ cdq := by decide

theorem rules_constructor : ConstructorRules rules := by
  intro r hr
  have he : r = rule := by simpa [rules] using hr
  subst r
  refine ⟨(), [p], rfl, ?_⟩
  intro t ht
  have ht' : t = p := by simpa using ht
  subst t
  exact ConOnly.var false

theorem rule_rhs_determined : Rule.RhsDetermined rule := by
  intro s t h
  change d (s false) = d (t false) at h
  change c (d (s false)) = c (d (t false))
  have he : s false = t false := by simpa [d] using h
  rw [he]

theorem rules_strong : StronglyAlmostNonOmegaOverlapping rules := by
  constructor
  · intro r hr r' hr' s hs happ _
    have he : r = rule := by simpa [rules] using hr
    subst r
    obtain ⟨f, args, a, heq, ha, hsa⟩ := hs
    change Term.app (.inr ()) [p] = Term.app f args at heq
    have hargs := (Term.app.inj heq).2
    have ha' : a = p := by simpa only [← hargs, List.mem_singleton] using ha
    subst a
    have hs' : s = p := hsa.eq_of_var
    subst s
    exact Bool.noConfusion happ
  · intro r hr r' hr' _
    have he : r = rule := by simpa [rules] using hr
    have he' : r' = rule := by simpa [rules] using hr'
    subst r
    subst r'
    refine ⟨CommonGeneralisation.self rule rule_rhs_determined, ?_⟩
    intro x hx
    change VarOccurs x cdp at hx
    change VarOccurs x dp
    obtain ⟨a, ha, hxa⟩ := hx.app_inv
    have ha' : a = dp := by simpa using ha
    subst a
    exact hxa

/-- Relation: rootStep; property: every substitution instance of the sole rule. -/
theorem root_d (t : T) : rootStep rules (d t) (c (d t)) :=
  ⟨rule, by simp [rules], fun _ => t, rfl, rfl⟩

theorem rootStep_iff (x y : T) :
    rootStep rules x y ↔ ∃ t, x = d t ∧ y = c (d t) := by
  constructor
  · rintro ⟨r, hr, s, hx, hy⟩
    have he : r = rule := by simpa [rules] using hr
    subst r
    exact ⟨s false, hx, hy⟩
  · rintro ⟨t, rfl, rfl⟩
    exact root_d t

/-- Relation: rootStep; property: exhaustive root-step enumeration on terms. -/
theorem rootStep_on_terms_iff (x y : T) :
    (x ∈ terms ∧ rootStep rules x y) ↔
      (x = dp ∧ y = cdp) ∨ (x = dq ∧ y = cdq) := by
  constructor
  · rintro ⟨hx, hroot⟩
    obtain ⟨t, rfl, rfl⟩ := (rootStep_iff x y).mp hroot
    have ht : t = p ∨ t = q := by
      simpa [mem_terms, dp, dq, cdp, cdq, d, c, p, q] using hx
    rcases ht with rfl | rfl
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨by simp [mem_terms], root_d p⟩
    · exact ⟨by simp [mem_terms], root_d q⟩

def parent (t : T) : Option T :=
  if t = dp then some cdp else if t = dq then some cdq else
    if t = cdp then some cdq else none

theorem parent_edge {x y : T} (h : parent x = some y) :
    (x = dp ∧ y = cdp) ∨ (x = dq ∧ y = cdq) ∨ (x = cdp ∧ y = cdq) := by
  by_cases h0 : x = dp
  · subst x
    exact Or.inl ⟨rfl, by simpa [parent] using h.symm⟩
  · by_cases h1 : x = dq
    · subst x
      exact Or.inr (Or.inl ⟨rfl, by simpa [parent, h0] using h.symm⟩)
    · by_cases h2 : x = cdp
      · subst x
        exact Or.inr (Or.inr ⟨rfl, by simpa [parent, h0, h1] using h.symm⟩)
      · simp [parent, h0, h1, h2] at h

theorem parent_edge_iff (x y : T) :
    parent x = some y ↔
      (x = dp ∧ y = cdp) ∨ (x = dq ∧ y = cdq) ∨ (x = cdp ∧ y = cdq) := by
  constructor
  · exact parent_edge
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> decide

theorem parent_mem {x y : T} (h : parent x = some y) : x ∈ terms ∧ y ∈ terms := by
  rcases parent_edge h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp [mem_terms]

def rank (t : T) : Nat :=
  if t = dp then 2 else if t = dq ∨ t = cdp then 1 else 0

theorem parent_rank_decreases {x y : T} (h : parent x = some y) : rank y < rank x := by
  rcases parent_edge h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

/-- Relation: the actual parent function; property: well-founded forward paths. -/
theorem parent_terminating : Terminating parent := by
  have hwf : WellFounded (fun x y : T => rank x < rank y) :=
    InvImage.wf (f := rank) Nat.lt_wfRel.wf
  have hsub : Subrelation (fun y x : T => parent x = some y)
      (fun y x : T => rank y < rank x) := by
    intro y x h
    exact parent_rank_decreases h
  exact Subrelation.wf hsub hwf

theorem parent_of_root {x y : T} (hx : x ∈ terms) (hroot : rootStep rules x y) :
    parent x = some y := by
  rcases (rootStep_on_terms_iff x y).mp ⟨hx, hroot⟩ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    decide

theorem rootSteps_represented {x y : T} (hx : x ∈ terms) (hy : y ∈ terms)
    (hroot : rootStep rules x y) : EqvOn terms parent x y :=
  EqvOn.of_reach hx hy (Reach.head (parent_of_root hx hroot) (Reach.refl y))

theorem eqv_dp_dq : EqvOn terms parent dp dq :=
  ⟨by simp [mem_terms], by simp [mem_terms], cdq,
    Reach.head (b := cdp) (by decide)
      (Reach.head (b := cdq) (by decide) (Reach.refl cdq)),
    Reach.head (b := cdq) (by decide) (Reach.refl cdq)⟩

theorem eqv_cdp_cdq : EqvOn terms parent cdp cdq :=
  ⟨by simp [mem_terms], by simp [mem_terms], cdq,
    Reach.head (b := cdq) (by decide) (Reach.refl cdq), Reach.refl cdq⟩

theorem hat_cdp_cdq : hatEq (EqvOn terms parent) cdp cdq :=
  Or.inr ⟨.inl (), [dp], [dq], ⟨(), rfl⟩, rfl, rfl,
    List.Forall₂.cons eqv_dp_dq List.Forall₂.nil⟩

/-- Relation: actual Grey with this parent's own EqvOn; property: all three edges. -/
theorem parent_grey {x y : T} (h : parent x = some y) :
    Grey terms rules (EqvOn terms parent) x y := by
  rcases parent_edge h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl (root_d p)
  · exact Or.inl (root_d q)
  · exact Or.inr (Or.inr hat_cdp_cdq)

/-- The observer uses syntax only and has no parent or graph parameter. -/
def SameVars (x y : T) : Prop := Term.vars x = Term.vars y

theorem vars_d (t : T) : Term.vars (d t) = Term.vars t := by simp [d]

theorem vars_c (t : T) : Term.vars (c t) = Term.vars t := by simp [c]

/-- Relation: rootStep on all finite terms; property: variable-set preservation. -/
theorem rootStep_preserves_vars {x y : T} (h : rootStep rules x y) : SameVars x y := by
  obtain ⟨t, rfl, rfl⟩ := (rootStep_iff x y).mp h
  exact (vars_c (d t)).symm

theorem forall₂_varsList_eq {xs ys : List T} (h : List.Forall₂ SameVars xs ys) :
    Term.varsList xs = Term.varsList ys := by
  induction h with
  | nil => rfl
  | @cons x y xs ys hxy _ ih =>
      change Term.vars x ∪ Term.varsList xs = Term.vars y ∪ Term.varsList ys
      exact congrArg₂ (fun (a b : Finset Bool) => a ∪ b) hxy ih

theorem sameVars_app {f : Unit ⊕ Unit} {xs ys : List T}
    (h : List.Forall₂ SameVars xs ys) : SameVars (.app f xs) (.app f ys) :=
  forall₂_varsList_eq h

/-- Relation: every actual DownStepOn clause; property: observer closure on any carrier. -/
theorem sameVars_closed (A : List T) (x y : T)
    (h : DownStepOn A rules SameVars x y) : SameVars x y := by
  obtain ⟨_, _, hbody⟩ := h
  rcases hbody with heq | hinv | ⟨z, _, hroot, hzy⟩ |
      ⟨f, xs, ys, hx, hargs, _, hmid⟩ | hhat | hbar
  · subst y
    rfl
  · exact Eq.symm hinv
  · exact Eq.trans (rootStep_preserves_vars hroot) hzy
  · subst x
    exact Eq.trans (sameVars_app (f := .inr f) hargs) hmid
  · obtain ⟨f, xs, ys, _, rfl, rfl, hargs⟩ := hhat
    exact sameVars_app (f := f) hargs
  · obtain ⟨f, xs, ys, _, rfl, rfl, hargs⟩ := hbar
    exact sameVars_app (f := f) hargs

/-- Relation: actual DownOn; property: leastness transfers observer closure. -/
theorem downOn_preserves_vars {A : List T} {x y : T} (h : DownOn A rules x y) :
    SameVars x y :=
  DownOn.least (sameVars_closed A) h

theorem vars_cdp : Term.vars cdp = {false} := by simp [cdp, dp, p]

theorem vars_cdq : Term.vars cdq = {true} := by simp [cdq, dq, q]

theorem vars_cdp_ne_cdq : Term.vars cdp ≠ Term.vars cdq := by decide

/-- Relation: actual DownOn; property: independent separation of the constructor pair. -/
theorem not_down_cdp_cdq : ¬ DownOn terms rules cdp cdq :=
  fun h => vars_cdp_ne_cdq (downOn_preserves_vars h)

theorem not_down_dp_dq : ¬ DownOn terms rules dp dq := by
  intro h
  have he := downOn_preserves_vars h
  exact (by decide : Term.vars dp ≠ Term.vars dq) he

theorem no_proofGraph_same_parent : ¬ ∃ rho : PGraph terms rules, rho.par = parent := by
  rintro ⟨rho, hpar⟩
  apply not_down_cdp_cdq
  apply rho.sub
  rw [hpar]
  exact eqv_cdp_cdq

/-- All raw hypotheses hold, both root steps remain, and the constructor equality is unsound. -/
theorem selfGrey_countermodel :
    ConstructorRules rules ∧ StronglyAlmostNonOmegaOverlapping rules ∧
      Coalgebra terms ∧ terms.length = 6 ∧ terms.Nodup ∧ p ≠ q ∧
      (∀ {x y}, parent x = some y → x ∈ terms ∧ y ∈ terms) ∧
      Terminating parent ∧
      (∀ {x y}, parent x = some y → Grey terms rules (EqvOn terms parent) x y) ∧
      (∀ {x y}, x ∈ terms → rootStep rules x y → parent x = some y) ∧
      rootStep rules dp cdp ∧ rootStep rules dq cdq ∧
      EqvOn terms parent cdp cdq ∧ ¬ DownOn terms rules cdp cdq ∧
      ¬ (∃ rho : PGraph terms rules, rho.par = parent) :=
  ⟨rules_constructor, rules_strong, terms_coalgebra, terms_length, terms_nodup, p_ne_q,
    parent_mem, parent_terminating, parent_grey, parent_of_root, root_d p, root_d q,
    eqv_cdp_cdq, not_down_cdp_cdq, no_proofGraph_same_parent⟩

/-- Raw self-grey soundness fails even when the parent retains every root step in its carrier. -/
theorem not_selfGrey_strong_terminating_soundness :
    ¬ (∀ (A : List T) (R : TRS (Unit ⊕ Unit) Bool) (g : T → Option T),
      Coalgebra A → ConstructorRules R → StronglyAlmostNonOmegaOverlapping R →
      (∀ {x y}, g x = some y → x ∈ A ∧ y ∈ A) → Terminating g →
      (∀ {x y}, g x = some y → Grey A R (EqvOn A g) x y) →
      (∀ {x y}, x ∈ A → rootStep R x y → g x = some y) →
      ∀ {x y}, EqvOn A g x y → DownOn A R x y) := by
  intro h
  exact not_down_cdp_cdq (h terms rules parent terms_coalgebra rules_constructor rules_strong
    parent_mem parent_terminating parent_grey parent_of_root eqv_cdp_cdq)

def reflexiveSeed (x y : T) : Prop := x = y ∧ x ∈ terms

theorem reflexiveSeed_sound {x y : T} (h : reflexiveSeed x y) : DownOn terms rules x y := by
  obtain ⟨rfl, hx⟩ := h
  exact DownOn.refl hx

/-- The constructor pair depends on itself through the actual dp/dq parent paths. -/
theorem constructor_support_self_cycle :
    ConstructorSupportDependency terms parent reflexiveSeed (cdp, cdq) (cdp, cdq) := by
  have hpair : ¬ reflexiveSeed cdp cdq := fun h => cdp_ne_cdq h.1
  have hargs : ¬ reflexiveSeed dp dq := fun h => (by decide : dp ≠ dq) h.1
  exact ⟨hpair, hpair, eqv_cdp_cdq, (), [dp], [dq], dp, dq,
    rfl, rfl, by decide, eqv_dp_dq, hargs,
    Reach.head (b := cdp) (by decide) (Reach.refl cdp),
    Reach.head (b := cdq) (by decide) (Reach.refl cdq),
    ConTopped.app () [dp], ConTopped.app () [dq], eqv_cdp_cdq⟩

theorem reflexiveSeed_support_not_wellFounded :
    ¬ WellFounded (ConstructorSupportDependency terms parent reflexiveSeed) := by
  intro hwf
  have hirr : ∀ z, ¬ ConstructorSupportDependency terms parent reflexiveSeed z z := by
    intro z
    induction hwf.apply z with
    | intro z _ ih => intro hz; exact ih z hz hz
  exact hirr (cdp, cdq) constructor_support_self_cycle

/-- No sound seed gives well-founded constructor support for this same parent. -/
theorem no_sound_support_certificate :
    ¬ ∃ seed : CRel Unit Bool,
      (∀ {x y}, seed x y → DownOn terms rules x y) ∧
      WellFounded (ConstructorSupportDependency terms parent seed) := by
  rintro ⟨seed, hseed, hwf⟩
  exact not_down_cdp_cdq (eqvOn_downOn_of_wellFounded_constructorSupport
    terms_coalgebra rules_constructor parent_mem parent_grey hseed hwf eqv_cdp_cdq)

end OperatorKO7.Meta.UniqueNormalization.Section7SelfGreyCountermodel
