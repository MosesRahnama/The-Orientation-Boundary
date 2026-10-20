import OperatorKO7.Meta.UniqueNormalization.Section7FiberReduction

/-!
# Lemma 64 counterexample

Kahrs and Smith, FSCD 2016, Lemma 64 as printed: if ⇓_A is a consistency
invariant, then every complete targeted proof graph is universal. The one-rule
system d(x) to x on the carrier {d(d(c)), d(c), c} is constructed in
`Section7FiberReduction`. This module names Definition 30 on a term-coalgebra
and records the printed-Lemma-64 refutation against that carrier.

It reuses the FiberReduction coalgebra, parent forest, and complete nonuniversal
targeted graph. It does not redeclare those objects.

It does not treat unique normalization of that system, RTA open problem 79, or
the Klop linearization development.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniqueNormalization

open OperatorKO7.Meta.Rewriting

universe u v

variable {sigma : Type u} {nu : Type v}

/-- **Definition 30 on a term-coalgebra.** A consistency invariant is a
consistent and `Σ`-closed relation `S` on `A` such that every
constructor-compatible equivalence contained in `S` has semantical critical
pairs inside `CT` of that equivalence. Relation: `DownOn` when instantiated
below. Property: Definition 30. -/
def ConsistencyInvariantOn (A : List (Term (sigma ⊕ sigma) nu))
    (R : TRS (sigma ⊕ sigma) nu) (S : CRel sigma nu) : Prop :=
  (∀ x y : nu, S (.var x) (.var y) → x = y)
  ∧ SigmaClosedOn A S
  ∧ ∀ E : CRel sigma nu, (∀ a b, E a b → S a b) →
      (∀ x y : Term (sigma ⊕ sigma) nu, E x y → E y x) →
      (∀ x y z : Term (sigma ⊕ sigma) nu, E x y → E y z → E x z) →
      ConstructorCompatible E →
      ∀ t₁ t₂ t₃ t₄ : Term (sigma ⊕ sigma) nu,
        rootStep R t₂ t₁ → barRel E t₂ t₃ → rootStep R t₃ t₄ → CT E t₁ t₄

namespace Section7Active

theorem not_mem_terms_var (x : Unit) : (.var x : T) ∉ terms := by
  intro h
  rcases (mem_terms _).1 h with h' | h' | h'
  · cases h'
  · cases h'
  · cases h'

/-- For `d(x) → x`, a semantic fork is already a `CT` pair: the two root steps
expose the destructor arguments, and the destructor tilde relates those
arguments. Relation: `rootStep` and `barRel`. Property: Definition 30 fork. -/
theorem semantic_fork {E : CRel Unit Unit} {t₁ t₂ t₃ t₄ : T}
    (h₁ : rootStep rules t₂ t₁) (h₂ : barRel E t₂ t₃) (h₃ : rootStep rules t₃ t₄) :
    CT E t₁ t₄ := by
  have ht₂ : t₂ = wrap t₁ := (rootStep_iff t₂ t₁).1 h₁
  have ht₃ : t₃ = wrap t₄ := (rootStep_iff t₃ t₄).1 h₃
  obtain ⟨f, as, bs, ⟨d, _hd⟩, hta, htb, hall⟩ := h₂
  subst f
  have hshape₂ : Term.app (Sum.inr d) as = wrap t₁ := hta.symm.trans ht₂
  have hshape₃ : Term.app (Sum.inr d) bs = wrap t₄ := htb.symm.trans ht₃
  obtain ⟨hf, has⟩ := Term.app.inj hshape₂
  obtain ⟨-, hbs⟩ := Term.app.inj hshape₃
  have hd0 : d = () := Sum.inr.inj hf
  subst d
  subst as
  subst bs
  cases hall with
  | cons hhead htail =>
      cases htail
      exact CT.base hhead

theorem downOn_sigmaClosedOn : SigmaClosedOn terms (DownOn terms rules) := by
  intro t u ht hu _
  exact down_all ht hu

/-- `⇓_A` is a consistency invariant for this carrier and this rule.
Relation: `DownOn terms rules`. Property: Definition 30. -/
theorem downOn_is_consistencyInvariant :
    ConsistencyInvariantOn terms rules (DownOn terms rules) := by
  refine ⟨?consist, downOn_sigmaClosedOn, ?fork⟩
  · intro x y h
    exact (not_mem_terms_var x (DownOn.mem h).1).elim
  · intro E _hsub _hsymm _htrans _hCC t₁ t₂ t₃ t₄ h₁ h₂ h₃
    exact semantic_fork h₁ h₂ h₃

end Section7Active

namespace Section7Active.Trap

/-- The printed Lemma 64 fiber-induction step fails: `t₁` and `t₂` are related
by the destructor tilde of `⇓_A`, but not by the destructor tilde of the graph
equivalence. Relation: `barRel`. Property: missing argumentwise graph equality. -/
theorem induction_promotion_fails :
    barRel (DownOn terms rules) once twice ∧
      ¬ barRel (EqvOn terms graph.par) once twice := by
  constructor
  · exact ⟨Sum.inr (), [constant], [once], ⟨(), rfl⟩, rfl, rfl,
      List.Forall₂.cons down_once_constant.symm List.Forall₂.nil⟩
  · rintro ⟨f, as, bs, ⟨d, _hd⟩, ha, hb, hall⟩
    subst f
    have honce : Term.app (Sum.inr ()) [constant] = Term.app (Sum.inr d) as := by
      simpa [once, wrap, constant] using ha
    have htwice : Term.app (Sum.inr ()) [once] = Term.app (Sum.inr d) bs := by
      simpa [twice, wrap, once, constant] using hb
    obtain ⟨hf, has⟩ := Term.app.inj honce
    obtain ⟨-, hbs⟩ := Term.app.inj htwice
    have hd0 : d = () := Sum.inr.inj hf.symm
    subst d
    subst as
    subst bs
    cases hall with
    | cons hhead _htail =>
        exact once_not_eqv_constant (EqvOn.symm hhead)

theorem eqvOn_eq_of_mutual_extends {alpha beta : PGraph terms rules}
    (hab : alpha.Extends beta) (hba : beta.Extends alpha) {a b : T} :
    EqvOn terms alpha.par a b ↔ EqvOn terms beta.par a b :=
  ⟨EqvOn.mono hab, EqvOn.mono hba⟩

/-- A universal proof graph cannot retain every parent edge of this complete
nonuniversal graph. Relation: `PGraph.par`. Property: edge-preserving repair
obstruction. -/
theorem repair_requires_parent_change (beta : PGraph terms rules)
    (hU : beta.Universal) : ¬ graph.Extends beta := by
  intro hExt
  have hrev : beta.Extends graph := graph_complete beta hExt
  exact once_not_eqv_constant
    ((eqvOn_eq_of_mutual_extends hExt hrev).2 ((hU once constant).2 down_once_constant))

/-- The printed Lemma 64 hypotheses that this graph satisfies, including that
`⇓_A` is a consistency invariant on this carrier. -/
theorem lemma64_as_printed :
    ConsistencyInvariantOn terms rules (DownOn terms rules) ∧
      Coalgebra terms ∧ ConstructorRules rules ∧ targeted.graph.Complete ∧
      ¬ targeted.Universal :=
  ⟨downOn_is_consistencyInvariant, terms_coalgebra, rules_constructor, graph_complete,
    targeted_not_universal⟩

/-- Lemma 64 as printed: if `⇓_A` is a consistency invariant, then every
complete targeted proof graph is universal. This carrier satisfies the
hypothesis and supplies a complete targeted graph that is not universal. -/
theorem lemma64_fails_as_printed :
    ConsistencyInvariantOn terms rules (DownOn terms rules) ∧
      ¬ ∀ rho : TermTargetedPGraph terms rules, rho.graph.Complete → rho.Universal :=
  ⟨downOn_is_consistencyInvariant, not_every_complete_targeted_graph_universal⟩

/-- Same statement as `downOn_is_consistencyInvariant`, named for the Trap
carrier used in the Lemma 64 refutation. -/
theorem trap_DownOn_is_consistencyInvariant :
    ConsistencyInvariantOn terms rules (DownOn terms rules) :=
  downOn_is_consistencyInvariant

end Section7Active.Trap

end OperatorKO7.Meta.UniqueNormalization
