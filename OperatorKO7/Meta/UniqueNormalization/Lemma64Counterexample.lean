import OperatorKO7.Meta.UniqueNormalization.Section7FiberReduction
import OperatorKO7.Meta.UniqueNormalization.Section7ChainClassification

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

/-! ## The lower record choice (ledger row 05-002)

On the same carrier two complete targeted proof graphs exist: `targeted` above, with the upper
stage `d(d(c))` as its target in the destructor fiber `{d(c), d(d(c))}`, and
`Section7Active.targeted`, with the lower stage `d(c)` as its target. Neither extends the other,
both are maximal in the extension order (`PGraph.Complete`), and only the lower choice is
universal. Lemma 64 inferred `greatest` from `maximal` in an order with these two incomparable
maximal elements. -/

/-- The lower graph does not extend the upper one: it gives `d(d(c))` the parent `d(c)`, and the
upper graph gives `d(d(c))` no parent. -/
theorem active_not_extends_trap : ¬ Section7Active.graph.Extends graph := by
  intro h
  have hp := h (show Section7Active.graph.par twice = some once from by
    simp [Section7Active.graph, Section7Active.parent])
  simp [graph, parent] at hp

/--
Proves: on the carrier `{c, d(c), d(d(c))}` of `d(x) → x`, the targeted graph with the lower
target `d(c)` is complete and universal, the targeted graph with the upper target `d(d(c))` is
complete and not universal, and neither graph extends the other.
Relation: the parent forests `Section7Active.graph.par` and `graph.par`; `DownOn terms rules`.
Scope: row 05-002, the Lean name the ledger asks for. Trust: kernel-only.
-/
theorem lower_target_universal :
    Section7Active.targeted.graph.Complete ∧ Section7Active.targeted.Universal ∧
      Section7Active.targeted.target.pick twice = once ∧
      Section7Active.targeted.target.pick once = once ∧
      targeted.graph.Complete ∧ ¬ targeted.Universal ∧
      targeted.target.pick once = twice ∧ targeted.target.pick twice = twice ∧
      ¬ graph.Extends Section7Active.graph ∧ ¬ Section7Active.graph.Extends graph := by
  refine ⟨Section7Active.graph_complete, Section7Active.targeted_universal, ?_, ?_,
    graph_complete, targeted_not_universal, ?_, ?_, repair_is_not_edge_preserving,
    active_not_extends_trap⟩
  · simp [Section7Active.targeted, Section7Active.target, Section7Active.pick]
  · simp [Section7Active.targeted, Section7Active.target, Section7Active.pick]
  · simp [targeted, target, pick]
  · simp [targeted, target, pick]

end Section7Active.Trap

namespace Section7Active

/-- The three-term chain carrier of the chain classification at `n = 2` is this carrier listed
from the root: `[c, d(c), d(d(c))]`. -/
theorem chain_carrier_eq :
    ChainClassification.carrier (nu := Unit) () () 2 = [constant, once, twice] := rfl

/-- The chain carrier and this carrier have the same members. -/
theorem chain_carrier_mem_iff (t : T) :
    t ∈ ChainClassification.carrier (nu := Unit) () () 2 ↔ t ∈ terms := by
  rw [chain_carrier_eq, mem_terms]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  tauto

/-- The erasing rule of the chain classification is the rule `d(x) → x` of this carrier. -/
theorem chain_rules_eq : ChainClassification.eraseRules () () = rules := rfl

/--
Proves: on the three-term chain carrier of `d(x) → x`, every complete targeted proof graph is
universal if and only if its target at `d(c)` is `d(c)`: the record choice in the destructor fiber
decides universality for every complete graph, not only for the two graphs above.
Relation: `DownOn` of the chain carrier and the represented parent-forest equality.
Scope: row 05-002; the instance `n = 2` of `ChainClassification.complete_target_universal_iff`
(normal-forms paper, Theorem 12.33). Trust: kernel-only.
-/
theorem chain_complete_targeted_universal_iff_lower
    (rho : TermTargetedPGraph (ChainClassification.carrier (nu := Unit) () () 2)
      (ChainClassification.eraseRules () ()))
    (hc : rho.graph.Complete) :
    rho.Universal ↔ rho.target.pick once = once :=
  ChainClassification.complete_target_universal_iff (n := 2) rho hc (by decide)

end Section7Active

end OperatorKO7.Meta.UniqueNormalization
