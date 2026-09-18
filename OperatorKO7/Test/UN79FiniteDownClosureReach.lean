import OperatorKO7.Meta.UniqueNormalization.FiniteDownClosure

/-! # Finite Down closure checks -/

open OperatorKO7.Meta.Rewriting
open OperatorKO7.Meta.UniqueNormalization

#check @FiniteSaturation.stage
#print axioms FiniteSaturation.stage
#check @FiniteSaturation.stage_subset_succ
#print axioms FiniteSaturation.stage_subset_succ
#check @FiniteSaturation.stage_subset_bound
#print axioms FiniteSaturation.stage_subset_bound
#check @FiniteSaturation.stage_add_eq_of_stable
#print axioms FiniteSaturation.stage_add_eq_of_stable
#check @FiniteSaturation.card_stage_ge_of_no_stable
#print axioms FiniteSaturation.card_stage_ge_of_no_stable
#check @FiniteSaturation.exists_stable_le_card
#print axioms FiniteSaturation.exists_stable_le_card
#check @FiniteSaturation.stable_at_card
#print axioms FiniteSaturation.stable_at_card
#check @FiniteDown.Pair
#print axioms FiniteDown.Pair
#check @FiniteDown.pairUniverse
#print axioms FiniteDown.pairUniverse
#check @FiniteDown.mem_pairUniverse
#print axioms FiniteDown.mem_pairUniverse
#check @FiniteDown.card_pairUniverse
#print axioms FiniteDown.card_pairUniverse
#check @FiniteDown.layer
#print axioms FiniteDown.layer
#check @FiniteDown.mem_layer
#print axioms FiniteDown.mem_layer
#check @FiniteDown.layer_subset
#print axioms FiniteDown.layer_subset
#check @FiniteDown.stage_sound
#print axioms FiniteDown.stage_sound
#check @FiniteDown.mem_bounded_stage_iff
#print axioms FiniteDown.mem_bounded_stage_iff
#check @FiniteDown.bounded_saturation
#print axioms FiniteDown.bounded_saturation
#check @FiniteDown.argsRelated
#print axioms FiniteDown.argsRelated
#check @FiniteDown.argsRelated_iff
#print axioms FiniteDown.argsRelated_iff
#check @FiniteDown.termRelated
#print axioms FiniteDown.termRelated
#check @FiniteDown.termRelated_iff
#print axioms FiniteDown.termRelated_iff
#check @FiniteDown.barRelated
#print axioms FiniteDown.barRelated
#check @FiniteDown.barRelated_iff
#print axioms FiniteDown.barRelated_iff
#check @FiniteDown.RootTableExact
#print axioms FiniteDown.RootTableExact
#check @FiniteDown.oneStep
#print axioms FiniteDown.oneStep
#check @FiniteDown.oneStep_iff
#print axioms FiniteDown.oneStep_iff
#check @FiniteDown.tableLayer
#print axioms FiniteDown.tableLayer
#check @FiniteDown.tableLayer_eq_layer
#print axioms FiniteDown.tableLayer_eq_layer
#check @FiniteDown.compute
#print axioms FiniteDown.compute
#check @FiniteDown.mem_compute_iff
#print axioms FiniteDown.mem_compute_iff
#check @FiniteDown.decidableDownOn
#print axioms FiniteDown.decidableDownOn
#check @FiniteMatching.Agrees
#print axioms FiniteMatching.Agrees
#check @FiniteMatching.matchList_complete_core
#print axioms FiniteMatching.matchList_complete_core
#check @FiniteMatching.match_complete_core
#print axioms FiniteMatching.match_complete_core
#check @FiniteMatching.matchList_complete
#print axioms FiniteMatching.matchList_complete
#check @FiniteMatching.matchList_iff
#print axioms FiniteMatching.matchList_iff
#check @FiniteMatching.ruleMatches
#print axioms FiniteMatching.ruleMatches
#check @FiniteMatching.ruleMatches_iff
#print axioms FiniteMatching.ruleMatches_iff
#check @FiniteMatching.rootMatches
#print axioms FiniteMatching.rootMatches
#check @FiniteMatching.rootMatches_iff
#print axioms FiniteMatching.rootMatches_iff
#check @FiniteMatching.decidableRootStep
#print axioms FiniteMatching.decidableRootStep
#check @FiniteDown.rootTable
#print axioms FiniteDown.rootTable
#check @FiniteDown.rootTable_exact
#print axioms FiniteDown.rootTable_exact
#check @FiniteDown.computeTRS
#print axioms FiniteDown.computeTRS
#check @FiniteDown.mem_computeTRS_iff
#print axioms FiniteDown.mem_computeTRS_iff
#check @FiniteDown.decidableDownOnTRS
#print axioms FiniteDown.decidableDownOnTRS

namespace FiniteDownControl

def atom (n : Nat) : Term (Nat ⊕ Nat) Empty := .app (.inr n) []

def leftRule : Rule (Nat ⊕ Nat) Empty := ⟨atom 0, atom 1, rfl⟩
def rightRule : Rule (Nat ⊕ Nat) Empty := ⟨atom 0, atom 2, rfl⟩
def rules : TRS (Nat ⊕ Nat) Empty := [leftRule, rightRule]
def terms : List (Term (Nat ⊕ Nat) Empty) := [atom 0, atom 1, atom 2]
def roots : Finset (FiniteDown.Pair Nat Empty) := {(atom 0, atom 1), (atom 0, atom 2)}

theorem root_iff (a b : Term (Nat ⊕ Nat) Empty) :
    rootStep rules a b ↔ a = atom 0 ∧ (b = atom 1 ∨ b = atom 2) := by
  constructor
  · rintro ⟨r, hr, s, ha, hb⟩
    have hcases : r = leftRule ∨ r = rightRule := by simpa [rules] using hr
    rcases hcases with rfl | rfl
    · exact ⟨by simpa [leftRule, atom, Subst.apply_app] using ha,
        Or.inl (by simpa [leftRule, atom, Subst.apply_app] using hb)⟩
    · exact ⟨by simpa [rightRule, atom, Subst.apply_app] using ha,
        Or.inr (by simpa [rightRule, atom, Subst.apply_app] using hb)⟩
  · rintro ⟨rfl, hb | hb⟩
    · subst b
      exact ⟨leftRule, by simp [rules], (fun x => nomatch x), rfl, rfl⟩
    · subst b
      exact ⟨rightRule, by simp [rules], (fun x => nomatch x), rfl, rfl⟩

theorem roots_exact : FiniteDown.RootTableExact terms rules roots := by
  intro a b _ _
  rw [root_iff]
  simp [roots, and_or_left]

/-- The raw iteration must not silently add transitivity: this root fork
relates both leaves to their source, but does not relate the two leaves. -/
theorem root_fork_nontransitive :
    DownOn terms rules (atom 1) (atom 0) ∧
    DownOn terms rules (atom 0) (atom 2) ∧
    ¬ DownOn terms rules (atom 1) (atom 2) := by
  refine ⟨(FiniteDown.mem_compute_iff roots_exact _ _).mp ?_,
    (FiniteDown.mem_compute_iff roots_exact _ _).mp ?_, ?_⟩
  · decide
  · decide
  · intro h
    have hmem := (FiniteDown.mem_compute_iff roots_exact _ _).mpr h
    exact (by decide : (atom 1, atom 2) ∉ FiniteDown.compute terms roots) hmem

/-- The actual rules reproduce the independently specified root table. -/
theorem synthesized_roots : FiniteDown.rootTable terms rules = roots := by decide

/-- The full computation still rejects the two leaves, without an input table. -/
theorem synthesized_rejects_leaves :
    (atom 1, atom 2) ∉ FiniteDown.computeTRS terms rules := by decide

/-- The rule syntax permits a variable occurring only on the right. -/
def freshRule : Rule (Nat ⊕ Nat) Nat :=
  ⟨.app (.inr 0) [.var 0], .var 1, rfl⟩

theorem fresh_rhs_step : rootStep [freshRule]
    (.app (.inr 0) [.var 0]) (.app (.inl 1) []) :=
  (FiniteMatching.rootMatches_iff _ _ _).mp (by decide)

def nonlinearRule : Rule (Nat ⊕ Nat) Nat :=
  ⟨.app (.inr 0) [.var 0, .var 0], .var 0, rfl⟩

end FiniteDownControl

#check @FiniteDownControl.atom
#print axioms FiniteDownControl.atom
#check @FiniteDownControl.leftRule
#print axioms FiniteDownControl.leftRule
#check @FiniteDownControl.rightRule
#print axioms FiniteDownControl.rightRule
#check @FiniteDownControl.rules
#print axioms FiniteDownControl.rules
#check @FiniteDownControl.terms
#print axioms FiniteDownControl.terms
#check @FiniteDownControl.roots
#print axioms FiniteDownControl.roots
#check @FiniteDownControl.root_iff
#print axioms FiniteDownControl.root_iff
#check @FiniteDownControl.roots_exact
#print axioms FiniteDownControl.roots_exact
#check @FiniteDownControl.root_fork_nontransitive
#print axioms FiniteDownControl.root_fork_nontransitive
#check @FiniteDownControl.synthesized_roots
#print axioms FiniteDownControl.synthesized_roots
#check @FiniteDownControl.synthesized_rejects_leaves
#print axioms FiniteDownControl.synthesized_rejects_leaves
#check @FiniteDownControl.freshRule
#print axioms FiniteDownControl.freshRule
#check @FiniteDownControl.fresh_rhs_step
#print axioms FiniteDownControl.fresh_rhs_step
#check @FiniteDownControl.nonlinearRule
#print axioms FiniteDownControl.nonlinearRule

/-- No iteration or table entry is needed for the empty carrier. -/
example : FiniteDown.compute ([] : List (Term (Nat ⊕ Nat) Empty)) ∅ = ∅ := by
  decide

/-- Duplicate list entries do not increase the iteration bound. -/
example : FiniteDown.compute [FiniteDownControl.atom 0, FiniteDownControl.atom 0] ∅ =
    {(FiniteDownControl.atom 0, FiniteDownControl.atom 0)} := by
  decide

/-- Unequal arities never count as one congruence layer. -/
example : FiniteDown.termRelated
    (∅ : Finset (FiniteDown.Pair Nat Empty))
    (.app (.inl 0) []) (.app (.inl 0) [FiniteDownControl.atom 0]) = false := by
  decide

/-- One substitution must respect every repeated pattern occurrence. -/
example : FiniteMatching.ruleMatches FiniteDownControl.nonlinearRule
    (.app (.inr 0) [.var 2, .var 3]) (.var 2) = false := by decide

/-- A matching source cannot be paired with an inconsistent rewrite target. -/
example : FiniteMatching.ruleMatches FiniteDownControl.nonlinearRule
    (.app (.inr 0) [.var 2, .var 2]) (.var 3) = false := by decide

example : FiniteMatching.ruleMatches FiniteDownControl.nonlinearRule
    (.app (.inr 0) [.var 2, .var 2]) (.var 2) = true := by decide

example : FiniteDown.computeTRS ([] : List (Term (Nat ⊕ Nat) Empty))
    FiniteDownControl.rules = ∅ := by decide
