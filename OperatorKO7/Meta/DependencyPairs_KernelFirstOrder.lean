import OperatorKO7.Meta.DependencyPairs_FiniteCarrierView

/-!
# Standalone KO7-Shaped First-Order Model

This module defines a hand-authored finite first-order system over KO7-shaped
symbols. A correspondence theorem connecting these records to the trace-kernel
`Step` relation lies outside this module.
-/

namespace OperatorKO7.DependencyPairsFragment.KernelFirstOrder

/-- Symbol type for the standalone eight-rule first-order model. -/
inductive Symbol
| void
| delta
| integrate
| merge
| app
| recD
| eqW
deriving DecidableEq, Repr

abbrev Term := OperatorKO7.DependencyPairsFragment.FOTerm Symbol String
abbrev Rule := OperatorKO7.DependencyPairsFragment.FORule Symbol String

/-- Variable shorthands for the standalone presentation. -/
def x : Term := .var "x"
def y : Term := .var "y"
def z : Term := .var "z"

/-- Internal symbol constructor shorthands. -/
def void : Term := .app Symbol.void []
def delta (t : Term) : Term := .app Symbol.delta [t]
def integrate (t : Term) : Term := .app Symbol.integrate [t]
def merge (a b : Term) : Term := .app Symbol.merge [a, b]
def app (a b : Term) : Term := .app Symbol.app [a, b]
def recD (b s n : Term) : Term := .app Symbol.recD [b, s, n]
def eqW (a b : Term) : Term := .app Symbol.eqW [a, b]

/-- Eight hand-authored rules of the standalone first-order model. -/
def ko7FullStepRules : Array Rule :=
  #[ ⟨integrate (delta x), void⟩
   , ⟨merge void x, x⟩
   , ⟨merge x void, x⟩
   , ⟨merge x x, x⟩
   , ⟨recD x y void, x⟩
   , ⟨recD x y (delta z), app y (recD x y z)⟩
   , ⟨eqW x x, void⟩
   , ⟨eqW x y, integrate (merge x y)⟩ ]

/-- Unit engine carrier for the standalone first-order model. -/
inductive EngineTag
| full
deriving DecidableEq, Repr

/-- Finite carrier indexing the eight standalone rules. -/
inductive RuleId
| integrate_delta
| merge_void_left
| merge_void_right
| merge_idem
| rec_zero
| rec_succ
| eq_refl
| eq_diff
deriving Fintype, DecidableEq, Repr

/-- Left-hand sides indexed by the finite rule carrier. -/
def ruleLhs : RuleId → Term
| .integrate_delta => integrate (delta x)
| .merge_void_left => merge void x
| .merge_void_right => merge x void
| .merge_idem => merge x x
| .rec_zero => recD x y void
| .rec_succ => recD x y (delta z)
| .eq_refl => eqW x x
| .eq_diff => eqW x y

/-- Right-hand sides indexed by the finite rule carrier. -/
def ruleRhs : RuleId → Term
| .integrate_delta => void
| .merge_void_left => x
| .merge_void_right => x
| .merge_idem => x
| .rec_zero => x
| .rec_succ => app y (recD x y z)
| .eq_refl => void
| .eq_diff => integrate (merge x y)

instance : OperatorKO7.DependencyPairsFragment.HasFiniteRawFirstOrderView EngineTag Symbol String where
  Rule := Rule
  Term := Term
  termView := OperatorKO7.DependencyPairsFragment.instHasFirstOrderTermViewFOTerm Symbol String
  rules _ := ko7FullStepRules
  lhs := FORule.lhs
  rhs := FORule.rhs

instance : OperatorKO7.DependencyPairsFragment.HasFiniteHeadRuleView EngineTag Symbol :=
  OperatorKO7.DependencyPairsFragment.finiteHeadRuleViewOfRaw EngineTag Symbol String

instance : OperatorKO7.DependencyPairsFragment.HasFiniteCarrierRawFirstOrderView EngineTag Symbol String where
  Rule := RuleId
  ruleFintype := inferInstance
  ruleDecEq := inferInstance
  Term := Term
  termView := OperatorKO7.DependencyPairsFragment.instHasFirstOrderTermViewFOTerm Symbol String
  lhs := ruleLhs
  rhs := ruleRhs

instance : OperatorKO7.DependencyPairsFragment.HasFiniteCarrierHeadView EngineTag Symbol :=
  OperatorKO7.DependencyPairsFragment.finiteCarrierHeadViewOfFiniteCarrierRaw
    EngineTag Symbol String

instance : OperatorKO7.DependencyPairsFragment.HasFiniteCarrierExtractedView EngineTag Symbol :=
  OperatorKO7.DependencyPairsFragment.finiteCarrierExtractedViewOfHeadCarrier
    EngineTag Symbol

/-- Standalone rules packaged through the generic internal-engine view. -/
def ko7Engine : OperatorKO7.DependencyPairsFragment.FiniteFirstOrderEngine Symbol String :=
  OperatorKO7.DependencyPairsFragment.HasFiniteFirstOrderView.toFiniteFirstOrderEngine EngineTag.full

/-- Standalone rules packaged through the finite rule-carrier engine view. -/
noncomputable def ko7CarrierEngine :
    OperatorKO7.DependencyPairsFragment.FiniteCarrierFirstOrderEngine Symbol String :=
  OperatorKO7.DependencyPairsFragment.HasFiniteCarrierFirstOrderView.toFiniteCarrierFirstOrderEngine
    EngineTag.full

/-- Standalone rules exposed through the finite rule-carrier first-order surface. -/
noncomputable def ko7CarrierFirstOrderEngine :
    OperatorKO7.DependencyPairsFragment.FiniteFirstOrderEngine Symbol String :=
  OperatorKO7.DependencyPairsFragment.HasFiniteCarrierFirstOrderView.toFiniteFirstOrderEngine
    (ε := EngineTag) (σ := Symbol) (ν := String) EngineTag.full

/-- Standalone rules packaged through the head and call-head interface. -/
def ko7HeadEngine : OperatorKO7.DependencyPairsFragment.FiniteHeadRuleEngine Symbol :=
  OperatorKO7.DependencyPairsFragment.FiniteHeadRuleEngine.ofRawFirstOrderView
    (ε := EngineTag) (σ := Symbol) (ν := String) EngineTag.full

/-- Standalone rules exposed through the typeclass-level head-view surface. -/
def ko7HeadViewEngine : OperatorKO7.DependencyPairsFragment.FiniteHeadRuleEngine Symbol :=
  OperatorKO7.DependencyPairsFragment.HasFiniteHeadRuleView.toFiniteHeadRuleEngine EngineTag.full

/-- Standalone rules exposed through the finite rule-carrier head-view surface. -/
noncomputable def ko7CarrierHeadEngine : OperatorKO7.DependencyPairsFragment.FiniteHeadRuleEngine Symbol :=
  OperatorKO7.DependencyPairsFragment.HasFiniteCarrierFirstOrderView.toFiniteHeadRuleEngine
    (ε := EngineTag) (σ := Symbol) (ν := String) EngineTag.full

/-- Standalone rules exposed through the finite head-carrier surface. -/
noncomputable def ko7CarrierHeadOnlyEngine : OperatorKO7.DependencyPairsFragment.FiniteHeadRuleEngine Symbol :=
  OperatorKO7.DependencyPairsFragment.HasFiniteCarrierHeadView.toFiniteHeadRuleEngine
    (ε := EngineTag) (σ := Symbol) EngineTag.full

/-- Standalone rules exposed through the finite call-head-data carrier surface. -/
noncomputable def ko7CarrierExtractedGraph :
    OperatorKO7.DependencyPairsFragment.FiniteExtractedCallGraph Symbol :=
  OperatorKO7.DependencyPairsFragment.HasFiniteCarrierExtractedView.extractedCallGraph
    (ε := EngineTag) (κ := Symbol) EngineTag.full

/-- Rule-level call-head records for the standalone first-order model. -/
def ko7FullStepExtractedNodes :=
  ko7Engine.extractedNodes

/-- Call graph constructed from the standalone first-order model. -/
def ko7FullStepExtractedCallGraph :
    OperatorKO7.DependencyPairsFragment.FiniteExtractedCallGraph Symbol :=
  ko7Engine.extractedCallGraph

theorem ko7_full_step_rule_count :
    ko7FullStepRules.size = 8 := by
  decide

theorem ko7_carrier_rule_card :
    Fintype.card RuleId = 8 := by
  decide

theorem ko7_full_step_extracted_node_count :
    ko7FullStepExtractedNodes.size = 8 := by
  decide

theorem ko7_full_step_defined_heads :
    ko7Engine.definedHeads =
      ({ Symbol.integrate, Symbol.merge, Symbol.recD, Symbol.eqW } : Finset Symbol) := by
  decide

theorem ko7_head_engine_defined_heads :
    ko7HeadEngine.definedHeads = ko7Engine.definedHeads := by
  decide

theorem ko7_head_engine_extracted_node_count :
    ko7HeadEngine.extractedNodes.size = 8 := by
  decide

theorem ko7_head_view_engine_matches :
    ko7HeadViewEngine.definedHeads = ko7HeadEngine.definedHeads := by
  decide

/-- The sixth rule-level record retains `recD` after filtering by defined heads. -/
theorem ko7_full_step_has_recD_successor :
    ∃ n ∈ ko7FullStepExtractedNodes.toList,
      n.nodeKey = Symbol.recD ∧ n.succKeys = ({ Symbol.recD } : Finset Symbol) := by
  have hsize : 5 < ko7FullStepExtractedNodes.size := by
    rw [ko7_full_step_extracted_node_count]
    decide
  let n := ko7FullStepExtractedNodes[5]
  refine ⟨n, Array.getElem_mem_toList hsize, rfl, ?_⟩
  have hsucc : n.succKeys =
      (FOTerm.allHeads (app y (recD x y z))).filter (· ∈ ko7Engine.definedHeads) := by
    rfl
  rw [hsucc, ko7_full_step_defined_heads]
  apply Finset.ext
  intro f
  simp [FOTerm.allHeads, app, recD, x, y, z]
  constructor
  · rintro ⟨hf, hd⟩
    rcases hf with rfl | rfl
    · simp at hd
    · rfl
  · intro h
    subst f
    simp

/-- The head-view engine's sixth record retains `recD` as its defined successor. -/
theorem ko7_head_engine_has_recD_successor :
    ∃ n ∈ ko7HeadEngine.extractedNodes.toList,
      n.nodeKey = Symbol.recD ∧ n.succKeys = ({ Symbol.recD } : Finset Symbol) := by
  have hsize : 5 < ko7HeadEngine.extractedNodes.size := by
    rw [ko7_head_engine_extracted_node_count]
    decide
  let n := ko7HeadEngine.extractedNodes[5]
  refine ⟨n, Array.getElem_mem_toList hsize, rfl, ?_⟩
  have hsucc : n.succKeys =
      (FOTerm.allHeads (app y (recD x y z))).filter
        (· ∈ ko7HeadEngine.definedHeads) := by
    rfl
  rw [hsucc, ko7_head_engine_defined_heads, ko7_full_step_defined_heads]
  apply Finset.ext
  intro f
  simp [FOTerm.allHeads, app, recD, x, y, z]
  constructor
  · rintro ⟨hf, hd⟩
    rcases hf with rfl | rfl
    · simp at hd
    · rfl
  · intro h
    subst f
    simp

end OperatorKO7.DependencyPairsFragment.KernelFirstOrder
