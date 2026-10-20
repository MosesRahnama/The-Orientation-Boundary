import OperatorKO7.Meta.DependencyPairs_ExtractedCallGraph
import OperatorKO7.Meta.TPDB_Export

/-!
# Rule-Head Call Graph from TPDB Rules

This module connects the finite SCC search surface to the concrete TPDB / TTT2 export
syntax already used in the artifact. Starting from a finite list of first-order TPDB
rules, it computes:

- the set of defined heads (left-hand side root symbols),
- the defined call-heads appearing in each right-hand side, and
- the corresponding array-backed rule-head call graph.

This is a rule-level abstraction, not marked dependency-pair extraction: it creates one
record per function-headed rule, and `Finset` storage collapses repeated head occurrences.
Semantic adequacy and SCC existence for an arbitrary TRS remain separate obligations.
-/

namespace OperatorKO7.DependencyPairsFragment

open OperatorKO7

namespace TpdbTerm

/-- Root head symbol of a TPDB term, when present. -/
def head? : TpdbTerm → Option String
| .var _ => none
| .app f _ => some f

/-- All function heads appearing anywhere in a TPDB term. -/
def allHeads : TpdbTerm → Finset String
| .var _ => ∅
| .app f args =>
    insert f <| args.foldl (fun acc t => acc ∪ allHeads t) ∅

end TpdbTerm

namespace TpdbRule

/-- Root head symbol of the left-hand side of a TPDB rule, when present. -/
def lhsHead? (r : TpdbRule) : Option String :=
  TpdbTerm.head? r.lhs

end TpdbRule

/-- Rule-head call-graph data for one TPDB rule. -/
structure ExtractedTpdbNode where
  rule : TpdbRule
  nodeKey : String
  succKeys : Finset String

/-- Defined heads of a finite TPDB rule set: the function symbols appearing at rule roots. -/
def tpdbDefinedHeads (rules : Array TpdbRule) : Finset String :=
  rules.foldl
    (fun acc r =>
      match TpdbRule.lhsHead? r with
      | some f => insert f acc
      | none => acc)
    ∅

/-- Build one rule-head record from a TPDB rule whose left-hand side has a function head.
The successor keys are the defined heads occurring in the right-hand side. -/
def extractTpdbNode? (defined : Finset String) (r : TpdbRule) : Option ExtractedTpdbNode :=
  match TpdbRule.lhsHead? r with
  | none => none
  | some f =>
      some
        { rule := r
          nodeKey := f
          succKeys := (TpdbTerm.allHeads r.rhs).filter (· ∈ defined) }

/-- Rule-head call-graph records for a finite TPDB rule set. -/
def extractTpdbNodes (rules : Array TpdbRule) : Array ExtractedTpdbNode :=
  let defined := tpdbDefinedHeads rules
  rules.filterMap (extractTpdbNode? defined)

/-- Array-backed rule-head call graph induced by a finite TPDB rule list. -/
def tpdbExtractedCallGraph (rules : Array TpdbRule) : FiniteExtractedCallGraph String :=
  FiniteExtractedCallGraph.ofArrayMap
    (nodes := extractTpdbNodes rules)
    (nodeKey := ExtractedTpdbNode.nodeKey)
    (succKeys := ExtractedTpdbNode.succKeys)

/-- Concrete rule-head records for the exported KO7 full-step TRS. -/
def ko7FullStepExtractedNodes : Array ExtractedTpdbNode :=
  extractTpdbNodes ko7FullStepTpdbRules.toArray

/-- Concrete rule-head call graph for the exported KO7 full-step TRS. -/
def ko7FullStepExtractedCallGraph : FiniteExtractedCallGraph String :=
  tpdbExtractedCallGraph ko7FullStepTpdbRules.toArray

theorem ko7_full_step_extracted_node_count :
    ko7FullStepExtractedNodes.size = 8 := by
  decide

theorem ko7_full_step_defined_heads :
    tpdbDefinedHeads ko7FullStepTpdbRules.toArray =
      ({ "integrate", "merge", "recD", "eqW" } : Finset String) := by
  decide

/-- The recursive rule supplies the sixth extracted node. Its right-hand side
contains `app` and `recD`; filtering by defined heads retains `recD`. -/
theorem ko7_full_step_has_recD_successor :
    ∃ n ∈ ko7FullStepExtractedNodes.toList,
      n.nodeKey = "recD" ∧ n.succKeys = ({ "recD" } : Finset String) := by
  have hsize : 5 < ko7FullStepExtractedNodes.size := by
    rw [ko7_full_step_extracted_node_count]
    decide
  let n := ko7FullStepExtractedNodes[5]
  refine ⟨n, Array.getElem_mem_toList hsize, rfl, ?_⟩
  have hsucc : n.succKeys =
      (TpdbTerm.allHeads (tapp ty (trecD tx ty tz))).filter
        (· ∈ tpdbDefinedHeads ko7FullStepTpdbRules.toArray) := by
    rfl
  rw [hsucc, ko7_full_step_defined_heads]
  apply Finset.ext
  intro f
  simp [TpdbTerm.allHeads, tapp, trecD, tx, ty, tz]
  constructor
  · rintro ⟨hf, hd⟩
    rcases hf with rfl | rfl
    · simp at hd
    · rfl
  · intro h
    subst f
    simp

end OperatorKO7.DependencyPairsFragment
