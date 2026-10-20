import OperatorKO7.Meta.DependencyPairs_TPDBExtraction

/-!
# Finite first-order rule-head call-graph extraction

From a finite first-order rule array with arbitrary symbol and variable types, this module computes:

- the defined heads (left-hand side root symbols),
- the defined call-heads appearing in right-hand sides, and
- an array-backed direct call graph obtained by matching those heads.

Each input rule contributes at most one node, and `allHeads` retains every defined symbol occurring
anywhere in its right-hand side as a `Finset`, so repeated occurrences of one head collapse. The
declarations do not construct marked dependency pairs or prove semantic correspondence between the
resulting graph and a rewrite relation. The TPDB bridge only converts syntax and proves root-head
preservation.
-/

namespace OperatorKO7.DependencyPairsFragment

/-- Generic first-order term syntax with variables and function symbols. -/
inductive FOTerm (σ ν : Type) : Type
| var : ν → FOTerm σ ν
| app : σ → List (FOTerm σ ν) → FOTerm σ ν

/-- Generic first-order rewrite rule. -/
structure FORule (σ ν : Type) where
  lhs : FOTerm σ ν
  rhs : FOTerm σ ν

namespace FOTerm

variable {σ ν : Type}

/-- Root head symbol of a first-order term, when present. -/
def head? : FOTerm σ ν → Option σ
| .var _ => none
| .app f _ => some f

/-- All function heads appearing anywhere in a first-order term. -/
def allHeads [DecidableEq σ] : FOTerm σ ν → Finset σ
| .var _ => ∅
| .app f args =>
    insert f <| args.foldl (fun acc t => acc ∪ allHeads t) ∅

end FOTerm

namespace FORule

variable {σ ν : Type}

/-- Root head symbol of the left-hand side of a first-order rule, when present. -/
def lhsHead? (r : FORule σ ν) : Option σ :=
  FOTerm.head? r.lhs

end FORule

/-- Rule-head and right-hand-side successor-key data for one first-order rule. -/
structure ExtractedFORuleNode (σ ν : Type) [DecidableEq σ] where
  rule : FORule σ ν
  nodeKey : σ
  succKeys : Finset σ

/-- Defined heads of a finite first-order TRS: the function symbols appearing at rule
roots. -/
def foDefinedHeads {σ ν : Type} [DecidableEq σ] (rules : Array (FORule σ ν)) : Finset σ :=
  rules.foldl
    (fun acc r =>
      match FORule.lhsHead? r with
      | some f => insert f acc
      | none => acc)
    ∅

/-- Build one call-graph node when the rule's left-hand side has a function head. -/
def extractFORuleNode? {σ ν : Type} [DecidableEq σ]
    (defined : Finset σ) (r : FORule σ ν) : Option (ExtractedFORuleNode σ ν) :=
  match FORule.lhsHead? r with
  | none => none
  | some f =>
      some
        { rule := r
          nodeKey := f
          succKeys := (FOTerm.allHeads r.rhs).filter (· ∈ defined) }

/-- Build one call-graph node for each rule with a function-headed left-hand side. -/
def extractFORuleNodes {σ ν : Type} [DecidableEq σ]
    (rules : Array (FORule σ ν)) : Array (ExtractedFORuleNode σ ν) :=
  let defined := foDefinedHeads rules
  rules.filterMap (extractFORuleNode? defined)

/-- Array-backed direct call graph induced by the rule-head data. -/
def foExtractedCallGraph {σ ν : Type} [DecidableEq σ]
    (rules : Array (FORule σ ν)) : FiniteExtractedCallGraph σ :=
  FiniteExtractedCallGraph.ofArrayMap
    (nodes := extractFORuleNodes rules)
    (nodeKey := ExtractedFORuleNode.nodeKey)
    (succKeys := ExtractedFORuleNode.succKeys)

namespace TPDBBridge

open OperatorKO7

/-- Convert a TPDB term to the generic first-order syntax. -/
def term : TpdbTerm → FOTerm String String
| .var x => .var x
| .app f args => .app f (args.map term)

/-- Convert a TPDB rule to the generic first-order syntax. -/
def rule (r : TpdbRule) : FORule String String where
  lhs := term r.lhs
  rhs := term r.rhs

@[simp] theorem term_head?_eq (t : TpdbTerm) :
    FOTerm.head? (term t) = OperatorKO7.DependencyPairsFragment.TpdbTerm.head? t := by
  cases t <;> simp [term, FOTerm.head?, OperatorKO7.DependencyPairsFragment.TpdbTerm.head?]

@[simp] theorem rule_lhsHead?_eq (r : TpdbRule) :
    FORule.lhsHead? (rule r) = OperatorKO7.DependencyPairsFragment.TpdbRule.lhsHead? r := by
  simp [FORule.lhsHead?, rule, OperatorKO7.DependencyPairsFragment.TpdbRule.lhsHead?, term_head?_eq]

end TPDBBridge

namespace KO7FirstOrder

open OperatorKO7

/-- First-order variable shorthands for the KO7 rule-array fixture. -/
def x : FOTerm String String := .var "x"
def y : FOTerm String String := .var "y"
def z : FOTerm String String := .var "z"

/-- First-order constructor and function shorthands for the KO7 rule-array fixture. -/
def void : FOTerm String String := .app "void" []
def delta (t : FOTerm String String) : FOTerm String String := .app "delta" [t]
def integrate (t : FOTerm String String) : FOTerm String String := .app "integrate" [t]
def merge (a b : FOTerm String String) : FOTerm String String := .app "merge" [a, b]
def app (a b : FOTerm String String) : FOTerm String String := .app "app" [a, b]
def recD (b s n : FOTerm String String) : FOTerm String String := .app "recD" [b, s, n]
def eqW (a b : FOTerm String String) : FOTerm String String := .app "eqW" [a, b]

/-- Unconditional first-order rule-array over-approximation of the KO7 root rules. The final `eqW`
rule omits the disequality premise of the guarded source constructor, and this module proves no
equivalence with the original `Step` relation. -/
def ko7FullStepFORules : Array (FORule String String) :=
  #[ ⟨integrate (delta x), void⟩
   , ⟨merge void x, x⟩
   , ⟨merge x void, x⟩
   , ⟨merge x x, x⟩
   , ⟨recD x y void, x⟩
   , ⟨recD x y (delta z), app y (recD x y z)⟩
   , ⟨eqW x x, void⟩
   , ⟨eqW x y, integrate (merge x y)⟩ ]

/-- Rule-head nodes computed from `ko7FullStepFORules`. -/
def ko7FullStepExtractedNodes : Array (ExtractedFORuleNode String String) :=
  extractFORuleNodes ko7FullStepFORules

/-- Direct key-matching call graph computed from `ko7FullStepFORules`. -/
def ko7FullStepExtractedCallGraph : FiniteExtractedCallGraph String :=
  foExtractedCallGraph ko7FullStepFORules

theorem ko7_full_step_extracted_node_count :
    ko7FullStepExtractedNodes.size = 8 := by
  decide

theorem ko7_full_step_defined_heads :
    foDefinedHeads ko7FullStepFORules =
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
      (FOTerm.allHeads (app y (recD x y z))).filter
        (· ∈ foDefinedHeads ko7FullStepFORules) := by
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

end KO7FirstOrder

end OperatorKO7.DependencyPairsFragment
