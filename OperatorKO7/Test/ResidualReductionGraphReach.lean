import OperatorKO7.Meta.ResidualReductionGraph

namespace ResidualReductionGraphReach

open OperatorKO7.ResidualReductionGraph
open OperatorKO7.ResidualMethodLedger

#check statusMeet
#check statusMeet_comm
#check statusMeet_idempotent
#check statusMeet_open_absorbs
#check ReductionEdge
#check canonicalEdges
#check canonicalEdges_length
#check canonicalEdges_no_self_loops
#check reduction_graph_acyclic
#check reduction_graph_no_self_loops
#check reduction_graph_no_two_cycles
#check reduceStatus
#check reduceStatus_le_own

-- R.4 headline: the canonical reduction graph is acyclic
-- (no edge has its target as a source in the canonical edge set)
example : ∀ e ∈ canonicalEdges,
    e.target ∉ canonicalEdges.map (·.source) :=
  reduction_graph_acyclic

-- No self-loops
example : ∀ e ∈ canonicalEdges, e.source ≠ e.target :=
  reduction_graph_no_self_loops

-- No two-cycles
example : ∀ e₁ ∈ canonicalEdges, ∀ e₂ ∈ canonicalEdges,
    ¬(e₁.source = e₂.target ∧ e₁.target = e₂.source) :=
  reduction_graph_no_two_cycles

-- The canonical graph has exactly 3 edges
example : canonicalEdges.length = 3 := canonicalEdges_length

-- Status meet properties
example : statusMeet .closed .open_status = .open_status := by rfl
example : statusMeet .closed .conditional = .conditional := by rfl
example : statusMeet .adapter_only .conditional = .adapter_only := by rfl
example : statusMeet .closed .closed = .closed := by rfl

-- Meet commutativity and idempotence
example (a b : ResidualCoverageStatus) :
    statusMeet a b = statusMeet b a :=
  statusMeet_comm a b

example (a : ResidualCoverageStatus) :
    statusMeet a a = a :=
  statusMeet_idempotent a

end ResidualReductionGraphReach
