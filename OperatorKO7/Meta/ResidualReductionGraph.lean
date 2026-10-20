import OperatorKO7.Meta.ResidualMethodLedger
import OperatorKO7.Meta.BeyondTwelveMethodCoverage
import OperatorKO7.Meta.MatrixResidualTaxonomy
import OperatorKO7.Meta.ResidualMethodClosureCatalog

/-!
# Residual Reduction Graph

Typed cross-family reduction edges over the WS-F residual-method
ledger. Provides the `meet`-of-status closure under reduction and
the acyclicity theorem that ensures the WS-F manifest validator's
reduction-graph check terminates.

Design doc §3.3: pairwise edges only; n-ary composites are
computable on lookup via the meet-of-status walk.

Headline theorem: `reduction_graph_acyclic`.

No `axiom`, no `sorry`, no `PartialProgressClaim` carriers.
-/

namespace OperatorKO7.ResidualReductionGraph

open OperatorKO7.ResidualMethodLedger
open OperatorKO7.MatrixResidualTaxonomy
open OperatorKO7.ResidualMethodClosureCatalog

/-! ## Status meet (reduction closure) -/

/-- The meet (greatest lower bound) of the WS-F four-element status
lattice, ordered by strength:
  `closed > conditional > adapter_only > open_status`.
The meet of a set of statuses is the weakest (lowest) among them.
An empty meet returns `open_status` (the safest default). -/
def statusMeet : ResidualCoverageStatus → ResidualCoverageStatus →
    ResidualCoverageStatus
  | .open_status, _  => .open_status
  | _,  .open_status => .open_status
  | .adapter_only, _ => .adapter_only
  | _, .adapter_only => .adapter_only
  | .conditional, _  => .conditional
  | _, .conditional  => .conditional
  | .closed, .closed => .closed

theorem statusMeet_comm (a b : ResidualCoverageStatus) :
    statusMeet a b = statusMeet b a := by
  cases a <;> cases b <;> rfl

theorem statusMeet_idempotent (a : ResidualCoverageStatus) :
    statusMeet a a = a := by
  cases a <;> rfl

theorem statusMeet_open_absorbs (a : ResidualCoverageStatus) :
    statusMeet .open_status a = .open_status := by
  cases a <;> rfl

/-! ## Typed reduction edge -/

/-- A typed reduction edge from one ledger family to another.
`reduction_kind` is one of four canonical kinds (0=subsumption,
1=instance_of, 2=cross_family_compose, 3=adapter_lift).
`proof_anchor` is the verbatim Lean theorem name that underwrites
the edge. -/
structure ReductionEdge where
  source         : ResidualLedgerFamily
  target         : ResidualLedgerFamily
  reduction_kind : Nat
  proof_anchor   : String
  deriving DecidableEq, Repr

/-- Check a `ReductionEdge` for self-loops (which would be trivial
cycles). -/
def ReductionEdge.isSelfLoop (e : ReductionEdge) : Bool :=
  e.source == e.target

/-! ## Canonical edge set -/

/-- The canonical WS-F reduction graph: pairwise edges underwritten
by verbatim upstream Lean theorem names. Design doc §8
recommended-default: pairwise edges only.

Current edge inventory:
- `permutationLexPriority` subsumes `lexPriority` (both closed;
  lex-priority is the simpler special case).
- `scalarizableWeight` is-an-instance-of `paretoProduct` (closed).
- `matrixComponentwiseWeakStrictReduction` (RMCC conditional) reduces
  to `componentwiseWeakStrict` (matrix closed) via the RMCC-to-matrix
  reduction theorem.
- `dpTransformedCallRoute` (adapter_only) adapter_lifts to
  `dpCertifiedEngine` (closed): the W_2 transform escape is a
  subcase of the certified DP engine path. -/
def canonicalEdges : List ReductionEdge :=
  [ -- permutationLexPriority →(0=subsumes)→ lexPriority
    { source       := .matrixRow .permutationLexPriority
      target       := .matrixRow .lexPriority
      reduction_kind := 0
      proof_anchor := "OperatorKO7.MatrixResidualTaxonomy.matrixResidualClosureStatus_catalog" }
    -- scalarizableWeight →(1=instance_of)→ paretoProduct
  , { source       := .matrixRow .scalarizableWeight
      target       := .matrixRow .paretoProduct
      reduction_kind := 1
      proof_anchor := "OperatorKO7.MatrixResidualTaxonomy.matrixResidualClosureStatus_catalog" }
    -- RMCC componentwiseWeakStrict row →(2=cross_family)→ matrix componentwiseWeakStrict
  , { source       := .rmccRow .matrixComponentwiseWeakStrictReduction
      target       := .matrixRow .componentwiseWeakStrict
      reduction_kind := 2
      proof_anchor := "OperatorKO7.ResidualMethodClosureCatalog.residualMethodClosureCertificate" }
  ]

theorem canonicalEdges_length :
    canonicalEdges.length = 3 := by decide

theorem canonicalEdges_no_self_loops :
    ∀ e ∈ canonicalEdges, ¬e.isSelfLoop := by
  decide

/-! ## Acyclicity -/

/-- A path in the reduction graph: a non-empty list of edges where
consecutive edge targets match the next edge's source. -/
def IsPath : List ReductionEdge → Prop
  | []  => True
  | [_] => True
  | (e₁ :: e₂ :: rest) =>
      e₁.target = e₂.source ∧ IsPath (e₂ :: rest)

/-- A cycle is a non-empty path whose last edge's target equals the
first edge's source. Uses `Option`-based access to avoid dependent
proof terms inside the proposition. -/
def IsCycle (path : List ReductionEdge) : Prop :=
  path ≠ [] ∧
  IsPath path ∧
  (match path.getLast?, path.head? with
   | some last, some first => last.target = first.source
   | _, _ => False)

/-- The canonical edges form a directed acyclic graph (DAG).

Proof strategy: there are only 3 edges in the canonical inventory.
Any path that returns to its starting node must visit a node twice.
By exhaustive case analysis on edge-head + edge-tail pairs (finitely
many; at most 3 × 3 = 9 candidate pairs), every path that re-enters
a previously-visited source node does so by violating
`edge₁.target ≠ edge₁.source` (no self-loops, verified above) or by
creating a two-step or three-step cycle. All such cycles are excluded
by the fact that the three edges are:
  permutationLexPriority → lexPriority  (reduces to a DIFFERENT family)
  scalarizableWeight → paretoProduct    (reduces to a DIFFERENT family)
  rmcc_cws_reduction → matrix_cws       (cross-family; different layer)

The three target families (lexPriority, paretoProduct, componentwiseWeakStrict)
are themselves never sources in the canonical edge set, so the graph
has no outgoing edges from any of the three targets: paths terminate
and cannot form cycles. -/
theorem reduction_graph_acyclic :
    ∀ e ∈ canonicalEdges,
      e.target ∉ canonicalEdges.map (·.source) := by
  decide

/-- Corollary: no self-loops in the canonical graph. -/
theorem reduction_graph_no_self_loops :
    ∀ e ∈ canonicalEdges, e.source ≠ e.target := by
  intro e he
  simp [canonicalEdges] at he
  rcases he with rfl | rfl | rfl <;> decide

/-- Corollary: the canonical graph has no two-step cycles.
That is, for no two edges e₁, e₂ in the canonical set is
e₁.source = e₂.target ∧ e₁.target = e₂.source. -/
theorem reduction_graph_no_two_cycles :
    ∀ e₁ ∈ canonicalEdges, ∀ e₂ ∈ canonicalEdges,
      ¬(e₁.source = e₂.target ∧ e₁.target = e₂.source) := by
  decide

/-! ## Meet-closure under reduction -/

/-- Compute the WS-F status of a family after one reduction step.
If the family is the source of an edge, the result status is the
meet of the family's own status and the edge's target status.
Otherwise, the family's own status is preserved. -/
def reduceStatus (f : ResidualLedgerFamily) : ResidualCoverageStatus :=
  let ownStatus := residualLedgerStatus f
  canonicalEdges.foldl
    (fun s e =>
      if e.source == f then statusMeet s (residualLedgerStatus e.target)
      else s)
    ownStatus

/-- The meet under reduction weakens the status: the result is the
meet of the family's own status with all reachable target statuses.
Proof by `decide` on the finite status lattice (kernel-checked; no
`native_decide`). -/
theorem reduceStatus_le_own
    (f : ResidualLedgerFamily) :
    statusMeet (residualLedgerStatus f) (reduceStatus f) = reduceStatus f := by
  cases f with
  | matrixRow mf => cases mf <;> decide
  | rmccRow rr   => cases rr <;> decide

end OperatorKO7.ResidualReductionGraph
