import OperatorKO7.Meta.ConfessionMethod
import OperatorKO7.Meta.ConfessionMethod_DP

/-!
# Confession Method Instance: Size-Change Termination (SCT)

Size-Change Termination (Lee, Jones, Ben-Amram 2001) constructs size-change
graphs for each recursive call site and checks that every infinite call
multipath contains an infinitely descending thread.

For the step-duplicating schema, the standard SCT reading is:
- There is one recursive call: `recur(b, s, succ(n))` calls `recur(b, s, n)`
- The size-change graph has one strict arc: argument 3 decreases strictly (↓)
- Arguments 1 and 2 are non-increasing (≥)
- Every call path passes through this single graph, whose argument-3 thread
  descends strictly at each call

The SCT rank on this schema is the same counter-projection rank used by
dependency pairs. What differs is:
- **Extraction:** SCT builds a call graph from the rule structure; DP extracts
  marked dependency-pair symbols
- **Descent check:** SCT checks for an infinitely descending thread in the
  graph monoid closure; DP applies the subterm criterion on a specific
  argument position
- **Soundness license:** Lee-Jones-Ben-Amram 2001; the DP route carries the
  Arts-Giesl 2000 license

The Lean scope covers the single graph, its one-step composition summary, the
persistent counter thread, equality with the DP counter rank, and local
orientation of the duplicating call. General SCT soundness, graph-monoid
closures, and idempotent analysis for multi-call systems belong to the cited
external theory recorded by the license tag.
-/

namespace OperatorKO7.ConfessionMethodFamily

open OperatorKO7.Trace
open OperatorKO7.StepDuplicating
open OperatorKO7.StepDuplicating.StepDuplicatingSchema
open OperatorKO7.CompositionalImpossibility

/-- A size-change arc records the relationship between a caller argument
    and a callee argument across a recursive call. -/
inductive SCArc
  | strictDecrease   -- ↓ : callee value is strictly smaller than caller value
  | nonIncreasing    -- ≥ : callee value is at most the caller value
  | untracked        -- relation left unspecified for this pair
  deriving DecidableEq, Repr

/-- Strength ordering on SCT arcs for summary/composition purposes. -/
def SCArc.join : SCArc → SCArc → SCArc
  | .strictDecrease, _ => .strictDecrease
  | _, .strictDecrease => .strictDecrease
  | .nonIncreasing, _ => .nonIncreasing
  | _, .nonIncreasing => .nonIncreasing
  | .untracked, .untracked => .untracked

/-- Composition of two size-change arc summaries. Any strict descent on either
    side remains strict; otherwise two non-increasing steps remain
    non-increasing; any other combination is treated as untracked. -/
def SCArc.comp : SCArc → SCArc → SCArc
  | .strictDecrease, .strictDecrease => .strictDecrease
  | .strictDecrease, .nonIncreasing => .strictDecrease
  | .nonIncreasing, .strictDecrease => .strictDecrease
  | .nonIncreasing, .nonIncreasing => .nonIncreasing
  | _, _ => .untracked

/-- A size-change graph for a function with `arity` arguments is a matrix
    of arcs from caller argument positions to callee argument positions.
    Entry `(i, j)` records the size-change relation between the caller's
    `i`-th argument and the callee's `j`-th argument. -/
structure SizeChangeGraph (arity : Nat) where
  arcs : Fin arity → Fin arity → SCArc

/-- Single-step composition summary specialized to the arity-3 schema case. -/
def SizeChangeGraph.comp3 (G H : SizeChangeGraph 3) : SizeChangeGraph 3 where
  arcs := fun i j =>
    SCArc.join
      (SCArc.join
        (SCArc.comp (G.arcs i ⟨0, by decide⟩) (H.arcs ⟨0, by decide⟩ j))
        (SCArc.comp (G.arcs i ⟨1, by decide⟩) (H.arcs ⟨1, by decide⟩ j)))
      (SCArc.comp (G.arcs i ⟨2, by decide⟩) (H.arcs ⟨2, by decide⟩ j))

/-- The size-change graph for the schema's single recursive call site.

    The schema has arity 3 for the recursor:
    - Position 0 (b, the base value): caller b maps to callee b (non-increasing)
    - Position 1 (s, the step argument): caller s maps to callee s (non-increasing)
    - Position 2 (n, the counter): caller succ(n) maps to callee n (strict decrease)

    Off-diagonal entries are untracked, leaving cross-argument relations
    unspecified. -/
def schemaRecCallGraph : SizeChangeGraph 3 where
  arcs := fun i j =>
    if i = j then
      if i.val = 2 then SCArc.strictDecrease
      else SCArc.nonIncreasing
    else SCArc.untracked

/-- The schema's size-change graph has a strict decrease on the diagonal
    entry for argument position 2 (the counter). -/
theorem schemaRecCallGraph_counter_descent :
    schemaRecCallGraph.arcs ⟨2, by omega⟩ ⟨2, by omega⟩ = SCArc.strictDecrease := by
  decide

/-- Argument positions 0 and 1 are non-increasing on the diagonal. -/
theorem schemaRecCallGraph_base_nonincreasing :
    schemaRecCallGraph.arcs ⟨0, by omega⟩ ⟨0, by omega⟩ = SCArc.nonIncreasing := by
  decide

theorem schemaRecCallGraph_step_nonincreasing :
    schemaRecCallGraph.arcs ⟨1, by omega⟩ ⟨1, by omega⟩ = SCArc.nonIncreasing := by
  decide

/-- Self-composition of the schema graph preserves the strict counter diagonal. The two
non-increasing diagonal computations are recorded separately below. The full graph-monoid
closure remains outside this calculation. -/
theorem schemaRecCallGraph_comp3_counter_descent :
    (SizeChangeGraph.comp3 schemaRecCallGraph schemaRecCallGraph).arcs
      ⟨2, by omega⟩ ⟨2, by omega⟩ = SCArc.strictDecrease := by
  decide

theorem schemaRecCallGraph_comp3_base_nonincreasing :
    (SizeChangeGraph.comp3 schemaRecCallGraph schemaRecCallGraph).arcs
      ⟨0, by omega⟩ ⟨0, by omega⟩ = SCArc.nonIncreasing := by
  decide

theorem schemaRecCallGraph_comp3_step_nonincreasing :
    (SizeChangeGraph.comp3 schemaRecCallGraph schemaRecCallGraph).arcs
      ⟨1, by omega⟩ ⟨1, by omega⟩ = SCArc.nonIncreasing := by
  decide

/-- Closure summary object for the single-call SCT route. -/
structure SCTClosureSummary where
  compositeGraph : SizeChangeGraph 3
  compositeCounterDescent :
    compositeGraph.arcs ⟨2, by decide⟩ ⟨2, by decide⟩ = SCArc.strictDecrease
  compositeBaseNonIncreasing :
    compositeGraph.arcs ⟨0, by decide⟩ ⟨0, by decide⟩ = SCArc.nonIncreasing
  compositeStepNonIncreasing :
    compositeGraph.arcs ⟨1, by decide⟩ ⟨1, by decide⟩ = SCArc.nonIncreasing

/-- The concrete closure/composition summary for the schema graph. -/
def schemaSCTClosureSummary : SCTClosureSummary where
  compositeGraph := SizeChangeGraph.comp3 schemaRecCallGraph schemaRecCallGraph
  compositeCounterDescent := by simpa using schemaRecCallGraph_comp3_counter_descent
  compositeBaseNonIncreasing := by simpa using schemaRecCallGraph_comp3_base_nonincreasing
  compositeStepNonIncreasing := by simpa using schemaRecCallGraph_comp3_step_nonincreasing

/-- Local single-graph witness predicate used in this module: the graph has a
    strict diagonal arc. The schema below also supplies a constant counter
    thread and a self-composition summary. -/
def sctSatisfied {n : Nat} (G : SizeChangeGraph n) : Prop :=
  ∃ i : Fin n, G.arcs i i = SCArc.strictDecrease

/-- The schema graph satisfies this module's local witness predicate at the counter coordinate. -/
theorem schema_sct_satisfied : sctSatisfied schemaRecCallGraph :=
  ⟨⟨2, by omega⟩, schemaRecCallGraph_counter_descent⟩

/-- The counter is the unique strict diagonal entry. -/
theorem schema_sct_unique_descent :
    ∀ i : Fin 3, schemaRecCallGraph.arcs i i = SCArc.strictDecrease → i = ⟨2, by omega⟩ := by
  intro i h
  match i with
  | ⟨0, _⟩ => simp [schemaRecCallGraph] at h
  | ⟨1, _⟩ => simp [schemaRecCallGraph] at h
  | ⟨2, _⟩ => rfl

/-- A route-local SCT witness object for the single-call schema. -/
structure SCTWitness where
  graph : SizeChangeGraph 3
  satisfied : sctSatisfied graph
  uniqueStrictDescent :
    ∀ i : Fin 3, graph.arcs i i = SCArc.strictDecrease → i = ⟨2, by omega⟩

/-- The schema's concrete SCT witness. -/
def schemaSCTWitness : SCTWitness where
  graph := schemaRecCallGraph
  satisfied := schema_sct_satisfied
  uniqueStrictDescent := schema_sct_unique_descent

/-- The local SCT witness identifies the counter coordinate as the sole strict
    diagonal entry. -/
theorem sctWitness_selects_counter_coordinate :
    ∀ i : Fin 3,
      schemaSCTWitness.graph.arcs i i = SCArc.strictDecrease →
      i = ⟨2, by omega⟩ :=
  schemaSCTWitness.uniqueStrictDescent

/-- A separately defined counter-depth rank associated with the local SCT route. Its definition
follows the recursive counter. Route-evidence packaging pairs it with the graph coordinate;
general SCT soundness remains external. -/
@[simp] def sctRankFn : Trace → Nat
  | void        => 0
  | delta t     => sctRankFn t + 1
  | integrate _ => 0
  | merge _ _   => 0
  | app _ _     => 0
  | recΔ _ _ n  => sctRankFn n
  | eqW _ _     => 0

/-- The local SCT construction yields the same counter-depth rank function as
    the DP route. -/
theorem sctRankFn_eq_dpProjection :
    sctRankFn = dpProjection := by
  funext t
  induction t <;> simp [sctRankFn, dpProjection, *]

/-- Package the fixed `sctRankFn` equations as a confession-core witness. The graph fields of
the supplied `SCTWitness` are unused by this definition. -/
def SCTWitness.toConfessionCoreWitness (_W : SCTWitness) : ConfessionCoreWitness ko7Schema where
  rank := sctRankFn
  rank_base := by rfl
  rank_succ := by intro t; rfl
  rank_wrap := by intro x y; rfl
  rank_recur := by intro b s n; rfl

/-- The projection rank derived from the SCT witness. -/
def sctDerivedRank : ProjectionRank ko7Schema where
  rank := sctRankFn
  rank_base := by rfl
  rank_succ := by intro t; rfl
  rank_wrap := by intro x y; rfl
  rank_recur := by intro b s n; rfl

/-- The derived SCT counter rank strictly orients the schema's duplicating call. -/
theorem sctDerivedRank_orients_dup_step (b s n : Trace) :
    sctDerivedRank.rank (ko7Schema.wrap s (ko7Schema.recur b s n)) <
      sctDerivedRank.rank (ko7Schema.recur b s (ko7Schema.succ n)) := by
  exact projection_orients_dup_step sctDerivedRank b s n

/-- The SCT route converges to the same rank function as the canonical DP
    projection core. -/
theorem sctDerivedRank_eq_dp_core :
    sctDerivedRank.rank = dpProjectionRank.rank := by
  simpa [sctDerivedRank, dpProjectionRank] using sctRankFn_eq_dpProjection

/-- The SCT route induces the same projection-rank structure as the canonical
    DP core. -/
theorem sctDerivedRank_eq_dpProjectionRank :
    sctDerivedRank = dpProjectionRank := by
  ext t
  simpa [sctDerivedRank, dpProjectionRank] using congrFun sctRankFn_eq_dpProjection t

/-- The SCT witness forgets the wrapper payload at the level of the
    intermediate confession core. -/
theorem sctWitness_forgets_wrapper_payload :
    ∀ x y : Trace,
      schemaSCTWitness.toConfessionCoreWitness.rank (app x y) = 0 := by
  intro x y
  rfl

/-- The SCT witness induces the same confession core as the canonical DP
    route. -/
theorem sctWitness_toConfessionCoreWitness_eq_core :
    schemaSCTWitness.toConfessionCoreWitness.toProjectionRank = dpProjectionRank := by
  ext t
  simpa [SCTWitness.toConfessionCoreWitness, dpProjectionRank] using
    congrFun sctRankFn_eq_dpProjection t

/-- Package `sctDerivedRank` with the Lee-Jones-Ben-Amram license tag. The graph witness and
general SCT soundness theorem remain separate from this definition. -/
def sctConfession : ConfessionMethod ko7Schema where
  toProjectionRank := sctDerivedRank
  license := SoundnessLicense.leeJonesBenAmram2001

/-- The exported SCT confession instance is routed through the derived
    SCT projection rank. -/
theorem sctConfession_is_derived :
    sctConfession.toProjectionRank = sctDerivedRank := rfl

/-- On the step-duplicating schema, the SCT and DP constructions produce the
same counter-depth rank. -/
theorem sct_eq_dp_rank :
    sctConfession.rank = dpConfession.rank := by
  simpa [sctConfession, dpConfession, sctDerivedRank, dpProjectionRank] using
    sctRankFn_eq_dpProjection

/-- Route-local record combining the fixed schema graph, its three diagonal facts, a constant
counter-coordinate thread through repeated uses of that graph, and the self-composition summary. -/
structure SCTRouteEvidence where
  witness : SCTWitness
  descendingThread :
    witness.graph.arcs ⟨2, by decide⟩ ⟨2, by decide⟩ = SCArc.strictDecrease
  baseDiagonalNonIncreasing :
    witness.graph.arcs ⟨0, by decide⟩ ⟨0, by decide⟩ = SCArc.nonIncreasing
  stepDiagonalNonIncreasing :
    witness.graph.arcs ⟨1, by decide⟩ ⟨1, by decide⟩ = SCArc.nonIncreasing
  constantCounterThread :
    Nat → Fin 3
  constantCounterThread_is_counter :
    ∀ k, constantCounterThread k = ⟨2, by decide⟩
  thread_descends_at_every_step :
    ∀ k,
      witness.graph.arcs (constantCounterThread k) (constantCounterThread (k + 1)) =
        SCArc.strictDecrease
  closureSummary : SCTClosureSummary

/-- The concrete route-local SCT evidence for the KO7 schema graph. -/
def schemaSCTRouteEvidence : SCTRouteEvidence where
  witness := schemaSCTWitness
  descendingThread := schemaRecCallGraph_counter_descent
  baseDiagonalNonIncreasing := schemaRecCallGraph_base_nonincreasing
  stepDiagonalNonIncreasing := schemaRecCallGraph_step_nonincreasing
  constantCounterThread := fun _ => ⟨2, by decide⟩
  constantCounterThread_is_counter := by
    intro k
    rfl
  thread_descends_at_every_step := by
    intro k
    simpa using schemaRecCallGraph_counter_descent
  closureSummary := schemaSCTClosureSummary

/-- Discard the graph-specific fields and retain the fixed counter-rank equations packaged by
the witness adapter. -/
def SCTRouteEvidence.toRouteEvidence (E : SCTRouteEvidence) : RouteEvidence ko7Schema where
  rank := E.witness.toConfessionCoreWitness.rank
  rank_base := E.witness.toConfessionCoreWitness.rank_base
  rank_succ := E.witness.toConfessionCoreWitness.rank_succ
  rank_wrap := E.witness.toConfessionCoreWitness.rank_wrap
  rank_recur := E.witness.toConfessionCoreWitness.rank_recur

/-- The concrete SCT route evidence packaged through the generic adapter. -/
abbrev schemaSCTGenericRouteEvidence : RouteEvidence ko7Schema :=
  schemaSCTRouteEvidence.toRouteEvidence

/-- The fixed counter rank reachable through the route-evidence adapter satisfies the four
generic projection-profile predicates. The proof uses only the fixed rank equations; the
graph-specific fields remain unused. -/
theorem sctRouteEvidence_implies_semantic_profile :
    NormalizedAtBase ko7Schema schemaSCTRouteEvidence.witness.toConfessionCoreWitness.rank
    ∧ TracksSuccessorDepth ko7Schema schemaSCTRouteEvidence.witness.toConfessionCoreWitness.rank
    ∧ ForgetsWrapperPayload ko7Schema schemaSCTRouteEvidence.witness.toConfessionCoreWitness.rank
    ∧ FollowsRecursiveCounter ko7Schema schemaSCTRouteEvidence.witness.toConfessionCoreWitness.rank := by
  exact schemaSCTRouteEvidence.witness.toConfessionCoreWitness.satisfies_semantic_profile

/-- The fixed counter rank packaged by `schemaSCTWitness` satisfies the four generic
projection-profile predicates. -/
theorem sctWitness_has_semantic_profile :
    NormalizedAtBase ko7Schema schemaSCTWitness.toConfessionCoreWitness.rank
    ∧ TracksSuccessorDepth ko7Schema schemaSCTWitness.toConfessionCoreWitness.rank
    ∧ ForgetsWrapperPayload ko7Schema schemaSCTWitness.toConfessionCoreWitness.rank
    ∧ FollowsRecursiveCounter ko7Schema schemaSCTWitness.toConfessionCoreWitness.rank := by
  exact schemaSCTWitness.toConfessionCoreWitness.satisfies_semantic_profile

end OperatorKO7.ConfessionMethodFamily
