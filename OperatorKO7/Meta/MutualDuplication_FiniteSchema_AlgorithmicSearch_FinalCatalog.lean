import OperatorKO7.Meta.MutualDuplication_FiniteSchema_AlgorithmicSearch
import OperatorKO7.Meta.MutualDuplication_FiniteSchema_FinalCatalog
import OperatorKO7.Meta.MutualDuplication_FiniteSchema_Closeout

/-!
# Final H3 Algorithmic Search Catalog

This module packages the executable H3 finite graph-search layer into one theorem-backed
surface. The executable program is still intentionally narrow: it searches only over the
explicit encoded finite edge space and transports successful results into the existing
graph-search and barrier stack.
-/

namespace OperatorKO7.MutualDuplicationFiniteSchema

open OperatorKO7.StepDuplicating

/-- Final paper-facing H3 catalog for the executable finite encoded search space. -/
structure FiniteCycleAlgorithmicSearchFinalCatalog
    {k : Nat} (S : FiniteCycleGraphSearch.EncodedSearchSpace k) : Prop where
  executable_search_sound :
    ∀ {W : FiniteCycleGraphSearch.EncodedSearchSpace.CycleCandidate S},
      FiniteCycleGraphSearch.EncodedSearchSpace.searchCycle? S = some W →
        FiniteCycleMutualDuplicationFinalCatalog W.toGraphSearchCertificate
  finite_completeness :
    (∀ i : Fin (k + 1),
      FiniteCycleGraphSearch.EncodedSearchSpace.Edge S i (FiniteCycleBuilder.advance i)) →
        ∃ W : FiniteCycleGraphSearch.EncodedSearchSpace.CycleCandidate S,
          FiniteCycleGraphSearch.EncodedSearchSpace.searchCycle? S = some W
  missing_successor_edge_boundary :
    FiniteCycleGraphSearch.EncodedSearchSpace.searchCycle? S = none →
      Nonempty (FiniteCycleGraphSearch.EncodedSearchSpace.MissingSuccessorEdgeStatus S)

/-- Canonical final catalog for the executable finite encoded H3 search space. -/
theorem finite_cycle_algorithmic_search_final_catalog
    {k : Nat} (S : FiniteCycleGraphSearch.EncodedSearchSpace k) :
    FiniteCycleAlgorithmicSearchFinalCatalog S := by
  refine ⟨?_, ?_, ?_⟩
  · intro W hsearch
    exact finite_cycle_mutual_duplication_final_catalog W.toGraphSearchCertificate
  · intro hall
    exact FiniteCycleGraphSearch.EncodedSearchSpace.exists_searchCycle?_eq_some hall
  · intro hnone
    exact
      (FiniteCycleGraphSearch.EncodedSearchSpace.searchCycle?_eq_none_iff_missingSuccessorEdgeStatus S).1
        hnone

/-- The final algorithmic catalog projects executable-search soundness into the existing
graph-search final catalog. -/
theorem final_catalog_projects_search_soundness
    {k : Nat} {S : FiniteCycleGraphSearch.EncodedSearchSpace k}
    (hcat : FiniteCycleAlgorithmicSearchFinalCatalog S)
    {W : FiniteCycleGraphSearch.EncodedSearchSpace.CycleCandidate S}
    (hsearch : FiniteCycleGraphSearch.EncodedSearchSpace.searchCycle? S = some W) :
    FiniteCycleMutualDuplicationFinalCatalog W.toGraphSearchCertificate :=
  hcat.executable_search_sound hsearch

/-- The final algorithmic catalog projects finite completeness over the explicit encoded
successor-edge space. -/
theorem final_catalog_projects_finite_completeness
    {k : Nat} {S : FiniteCycleGraphSearch.EncodedSearchSpace k}
    (hcat : FiniteCycleAlgorithmicSearchFinalCatalog S)
    (hall : ∀ i : Fin (k + 1),
      FiniteCycleGraphSearch.EncodedSearchSpace.Edge S i (FiniteCycleBuilder.advance i)) :
    ∃ W : FiniteCycleGraphSearch.EncodedSearchSpace.CycleCandidate S,
      FiniteCycleGraphSearch.EncodedSearchSpace.searchCycle? S = some W :=
  hcat.finite_completeness hall

/-- The final algorithmic catalog projects the typed failure boundary for a missing successor
edge in the explicit encoded search space. -/
theorem final_catalog_projects_missing_successor_edge_boundary
    {k : Nat} {S : FiniteCycleGraphSearch.EncodedSearchSpace k}
    (hcat : FiniteCycleAlgorithmicSearchFinalCatalog S)
    (hnone : FiniteCycleGraphSearch.EncodedSearchSpace.searchCycle? S = none) :
    Nonempty (FiniteCycleGraphSearch.EncodedSearchSpace.MissingSuccessorEdgeStatus S) :=
  hcat.missing_successor_edge_boundary hnone

/-- The final algorithmic catalog projects cycle realization for every successful search. -/
theorem final_catalog_projects_cycle_realization_transport
    {k : Nat} {S : FiniteCycleGraphSearch.EncodedSearchSpace k}
    (hcat : FiniteCycleAlgorithmicSearchFinalCatalog S)
    {W : FiniteCycleGraphSearch.EncodedSearchSpace.CycleCandidate S}
    (hsearch : FiniteCycleGraphSearch.EncodedSearchSpace.searchCycle? S = some W)
    (i : Fin (k + 1)) (b s n : S.T) :
    Relation.TransGen
      (FiniteCycleGraphSearch.GraphSearchCertificate.StepCtx W.toGraphSearchCertificate)
      (KCycleSchema.cycleSource W.toGraphSearchCertificate.toBuilder.toKCycleSystem.toKCycleSchema i b s n)
      (KCycleSchema.cycleTarget W.toGraphSearchCertificate.toBuilder.toKCycleSystem.toKCycleSchema i b s n) :=
  final_catalog_projects_cycle_realization
    (final_catalog_projects_search_soundness hcat hsearch) i b s n

/-- The final algorithmic catalog projects the additive contextual barrier for every successful
search. -/
theorem final_catalog_projects_additive_barrier_transport
    {k : Nat} {S : FiniteCycleGraphSearch.EncodedSearchSpace k}
    (hcat : FiniteCycleAlgorithmicSearchFinalCatalog S)
    {W : FiniteCycleGraphSearch.EncodedSearchSpace.CycleCandidate S}
    (hsearch : FiniteCycleGraphSearch.EncodedSearchSpace.searchCycle? S = some W)
    (M : KCycleSchema.AdditiveMeasure W.toGraphSearchCertificate.toBuilder.toKCycleSystem.toKCycleSchema) :
    ¬ FiniteCycleGraphSearch.GraphSearchCertificate.GlobalOrientsCtx
      W.toGraphSearchCertificate M.eval (· < ·) :=
  final_catalog_projects_additive_barrier
    (final_catalog_projects_search_soundness hcat hsearch) M

/-- The final algorithmic catalog projects the node-`0` affine contextual barrier for every
successful search. -/
theorem final_catalog_projects_affine_barrier_transport
    {k : Nat} {S : FiniteCycleGraphSearch.EncodedSearchSpace k}
    (hcat : FiniteCycleAlgorithmicSearchFinalCatalog S)
    {W : FiniteCycleGraphSearch.EncodedSearchSpace.CycleCandidate S}
    (hsearch : FiniteCycleGraphSearch.EncodedSearchSpace.searchCycle? S = some W)
    (M : KCycleSchema.AffineMeasure W.toGraphSearchCertificate.toBuilder.toKCycleSystem.toKCycleSchema)
    (hunbounded : StepDuplicatingSchema.HasUnboundedRange
      (FiniteCycleGraphSearch.GraphSearchCertificate.KCycleAffineAtZero
        (C := W.toGraphSearchCertificate) M)) :
    ¬ FiniteCycleGraphSearch.GraphSearchCertificate.GlobalOrientsCtx
      W.toGraphSearchCertificate M.eval (· < ·) :=
  final_catalog_projects_affine_barrier_zero
    (final_catalog_projects_search_soundness hcat hsearch) M hunbounded

/-- The final algorithmic catalog projects the global H3 closeout catalog. -/
theorem final_catalog_projects_closeout_catalog
    {k : Nat} {S : FiniteCycleGraphSearch.EncodedSearchSpace k}
    (_hcat : FiniteCycleAlgorithmicSearchFinalCatalog S) :
    OperatorKO7.MutualDuplicationFiniteSchemaCloseout.MutualDuplicationFiniteSchemaCloseoutCatalog :=
  OperatorKO7.MutualDuplicationFiniteSchemaCloseout.mutual_duplication_finite_schema_closeout_catalog

end OperatorKO7.MutualDuplicationFiniteSchema
