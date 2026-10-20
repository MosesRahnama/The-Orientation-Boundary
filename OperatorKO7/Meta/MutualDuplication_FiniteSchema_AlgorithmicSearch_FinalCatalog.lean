import OperatorKO7.Meta.MutualDuplication_FiniteSchema_AlgorithmicSearch
import OperatorKO7.Meta.MutualDuplication_FiniteSchema_FinalCatalog
import OperatorKO7.Meta.MutualDuplication_FiniteSchema_Closeout

/-!
# Finite encoded-cycle search catalog

This module packages search over an explicit encoded finite edge space. A successful search returns
a cycle candidate whose graph-search certificate is mapped into the imported finite-cycle catalog.
The other fields characterize existence under all successor edges and the typed missing-edge case.
-/

namespace OperatorKO7.MutualDuplicationFiniteSchema

open OperatorKO7.StepDuplicating

/-- Three properties of search over one encoded finite edge space. -/
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

/-- Constructs the three search properties from the imported encoded-search theorems. -/
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

/-- Projects successful-search classification from the supplied catalog package. -/
theorem final_catalog_projects_search_soundness
    {k : Nat} {S : FiniteCycleGraphSearch.EncodedSearchSpace k}
    (hcat : FiniteCycleAlgorithmicSearchFinalCatalog S)
    {W : FiniteCycleGraphSearch.EncodedSearchSpace.CycleCandidate S}
    (hsearch : FiniteCycleGraphSearch.EncodedSearchSpace.searchCycle? S = some W) :
    FiniteCycleMutualDuplicationFinalCatalog W.toGraphSearchCertificate :=
  hcat.executable_search_sound hsearch

/-- Projects candidate existence under the supplied all-successor-edges premise. -/
theorem final_catalog_projects_finite_completeness
    {k : Nat} {S : FiniteCycleGraphSearch.EncodedSearchSpace k}
    (hcat : FiniteCycleAlgorithmicSearchFinalCatalog S)
    (hall : ∀ i : Fin (k + 1),
      FiniteCycleGraphSearch.EncodedSearchSpace.Edge S i (FiniteCycleBuilder.advance i)) :
    ∃ W : FiniteCycleGraphSearch.EncodedSearchSpace.CycleCandidate S,
      FiniteCycleGraphSearch.EncodedSearchSpace.searchCycle? S = some W :=
  hcat.finite_completeness hall

/-- Projects the missing-successor-edge status from a failed search. -/
theorem final_catalog_projects_missing_successor_edge_boundary
    {k : Nat} {S : FiniteCycleGraphSearch.EncodedSearchSpace k}
    (hcat : FiniteCycleAlgorithmicSearchFinalCatalog S)
    (hnone : FiniteCycleGraphSearch.EncodedSearchSpace.searchCycle? S = none) :
    Nonempty (FiniteCycleGraphSearch.EncodedSearchSpace.MissingSuccessorEdgeStatus S) :=
  hcat.missing_successor_edge_boundary hnone

/-- A successful search supplies the imported cycle-realization theorem. -/
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

/-- A successful search supplies the imported additive contextual barrier. -/
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

/-- A successful search and the unboundedness premise supply the imported node-zero affine barrier. -/
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

/-- The imported finite-schema catalog, independent of an encoded search space. -/
theorem mutual_duplication_finite_schema_catalog :
    OperatorKO7.MutualDuplicationFiniteSchemaCloseout.MutualDuplicationFiniteSchemaCloseoutCatalog :=
  OperatorKO7.MutualDuplicationFiniteSchemaCloseout.mutual_duplication_finite_schema_closeout_catalog

/-- Compatibility wrapper for the historical declaration name. The supplied search catalog is not
used because the conclusion is the independent imported finite-schema catalog. -/
theorem final_catalog_projects_closeout_catalog
    {k : Nat} {S : FiniteCycleGraphSearch.EncodedSearchSpace k}
    (_hcat : FiniteCycleAlgorithmicSearchFinalCatalog S) :
    OperatorKO7.MutualDuplicationFiniteSchemaCloseout.MutualDuplicationFiniteSchemaCloseoutCatalog :=
  mutual_duplication_finite_schema_catalog

end OperatorKO7.MutualDuplicationFiniteSchema
