import OperatorKO7.Meta.MutualDuplication_FiniteSchema_AlgorithmicSearch_FinalCatalog

/-!
# H3 Finite-Cycle API

This module exposes the already-validated H3 final catalog through stable API
names only. It does not add a new theorem program.
-/

namespace OperatorKO7.MutualDuplicationFiniteSchemaAPI

open OperatorKO7.MutualDuplicationFiniteSchema

/-- API alias for the theorem-visible H3 graph-search certificate. -/
abbrev GraphSearchCertificate := FiniteCycleGraphSearch.GraphSearchCertificate

/-- API alias for the executable finite encoded H3 search space. -/
abbrev EncodedSearchSpace := FiniteCycleGraphSearch.EncodedSearchSpace

/-- API alias for a successful executable H3 cycle-search witness. -/
abbrev CycleCandidate {k : Nat} (S : EncodedSearchSpace k) : Type :=
  FiniteCycleGraphSearch.EncodedSearchSpace.CycleCandidate S

/-- API alias for the typed executable-search failure boundary. -/
abbrev MissingSuccessorEdgeStatus {k : Nat} (S : EncodedSearchSpace k) : Type :=
  FiniteCycleGraphSearch.EncodedSearchSpace.MissingSuccessorEdgeStatus S

/-- API alias for the H3 catalog. -/
abbrev FinalCatalog {k : Nat} (C : GraphSearchCertificate k) : Prop :=
  FiniteCycleMutualDuplicationFinalCatalog C

/-- API alias for the executable H3 catalog. -/
abbrev AlgorithmicFinalCatalog {k : Nat} (S : EncodedSearchSpace k) : Prop :=
  FiniteCycleAlgorithmicSearchFinalCatalog S

/-- API alias for the finite H3 catalog. -/
abbrev CloseoutCatalog : Prop :=
  OperatorKO7.MutualDuplicationFiniteSchemaCloseout.MutualDuplicationFiniteSchemaCloseoutCatalog

/-- API executable H3 search entrypoint. -/
def searchCycle? {k : Nat} (S : EncodedSearchSpace k) : Option (CycleCandidate S) :=
  FiniteCycleGraphSearch.EncodedSearchSpace.searchCycle? S

/-- API entrypoint for the H3 catalog. -/
theorem final_catalog
    {k : Nat} (C : GraphSearchCertificate k) :
    FinalCatalog C :=
  finite_cycle_mutual_duplication_final_catalog C

/-- API projection for cycle realization at any certified cycle index. -/
theorem cycle_realization
    {k : Nat} {C : GraphSearchCertificate k}
    (h : FinalCatalog C)
    (i : Fin (k + 1)) (b s n : C.T) :
    Relation.TransGen
      (FiniteCycleGraphSearch.GraphSearchCertificate.StepCtx C)
      (KCycleSchema.cycleSource C.toBuilder.toKCycleSystem.toKCycleSchema i b s n)
      (KCycleSchema.cycleTarget C.toBuilder.toKCycleSystem.toKCycleSchema i b s n) :=
  final_catalog_projects_cycle_realization h i b s n

/-- API projection for the additive barrier. -/
theorem additive_barrier
    {k : Nat} {C : GraphSearchCertificate k}
    (h : FinalCatalog C)
    (M : KCycleSchema.AdditiveMeasure C.toBuilder.toKCycleSystem.toKCycleSchema) :
    ¬ FiniteCycleGraphSearch.GraphSearchCertificate.GlobalOrientsCtx C M.eval (· < ·) :=
  final_catalog_projects_additive_barrier h M

/-- API projection for the node-`0` affine barrier. -/
theorem affine_barrier
    {k : Nat} {C : GraphSearchCertificate k}
    (h : FinalCatalog C)
    (M : KCycleSchema.AffineMeasure C.toBuilder.toKCycleSystem.toKCycleSchema)
    (hunbounded : StepDuplicating.StepDuplicatingSchema.HasUnboundedRange
      (FiniteCycleGraphSearch.GraphSearchCertificate.KCycleAffineAtZero (C := C) M)) :
    ¬ FiniteCycleGraphSearch.GraphSearchCertificate.GlobalOrientsCtx C M.eval (· < ·) :=
  final_catalog_projects_affine_barrier_zero h M hunbounded

/-- API boundary statement: the H3 catalog follows from certified successor-edge
data; algorithmic extraction requires a separate implementation and soundness bridge. -/
theorem certified_successor_edge_boundary
    {k : Nat} {T : Type} {base : T} {succ : T → T} {wrap : T → T → T}
    {recur : Fin (k + 1) → T → T → T → T}
    {Edge : Fin (k + 1) → Fin (k + 1) → Prop} {Step : T → T → Prop}
    (local_graph_edge : ∀ i : Fin (k + 1), Edge i (FiniteCycleBuilder.advance i))
    (step_succ_of_edge :
      ∀ {i j : Fin (k + 1)}, Edge i j → ∀ b s n,
        Step (recur i b s (succ n)) (wrap s (recur j b s n))) :
    FinalCatalog
      ({ T := T
         base := base
         succ := succ
         wrap := wrap
         recur := recur
         Edge := Edge
         Step := Step
         local_graph_edge := local_graph_edge
         step_succ_of_edge := step_succ_of_edge } :
        GraphSearchCertificate k) :=
  graph_search_requires_certified_successor_edges local_graph_edge step_succ_of_edge

/-- API witness theorem for the two-rule H3 graph certificate. -/
theorem two_rule_witness :
    FinalCatalog KCycleSystem.twoRuleWitnessGraphSearchCertificate :=
  finite_cycle_mutual_duplication_final_catalog _

/-- API witness theorem for the three-rule H3 graph certificate. -/
theorem three_rule_witness :
    FinalCatalog KCycleSystem.threeRuleWitnessGraphSearchCertificate :=
  finite_cycle_mutual_duplication_final_catalog _

/-- API entrypoint for the executable H3 catalog. -/
theorem algorithmic_final_catalog
    {k : Nat} (S : EncodedSearchSpace k) :
    AlgorithmicFinalCatalog S :=
  finite_cycle_algorithmic_search_final_catalog S

/-- API entrypoint for the finite H3 catalog. -/
theorem closeout_catalog
    {k : Nat} (S : EncodedSearchSpace k) :
    CloseoutCatalog :=
  final_catalog_projects_closeout_catalog (algorithmic_final_catalog S)

/-- API soundness theorem for the executable H3 search. -/
theorem executable_search_sound
    {k : Nat} {S : EncodedSearchSpace k}
    {W : CycleCandidate S}
    (hsearch : searchCycle? S = some W) :
    FinalCatalog W.toGraphSearchCertificate :=
  final_catalog_projects_search_soundness (algorithmic_final_catalog S) hsearch

/-- API finite completeness theorem for the explicit encoded H3 search space. -/
theorem finite_completeness
    {k : Nat} {S : EncodedSearchSpace k}
    (hall : ∀ i : Fin (k + 1),
      FiniteCycleGraphSearch.EncodedSearchSpace.Edge S i (FiniteCycleBuilder.advance i)) :
    ∃ W : CycleCandidate S, searchCycle? S = some W :=
  final_catalog_projects_finite_completeness (algorithmic_final_catalog S) hall

/-- API typed failure boundary for a missing successor edge in the explicit encoded H3
search space. -/
theorem missing_successor_edge_boundary
    {k : Nat} {S : EncodedSearchSpace k}
    (hnone : searchCycle? S = none) :
    Nonempty (MissingSuccessorEdgeStatus S) :=
  final_catalog_projects_missing_successor_edge_boundary (algorithmic_final_catalog S) hnone

/-- API cycle-realization transport for every successful executable H3 search. -/
theorem algorithmic_cycle_realization
    {k : Nat} {S : EncodedSearchSpace k}
    {W : CycleCandidate S}
    (hsearch : searchCycle? S = some W)
    (i : Fin (k + 1)) (b s n : S.T) :
    Relation.TransGen
      (FiniteCycleGraphSearch.GraphSearchCertificate.StepCtx W.toGraphSearchCertificate)
      (KCycleSchema.cycleSource W.toGraphSearchCertificate.toBuilder.toKCycleSystem.toKCycleSchema i b s n)
      (KCycleSchema.cycleTarget W.toGraphSearchCertificate.toBuilder.toKCycleSystem.toKCycleSchema i b s n) :=
  final_catalog_projects_cycle_realization_transport (algorithmic_final_catalog S) hsearch i b s n

/-- API additive contextual barrier transport for every successful executable H3 search. -/
theorem algorithmic_additive_barrier
    {k : Nat} {S : EncodedSearchSpace k}
    {W : CycleCandidate S}
    (hsearch : searchCycle? S = some W)
    (M : KCycleSchema.AdditiveMeasure W.toGraphSearchCertificate.toBuilder.toKCycleSystem.toKCycleSchema) :
    ¬ FiniteCycleGraphSearch.GraphSearchCertificate.GlobalOrientsCtx
      W.toGraphSearchCertificate M.eval (· < ·) :=
  final_catalog_projects_additive_barrier_transport (algorithmic_final_catalog S) hsearch M

/-- API node-`0` affine contextual barrier transport for every successful executable H3
search. -/
theorem algorithmic_affine_barrier
    {k : Nat} {S : EncodedSearchSpace k}
    {W : CycleCandidate S}
    (hsearch : searchCycle? S = some W)
    (M : KCycleSchema.AffineMeasure W.toGraphSearchCertificate.toBuilder.toKCycleSystem.toKCycleSchema)
    (hunbounded : StepDuplicating.StepDuplicatingSchema.HasUnboundedRange
      (FiniteCycleGraphSearch.GraphSearchCertificate.KCycleAffineAtZero
        (C := W.toGraphSearchCertificate) M)) :
    ¬ FiniteCycleGraphSearch.GraphSearchCertificate.GlobalOrientsCtx
      W.toGraphSearchCertificate M.eval (· < ·) :=
  final_catalog_projects_affine_barrier_transport (algorithmic_final_catalog S) hsearch M hunbounded

/-- API concrete encoded H3 search space for the two-rule witness system. -/
def two_rule_encoded_search_space : EncodedSearchSpace 1 :=
  FiniteCycleGraphSearch.KCycleSystem.twoRuleWitnessEncodedSearchSpace

/-- API concrete encoded H3 search space for the three-rule witness system. -/
def three_rule_encoded_search_space : EncodedSearchSpace 2 :=
  FiniteCycleGraphSearch.KCycleSystem.threeRuleWitnessEncodedSearchSpace

/-- API executable-search success theorem for the two-rule witness space. -/
theorem two_rule_algorithmic_search_succeeds :
    ∃ W : CycleCandidate two_rule_encoded_search_space,
      searchCycle? two_rule_encoded_search_space = some W :=
  FiniteCycleGraphSearch.KCycleSystem.twoRuleWitness_searchCycle?_succeeds

/-- API executable-search success theorem for the three-rule witness space. -/
theorem three_rule_algorithmic_search_succeeds :
    ∃ W : CycleCandidate three_rule_encoded_search_space,
      searchCycle? three_rule_encoded_search_space = some W :=
  FiniteCycleGraphSearch.KCycleSystem.threeRuleWitness_searchCycle?_succeeds

end OperatorKO7.MutualDuplicationFiniteSchemaAPI
