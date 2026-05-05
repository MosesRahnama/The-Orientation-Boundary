import OperatorKO7.Meta.MutualDuplication_FiniteSchema_GraphSearch

/-!
# Final H3 Finite-Cycle Catalog

This module packages the H3 finite-cycle mutual-recursion stack into one
paper-facing theorem surface. The theorem-visible boundary is explicit:
graph-search data contributes only through certified successor-edge witnesses,
not through any claim of algorithmic graph discovery.
-/

namespace OperatorKO7.MutualDuplicationFiniteSchema

open OperatorKO7.StepDuplicating

/-- Final paper-facing H3 catalog for a theorem-visible graph-search
certificate. It records exactly the bridges and barrier consequences that are
recoverable from certified successor-edge data. -/
structure FiniteCycleMutualDuplicationFinalCatalog
    {k : Nat} (C : FiniteCycleGraphSearch.GraphSearchCertificate k) : Prop where
  search_certificate_builder_bridge :
    C.toSearchCertificate.toBuilder = C.toBuilder
  search_certificate_kCycleSystem_bridge :
    C.toSearchCertificate.toBuilder.toKCycleSystem = C.toBuilder.toKCycleSystem
  cycle_realization :
    ∀ (i : Fin (k + 1)) (b s n : C.T),
      Relation.TransGen
        (FiniteCycleGraphSearch.GraphSearchCertificate.StepCtx C)
        (KCycleSchema.cycleSource C.toBuilder.toKCycleSystem.toKCycleSchema i b s n)
        (KCycleSchema.cycleTarget C.toBuilder.toKCycleSystem.toKCycleSchema i b s n)
  additive_barrier :
    ∀ (M : KCycleSchema.AdditiveMeasure C.toBuilder.toKCycleSystem.toKCycleSchema),
      ¬ FiniteCycleGraphSearch.GraphSearchCertificate.GlobalOrientsCtx C M.eval (· < ·)
  affine_barrier_at :
    ∀ (M : KCycleSchema.AffineMeasure C.toBuilder.toKCycleSystem.toKCycleSchema)
      (i : Fin (k + 1))
      (_hunbounded : StepDuplicatingSchema.HasUnboundedRange
        (FiniteCycleGraphSearch.GraphSearchCertificate.KCycleAffineAt (C := C) i M)),
      ¬ FiniteCycleGraphSearch.GraphSearchCertificate.GlobalOrientsCtx C M.eval (· < ·)
  affine_barrier_zero :
    ∀ (M : KCycleSchema.AffineMeasure C.toBuilder.toKCycleSystem.toKCycleSchema)
      (_hunbounded : StepDuplicatingSchema.HasUnboundedRange
        (FiniteCycleGraphSearch.GraphSearchCertificate.KCycleAffineAtZero (C := C) M)),
      ¬ FiniteCycleGraphSearch.GraphSearchCertificate.GlobalOrientsCtx C M.eval (· < ·)

/-- Final H3 catalog theorem: certified successor-edge graph-search data is
enough to recover the finite-cycle realization and additive/affine barrier
stack. -/
theorem finite_cycle_mutual_duplication_final_catalog
    {k : Nat} (C : FiniteCycleGraphSearch.GraphSearchCertificate k) :
    FiniteCycleMutualDuplicationFinalCatalog C := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact FiniteCycleGraphSearch.GraphSearchCertificate.toSearchCertificate_toBuilder_eq C
  · exact
      congrArg FiniteCycleBuilder.Builder.toKCycleSystem
        (FiniteCycleGraphSearch.GraphSearchCertificate.toSearchCertificate_toBuilder_eq C)
  · intro i b s n
    exact FiniteCycleGraphSearch.GraphSearchCertificate.cycle_realized_at C i b s n
  · intro M
    exact FiniteCycleGraphSearch.GraphSearchCertificate.no_global_orients_ctx_additive M
  · intro M i hunbounded
    exact
      FiniteCycleGraphSearch.GraphSearchCertificate.no_global_orients_ctx_affine_of_unbounded_at
        M i hunbounded
  · intro M hunbounded
    exact
      FiniteCycleGraphSearch.GraphSearchCertificate.no_global_orients_ctx_affine_of_unbounded
        M hunbounded

/-- The final catalog projects the search-certificate layer itself. -/
theorem final_catalog_projects_search_certificate
    {k : Nat} {C : FiniteCycleGraphSearch.GraphSearchCertificate k}
    (_ : FiniteCycleMutualDuplicationFinalCatalog C) :
    Nonempty (FiniteCycleBuilderMapping.SearchCertificate k) :=
  ⟨C.toSearchCertificate⟩

/-- The final catalog projects the builder layer recovered from the theorem-visible
search certificate. -/
theorem final_catalog_projects_builder
    {k : Nat} {C : FiniteCycleGraphSearch.GraphSearchCertificate k}
    (_ : FiniteCycleMutualDuplicationFinalCatalog C) :
    Nonempty (FiniteCycleBuilder.Builder k) :=
  ⟨C.toBuilder⟩

/-- The final catalog projects the K-cycle system bridge recovered from the
theorem-visible search certificate. -/
theorem final_catalog_projects_kCycleSystem_bridge
    {k : Nat} {C : FiniteCycleGraphSearch.GraphSearchCertificate k}
    (h : FiniteCycleMutualDuplicationFinalCatalog C) :
    C.toSearchCertificate.toBuilder.toKCycleSystem = C.toBuilder.toKCycleSystem :=
  h.search_certificate_kCycleSystem_bridge

/-- The final catalog projects cycle realization at any certified cycle index. -/
theorem final_catalog_projects_cycle_realization
    {k : Nat} {C : FiniteCycleGraphSearch.GraphSearchCertificate k}
    (h : FiniteCycleMutualDuplicationFinalCatalog C)
    (i : Fin (k + 1)) (b s n : C.T) :
    Relation.TransGen
      (FiniteCycleGraphSearch.GraphSearchCertificate.StepCtx C)
      (KCycleSchema.cycleSource C.toBuilder.toKCycleSystem.toKCycleSchema i b s n)
      (KCycleSchema.cycleTarget C.toBuilder.toKCycleSystem.toKCycleSchema i b s n) :=
  h.cycle_realization i b s n

/-- The final catalog projects the additive contextual barrier. -/
theorem final_catalog_projects_additive_barrier
    {k : Nat} {C : FiniteCycleGraphSearch.GraphSearchCertificate k}
    (h : FiniteCycleMutualDuplicationFinalCatalog C)
    (M : KCycleSchema.AdditiveMeasure C.toBuilder.toKCycleSystem.toKCycleSchema) :
    ¬ FiniteCycleGraphSearch.GraphSearchCertificate.GlobalOrientsCtx C M.eval (· < ·) :=
  h.additive_barrier M

/-- The final catalog projects the arbitrary-node affine contextual barrier once
the corresponding one-cycle affine witness is unbounded. -/
theorem final_catalog_projects_affine_barrier_at
    {k : Nat} {C : FiniteCycleGraphSearch.GraphSearchCertificate k}
    (h : FiniteCycleMutualDuplicationFinalCatalog C)
    (M : KCycleSchema.AffineMeasure C.toBuilder.toKCycleSystem.toKCycleSchema)
    (i : Fin (k + 1))
    (hunbounded : StepDuplicatingSchema.HasUnboundedRange
      (FiniteCycleGraphSearch.GraphSearchCertificate.KCycleAffineAt (C := C) i M)) :
    ¬ FiniteCycleGraphSearch.GraphSearchCertificate.GlobalOrientsCtx C M.eval (· < ·) :=
  h.affine_barrier_at M i hunbounded

/-- The final catalog projects the node-`0` affine contextual barrier once the
derived one-cycle affine witness is unbounded. -/
theorem final_catalog_projects_affine_barrier_zero
    {k : Nat} {C : FiniteCycleGraphSearch.GraphSearchCertificate k}
    (h : FiniteCycleMutualDuplicationFinalCatalog C)
    (M : KCycleSchema.AffineMeasure C.toBuilder.toKCycleSystem.toKCycleSchema)
    (hunbounded : StepDuplicatingSchema.HasUnboundedRange
      (FiniteCycleGraphSearch.GraphSearchCertificate.KCycleAffineAtZero (C := C) M)) :
    ¬ FiniteCycleGraphSearch.GraphSearchCertificate.GlobalOrientsCtx C M.eval (· < ·) :=
  h.affine_barrier_zero M hunbounded

/-- No-overclaim boundary statement: the final catalog is recovered only from
certified successor-edge data, not from an unformalized graph-search algorithm. -/
theorem graph_search_requires_certified_successor_edges
    {k : Nat} {T : Type} {base : T} {succ : T → T} {wrap : T → T → T}
    {recur : Fin (k + 1) → T → T → T → T}
    {Edge : Fin (k + 1) → Fin (k + 1) → Prop} {Step : T → T → Prop}
    (local_graph_edge : ∀ i : Fin (k + 1), Edge i (FiniteCycleBuilder.advance i))
    (step_succ_of_edge :
      ∀ {i j : Fin (k + 1)}, Edge i j → ∀ b s n,
        Step (recur i b s (succ n)) (wrap s (recur j b s n))) :
    FiniteCycleMutualDuplicationFinalCatalog
      ({ T := T
         base := base
         succ := succ
         wrap := wrap
         recur := recur
         Edge := Edge
         Step := Step
         local_graph_edge := local_graph_edge
         step_succ_of_edge := step_succ_of_edge } :
        FiniteCycleGraphSearch.GraphSearchCertificate k) :=
  finite_cycle_mutual_duplication_final_catalog _

/-- The two-rule witness graph-search certificate is a nonvacuous instance of the
final H3 catalog. -/
theorem final_catalog_two_rule_nonvacuous
    (b s n : OperatorKO7.MutualDuplicationCase.AltTerm) :
    Relation.TransGen
      (FiniteCycleGraphSearch.GraphSearchCertificate.StepCtx KCycleSystem.twoRuleWitnessGraphSearchCertificate)
      (KCycleSchema.cycleSource
        KCycleSystem.twoRuleWitnessGraphSearchCertificate.toBuilder.toKCycleSystem.toKCycleSchema
        0 b s n)
      (KCycleSchema.cycleTarget
        KCycleSystem.twoRuleWitnessGraphSearchCertificate.toBuilder.toKCycleSystem.toKCycleSchema
        0 b s n) := by
  exact
    final_catalog_projects_cycle_realization
      (finite_cycle_mutual_duplication_final_catalog KCycleSystem.twoRuleWitnessGraphSearchCertificate)
      0 b s n

/-- The three-rule witness graph-search certificate is a nonvacuous instance of the
final H3 catalog. -/
theorem final_catalog_three_rule_nonvacuous
    (b s n : KCycleSystem.ThreeRuleWitness.Term) :
    Relation.TransGen
      (FiniteCycleGraphSearch.GraphSearchCertificate.StepCtx KCycleSystem.threeRuleWitnessGraphSearchCertificate)
      (KCycleSchema.cycleSource
        KCycleSystem.threeRuleWitnessGraphSearchCertificate.toBuilder.toKCycleSystem.toKCycleSchema
        0 b s n)
      (KCycleSchema.cycleTarget
        KCycleSystem.threeRuleWitnessGraphSearchCertificate.toBuilder.toKCycleSystem.toKCycleSchema
        0 b s n) := by
  exact
    final_catalog_projects_cycle_realization
      (finite_cycle_mutual_duplication_final_catalog KCycleSystem.threeRuleWitnessGraphSearchCertificate)
      0 b s n

end OperatorKO7.MutualDuplicationFiniteSchema
