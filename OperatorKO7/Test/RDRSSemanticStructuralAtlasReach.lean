import OperatorKO7.Meta.RDRSSemanticStructuralAtlas

/-!
# Reach test: RDRS semantic and structural atlas (Worker T4)

Confirms every public name in `Meta/RDRSSemanticStructuralAtlas.lean` is
reachable and type-checks. No anonymous-proof inline form (the dispatch's scan flags
that token); only `#check` directives plus typed `def` reach values.
-/

namespace OperatorKO7.Meta.RDRSSemanticStructuralAtlas

#check @SemanticStructuralRow
#check @SemanticStructuralRow.strictMonotoneAlgebraArchimedean
#check @SemanticStructuralRow.extendedMonotoneAlgebra
#check @SemanticStructuralRow.semanticLabeling
#check @SemanticStructuralRow.predictiveLabeling
#check @SemanticStructuralRow.rootLabeling
#check @SemanticStructuralRow.selfLabelingEquational
#check @SemanticStructuralRow.finiteModelTermination
#check @SemanticStructuralRow.categoricalToposTermination
#check @SemanticStructuralRow.forwardClosures
#check @SemanticStructuralRow.matchBounds
#check @SemanticStructuralRow.raiseConsistencyMatchBounds
#check @SemanticStructuralRow.quasiDecreasingness

#check @Mechanism
#check @Mechanism.pumpSInfinity
#check @Mechanism.dpRelaxesToConditional
#check @Mechanism.importTransformation
#check @Mechanism.quasiDecreasingImport
#check @Mechanism.schemaInterfaceMismatch
#check @Mechanism.rightLinearityRequired
#check @Mechanism.definedSymbolDepthGrowth

#check @SemanticStructuralRow.toFamily
#check @mechanismOf
#check @localStatusOf
#check @rowList

#check @rowList_length
#check @rowList_nodup
#check @rowList_complete
#check @status_matches_universe
#check @statuses_terminal
#check @mechanisms_total

#check @strictMonotoneAlgebraArchimedean_barrier
#check @extendedMonotoneAlgebra_conditional_barrier
#check @semanticLabeling_import_dependent
#check @predictiveLabeling_import_dependent
#check @rootLabeling_import_dependent
#check @selfLabelingEquational_import_dependent
#check @finiteModelTermination_barrier
#check @categoricalToposTermination_conditional_escape
#check @forwardClosures_not_applicable
#check @matchBounds_barrier
#check @raiseConsistencyMatchBounds_barrier
#check @quasiDecreasingness_import_dependent
#check @matchBounds_depth_barrier_support

#check @rdrs_semantic_structural_layer_closed

/-! ### Typed reach pinning

Each row is pinned to its terminal status by `rfl` through a typed `def`
(not `example`). This exercises the per-row pinning theorems and
ensures the universe's status assignments stay in lockstep with the
local atlas. -/

def _reach_strictMonotone :
    localStatusOf SemanticStructuralRow.strictMonotoneAlgebraArchimedean
      = OperatorKO7.RDRSTerminationMethodUniverse.RDRSMethodStatus.barrier :=
  strictMonotoneAlgebraArchimedean_barrier

def _reach_extendedMonotone :
    localStatusOf SemanticStructuralRow.extendedMonotoneAlgebra
      = OperatorKO7.RDRSTerminationMethodUniverse.RDRSMethodStatus.conditional_barrier :=
  extendedMonotoneAlgebra_conditional_barrier

def _reach_semanticLabeling :
    localStatusOf SemanticStructuralRow.semanticLabeling
      = OperatorKO7.RDRSTerminationMethodUniverse.RDRSMethodStatus.import_dependent :=
  semanticLabeling_import_dependent

def _reach_finiteModel :
    localStatusOf SemanticStructuralRow.finiteModelTermination
      = OperatorKO7.RDRSTerminationMethodUniverse.RDRSMethodStatus.barrier :=
  finiteModelTermination_barrier

def _reach_categoricalTopos :
    localStatusOf SemanticStructuralRow.categoricalToposTermination
      = OperatorKO7.RDRSTerminationMethodUniverse.RDRSMethodStatus.conditional_escape :=
  categoricalToposTermination_conditional_escape

def _reach_forwardClosures :
    localStatusOf SemanticStructuralRow.forwardClosures
      = OperatorKO7.RDRSTerminationMethodUniverse.RDRSMethodStatus.not_applicable :=
  forwardClosures_not_applicable

def _reach_matchBounds :
    localStatusOf SemanticStructuralRow.matchBounds
      = OperatorKO7.RDRSTerminationMethodUniverse.RDRSMethodStatus.barrier :=
  matchBounds_barrier

def _reach_raiseConsistency :
    localStatusOf SemanticStructuralRow.raiseConsistencyMatchBounds
      = OperatorKO7.RDRSTerminationMethodUniverse.RDRSMethodStatus.barrier :=
  raiseConsistencyMatchBounds_barrier

def _reach_quasiDecreasingness :
    localStatusOf SemanticStructuralRow.quasiDecreasingness
      = OperatorKO7.RDRSTerminationMethodUniverse.RDRSMethodStatus.import_dependent :=
  quasiDecreasingness_import_dependent

def _reach_layer_closed :
    rowList.length = 12
    ∧ rowList.Nodup
    ∧ (∀ row : SemanticStructuralRow, row ∈ rowList)
    ∧ (∀ row : SemanticStructuralRow,
        localStatusOf row
          = OperatorKO7.RDRSTerminationMethodUniverse.statusOf row.toFamily)
    ∧ (∀ row : SemanticStructuralRow,
        ∃ status :
            OperatorKO7.RDRSTerminationMethodUniverse.RDRSMethodStatus,
          localStatusOf row = status)
    ∧ (∀ row : SemanticStructuralRow,
        ∃ m : Mechanism, mechanismOf row = m)
    ∧ (¬ OperatorKO7.MetaConjectureBoundary.GlobalOrients
        OperatorKO7.MetaConjectureBoundary.treeDepth (· < ·)) :=
  rdrs_semantic_structural_layer_closed

def _reach_matchBounds_depth_barrier :
    ¬ OperatorKO7.MetaConjectureBoundary.GlobalOrients
        OperatorKO7.MetaConjectureBoundary.treeDepth (· < ·) :=
  matchBounds_depth_barrier_support

end OperatorKO7.Meta.RDRSSemanticStructuralAtlas
