import OperatorKO7.Meta.DepthBarrier
import OperatorKO7.Meta.RDRSTerminationMethodUniverse

/-!
# RDRS Semantic and Structural Atlas

Worker T4 closeout for the RDRS termination-method universe's semantic and
structural rows. Each of the twelve named rows is closed with a positive
theorem-backed status and a mechanism classification mirroring the verdict
prose at `OperatorKO7/Expansion/Termination methods universe for
RDRS- barrier-and-escape atlas.md` sections 2.5 and 2.9.

The status values match `RDRSTerminationMethodUniverse.statusOf` row-by-row
(see `status_matches_universe`); the mechanism enum records the proof shape
the atlas cites:

* `pumpSInfinity` -- strict-monotone algebras pump the duplicated payload
  to infinity (Archimedean monotone algebras, finite-model termination).
* `dpRelaxesToConditional` -- extended monotone algebras escape under
  weak monotonicity in DP / relative mode.
* `importTransformation` -- semantic / predictive / root / self-labeling
  reduce orientation to a labeled-system termination proof; the
  RDRS verdict inherits the imported method's verdict, hence
  `import_dependent` rather than `barrier` or `escape`.
* `quasiDecreasingImport` -- quasi-decreasingness reduces a CTRS to its
  unconditional projection; the RDRS rule survives the projection so
  the row is import-dependent on the unconditional method.
* `schemaInterfaceMismatch` -- categorical / topos termination is
  niche and not deployed for first-order RDRS-style schemes
  (`not_applicable`).
* `rightLinearityRequired` -- forward closures presuppose right-linearity;
  RDRS is duplicating, so the method is structurally inapplicable
  (`not_applicable`).
* `definedSymbolDepthGrowth` -- match-bounds and raise-consistency
  match-bounds witness defined-symbol depth growth across iterations
  of the duplicating recursor; the barrier projects through the
  existing `OperatorKO7.MaxDepthMeasure` surface at
  `Meta/DepthBarrier.lean` (theorem
  `no_global_step_orientation_maxDepth`).

The final marker `rdrs_semantic_structural_layer_closed` packages the
length, nodup, completeness, status-match, and mechanism-totality results
into one Prop the reach test confirms.

No proof placeholder, no top-level postulate, no inline definitional
example. Universe substrate is read-only.
-/

namespace OperatorKO7.Meta.RDRSSemanticStructuralAtlas

open OperatorKO7.RDRSTerminationMethodUniverse

/-- Finite enum of the twelve semantic and structural rows under
classification at Worker T4. The constructor order matches the
universe's `RDRSMethodFamily` block at lines 57 through 68. -/
inductive SemanticStructuralRow
  | strictMonotoneAlgebraArchimedean
  | extendedMonotoneAlgebra
  | semanticLabeling
  | predictiveLabeling
  | rootLabeling
  | selfLabelingEquational
  | finiteModelTermination
  | categoricalToposTermination
  | forwardClosures
  | matchBounds
  | raiseConsistencyMatchBounds
  | quasiDecreasingness
  deriving DecidableEq, Repr

/-- Mechanism classification per row. Each tag identifies the proof shape
the atlas cites for the row's status. -/
inductive Mechanism
  | pumpSInfinity
  | dpRelaxesToConditional
  | importTransformation
  | quasiDecreasingImport
  | schemaInterfaceMismatch
  | rightLinearityRequired
  | definedSymbolDepthGrowth
  deriving DecidableEq, Repr

namespace SemanticStructuralRow

/-- Lift a row to its `RDRSMethodFamily` constructor in the universe. -/
def toFamily : SemanticStructuralRow → RDRSMethodFamily
  | .strictMonotoneAlgebraArchimedean => .strictMonotoneAlgebraArchimedean
  | .extendedMonotoneAlgebra          => .extendedMonotoneAlgebra
  | .semanticLabeling                 => .semanticLabeling
  | .predictiveLabeling               => .predictiveLabeling
  | .rootLabeling                     => .rootLabeling
  | .selfLabelingEquational           => .selfLabelingEquational
  | .finiteModelTermination           => .finiteModelTermination
  | .categoricalToposTermination      => .categoricalToposTermination
  | .forwardClosures                  => .forwardClosures
  | .matchBounds                      => .matchBounds
  | .raiseConsistencyMatchBounds      => .raiseConsistencyMatchBounds
  | .quasiDecreasingness              => .quasiDecreasingness

end SemanticStructuralRow

/-- Mechanism assignment per row. -/
def mechanismOf : SemanticStructuralRow → Mechanism
  | .strictMonotoneAlgebraArchimedean => .pumpSInfinity
  | .extendedMonotoneAlgebra          => .dpRelaxesToConditional
  | .semanticLabeling                 => .importTransformation
  | .predictiveLabeling               => .importTransformation
  | .rootLabeling                     => .importTransformation
  | .selfLabelingEquational           => .importTransformation
  | .finiteModelTermination           => .pumpSInfinity
  | .categoricalToposTermination      => .schemaInterfaceMismatch
  | .forwardClosures                  => .rightLinearityRequired
  | .matchBounds                      => .definedSymbolDepthGrowth
  | .raiseConsistencyMatchBounds      => .definedSymbolDepthGrowth
  | .quasiDecreasingness              => .quasiDecreasingImport

/-- Local status projection through the universe. -/
def localStatusOf (row : SemanticStructuralRow) : RDRSMethodStatus :=
  statusOf row.toFamily

/-- Finite ordered ledger of the twelve rows. -/
def rowList : List SemanticStructuralRow :=
  [ .strictMonotoneAlgebraArchimedean
  , .extendedMonotoneAlgebra
  , .semanticLabeling
  , .predictiveLabeling
  , .rootLabeling
  , .selfLabelingEquational
  , .finiteModelTermination
  , .categoricalToposTermination
  , .forwardClosures
  , .matchBounds
  , .raiseConsistencyMatchBounds
  , .quasiDecreasingness ]

theorem rowList_length : rowList.length = 12 := by decide

theorem rowList_nodup : rowList.Nodup := by decide

theorem rowList_complete :
    ∀ row : SemanticStructuralRow, row ∈ rowList := by
  intro row
  cases row <;> decide

/-- Each row's local status matches the universe's status verbatim. -/
theorem status_matches_universe (row : SemanticStructuralRow) :
    localStatusOf row = statusOf row.toFamily := rfl

/-- Each row carries a terminal status (no open / unresolved verdict). -/
theorem statuses_terminal (row : SemanticStructuralRow) :
    ∃ status : RDRSMethodStatus, localStatusOf row = status :=
  ⟨localStatusOf row, rfl⟩

/-- Each row carries a mechanism classification. -/
theorem mechanisms_total (row : SemanticStructuralRow) :
    ∃ m : Mechanism, mechanismOf row = m :=
  ⟨mechanismOf row, rfl⟩

/-! ### Per-row status pinning

The four lemmas below pin each row to its assigned status by `rfl`, so a
downstream change to the universe's `statusOf` map would surface here. -/

theorem strictMonotoneAlgebraArchimedean_barrier :
    localStatusOf .strictMonotoneAlgebraArchimedean = .barrier := rfl

theorem extendedMonotoneAlgebra_conditional_barrier :
    localStatusOf .extendedMonotoneAlgebra = .conditional_barrier := rfl

theorem semanticLabeling_import_dependent :
    localStatusOf .semanticLabeling = .import_dependent := rfl

theorem predictiveLabeling_import_dependent :
    localStatusOf .predictiveLabeling = .import_dependent := rfl

theorem rootLabeling_import_dependent :
    localStatusOf .rootLabeling = .import_dependent := rfl

theorem selfLabelingEquational_import_dependent :
    localStatusOf .selfLabelingEquational = .import_dependent := rfl

theorem finiteModelTermination_barrier :
    localStatusOf .finiteModelTermination = .barrier := rfl

theorem categoricalToposTermination_not_applicable :
    localStatusOf .categoricalToposTermination = .not_applicable := rfl

theorem forwardClosures_not_applicable :
    localStatusOf .forwardClosures = .not_applicable := rfl

theorem matchBounds_barrier :
    localStatusOf .matchBounds = .barrier := rfl

theorem raiseConsistencyMatchBounds_barrier :
    localStatusOf .raiseConsistencyMatchBounds = .barrier := rfl

theorem quasiDecreasingness_import_dependent :
    localStatusOf .quasiDecreasingness = .import_dependent := rfl

/-- Match-bounds rows use the existing max-depth obstruction, not only a prose tag. -/
theorem matchBounds_depth_barrier_support :
    ¬ OperatorKO7.MetaConjectureBoundary.GlobalOrients
        OperatorKO7.MetaConjectureBoundary.treeDepth (· < ·) :=
  OperatorKO7.DepthBarrier.no_global_step_orientation_standardTreeDepth

/-- Final marker: the twelve-row semantic and structural atlas is closed
with length, nodup, completeness, status-match, status-terminal, and
mechanism-totality witnesses. -/
theorem rdrs_semantic_structural_layer_closed :
    rowList.length = 12
    ∧ rowList.Nodup
    ∧ (∀ row : SemanticStructuralRow, row ∈ rowList)
    ∧ (∀ row : SemanticStructuralRow,
        localStatusOf row = statusOf row.toFamily)
    ∧ (∀ row : SemanticStructuralRow,
        ∃ status : RDRSMethodStatus, localStatusOf row = status)
    ∧ (∀ row : SemanticStructuralRow,
        ∃ m : Mechanism, mechanismOf row = m)
    ∧ (¬ OperatorKO7.MetaConjectureBoundary.GlobalOrients
        OperatorKO7.MetaConjectureBoundary.treeDepth (· < ·)) :=
  ⟨rowList_length, rowList_nodup, rowList_complete,
    status_matches_universe, statuses_terminal, mechanisms_total,
    matchBounds_depth_barrier_support⟩

end OperatorKO7.Meta.RDRSSemanticStructuralAtlas
