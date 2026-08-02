import OperatorKO7.Meta.DM_TripleLexExactness_FinalCatalog
import OperatorKO7.Meta.SafeTrace_TripleLexExactness_FinalCatalog
import OperatorKO7.Meta.MutualDuplication_FiniteSchema_API
import OperatorKO7.Meta.HigherOrderSharingBoundary_API
import OperatorKO7.Meta.BoundaryGeneral.DirectMeasureGrammarClosure
import OperatorKO7.Meta.BoundaryGeneral.VectorOrderRepair
import OperatorKO7.Meta.BoundaryGeneral.CheckedNonOrientationCertificate
import OperatorKO7.Meta.BoundaryGeneral.DeclaredMethodUniverse
import OperatorKO7.Meta.RDRSMethodCertificate
import OperatorKO7.Meta.RDRSSemanticCoverageLedger

/-!
# Orientation Boundary API

Narrow public root for the orientation-boundary surfaces used by Paper A.

This file re-exports only the stable theorem-backed orientation surfaces that
Paper A currently treats as public import boundaries: the final M3
calibrated-carrier exactness catalog, the safe-trace exactness, range-status,
image-subtype exactness, safe-step certificate bridge, safe-trace complexity
bridge, finite certificate audit, safe-trace roadmap closeout, root API export,
full-carrier obstruction catalogs, the stable H3 finite-cycle and M2 no-sharing
API wrappers, and the exact scalar grammar characterization of duplicating-step
orientation.

The Tier-17 `VectorOrderRepair`, `CheckedNonOrientationCertificate`, and
`DeclaredMethodUniverse` imports passed the targeted Tier-17B elaboration,
reach, API-preservation, and axiom-audit gates on 2026-08-02.  Their exact
trust surface remains the one printed by the dated Tier-17B receipt.

`VectorOrderRepair` now also exports
`primaryFirstLt_not_wellFounded_of_three_le`, the Tier-17B P1 statement for
every dimension at least three and every primary coordinate.  Importing it
here records public API reach; the dedicated Tier-17B reach and axiom gates
record its exact elaborated type and trust surface.

`RDRSSemanticCoverageLedger` exports the proof-bearing mirror of the complete
sixteen-row semantic ledger.  Its six projection-escape rows now store
anchor-indexed transaction evidence, while forgetting the proof layer recovers
the original metadata ledger definitionally.

It excludes the broader schema/tooling surface in `SchemaExtendedAPI` and the
KO7-facing cross-paper layer in `CrossPaperAPI`. It does not add an exact-order-
type theorem for every guarded reduction trace, an algorithmic graph-search
theorem, or a full higher-order impossibility theorem.
-/
