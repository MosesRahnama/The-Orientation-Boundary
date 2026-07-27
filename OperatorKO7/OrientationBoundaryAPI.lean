import OperatorKO7.Meta.DM_TripleLexExactness_FinalCatalog
import OperatorKO7.Meta.SafeTrace_TripleLexExactness_FinalCatalog
import OperatorKO7.Meta.MutualDuplication_FiniteSchema_API
import OperatorKO7.Meta.HigherOrderSharingBoundary_API
import OperatorKO7.Meta.BoundaryGeneral.DirectMeasureGrammarClosure

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

It excludes the broader schema/tooling surface in `SchemaExtendedAPI` and the
KO7-facing cross-paper layer in `CrossPaperAPI`. It does not add an exact-order-
type theorem for every guarded reduction trace, an algorithmic graph-search
theorem, or a full higher-order impossibility theorem.
-/
