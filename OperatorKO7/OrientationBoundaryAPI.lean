import OperatorKO7.Meta.DM_TripleLexExactness_FinalCatalog
import OperatorKO7.Meta.SafeTrace_TripleLexExactness_FinalCatalog
import OperatorKO7.Meta.MutualDuplication_FiniteSchema_API
import OperatorKO7.Meta.HigherOrderSharingBoundary_API

/-!
# Orientation Boundary API

Narrow public root for the orientation-boundary surfaces used by *The Orientation
Boundary for Step-Duplicating Recursors: Mechanized Impossibility, Escape, and
Certification*.

This file re-exports only the stable theorem-backed orientation surfaces that
*The Orientation Boundary for Step-Duplicating Recursors: Mechanized
Impossibility, Escape, and Certification* currently treats as public import
boundaries: the final M3
calibrated-carrier exactness catalog, the safe-trace exactness, range-status,
image-subtype exactness, safe-step certificate bridge, safe-trace complexity
bridge, finite certificate audit, safe-trace roadmap closeout, root API export,
and full-carrier obstruction catalogs, and the stable H3 finite-cycle and M2
no-sharing API wrappers.

It excludes the broader schema/tooling surface in `SchemaExtendedAPI` and the
KO7-facing cross-manuscript layer in `CrossPaperAPI`. It does not add an exact-order-
type theorem for every guarded reduction trace, an algorithmic graph-search
theorem, or a full higher-order impossibility theorem.
-/
