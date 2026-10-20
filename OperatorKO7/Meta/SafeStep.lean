import OperatorKO7.Meta.SafeStep.EqWVoidAnomaly
import OperatorKO7.Meta.SafeStep.GaugeFixingGuard
import OperatorKO7.Meta.SafeStep.SmugglingUndecidability
import OperatorKO7.Meta.SafeStep.SyntacticNonDerivability
import OperatorKO7.Meta.SafeStep.DynamicalBoundaryFunctor
import OperatorKO7.Meta.SafeStep.FaithfulnessNoGo
import OperatorKO7.Meta.SafeStep.NonlinearityDichotomy

/-!
# SafeStep Worked Gauge-Fixing Example: namespace aggregator

This module re-exports the gauge-fixing modules as a single
`OperatorKO7.Meta.SafeStep` namespace surface so
downstream callers (paper citations,
CrossPaperAPI) can resolve the entire SafeStep gauge-fixing
chain through one import.

## Citation chain (canonical)

- `PayloadDiscarding` (Axiom 5): the payload-discarding mass premise.
- `EqWVoidAnomaly` (this directory): the object-level critical pair.
- `GaugeFixingGuard`: the meta-level operational structure.
- `SyntacticNonDerivability`: the classification claim in unconditional proven form.
- `SmugglingUndecidability`: the smuggling-undecidability
 link to `PreUndecidabilityFracture`.
- `TypedRefusalCompleteness`: the typed-refusal completeness result.

## Anchors exposed

```
audit_safestep_eqw_void_void_critical_pair_anchor
  -> OperatorKO7.Meta.SafeStep.EqWVoidAnomaly.local_confluence_fails_at_eqW_void_void

audit_safestep_gauge_guard_restores_local_confluence_anchor
  -> OperatorKO7.Meta.SafeStep.GaugeFixingGuard.safestep_guard_restores_local_confluence

audit_safestep_is_meta_halt_anchor
  -> OperatorKO7.Meta.SafeStep.GaugeFixingGuard.safestep_is_meta_halt

audit_safestep_eqw_void_void_is_pre_undecidability_fracture_anchor
  -> OperatorKO7.Meta.SafeStep.SmugglingUndecidability.eqW_void_void_is_pre_undecidability_fracture

audit_safestep_smuggles_external_observer_anchor
  -> OperatorKO7.Meta.SafeStep.SmugglingUndecidability.safestep_guard_smuggles_external_observer

audit_safestep_disequality_not_sigma_expressible_anchor
  -> OperatorKO7.Meta.SafeStep.SyntacticNonDerivability.disequality_not_sigma_expressible
   (status: unconditional; proven via disequality_not_sigma_expressible_unconditional)

audit_safestep_dynamical_boundary_functor_anchor
  -> OperatorKO7.Meta.SafeStep.DynamicalBoundaryFunctor.eqW_critical_pair_maps_to_distinction_boundary

audit_safestep_dynamical_boundary_nonfaithful_anchor
  -> OperatorKO7.Meta.SafeStep.DynamicalBoundaryFunctor.distinction_dynamical_functor_not_faithful
```

This namespace re-exports the sibling modules with no
additional declarations. Pure additive aggregator.
-/

namespace OperatorKO7.Meta.SafeStep
end OperatorKO7.Meta.SafeStep
