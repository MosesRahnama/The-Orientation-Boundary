import OperatorKO7.Meta.SafeStep.EqWVoidAnomaly
import OperatorKO7.Meta.SafeStep.GaugeFixingGuard
import OperatorKO7.Meta.SafeStep.SmugglingUndecidability
import OperatorKO7.Meta.SafeStep.SyntacticNonDerivability
import OperatorKO7.Meta.SafeStep.DynamicalBoundaryFunctor
import OperatorKO7.Meta.SafeStep.FaithfulnessNoGo
import OperatorKO7.Meta.SafeStep.NonlinearityDichotomy

/-!
# SafeStep Worked Gauge-Fixing Example: namespace aggregator (W16.4)

W16.4: re-exports the W16 modules (W16.1, W16.2, W16.3,
W16.7, and the later dynamical boundary functor) as a single
`OperatorKO7.Meta.SafeStep` namespace surface so
downstream callers (engine cert emitters, paper citations,
CrossPaperAPI) can grep-resolve the entire SafeStep gauge-fixing
chain through one import.

## Citation chain (canonical)

  PayloadDiscarding (Axiom 5; `Meta/BoundaryOperator/PayloadDiscarding.lean`)
    -> EqWVoidAnomaly (W16.1; this dir; the object-level critical pair)
      -> GaugeFixingGuard (W16.2; the meta-level operational structure)
        -> SyntacticNonDerivability (W16.7; path-(a) commercial claim,
                                       now unconditional proven form)
          -> SmugglingUndecidability (W16.3; the smuggling-undecidability
                                        link to PreUndecidabilityFracture)
            -> TypedRefusalCompleteness (Meta/BoundaryOperator/
                                         TypedRefusalCompleteness.lean)

## Engine wire-up

The engine consumes this aggregator at four cert sites:

  * `code/supervisor/smuggling_detector.py::SmugglingSubtype.GAUGE_ANOMALY_SELF_IDENTITY`
  * `code/supervisor/audit_log.py::PROVIDER_DNS_FAILOVER_EVENT_KIND`
    (sibling event kind; the new W16.5 event is
     `gauge_fixing_meta_halt`)
  * The W16.5 cert payload's primary anchor:
    `OperatorKO7.Meta.SafeStep.SmugglingUndecidability.eqW_void_void_is_pre_undecidability_fracture`
  * The W16.5 cert payload's secondary anchor (commercial claim):
    `OperatorKO7.Meta.SafeStep.SyntacticNonDerivability.disequality_not_sigma_expressible`
    (current status: unconditional/proven; alias for
     `disequality_not_sigma_expressible_unconditional`, carries
     `commercial_claim_status: unconditional`; the substitution-invariance
     proof closure path is discharged in `SyntacticNonDerivability.lean`)

## Anchors exposed (for `LEAN_AUDIT_ANCHORS` registration)

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
