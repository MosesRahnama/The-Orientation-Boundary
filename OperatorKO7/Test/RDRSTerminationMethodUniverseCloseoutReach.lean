import OperatorKO7.Meta.RDRSTerminationMethodUniverseCloseout

/-!
# Reach test: RDRS termination-method universe final closeout

Probes that every layer marker is reachable through the final
closeout certificate and that the 76-row universe substrate is
visible at the top level.

Bible compliance:
- W2: `set_option autoImplicit false` set below.
- Reach / smoke test; not a release-facing theorem module.
  All theorems pin existing aggregate facts by structural projection
  on the closeout certificate; Trust: kernel-only.
-/

set_option autoImplicit false

namespace RDRSTerminationMethodUniverseCloseoutReach

open OperatorKO7.RDRSTerminationMethodUniverse
open OperatorKO7.RDRSTerminationMethodUniverseCloseout

#check RDRSUniverseClosed
#check rdrs_termination_method_universe_closed
#check rdrs_termination_method_universe_closed_anchor
#check rdrs_termination_method_universe_closed.universeRowCount
#check rdrs_termination_method_universe_closed.universeRowsNodup
#check rdrs_termination_method_universe_closed.universeRowsComplete
#check rdrs_termination_method_universe_closed.statusTotal
#check rdrs_termination_method_universe_closed.atlasComplete
#check rdrs_termination_method_universe_closed.pathOrderLayerClosed
#check rdrs_termination_method_universe_closed.algebraicInterpretationLayerClosed
#check rdrs_termination_method_universe_closed.semanticStructuralLayerClosed
#check rdrs_termination_method_universe_closed.dpProcessorClassificationClosed
#check rdrs_termination_method_universe_closed.typeComputabilityNoBarrierZonesClosed
#check rdrs_termination_method_universe_closed.nonconservativeEscapeLayerClosed
#check rdrs_termination_method_universe_closed.conditionalTypedLayerClosed

/-- The 76-row universe count is reachable through the closeout. -/
theorem reach_universe_row_count :
    OperatorKO7.RDRSTerminationMethodUniverse.allMethodFamilies.length = 76 :=
  rdrs_termination_method_universe_closed.universeRowCount

/-- The universe row enum is `Nodup` through the closeout. -/
theorem reach_universe_rows_nodup :
    OperatorKO7.RDRSTerminationMethodUniverse.allMethodFamilies.Nodup :=
  rdrs_termination_method_universe_closed.universeRowsNodup

/-- Every termination-method family appears in the universe row list. -/
theorem reach_universe_rows_complete
    (family : OperatorKO7.RDRSTerminationMethodUniverse.RDRSMethodFamily) :
    family ∈ OperatorKO7.RDRSTerminationMethodUniverse.allMethodFamilies :=
  rdrs_termination_method_universe_closed.universeRowsComplete family

/-- Every row has a terminal `statusOf` through the closeout. -/
theorem reach_status_total
    (family : OperatorKO7.RDRSTerminationMethodUniverse.RDRSMethodFamily) :
    ∃ status : OperatorKO7.RDRSTerminationMethodUniverse.RDRSMethodStatus,
      OperatorKO7.RDRSTerminationMethodUniverse.statusOf family = status :=
  rdrs_termination_method_universe_closed.statusTotal family

/-- The audit anchor is the expected fully-qualified Lean name. -/
theorem reach_anchor_value :
    rdrs_termination_method_universe_closed_anchor =
      "OperatorKO7.RDRSTerminationMethodUniverseCloseout.rdrs_termination_method_universe_closed" :=
  rfl

end RDRSTerminationMethodUniverseCloseoutReach
