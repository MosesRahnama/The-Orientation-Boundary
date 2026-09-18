import OperatorKO7.Meta.RDRSNonConservativeEscapeAtlas

/-!
# Reach tests for the RDRS T8 nonconservative escape layer.
-/

namespace OperatorKO7.RDRSNonConservativeEscapeAtlas

#check rdrs_nonconservative_escape_layer_closed
#check nonConservativeRows_complete
#check rowStatus_terminal
#check sharing_counter_witness
#check quotient_collapses_duplicate_wrap

theorem reach_marker :
    NonConservativeEscapeLayerClosed :=
  rdrs_nonconservative_escape_layer_closed

theorem reach_row_count :
    nonConservativeRows.length = 10 :=
  nonConservativeRows_length

theorem reach_weighted_type_graph_reason :
    rowReason .weightedTypeGraph = .graphWeightUsesDAGCarrier :=
  weighted_type_graph_row_reason

theorem reach_equational_quotient_reason :
    rowReason .equationalQuotient = .quotientCollapsesDuplication :=
  equational_quotient_row_reason

theorem reach_quasi_interpretation_reason :
    rowReason .quasiInterpretation = .sharingAwareComplexity :=
  quasi_interpretation_row_reason

end OperatorKO7.RDRSNonConservativeEscapeAtlas
