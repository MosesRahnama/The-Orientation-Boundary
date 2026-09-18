import OperatorKO7.Meta.EstimatedDPGraphTCAPSoundness

set_option autoImplicit false

/-!
# Reach test for `OperatorKO7.Meta.EstimatedDPGraphTCAPSoundness`
-/

namespace OperatorKO7.Test.EstimatedDPGraphTCAPSoundnessReach

open OperatorKO7.Meta.EstimatedDPGraphTcap
open OperatorKO7.Meta.EstimatedDPGraphTCAPSoundness

#check KO7DPPairNode
#check ko7_pair_surface_matches_replay
#check ko7_dp_schema_count_matches_replay
#check ko7_extracted_call_graph_supports_recD_successor
#check ko7PairRule
#check ko7RealDPEdge
#check ko7EstimatedDPEdge
#check ko7_estimated_self_edge
#check @estimated_dp_graph_tcap_overapproximation_sound
#check @transGen_transport
#check @real_dp_path_is_tcap_path
#check @real_dp_cycle_is_tcap_cycle
#check positive_real_edge_witness
#check positive_real_edge_is_estimated
#check negative_estimated_edge_witness
#check audit_estimated_dp_graph_tcap_soundness_anchor

example : ko7EstimatedDPEdge .recSucc .recSucc :=
  ko7_estimated_self_edge

example :
    ko7RealDPEdge .recSucc .recSucc →
      ko7EstimatedDPEdge .recSucc .recSucc :=
  estimated_dp_graph_tcap_overapproximation_sound

example :
    EstEdge witnessTRS positiveSourcePair positiveTargetPair :=
  positive_real_edge_is_estimated

example :
    ¬ EstEdge witnessTRS negativeSourcePair negativeTargetPair :=
  negative_estimated_edge_witness

end OperatorKO7.Test.EstimatedDPGraphTCAPSoundnessReach
