import OperatorKO7.Meta.EstimatedDPGraphTcap

/-!
# Reach test for `OperatorKO7.Meta.EstimatedDPGraphTcap`

Forces elaboration of every public declaration of the estimated-DP-graph TCAP
over-approximation module.
-/

namespace OperatorKO7.Meta.EstimatedDPGraphTcapReach

open OperatorKO7.Meta.EstimatedDPGraphTcap

-- types / carriers
#check (FOTm)
#check (Cap)
#check (Rule)
#check (TRS)

-- defs
#check @FOTm.head
#check @applySubst
#check @applySubstList
#check @definedB
#check @tcap
#check @tcapList
#check @EstEdge
#check @RealEdge
#check (audit_theory_expansion_estimated_dp_graph_tcap_module_anchor)

-- relations
#check @Rstep
#check @Rstar
#check @CapMatches
#check @CapInv

-- lemmas / theorems
#check @capInv_tcap
#check @capMatches_tcap_applySubst
#check @capInv_match_defined_hole
#check @forall₂_append
#check @forall₂_split
#check @capMatches_step_closed
#check @capMatches_tcap_of_rstar
#check @estimated_dp_graph_tcap_unconditional
#check @no_real_edge_of_no_estimated

#print axioms estimated_dp_graph_tcap_unconditional

end OperatorKO7.Meta.EstimatedDPGraphTcapReach
