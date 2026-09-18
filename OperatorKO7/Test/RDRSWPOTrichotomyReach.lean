import OperatorKO7.Meta.RDRSWPOTrichotomy

/-!
Reach test for the T3 WPO-trichotomy shim at
`Meta/RDRSWPOTrichotomy.lean`. Confirms that:

* The shim's namespace is reachable.
* The supersession marker is closed.
* The two real substitute modules' closure markers resolve transitively.
-/

namespace OperatorKO7.Test.RDRSWPOTrichotomyReach

#check @OperatorKO7.RDRSWPOTrichotomy.supersededBy
#check @OperatorKO7.RDRSWPOTrichotomy.rdrs_wpo_trichotomy_shim_marker
#check @OperatorKO7.RDRSAlgebraicInterpretationAtlas.rdrs_algebraic_interpretation_layer_closed
#check @OperatorKO7.RDRSPathOrderDichotomy.pathOrderAtlasRows_length

end OperatorKO7.Test.RDRSWPOTrichotomyReach
