import OperatorKO7.Meta.BoundaryOperator

namespace BoundaryOperatorReach

open OperatorKO7.Meta.BoundaryOperator

#check KineticEnergy
#check Observable
#check Channel
#check Channel.send
#check Channel.preserves_isolation
#check MetaLayer
#check LawvereYanofskyNegativeSeparation
#check BoundaryOperator
#check DomainPoint
#check partiality_holds
#check irreversibility_holds
#check gaugeCovariance_holds
#check channelPreservation_holds
#check payloadDiscarding_holds
#check landauerCost_holds
#check Z2
#check Z2.actOptionBool
#check Z2.actBool
#check toyChannel
#check toyBoundaryOperator
#check toyBoundaryOperator_domain_none
#check toyBoundaryOperator_domain_some
#check toyBoundaryOperator_apply_some
#check toyBoundaryOperator_two_live_inputs
#check toyBoundaryOperator_second_live_input

example : toyBoundaryOperator.domain (some false) := by
  simpa using toyBoundaryOperator_domain_some false

example : toyBoundaryOperator.domain (some true) := by
  simpa using toyBoundaryOperator_domain_some true

example : toyBoundaryOperator.channel.send (some true) = some false := by
  rfl

example (h : toyBoundaryOperator.domain (some true)) :
    toyBoundaryOperator.apply (some true) h = false := by
  simpa using toyBoundaryOperator_apply_some true h

example : ¬ toyBoundaryOperator.domain none :=
  toyBoundaryOperator_domain_none

end BoundaryOperatorReach
