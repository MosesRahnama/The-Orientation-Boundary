import OperatorKO7.Meta.DistinctionBoundary.TransportStrengthGate

/-! # Reach and axiom gate for the evidence-indexed transport strength gate. -/

set_option autoImplicit false

open OperatorKO7.Meta.DistinctionBoundary.TransportStrengthGate

#check @RequestedTier
#print axioms RequestedTier
#check @RequestedTier.simulation
#print axioms RequestedTier.simulation
#check @RequestedTier.equivalence
#print axioms RequestedTier.equivalence
#check @RequestedTier.isomorphism
#print axioms RequestedTier.isomorphism
#check @MissingLaw
#print axioms MissingLaw
#check @MissingLaw.forwardSimulation
#print axioms MissingLaw.forwardSimulation
#check @MissingLaw.reductionEquivalence
#print axioms MissingLaw.reductionEquivalence
#check @MissingLaw.requestedMapIsomorphism
#print axioms MissingLaw.requestedMapIsomorphism
#check @RequestedMapIsomorphism
#print axioms RequestedMapIsomorphism
#check @RequestedMapIsomorphism.mk
#print axioms RequestedMapIsomorphism.mk
#check @RequestedMapIsomorphism.iso
#print axioms RequestedMapIsomorphism.iso
#check @RequestedMapIsomorphism.map_eq
#print axioms RequestedMapIsomorphism.map_eq
#check @GateResult
#print axioms GateResult
#check @GateResult.sim
#print axioms GateResult.sim
#check @GateResult.equiv
#print axioms GateResult.equiv
#check @GateResult.iso
#print axioms GateResult.iso
#check @GateResult.simulationRejected
#print axioms GateResult.simulationRejected
#check @GateResult.equivalenceRejected
#print axioms GateResult.equivalenceRejected
#check @GateResult.isomorphismRejected
#print axioms GateResult.isomorphismRejected
#check @requestedTier
#print axioms requestedTier
#check @missingLaw?
#print axioms missingLaw?
#check @requestSimulation
#print axioms requestSimulation
#check @requestSimulationRejected
#print axioms requestSimulationRejected
#check @requestEquivalence
#print axioms requestEquivalence
#check @requestEquivalenceRejected
#print axioms requestEquivalenceRejected
#check @requestIsomorphism
#print axioms requestIsomorphism
#check @requestIsoRejected
#print axioms requestIsoRejected
#check @iso_realizes_requested_map
#print axioms iso_realizes_requested_map
#check @simulation_success_ne_rejection
#print axioms simulation_success_ne_rejection
#check @identityARS
#print axioms identityARS
#check @identity_forward_simulation
#print axioms identity_forward_simulation
#check @identitySimulationGate
#print axioms identitySimulationGate
#check @identityIsomorphismGate
#print axioms identityIsomorphismGate
