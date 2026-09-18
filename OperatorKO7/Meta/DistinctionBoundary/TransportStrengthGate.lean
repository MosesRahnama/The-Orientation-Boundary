import OperatorKO7.Meta.LicensedBoundaryCalculus.Transport.Strength

set_option autoImplicit false

/-!
# Transport strength gate

A requested transport map returns theorem-backed success evidence or an exact
negative proof for the requested tier.  Neither success nor rejection is
represented by a proof-free status tag.
-/

namespace OperatorKO7.Meta.DistinctionBoundary.TransportStrengthGate

open OperatorKO7.Meta.LicensedBoundaryCalculus
open OperatorKO7.Meta.LicensedBoundaryCalculus.TransportStrength

universe u v

inductive RequestedTier where
  | simulation
  | equivalence
  | isomorphism
deriving DecidableEq, Repr

inductive MissingLaw where
  | forwardSimulation
  | reductionEquivalence
  | requestedMapIsomorphism
deriving DecidableEq, Repr

/-- An ARS isomorphism that realizes the exact requested map. -/
structure RequestedMapIsomorphism {A : ARS.{u}} {B : ARS.{v}}
    (f : A.Carrier → B.Carrier) where
  iso : ARSIsomorphism A B
  map_eq : ∀ x, iso.toEquiv x = f x

/-- Evidence-indexed result for one exact requested map. -/
inductive GateResult {A : ARS.{u}} {B : ARS.{v}}
    (f : A.Carrier → B.Carrier) where
  | sim (evidence : ForwardStepSimulation f) : GateResult f
  | equiv (evidence : ReductionEquivalence f) : GateResult f
  | iso (evidence : RequestedMapIsomorphism f) : GateResult f
  | simulationRejected (evidence : ¬ ForwardStepSimulation f) : GateResult f
  | equivalenceRejected (evidence : ¬ ReductionEquivalence f) : GateResult f
  | isomorphismRejected (evidence : ¬ Nonempty (RequestedMapIsomorphism f)) :
      GateResult f

/-- Summary tier is derived from the evidence constructor. -/
def requestedTier {A : ARS.{u}} {B : ARS.{v}} {f : A.Carrier → B.Carrier} :
    GateResult f → RequestedTier
  | .sim _ | .simulationRejected _ => .simulation
  | .equiv _ | .equivalenceRejected _ => .equivalence
  | .iso _ | .isomorphismRejected _ => .isomorphism

/-- Missing-law summary exists only for negative constructors. -/
def missingLaw? {A : ARS.{u}} {B : ARS.{v}} {f : A.Carrier → B.Carrier} :
    GateResult f → Option MissingLaw
  | .simulationRejected _ => some .forwardSimulation
  | .equivalenceRejected _ => some .reductionEquivalence
  | .isomorphismRejected _ => some .requestedMapIsomorphism
  | _ => none

def requestSimulation {A : ARS.{u}} {B : ARS.{v}}
    (f : A.Carrier → B.Carrier)
    (h : ForwardStepSimulation f) : GateResult f :=
  .sim h

def requestSimulationRejected {A : ARS.{u}} {B : ARS.{v}}
    (f : A.Carrier → B.Carrier) (h : ¬ ForwardStepSimulation f) : GateResult f :=
  .simulationRejected h

def requestEquivalence {A : ARS.{u}} {B : ARS.{v}}
    (f : A.Carrier → B.Carrier) (h : ReductionEquivalence f) : GateResult f :=
  .equiv h

def requestEquivalenceRejected {A : ARS.{u}} {B : ARS.{v}}
    (f : A.Carrier → B.Carrier) (h : ¬ ReductionEquivalence f) : GateResult f :=
  .equivalenceRejected h

def requestIsomorphism {A : ARS.{u}} {B : ARS.{v}}
    (f : A.Carrier → B.Carrier) (h : RequestedMapIsomorphism f) : GateResult f :=
  .iso h

def requestIsoRejected {A : ARS.{u}} {B : ARS.{v}}
    (f : A.Carrier → B.Carrier)
    (h : ¬ Nonempty (RequestedMapIsomorphism f)) : GateResult f :=
  .isomorphismRejected h

/-- Success at the isomorphism tier really supplies the requested map. -/
theorem iso_realizes_requested_map {A : ARS.{u}} {B : ARS.{v}}
    {f : A.Carrier → B.Carrier} (h : RequestedMapIsomorphism f) :
    ∀ x, h.iso.toEquiv x = f x :=
  h.map_eq

/-- A positive and negative simulation result cannot coincide. -/
theorem simulation_success_ne_rejection {A : ARS.{u}} {B : ARS.{v}}
    (f : A.Carrier → B.Carrier) (h : ForwardStepSimulation f)
    (hn : ¬ ForwardStepSimulation f) :
    requestSimulation f h ≠ requestSimulationRejected f hn := by
  intro hEq
  cases hEq

/-- A concrete identity transport has proof-carrying simulation and isomorphism success. -/
def identityARS (A : ARS.{u}) : RequestedMapIsomorphism (id : A.Carrier → A.Carrier) where
  iso :=
    { toEquiv := Equiv.refl A.Carrier
      step_iff := by intro x y; rfl }
  map_eq := by intro x; rfl

/-- The identity map always simulates one-step reduction. -/
theorem identity_forward_simulation (A : ARS.{u}) :
    ForwardStepSimulation (A := A) (B := A) (id : A.Carrier → A.Carrier) := by
  intro x y h
  exact h

/-- Positive non-vacuity of the repaired gate. -/
def identitySimulationGate (A : ARS.{u}) :
    GateResult (id : A.Carrier → A.Carrier) :=
  requestSimulation _ (identity_forward_simulation A)

/-- Positive isomorphism result is tied to the exact identity map. -/
def identityIsomorphismGate (A : ARS.{u}) :
    GateResult (id : A.Carrier → A.Carrier) :=
  requestIsomorphism _ (identityARS A)

#check @RequestedMapIsomorphism
#check @GateResult.sim
#check @GateResult.simulationRejected
#check @GateResult.iso
#check @GateResult.isomorphismRejected
#check @requestedTier
#check @missingLaw?
#check @iso_realizes_requested_map
#check @identity_forward_simulation
#print axioms iso_realizes_requested_map
#print axioms simulation_success_ne_rejection
#print axioms identity_forward_simulation

end OperatorKO7.Meta.DistinctionBoundary.TransportStrengthGate
