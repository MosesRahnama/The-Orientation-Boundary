import OperatorKO7.Meta.LicensedBoundaryCalculus.Transport.Strength
import OperatorKO7.Meta.LicensedBoundaryCalculus.Core.AdmittedEdgeARS

/-!
# Sharp counterexamples for the transport hierarchy

Finite fixtures prove that a bare carrier map need not simulate steps and that
forward one-step simulation need not provide lifting, bisimulation, or relation
reflection.  These are mechanized no-go results against unconditional upgrades
of weaker transport levels.

## Audit slots

Relation: explicit finite source and target relations.
Closure: one-step counterexamples; no closure ambiguity.
Trust: kernel-only.
Scope: invalid converse exclusions for the transport-strength hierarchy.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.LicensedBoundaryCalculus
namespace TransportStrength

open PartialLicensedReductionMorphism

/-- One-point system with no edge. -/
def emptyUnitARS_fixture : ARS where
  Carrier := Unit
  step := fun _ _ => False
  scope := ⟨.root, .oneStep, .full, .original⟩

/-- A bare carrier map from the chain to a one-point carrier. -/
def chainToEmptyUnitMap_fixture : chainARS_fixture.Carrier -> emptyUnitARS_fixture.Carrier :=
  fun _ => ()

/-- Level 1 does not imply level 2: a carrier map need not simulate a source edge. -/
theorem carrierMap_not_forwardStep_fixture :
    Not (ForwardStepSimulation chainToEmptyUnitMap_fixture) := by
  intro h
  exact h ChainStep.descend

/-- The pure state-collapse morphism does provide forward step simulation. -/
theorem pureStateCollapse_forwardStep_fixture :
    ForwardStepSimulation
      (A := pureStateCollapse_fixture.admittedEdgeARS)
      (B := pureStateCollapseTarget_fixture)
      pureStateCollapse_fixture.map := by
  intro x y h
  convert pureStateCollapse_fixture.map_step h

/-- Forward simulation does not imply step reflection. -/
theorem pureStateCollapse_not_stepReflection_fixture :
    Not (StepReflection
      (A := pureStateCollapse_fixture.admittedEdgeARS)
      (B := pureStateCollapseTarget_fixture)
      pureStateCollapse_fixture.map) := by
  intro hReflect
  let s : DomainCarrier pureStateCollapse_fixture :=
    ⟨ChainNode.source, trivial⟩
  have hTarget : pureStateCollapseTarget_fixture.step
      (pureStateCollapse_fixture.map s)
      (pureStateCollapse_fixture.map s) :=
    trivial
  have hSource := hReflect hTarget
  exact pureStateCollapse_not_step_reflecting_fixture.2 hSource

/-- Forward simulation does not imply step lifting. -/
theorem pureStateCollapse_not_stepLifting_fixture :
    Not (StepLifting
      (A := pureStateCollapse_fixture.admittedEdgeARS)
      (B := pureStateCollapseTarget_fixture)
      pureStateCollapse_fixture.map) := by
  intro hLift
  let t : DomainCarrier pureStateCollapse_fixture :=
    ⟨ChainNode.target, trivial⟩
  rcases hLift t () trivial with ⟨y, hty, _⟩
  cases hty

/-- Consequently, forward simulation alone does not imply bisimulation on the image. -/
theorem pureStateCollapse_not_bisimulationOnImage_fixture :
    Not (BisimulationOnImage
      (A := pureStateCollapse_fixture.admittedEdgeARS)
      (B := pureStateCollapseTarget_fixture)
      pureStateCollapse_fixture.map) := by
  intro h
  exact pureStateCollapse_not_stepLifting_fixture h.lift

#check carrierMap_not_forwardStep_fixture
#check pureStateCollapse_forwardStep_fixture
#check pureStateCollapse_not_stepReflection_fixture
#check pureStateCollapse_not_stepLifting_fixture
#check pureStateCollapse_not_bisimulationOnImage_fixture
#print axioms carrierMap_not_forwardStep_fixture
#print axioms pureStateCollapse_forwardStep_fixture
#print axioms pureStateCollapse_not_stepReflection_fixture
#print axioms pureStateCollapse_not_stepLifting_fixture
#print axioms pureStateCollapse_not_bisimulationOnImage_fixture

end TransportStrength
end OperatorKO7.Meta.LicensedBoundaryCalculus
