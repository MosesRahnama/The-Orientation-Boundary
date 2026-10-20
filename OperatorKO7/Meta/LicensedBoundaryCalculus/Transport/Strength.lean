import OperatorKO7.Meta.LicensedBoundaryCalculus.LicensedARS

/-!
# Transport-strength hierarchy

This module assigns separate formal predicates to forward simulation,
reflection, lifting, terminal exactness, bisimulation on the image, reduction
equivalence, and full ARS isomorphism.  Strong terminology is therefore
licensed only by the corresponding proved field.

## Audit slots

Relation: caller-supplied source and target one-step relations.
Closure: one-step and reflexive-transitive reachability are kept separate.
Trust: kernel-only.
Scope: universal transport-strength definitions and valid implication arrows.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.LicensedBoundaryCalculus
namespace TransportStrength

universe u v

variable {A : ARS.{u}} {B : ARS.{v}}

/-- Every source step maps to a target step. -/
def ForwardStepSimulation (f : A.Carrier -> B.Carrier) : Prop :=
  forall {x y}, A.step x y -> B.step (f x) (f y)

/-- Every source reachability witness maps to target reachability. -/
def ForwardReachSimulation (f : A.Carrier -> B.Carrier) : Prop :=
  forall {x y}, Reach A x y -> Reach B (f x) (f y)

/-- Target steps between mapped endpoints reflect to source steps. -/
def StepReflection (f : A.Carrier -> B.Carrier) : Prop :=
  forall {x y}, B.step (f x) (f y) -> A.step x y

/-- Every target successor of a mapped state has a source-step lift. -/
def StepLifting (f : A.Carrier -> B.Carrier) : Prop :=
  forall (x : A.Carrier) (z : B.Carrier), B.step (f x) z ->
    exists y : A.Carrier, A.step x y ∧ f y = z

/-- Target reachability between mapped endpoints reflects to the source. -/
def ReachReflection (f : A.Carrier -> B.Carrier) : Prop :=
  forall {x y}, Reach B (f x) (f y) -> Reach A x y

/-- A state has no outgoing one-step edge. -/
def IsTerminal (A : ARS.{u}) (x : A.Carrier) : Prop :=
  forall y, Not (A.step x y)

/-- Source terminality agrees exactly with target terminality on mapped states. -/
def TerminalExactness (f : A.Carrier -> B.Carrier) : Prop :=
  forall x, IsTerminal A x <-> IsTerminal B (f x)

/-- Forward simulation plus lifting of every target successor from the image. -/
structure BisimulationOnImage (f : A.Carrier -> B.Carrier) : Prop where
  forward : ForwardStepSimulation f
  lift : StepLifting f

/-- Forward and reflected reachability on mapped endpoints. -/
structure ReductionEquivalence (f : A.Carrier -> B.Carrier) : Prop where
  forward : ForwardReachSimulation f
  reflect : ReachReflection f

/-- A carrier equivalence preserving and reflecting the one-step relation. -/
structure ARSIsomorphism (A : ARS.{u}) (B : ARS.{v}) where
  toEquiv : A.Carrier ≃ B.Carrier
  step_iff : forall x y, A.step x y <-> B.step (toEquiv x) (toEquiv y)

/-- One-step simulation universally implies forward reachability simulation. -/
theorem forwardStep_implies_forwardReach
    (f : A.Carrier -> B.Carrier) (h : ForwardStepSimulation f) :
    ForwardReachSimulation f := by
  intro x y hxy
  rcases hxy with ⟨n, hn⟩
  exact ⟨n, Steps.map f h hn⟩

/-- Bisimulation on the image forces terminal exactness. -/
theorem bisimulationOnImage_implies_terminalExactness
    (f : A.Carrier -> B.Carrier) (h : BisimulationOnImage f) :
    TerminalExactness f := by
  intro x
  constructor
  · intro hx z hz
    rcases h.lift x z hz with ⟨y, hxy, _⟩
    exact hx y hxy
  · intro hx y hxy
    exact hx (f y) (h.forward hxy)

/-- An ARS isomorphism gives forward one-step simulation. -/
theorem arsIsomorphism_forwardStep (I : ARSIsomorphism A B) :
    ForwardStepSimulation I.toEquiv := by
  intro x y hxy
  exact (I.step_iff x y).1 hxy

/-- An ARS isomorphism lifts every target successor. -/
theorem arsIsomorphism_stepLifting (I : ARSIsomorphism A B) :
    StepLifting I.toEquiv := by
  intro x z hxz
  refine ⟨I.toEquiv.symm z, ?_, I.toEquiv.apply_symm_apply z⟩
  apply (I.step_iff x (I.toEquiv.symm z)).2
  simpa using hxz

/-- An ARS isomorphism gives bisimulation on the image. -/
theorem arsIsomorphism_bisimulationOnImage (I : ARSIsomorphism A B) :
    BisimulationOnImage I.toEquiv :=
  ⟨arsIsomorphism_forwardStep I, arsIsomorphism_stepLifting I⟩

/-- An ARS isomorphism preserves forward reachability. -/
theorem arsIsomorphism_forwardReach (I : ARSIsomorphism A B) :
    ForwardReachSimulation I.toEquiv :=
  forwardStep_implies_forwardReach I.toEquiv (arsIsomorphism_forwardStep I)

/-- An ARS isomorphism reflects reachability. -/
theorem arsIsomorphism_reachReflection (I : ARSIsomorphism A B) :
    ReachReflection I.toEquiv := by
  intro x y hxy
  rcases hxy with ⟨n, hn⟩
  have hback : forall {p q : B.Carrier}, B.step p q ->
      A.step (I.toEquiv.symm p) (I.toEquiv.symm q) := by
    intro p q hpq
    apply (I.step_iff (I.toEquiv.symm p) (I.toEquiv.symm q)).2
    simpa using hpq
  have hmapped := Steps.map I.toEquiv.symm hback hn
  refine ⟨n, ?_⟩
  simpa using hmapped

/-- An ARS isomorphism gives reduction equivalence. -/
theorem arsIsomorphism_reductionEquivalence (I : ARSIsomorphism A B) :
    ReductionEquivalence I.toEquiv :=
  ⟨arsIsomorphism_forwardReach I, arsIsomorphism_reachReflection I⟩

/-- An ARS isomorphism forces terminal exactness. -/
theorem arsIsomorphism_terminalExactness (I : ARSIsomorphism A B) :
    TerminalExactness I.toEquiv :=
  bisimulationOnImage_implies_terminalExactness _
    (arsIsomorphism_bisimulationOnImage I)

#check @forwardStep_implies_forwardReach
#check @bisimulationOnImage_implies_terminalExactness
#check @arsIsomorphism_bisimulationOnImage
#check @arsIsomorphism_reductionEquivalence
#check @arsIsomorphism_terminalExactness
#print axioms forwardStep_implies_forwardReach
#print axioms bisimulationOnImage_implies_terminalExactness
#print axioms arsIsomorphism_bisimulationOnImage
#print axioms arsIsomorphism_reductionEquivalence
#print axioms arsIsomorphism_terminalExactness

end TransportStrength
end OperatorKO7.Meta.LicensedBoundaryCalculus
