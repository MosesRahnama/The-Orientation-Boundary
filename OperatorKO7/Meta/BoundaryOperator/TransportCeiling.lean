import OperatorKO7.Meta.LicensedBoundaryCalculus.Transport.Counterexamples
import OperatorKO7.Meta.LicensedBoundaryCalculus.Transport.StepLifting

/-!
# Semantic transport implication ceiling

Transport strength is ordered here by theorem-backed implication on one exact
`TransportDatum`.  Constructor ordinals and promotion labels play no role.
`ImplicationRule` is a closed language of generic transport implications, and
`ImplicationRule.apply` interprets every rule on the fixed datum.

A ceiling is not merely a finite list: its members must be supported, pairwise
incomparable under the generic implication language, and every supported
property must be implied by a ceiling member.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.BoundaryOperator.TransportCeiling

open OperatorKO7.Meta.LicensedBoundaryCalculus
open OperatorKO7.Meta.LicensedBoundaryCalculus.PartialLicensedReductionMorphism

universe u v

/-- One exact source, target, and carrier map. -/
structure TransportDatum where
  source : ARS.{u}
  target : ARS.{v}
  map : source.Carrier -> target.Carrier

/-- Semantic properties whose implication structure is audited in this module. -/
inductive TransportProperty where
  | forwardStep
  | forwardReach
  | stepReflection
  | stepLifting
  | terminalExactness
  | bisimulationOnImage
  | reductionEquivalence
  | arsIsomorphism
/-- The proposition represented by one property on one exact datum. -/
def Statement (datum : TransportDatum.{u, v}) : TransportProperty -> Prop
  | .forwardStep => OperatorKO7.Meta.LicensedBoundaryCalculus.TransportStrength.ForwardStepSimulation datum.map
  | .forwardReach => OperatorKO7.Meta.LicensedBoundaryCalculus.TransportStrength.ForwardReachSimulation datum.map
  | .stepReflection => OperatorKO7.Meta.LicensedBoundaryCalculus.TransportStrength.StepReflection datum.map
  | .stepLifting => OperatorKO7.Meta.LicensedBoundaryCalculus.TransportStrength.StepLifting datum.map
  | .terminalExactness => OperatorKO7.Meta.LicensedBoundaryCalculus.TransportStrength.TerminalExactness datum.map
  | .bisimulationOnImage => OperatorKO7.Meta.LicensedBoundaryCalculus.TransportStrength.BisimulationOnImage datum.map
  | .reductionEquivalence => OperatorKO7.Meta.LicensedBoundaryCalculus.TransportStrength.ReductionEquivalence datum.map
  | .arsIsomorphism =>
      ∃ I : OperatorKO7.Meta.LicensedBoundaryCalculus.TransportStrength.ARSIsomorphism datum.source datum.target,
        ∀ x, I.toEquiv x = datum.map x

/-- Semantic support is actual evidence of the represented proposition. -/
def Supported (datum : TransportDatum.{u, v}) (property : TransportProperty) : Prop :=
  Statement datum property

/--
Closed language of generic semantic implications.  It contains only implications
proved from the actual transport semantics.  In particular, no constructor is
generated from a name, annotation, or datum-local target proof.
-/
inductive ImplicationRule : TransportProperty -> TransportProperty -> Type where
  | refl (property : TransportProperty) : ImplicationRule property property
  | forwardStep_to_forwardReach : ImplicationRule .forwardStep .forwardReach
  | bisimulation_to_forwardStep : ImplicationRule .bisimulationOnImage .forwardStep
  | bisimulation_to_stepLifting : ImplicationRule .bisimulationOnImage .stepLifting
  | bisimulation_to_terminalExactness :
      ImplicationRule .bisimulationOnImage .terminalExactness
  | reductionEquivalence_to_forwardReach :
      ImplicationRule .reductionEquivalence .forwardReach
  | arsIsomorphism_to_forwardStep : ImplicationRule .arsIsomorphism .forwardStep
  | arsIsomorphism_to_forwardReach : ImplicationRule .arsIsomorphism .forwardReach
  | arsIsomorphism_to_stepReflection :
      ImplicationRule .arsIsomorphism .stepReflection
  | arsIsomorphism_to_stepLifting : ImplicationRule .arsIsomorphism .stepLifting
  | arsIsomorphism_to_terminalExactness :
      ImplicationRule .arsIsomorphism .terminalExactness
  | arsIsomorphism_to_bisimulationOnImage :
      ImplicationRule .arsIsomorphism .bisimulationOnImage
  | arsIsomorphism_to_reductionEquivalence :
      ImplicationRule .arsIsomorphism .reductionEquivalence
  | trans {p q r : TransportProperty} :
      ImplicationRule p q -> ImplicationRule q r -> ImplicationRule p r

/-- Recover one-step simulation for the exact datum from an isomorphism witness. -/
theorem isomorphismStatement_forwardStep
    {datum : TransportDatum.{u, v}} (h : Statement datum .arsIsomorphism) :
    OperatorKO7.Meta.LicensedBoundaryCalculus.TransportStrength.ForwardStepSimulation datum.map := by
  rcases h with ⟨I, hmap⟩
  intro x y hxy
  have hI := OperatorKO7.Meta.LicensedBoundaryCalculus.TransportStrength.arsIsomorphism_forwardStep I hxy
  simpa only [hmap x, hmap y] using hI

/-- Recover step reflection for the exact datum from an isomorphism witness. -/
theorem isomorphismStatement_stepReflection
    {datum : TransportDatum.{u, v}} (h : Statement datum .arsIsomorphism) :
    OperatorKO7.Meta.LicensedBoundaryCalculus.TransportStrength.StepReflection datum.map := by
  rcases h with ⟨I, hmap⟩
  intro x y hxy
  have hI : datum.target.step (I.toEquiv x) (I.toEquiv y) := by
    simpa only [hmap x, hmap y] using hxy
  exact (I.step_iff x y).2 hI

/-- Recover step lifting for the exact datum from an isomorphism witness. -/
theorem isomorphismStatement_stepLifting
    {datum : TransportDatum.{u, v}} (h : Statement datum .arsIsomorphism) :
    OperatorKO7.Meta.LicensedBoundaryCalculus.TransportStrength.StepLifting datum.map := by
  rcases h with ⟨I, hmap⟩
  intro x z hxz
  have hI : datum.target.step (I.toEquiv x) z := by
    simpa only [hmap x] using hxz
  rcases (OperatorKO7.Meta.LicensedBoundaryCalculus.TransportStrength.arsIsomorphism_stepLifting I) x z hI with
    ⟨y, hxy, hyz⟩
  exact ⟨y, hxy, (hmap y).symm.trans hyz⟩

/-- Recover bisimulation on the exact image. -/
theorem isomorphismStatement_bisimulationOnImage
    {datum : TransportDatum.{u, v}} (h : Statement datum .arsIsomorphism) :
    OperatorKO7.Meta.LicensedBoundaryCalculus.TransportStrength.BisimulationOnImage datum.map :=
  ⟨isomorphismStatement_forwardStep h, isomorphismStatement_stepLifting h⟩

/-- Recover forward reach simulation for the exact datum. -/
theorem isomorphismStatement_forwardReach
    {datum : TransportDatum.{u, v}} (h : Statement datum .arsIsomorphism) :
    OperatorKO7.Meta.LicensedBoundaryCalculus.TransportStrength.ForwardReachSimulation datum.map :=
  OperatorKO7.Meta.LicensedBoundaryCalculus.TransportStrength.forwardStep_implies_forwardReach datum.map (isomorphismStatement_forwardStep h)

/-- Recover reach reflection for the exact datum. -/
theorem isomorphismStatement_reachReflection
    {datum : TransportDatum.{u, v}} (h : Statement datum .arsIsomorphism) :
    OperatorKO7.Meta.LicensedBoundaryCalculus.TransportStrength.ReachReflection datum.map := by
  rcases h with ⟨I, hmap⟩
  intro x y hxy
  have hI : Reach datum.target (I.toEquiv x) (I.toEquiv y) := by
    simpa only [hmap x, hmap y] using hxy
  exact OperatorKO7.Meta.LicensedBoundaryCalculus.TransportStrength.arsIsomorphism_reachReflection I hI

/-- Recover reduction equivalence for the exact datum. -/
theorem isomorphismStatement_reductionEquivalence
    {datum : TransportDatum.{u, v}} (h : Statement datum .arsIsomorphism) :
    OperatorKO7.Meta.LicensedBoundaryCalculus.TransportStrength.ReductionEquivalence datum.map :=
  ⟨isomorphismStatement_forwardReach h, isomorphismStatement_reachReflection h⟩

/-- Every implication-rule constructor is semantically valid on every exact datum. -/
theorem ImplicationRule.apply
    {datum : TransportDatum.{u, v}} {p q : TransportProperty}
    (rule : ImplicationRule p q) : Statement datum p -> Statement datum q := by
  induction rule with
  | refl property =>
      intro h
      exact h
  | forwardStep_to_forwardReach =>
      intro h
      exact OperatorKO7.Meta.LicensedBoundaryCalculus.TransportStrength.forwardStep_implies_forwardReach datum.map h
  | bisimulation_to_forwardStep =>
      intro h
      exact h.forward
  | bisimulation_to_stepLifting =>
      intro h
      exact h.lift
  | bisimulation_to_terminalExactness =>
      intro h
      exact OperatorKO7.Meta.LicensedBoundaryCalculus.TransportStrength.bisimulationOnImage_implies_terminalExactness datum.map h
  | reductionEquivalence_to_forwardReach =>
      intro h
      exact h.forward
  | arsIsomorphism_to_forwardStep =>
      exact isomorphismStatement_forwardStep
  | arsIsomorphism_to_forwardReach =>
      exact isomorphismStatement_forwardReach
  | arsIsomorphism_to_stepReflection =>
      exact isomorphismStatement_stepReflection
  | arsIsomorphism_to_stepLifting =>
      exact isomorphismStatement_stepLifting
  | arsIsomorphism_to_terminalExactness =>
      intro h
      exact OperatorKO7.Meta.LicensedBoundaryCalculus.TransportStrength.bisimulationOnImage_implies_terminalExactness datum.map
        (isomorphismStatement_bisimulationOnImage h)
  | arsIsomorphism_to_bisimulationOnImage =>
      exact isomorphismStatement_bisimulationOnImage
  | arsIsomorphism_to_reductionEquivalence =>
      exact isomorphismStatement_reductionEquivalence
  | trans first second ihFirst ihSecond =>
      intro h
      exact ihSecond (ihFirst h)

/-- Generic implication order, with the stronger property on the left. -/
def GenericallyImplies (p q : TransportProperty) : Prop :=
  Nonempty (ImplicationRule p q)

/-- A simple monotone rank used only to prove strictness of a generic arrow. -/
def implicationRank : TransportProperty -> Nat
  | .arsIsomorphism => 5
  | .bisimulationOnImage => 4
  | .reductionEquivalence => 4
  | .forwardStep => 3
  | .stepReflection => 3
  | .stepLifting => 3
  | .forwardReach => 2
  | .terminalExactness => 2

/-- Every constructor of the generic implication language is rank non-increasing. -/
theorem ImplicationRule.rank_nonincrease {p q : TransportProperty}
    (rule : ImplicationRule p q) : implicationRank q <= implicationRank p := by
  induction rule with
  | refl => exact le_rfl
  | forwardStep_to_forwardReach => norm_num [implicationRank]
  | bisimulation_to_forwardStep => norm_num [implicationRank]
  | bisimulation_to_stepLifting => norm_num [implicationRank]
  | bisimulation_to_terminalExactness => norm_num [implicationRank]
  | reductionEquivalence_to_forwardReach => norm_num [implicationRank]
  | arsIsomorphism_to_forwardStep => norm_num [implicationRank]
  | arsIsomorphism_to_forwardReach => norm_num [implicationRank]
  | arsIsomorphism_to_stepReflection => norm_num [implicationRank]
  | arsIsomorphism_to_stepLifting => norm_num [implicationRank]
  | arsIsomorphism_to_terminalExactness => norm_num [implicationRank]
  | arsIsomorphism_to_bisimulationOnImage => norm_num [implicationRank]
  | arsIsomorphism_to_reductionEquivalence => norm_num [implicationRank]
  | trans first second ihFirst ihSecond =>
      exact ihSecond.trans ihFirst

/-- One genuine strict implication: one-step simulation generically yields reach simulation. -/
theorem forwardStep_strictly_implies_forwardReach :
    GenericallyImplies .forwardStep .forwardReach ∧
      Not (GenericallyImplies .forwardReach .forwardStep) := by
  constructor
  · exact ⟨.forwardStep_to_forwardReach⟩
  · rintro ⟨rule⟩
    have h := rule.rank_nonincrease
    norm_num [implicationRank] at h

/-- Typed falsifier for an advertised non-implication. -/
structure NonImplicationWitness (premise conclusion : TransportProperty) where
  datum : TransportDatum
  premiseEvidence : Statement datum premise
  conclusionFails : Not (Statement datum conclusion)

/-- Semantic antichain: each side is supported somewhere the other fails. -/
structure SemanticAntichain (left right : TransportProperty) where
  leftNotRight : NonImplicationWitness left right
  rightNotLeft : NonImplicationWitness right left

/-! ## Reuse the genuine collapse counterfixtures -/

/-- Exact datum of the pure-state-collapse transport counterexample. -/
def collapseDatum : TransportDatum where
  source := pureStateCollapse_fixture.admittedEdgeARS
  target := pureStateCollapseTarget_fixture
  map := pureStateCollapse_fixture.map

/-- Forward step simulation does not imply step reflection. -/
def forwardStep_not_stepReflection :
    NonImplicationWitness .forwardStep .stepReflection where
  datum := collapseDatum
  premiseEvidence := OperatorKO7.Meta.LicensedBoundaryCalculus.TransportStrength.pureStateCollapse_forwardStep_fixture
  conclusionFails := OperatorKO7.Meta.LicensedBoundaryCalculus.TransportStrength.pureStateCollapse_not_stepReflection_fixture

/-- Forward step simulation does not imply step lifting. -/
def forwardStep_not_stepLifting :
    NonImplicationWitness .forwardStep .stepLifting where
  datum := collapseDatum
  premiseEvidence := OperatorKO7.Meta.LicensedBoundaryCalculus.TransportStrength.pureStateCollapse_forwardStep_fixture
  conclusionFails := OperatorKO7.Meta.LicensedBoundaryCalculus.TransportStrength.pureStateCollapse_not_stepLifting_fixture

/-- Forward step simulation does not imply bisimulation on the image. -/
def forwardStep_not_bisimulationOnImage :
    NonImplicationWitness .forwardStep .bisimulationOnImage where
  datum := collapseDatum
  premiseEvidence := OperatorKO7.Meta.LicensedBoundaryCalculus.TransportStrength.pureStateCollapse_forwardStep_fixture
  conclusionFails := OperatorKO7.Meta.LicensedBoundaryCalculus.TransportStrength.pureStateCollapse_not_bisimulationOnImage_fixture

/-! ## A reverse counterfixture for a genuine antichain -/

inductive AntichainNode
  | source
  | target
  | extra
/-- Source has one supported edge plus one extra edge. -/
def antichainSourceStep (x y : AntichainNode) : Prop :=
  (x = .source ∧ y = .target) ∨ (x = .source ∧ y = .extra)

/-- Target retains only the first edge. -/
def antichainTargetStep (x y : AntichainNode) : Prop :=
  x = .source ∧ y = .target

/-- Source relation for the antichain fixture. -/
def antichainSourceARS : ARS where
  Carrier := AntichainNode
  step := antichainSourceStep
  scope := ⟨.root, .oneStep, .full, .original⟩

/-- Target relation for the antichain fixture. -/
def antichainTargetARS : ARS where
  Carrier := AntichainNode
  step := antichainTargetStep
  scope := ⟨.root, .oneStep, .full, .original⟩

/-- Exact identity-map datum whose target relation is a strict subrelation. -/
def reflectionDatum : TransportDatum where
  source := antichainSourceARS
  target := antichainTargetARS
  map := id

/-- Every target edge is reflected by the source relation. -/
theorem reflectionDatum_stepReflection : Statement reflectionDatum .stepReflection := by
  intro x y hxy
  exact Or.inl hxy

/-- The extra source edge is not simulated by the target relation. -/
theorem reflectionDatum_not_forwardStep : Not (Statement reflectionDatum .forwardStep) := by
  intro h
  have hExtra : antichainSourceStep .source .extra := Or.inr ⟨rfl, rfl⟩
  have hTarget := h hExtra
  simpa [reflectionDatum, antichainTargetARS, antichainTargetStep] using hTarget

/-- Reflection does not imply forward simulation. -/
def stepReflection_not_forwardStep :
    NonImplicationWitness .stepReflection .forwardStep where
  datum := reflectionDatum
  premiseEvidence := reflectionDatum_stepReflection
  conclusionFails := reflectionDatum_not_forwardStep

/-- `forwardStep` and `stepReflection` form a genuine semantic antichain. -/
def forwardStep_stepReflection_antichain :
    SemanticAntichain .forwardStep .stepReflection where
  leftNotRight := forwardStep_not_stepReflection
  rightNotLeft := stepReflection_not_forwardStep

/-! ## A datum with no supported property -/

/-- Forward Boolean edge. -/
def forwardBoolStep (x y : Bool) : Prop := x = false ∧ y = true

/-- Reverse Boolean edge. -/
def reverseBoolStep (x y : Bool) : Prop := x = true ∧ y = false

/-- Forward one-edge system. -/
def forwardBoolARS : ARS where
  Carrier := Bool
  step := forwardBoolStep
  scope := ⟨.root, .oneStep, .full, .original⟩

/-- Oppositely directed one-edge system. -/
def reverseBoolARS : ARS where
  Carrier := Bool
  step := reverseBoolStep
  scope := ⟨.root, .oneStep, .full, .original⟩

/-- Exact identity map between opposite relations. -/
def emptySupportDatum : TransportDatum where
  source := forwardBoolARS
  target := reverseBoolARS
  map := id

/-- The reverse Boolean relation has no outgoing edge from `false`. -/
theorem reverseBool_no_step_from_false (y : Bool) :
    ¬ reverseBoolARS.step false y := by
  intro h
  change reverseBoolStep false y at h
  exact Bool.noConfusion h.1

/-- Any reverse-system path whose source is `false` remains at `false`. -/
theorem reverseSteps_from_false_aux {n : Nat} {x y : Bool}
    (h : Steps reverseBoolARS n x y) (hx : x = false) : y = false :=
  Steps.rec
    (motive := fun _ x y _ => x = false -> y = false)
    (fun _ hx => hx)
    (by
      intro n x next z hxy hyz ih hx
      have hBad : reverseBoolARS.step false next := by
        simpa only [hx] using hxy
      exact (reverseBool_no_step_from_false next hBad).elim)
    h hx

/-- A reverse-system path starting at `false` cannot leave `false`. -/
theorem reverseSteps_from_false {n : Nat} {y : Bool}
    (h : Steps reverseBoolARS n false y) : y = false :=
  reverseSteps_from_false_aux h rfl

/-- The opposite relation does not simulate source steps. -/
theorem emptySupport_not_forwardStep :
    Not (Statement emptySupportDatum .forwardStep) := by
  intro h
  have hBad : reverseBoolStep false true := h ⟨rfl, rfl⟩
  simpa [reverseBoolStep] using hBad

/-- The opposite relation does not simulate source reachability. -/
theorem emptySupport_not_forwardReach :
    Not (Statement emptySupportDatum .forwardReach) := by
  intro h
  have hSource : Reach forwardBoolARS false true :=
    reach_step (A := forwardBoolARS) ⟨rfl, rfl⟩
  rcases h hSource with ⟨n, hTarget⟩
  have hEnd := reverseSteps_from_false hTarget
  cases hEnd

/-- The opposite relation does not reflect target steps. -/
theorem emptySupport_not_stepReflection :
    Not (Statement emptySupportDatum .stepReflection) := by
  intro h
  have hBad : forwardBoolStep true false := h ⟨rfl, rfl⟩
  simpa [forwardBoolStep] using hBad

/-- The opposite relation cannot lift the target edge from `true`. -/
theorem emptySupport_not_stepLifting :
    Not (Statement emptySupportDatum .stepLifting) := by
  intro h
  rcases h (x := true) (z := false) ⟨rfl, rfl⟩ with ⟨y, hSource, _hMap⟩
  change forwardBoolStep true y at hSource
  exact Bool.noConfusion hSource.1

/-- Terminality disagrees at `true`. -/
theorem emptySupport_not_terminalExactness :
    Not (Statement emptySupportDatum .terminalExactness) := by
  intro h
  have hSourceTerminal : OperatorKO7.Meta.LicensedBoundaryCalculus.TransportStrength.IsTerminal forwardBoolARS true := by
    intro y hy
    have hFalse : False := by
      simpa [forwardBoolARS, forwardBoolStep] using hy
    exact False.elim hFalse
  have hTargetNotTerminal : Not (OperatorKO7.Meta.LicensedBoundaryCalculus.TransportStrength.IsTerminal reverseBoolARS true) := by
    intro hTerminal
    exact hTerminal false ⟨rfl, rfl⟩
  exact hTargetNotTerminal ((h true).1 hSourceTerminal)

/-- Bisimulation fails because forward simulation fails. -/
theorem emptySupport_not_bisimulationOnImage :
    Not (Statement emptySupportDatum .bisimulationOnImage) := by
  intro h
  exact emptySupport_not_forwardStep h.forward

/-- Reduction equivalence fails because forward reachability fails. -/
theorem emptySupport_not_reductionEquivalence :
    Not (Statement emptySupportDatum .reductionEquivalence) := by
  intro h
  exact emptySupport_not_forwardReach h.forward

/-- No ARS isomorphism can realize the identity map between the opposite relations. -/
theorem emptySupport_not_arsIsomorphism :
    Not (Statement emptySupportDatum .arsIsomorphism) := by
  rintro ⟨I, hmap⟩
  have hTarget := (I.step_iff false true).1
    (show forwardBoolStep false true from ⟨rfl, rfl⟩)
  have hBad : reverseBoolStep false true := by
    simpa only [hmap false, hmap true] using hTarget
  simpa [reverseBoolStep] using hBad

/-- Exact characterization: the opposite-edge datum supports none of the audited properties. -/
theorem emptySupportDatum_support_empty (property : TransportProperty) :
    Not (Supported emptySupportDatum property) := by
  cases property with
  | forwardStep => exact emptySupport_not_forwardStep
  | forwardReach => exact emptySupport_not_forwardReach
  | stepReflection => exact emptySupport_not_stepReflection
  | stepLifting => exact emptySupport_not_stepLifting
  | terminalExactness => exact emptySupport_not_terminalExactness
  | bisimulationOnImage => exact emptySupport_not_bisimulationOnImage
  | reductionEquivalence => exact emptySupport_not_reductionEquivalence
  | arsIsomorphism => exact emptySupport_not_arsIsomorphism

/-! ## Typed maximal supported antichain -/

/-- A proved semantic ceiling on one exact datum. -/
structure Ceiling (datum : TransportDatum.{u, v}) where
  members : List TransportProperty
  supported : ∀ property, property ∈ members -> Supported datum property
  antichain : ∀ left right,
    left ∈ members -> right ∈ members -> GenericallyImplies left right -> left = right
  dominates : ∀ property, Supported datum property ->
    ∃ ceilingProperty,
      ceilingProperty ∈ members ∧ GenericallyImplies ceilingProperty property

/-- Identity ARS isomorphism on an arbitrary reduction system. -/
def identityIsomorphism (A : ARS.{u}) : OperatorKO7.Meta.LicensedBoundaryCalculus.TransportStrength.ARSIsomorphism A A where
  toEquiv := Equiv.refl A.Carrier
  step_iff := by intro x y; rfl

/-- Exact identity transport datum. -/
def identityDatum (A : ARS.{u}) : TransportDatum.{u, u} where
  source := A
  target := A
  map := id

/-- The identity datum carries actual ARS-isomorphism evidence. -/
theorem identityDatum_isomorphism (A : ARS.{u}) :
    Statement (identityDatum A) .arsIsomorphism := by
  refine ⟨identityIsomorphism A, ?_⟩
  intro x
  rfl

/-- ARS isomorphism generically implies every audited property. -/
theorem arsIsomorphism_dominates (property : TransportProperty) :
    GenericallyImplies .arsIsomorphism property := by
  cases property with
  | forwardStep => exact ⟨.arsIsomorphism_to_forwardStep⟩
  | forwardReach => exact ⟨.arsIsomorphism_to_forwardReach⟩
  | stepReflection => exact ⟨.arsIsomorphism_to_stepReflection⟩
  | stepLifting => exact ⟨.arsIsomorphism_to_stepLifting⟩
  | terminalExactness => exact ⟨.arsIsomorphism_to_terminalExactness⟩
  | bisimulationOnImage => exact ⟨.arsIsomorphism_to_bisimulationOnImage⟩
  | reductionEquivalence => exact ⟨.arsIsomorphism_to_reductionEquivalence⟩
  | arsIsomorphism => exact ⟨.refl .arsIsomorphism⟩

/-- Exact maximal supported antichain for an actual ARS isomorphism datum. -/
def identityTransportCeiling (A : ARS.{u}) : Ceiling (identityDatum A) where
  members := [.arsIsomorphism]
  supported := by
    intro property hmem
    simp only [List.mem_singleton] at hmem
    subst property
    exact identityDatum_isomorphism A
  antichain := by
    intro left right hleft hright himp
    simp only [List.mem_singleton] at hleft hright
    exact hleft.trans hright.symm
  dominates := by
    intro property hSupported
    have _ := hSupported
    exact ⟨.arsIsomorphism, by simp, arsIsomorphism_dominates property⟩

/-- Typed failure object for a requested semantic promotion. -/
structure PromotionFailure (datum : TransportDatum.{u, v})
    (sourceProperty targetProperty : TransportProperty) where
  sourceEvidence : Statement datum sourceProperty
  targetUnavailable : Not (Statement datum targetProperty)
  genericImplicationUnavailable : Not (GenericallyImplies sourceProperty targetProperty)

/-- The collapse fixture yields an evidence-backed failure of promotion to step reflection. -/
def collapsePromotionFailure :
    PromotionFailure collapseDatum .forwardStep .stepReflection where
  sourceEvidence := OperatorKO7.Meta.LicensedBoundaryCalculus.TransportStrength.pureStateCollapse_forwardStep_fixture
  targetUnavailable := OperatorKO7.Meta.LicensedBoundaryCalculus.TransportStrength.pureStateCollapse_not_stepReflection_fixture
  genericImplicationUnavailable := by
    rintro ⟨rule⟩
    have hReflection : Statement collapseDatum .stepReflection :=
      rule.apply (datum := collapseDatum)
        OperatorKO7.Meta.LicensedBoundaryCalculus.TransportStrength.pureStateCollapse_forwardStep_fixture
    exact OperatorKO7.Meta.LicensedBoundaryCalculus.TransportStrength.pureStateCollapse_not_stepReflection_fixture
      hReflection

#check @ImplicationRule.apply
#check @forwardStep_strictly_implies_forwardReach
#check forwardStep_stepReflection_antichain
#check emptySupportDatum_support_empty
#check @Ceiling.dominates
#check @identityTransportCeiling
#check collapsePromotionFailure
#print axioms ImplicationRule.apply
#print axioms forwardStep_strictly_implies_forwardReach
#print axioms reflectionDatum_stepReflection
#print axioms emptySupportDatum_support_empty
#print axioms identityDatum_isomorphism
#print axioms identityTransportCeiling
#print axioms collapsePromotionFailure

end OperatorKO7.Meta.BoundaryOperator.TransportCeiling
