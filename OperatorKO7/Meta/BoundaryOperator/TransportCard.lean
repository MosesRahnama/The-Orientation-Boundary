import OperatorKO7.Meta.LicensedBoundaryCalculus.API.Structural
import OperatorKO7.Meta.LicensedBoundaryCalculus.Audit.ClaimEntry

/-!
# Transport evidence and blocked-transport records

`VerifiedTransportCard` stores source and target carriers, one-step relations, a map, and evidence
for the proposition selected by its `TransportStrength`. Its source carrier also has a supplied
distinctness witness. The claim tier, preservation lists, and `Lean.Name` anchors are annotations;
this structure does not verify their coherence or declaration resolution. `NoTransportCard` stores
a designated missing proposition, an optional strength annotation, and a typed falsifier
specification, with no transport-map or transport-evidence fields.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.BoundaryOperator

open OperatorKO7.Meta.LicensedBoundaryCalculus.Audit

inductive TransportStrength
  | commonCarrier
  | forwardStepSimulation
  | forwardReachSimulation
  | galoisConnection
  | stepLifting
  | bisimulationOnImage
  | reductionEquivalence
  | arsIsomorphism
  deriving DecidableEq, Repr

inductive ClaimTier
  | theorem
  | conditional
  | model
  | analogy
  | externalCitation
  | noTransport
  deriving DecidableEq, Repr

abbrev Reach {X : Type} (step : X -> X -> Prop) :=
  Relation.ReflTransGen step

/-- Proposition selected by each transport-strength constructor. -/
def TransportStatement
    {Source Target : Type}
    (sourceStep : Source -> Source -> Prop)
    (targetStep : Target -> Target -> Prop)
    (forwardMap : Source -> Target)
    (backwardMap? : Option (Target -> Source)) :
    TransportStrength -> Prop
  | .commonCarrier =>
      ∃ e : Source ≃ Target, ∀ x, forwardMap x = e x
  | .forwardStepSimulation =>
      ∀ {x y}, sourceStep x y -> targetStep (forwardMap x) (forwardMap y)
  | .forwardReachSimulation =>
      ∀ {x y}, Reach sourceStep x y ->
        Reach targetStep (forwardMap x) (forwardMap y)
  | .galoisConnection =>
      ∃ backwardMap : Target -> Source,
        backwardMap? = some backwardMap ∧
          ∀ x y, targetStep (forwardMap x) y ↔
            sourceStep x (backwardMap y)
  | .stepLifting =>
      (∀ {x y}, sourceStep x y ->
        targetStep (forwardMap x) (forwardMap y)) ∧
      ∀ {x y}, targetStep (forwardMap x) y ->
        ∃ x', sourceStep x x' ∧ forwardMap x' = y
  | .bisimulationOnImage =>
      (∀ {x y}, sourceStep x y ->
        targetStep (forwardMap x) (forwardMap y)) ∧
      ∀ {x y}, targetStep (forwardMap x) (forwardMap y) ->
        sourceStep x y
  | .reductionEquivalence =>
      ∃ backwardMap : Target -> Source,
        backwardMap? = some backwardMap ∧
          (∀ x y, Reach sourceStep x y ↔
            Reach targetStep (forwardMap x) (forwardMap y)) ∧
          ∀ x y, Reach targetStep x y ↔
            Reach sourceStep (backwardMap x) (backwardMap y)
  | .arsIsomorphism =>
      ∃ e : Source ≃ Target,
        (∀ x, forwardMap x = e x) ∧
        backwardMap? = some e.symm ∧
        ∀ x y, sourceStep x y ↔ targetStep (e x) (e y)

/-- A typed transport witness plus source-side distinctness and unchecked descriptive annotations. -/
structure VerifiedTransportCard where
  name : String
  Source : Type
  Target : Type
  sourceStep : Source -> Source -> Prop
  targetStep : Target -> Target -> Prop
  forwardMap : Source -> Target
  backwardMap? : Option (Target -> Source)
  strength : TransportStrength
  evidence :
    TransportStatement sourceStep targetStep forwardMap backwardMap? strength
  sourceNontrivial : ∃ x y : Source, x ≠ y
  preservedRelations : List String
  preservedObservables : List String
  preservedResources : List String
  claimTier : ClaimTier
  sourceAnchor : Lean.Name
  targetAnchor : Lean.Name
  mapAnchor : Lean.Name

/-- Alias for `VerifiedTransportCard`. -/
abbrev TransportCard := VerifiedTransportCard

/-- A named proposition designated by a blocked-transport record. -/
structure MissingTheorem where
  name : String
  name_nonempty : name ≠ ""
  statement : Prop

/-- Blocked-transport record containing a missing proposition and falsifier specification. -/
structure NoTransportCard where
  name : String
  missingTheorem : MissingTheorem
  currentMaximumStrength : Option TransportStrength
  falsifierSpec : TypedFalsifierSpec
  claimTier : ClaimTier
  sourceAnchorHints : List String
  targetAnchorHints : List String

inductive TransportDisposition
  | verified (card : VerifiedTransportCard)
  | blocked (card : NoTransportCard)

/-- Both carriers are equivalent to `Unit`. -/
def VerifiedTransportCard.UsesUnitPlaceholder
    (card : VerifiedTransportCard) : Prop :=
  Nonempty (card.Source ≃ Unit) ∧ Nonempty (card.Target ≃ Unit)

theorem verifiedTransportCard_not_unit_placeholder
    (card : VerifiedTransportCard) :
    ¬ card.UsesUnitPlaceholder := by
  intro hplaceholder
  rcases card.sourceNontrivial with ⟨x, y, hxy⟩
  rcases hplaceholder.1 with ⟨equiv⟩
  apply hxy
  apply equiv.injective
  cases equiv x
  cases equiv y
  rfl

/-! ## Two-point fixture -/

def twoPointCarrier_fixture : VerifiedTransportCard where
  name := "two-point-identity"
  Source := Bool
  Target := Bool
  sourceStep := Eq
  targetStep := Eq
  forwardMap := id
  backwardMap? := some id
  strength := .commonCarrier
  evidence := by
    exact ⟨Equiv.refl Bool, fun _ => rfl⟩
  sourceNontrivial := ⟨false, true, by decide⟩
  preservedRelations := ["equality"]
  preservedObservables := []
  preservedResources := []
  claimTier := .model
  sourceAnchor := ``Bool
  targetAnchor := ``Bool
  mapAnchor := ``id

theorem twoPointCarrier_fixture_nonplaceholder :
    ¬ twoPointCarrier_fixture.UsesUnitPlaceholder :=
  verifiedTransportCard_not_unit_placeholder twoPointCarrier_fixture

#check @TransportStatement
#check verifiedTransportCard_not_unit_placeholder
#check twoPointCarrier_fixture_nonplaceholder
#print axioms verifiedTransportCard_not_unit_placeholder
#print axioms twoPointCarrier_fixture_nonplaceholder

end OperatorKO7.Meta.BoundaryOperator
