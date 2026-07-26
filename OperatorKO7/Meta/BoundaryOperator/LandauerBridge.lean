import OperatorKO7.Meta.BoundaryOperator
import OperatorKO7.Meta.Physics.LandauerHeatBound

/-!
# Boundary Operator Landauer Bridge

This module connects a fired boundary-operator point to a record-formation
surface. It transports the supplied `landauer_per_bit_floor` theorem to a
boundary-level cost lower bound from a concrete record-formation event and heat
comparison witness. The physical heat law remains an explicit premise.
-/

namespace OperatorKO7.Meta.BoundaryOperator

open OperatorKO7.Meta.Physics.RecordFormation
open OperatorKO7.Meta.Physics.LandauerHeatBound

universe u v

/-- Explicit certificate linking one fired boundary-operator plug to one
record-formation event and the released heat used in the Landauer lane. -/
structure BoundaryRecordFormationLink
    {X : Type u} {Y : Type v} (B : BoundaryOperator X Y) where
  point : DomainPoint B
  event : RecordFormationEvent
  releasedHeat : ℝ
  releasedHeat_le_boundary_cost :
    releasedHeat ≤ B.landauer_cost point.1 point.2

/-- The fired verdict attached to a boundary/record-formation link. -/
abbrev BoundaryRecordFormationLink.verdict
    {X : Type u} {Y : Type v} {B : BoundaryOperator X Y}
    (L : BoundaryRecordFormationLink B) : Y :=
  B.apply L.point.1 L.point.2

/-- The underlying boundary channel still records the linked verdict. -/
theorem BoundaryRecordFormationLink.channel_records_verdict
    {X : Type u} {Y : Type v} {B : BoundaryOperator X Y}
    (L : BoundaryRecordFormationLink B) :
    B.channel.send L.point.1 = some L.verdict := by
  simpa [BoundaryRecordFormationLink.verdict] using
    channelPreservation_holds B L.point.1 L.point.2

/-- Transport the conditional Landauer lower bound into a boundary-level cost
statement under the supplied physical heat-law hypothesis. -/
theorem boundaryLandauerCostDominatesPerBitFloor
    {X : Type u} {Y : Type v} {B : BoundaryOperator X Y}
    (L : BoundaryRecordFormationLink B)
    (hApp : LandauerApplicable L.event B.temperature)
    (hLaw : LandauerHeatLaw L.event B.kB B.temperature L.releasedHeat) :
    landauerLowerBound L.event B.kB B.temperature ≤
      B.landauer_cost L.point.1 L.point.2 := by
  have hFloor := landauer_per_bit_floor hApp hLaw
  exact le_trans hFloor L.releasedHeat_le_boundary_cost

/-- The bridge also yields the available/unavailable status object from the
physics lane once the explicit hypotheses are present. -/
noncomputable def boundaryLandauerAvailableStatus
    {X : Type u} {Y : Type v} {B : BoundaryOperator X Y}
    (L : BoundaryRecordFormationLink B)
    (hApp : LandauerApplicable L.event B.temperature)
    (hLaw : LandauerHeatLaw L.event B.kB B.temperature L.releasedHeat) :
    LandauerBoundStatus L.event B.kB B.temperature :=
  availableBound hApp hLaw

end OperatorKO7.Meta.BoundaryOperator
