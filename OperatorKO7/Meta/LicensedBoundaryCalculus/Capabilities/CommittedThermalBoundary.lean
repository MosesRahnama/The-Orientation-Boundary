import OperatorKO7.Meta.LicensedBoundaryCalculus.Capabilities.GaugeCapability
import OperatorKO7.Meta.LicensedBoundaryCalculus.Capabilities.ChannelCapability
import OperatorKO7.Meta.LicensedBoundaryCalculus.Capabilities.PayloadForgettingCapability
import OperatorKO7.Meta.LicensedBoundaryCalculus.Capabilities.RecordCapability
import OperatorKO7.Meta.LicensedBoundaryCalculus.Capabilities.ThermalErasureCapability

/-!
# Committed thermal boundary

This specialized carrier bundles the optional evidence required by the legacy
physical reading.  It is intentionally separate from `MinimalBoundary`.

## Audit slots

Relation: one minimal boundary plus five explicit capabilities.
Closure: inherited capability laws.
Trust: kernel-only over supplied physical evidence.
Scope: gauge-covariant, channel-backed, recorded thermal erasure.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.LicensedBoundaryCalculus

universe u v g p r

structure CommittedThermalBoundary (A : ARS.{u}) (B : ARS.{v}) where
  toMinimal : MinimalBoundary A B
  gauge : GaugeCapability.{u, v, g} toMinimal
  channel : ChannelCapability toMinimal
  payloadForgetting : PayloadForgettingCapability.{u, v, p} toMinimal
  record : RecordCapability.{u, v, r} toMinimal
  thermalErasure : ThermalErasureCapability toMinimal

namespace CommittedThermalBoundary

noncomputable section

theorem landauer_floor
    {A : ARS.{u}} {B : ARS.{v}} (boundary : CommittedThermalBoundary A B)
    (x : MinimalBoundary.DomainPoint boundary.toMinimal) :
    boundary.thermalErasure.boltzmannConstant *
        boundary.thermalErasure.temperature * Real.log 2 *
        boundary.thermalErasure.discardedInformationBits x ≤
      boundary.thermalErasure.energyCost x :=
  boundary.thermalErasure.landauer_floor x

/-! ## Non-vacuous two-to-one collapse fixture -/

def collapseMinimal_fixture :
    MinimalBoundary chainARS_fixture
      PartialLicensedReductionMorphism.pureStateCollapseTarget_fixture :=
  ⟨PartialLicensedReductionMorphism.pureStateCollapse_fixture⟩

def collapseGauge_fixture : GaugeCapability collapseMinimal_fixture where
  Gauge := PUnit
  gaugeGroup := inferInstance
  actSource := fun _ x => x
  actTarget := fun _ y => y
  source_one := by intro x; rfl
  source_mul := by intro g h x; rfl
  target_one := by intro y; rfl
  target_mul := by intro g h y; rfl
  domain_preserved := by intro g x hx; exact hx
  map_covariant := by intro g x hx; rfl

def collapseChannel_fixture : ChannelCapability collapseMinimal_fixture where
  send := fun _ => some ()
  sends_domain := by intro x hx; rfl
  silent_outside := by
    intro x houtside
    exact False.elim (houtside trivial)

def collapsePayloadForgetting_fixture :
    PayloadForgettingCapability collapseMinimal_fixture where
  Payload := ChainNode
  payload := fun x => x
  no_recovery := by
    rintro ⟨recover, hrecover⟩
    have hsource := hrecover
      (⟨ChainNode.source, trivial⟩ :
        MinimalBoundary.DomainPoint collapseMinimal_fixture)
    have htarget := hrecover
      (⟨ChainNode.target, trivial⟩ :
        MinimalBoundary.DomainPoint collapseMinimal_fixture)
    have hfalse : ChainNode.source = ChainNode.target :=
      hsource.symm.trans htarget
    cases hfalse

def collapseRecord_fixture : RecordCapability collapseMinimal_fixture where
  Record := Unit
  emit := fun _ => ()
  recordedOutput := fun _ => ()
  record_sound := by intro x; rfl

def collapseThermalErasure_fixture :
    ThermalErasureCapability collapseMinimal_fixture where
  physicalImplementation := True
  implementationWitness := trivial
  discardedInformationBits := fun _ => 1
  discardedInformation_nonneg := by intro x; norm_num
  boltzmannConstant := 1
  boltzmannConstant_pos := by norm_num
  temperature := 1
  temperature_nonneg := by norm_num
  energyCost := fun _ => Real.log 2
  energyCalibration := fun _ energy => energy = Real.log 2
  calibrationHolds := by intro x; rfl
  energyCost_nonneg := by
    intro x
    exact Real.log_nonneg (by norm_num)
  landauerFloor := by intro x; norm_num

def collapseCommittedThermalBoundary_fixture :
    CommittedThermalBoundary chainARS_fixture
      PartialLicensedReductionMorphism.pureStateCollapseTarget_fixture where
  toMinimal := collapseMinimal_fixture
  gauge := collapseGauge_fixture
  channel := collapseChannel_fixture
  payloadForgetting := collapsePayloadForgetting_fixture
  record := collapseRecord_fixture
  thermalErasure := collapseThermalErasure_fixture

theorem collapse_committed_boundary_nonvacuous_fixture :
    collapseCommittedThermalBoundary_fixture.toMinimal.morphism.map
        ⟨ChainNode.source, trivial⟩ = () ∧
      collapseCommittedThermalBoundary_fixture.toMinimal.morphism.map
        ⟨ChainNode.target, trivial⟩ = () ∧
      collapseCommittedThermalBoundary_fixture.thermalErasure.energyCost
        ⟨ChainNode.source, trivial⟩ = Real.log 2 := by
  exact ⟨rfl, rfl, rfl⟩

#check @landauer_floor
#check collapseCommittedThermalBoundary_fixture
#check collapse_committed_boundary_nonvacuous_fixture
#print axioms landauer_floor
#print axioms collapse_committed_boundary_nonvacuous_fixture

end
end CommittedThermalBoundary
end OperatorKO7.Meta.LicensedBoundaryCalculus
