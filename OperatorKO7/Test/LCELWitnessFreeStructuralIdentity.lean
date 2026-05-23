import OperatorKO7.Meta.LCELAdmissibilityData
import OperatorKO7.Meta.LCELUnrestrictedExistence
import OperatorKO7.Meta.LCELUnrestrictedClassification
import OperatorKO7.Meta.LCELWitnessFreeStructuralIdentity

namespace LCELWitnessFreeStructuralIdentityReach

open OperatorKO7
open OperatorKO7.LCELAdmissibility
open OperatorKO7.LCELUnrestrictedTheorem
open OperatorKO7.LCELUnrestrictedExistence
open OperatorKO7.LCELUnrestrictedClassification
open OperatorKO7.LCELWitnessFreeStructuralIdentity
open OperatorKO7.LCELBenchmarkDpUnrestrictedTheorem

/-! Tests covering the post-closure Phases P2 / P3 / P4A / P4B. -/

/-! ### Phase P2: admissibility data carrier and coincidence with
canonical admissible instances -/

example : True := by
  have := godel1931LCELAdmissibilityData
  trivial

example : True := by
  have := benchmarkTransportLCELAdmissibilityData
  trivial

example : True := by
  have := dpEmitterLCELAdmissibilityData
  trivial

example : True := by
  have :=
    LCELAdmissibilityData.toAdmissibleInstance godel1931LCELAdmissibilityData
  trivial

/-- Regression: the lifted admissible instance coincides with the
existing canonical admissible instance. -/
example :
    godel1931LCELAdmissibilityData.toAdmissibleInstance
      = OperatorKO7.LCELUniversalTheorem.godel1931AdmissibleLCELInstance :=
  godel1931LCELAdmissibilityData_toAdmissibleInstance_eq

example :
    benchmarkTransportLCELAdmissibilityData.toAdmissibleInstance
      = OperatorKO7.LCELUniversalTheorem.benchmarkTransportAdmissibleLCELInstance :=
  benchmarkTransportLCELAdmissibilityData_toAdmissibleInstance_eq

example :
    dpEmitterLCELAdmissibilityData.toAdmissibleInstance
      = OperatorKO7.LCELUniversalTheorem.dpEmitterAdmissibleLCELInstance :=
  dpEmitterLCELAdmissibilityData_toAdmissibleInstance_eq

/-! ### Phase P3: witness-existence predicate and canonical existence lemmas -/

example : True := by
  have := @AdmitsLCELUnrestrictedWitness
  trivial

example : True := by
  have := godel_dp_admitsUnrestrictedWitness
  trivial

example : True := by
  have := godel_benchmark_admitsUnrestrictedWitness
  trivial

example : True := by
  have := godel_dp_existsStructuralIdentityFromExistsWitness
  trivial

example : True := by
  have := godel_benchmark_existsStructuralIdentityFromExistsWitness
  trivial

/-- The canonical Gödel ↔ DP existence lemma really does produce an
admissibility pair whose underlying LCEL carriers are the raw canonical
instances. Extracts the existential and checks the equality fields. -/
example :
    ∃ A₁ A₂ : OperatorKO7.LCELUniversalTheorem.AdmissibleLCELInstance,
      A₁.instance_ = OperatorKO7.LCELSchema.godel1931LCELInstance
        ∧ A₂.instance_ = OperatorKO7.LCELDpInstance.dpEmitterLCELInstance
        ∧ Nonempty
            (OperatorKO7.LCELUniversalTheorem.LCELUniversalQuasiFunctor A₁ A₂) :=
  lcel_unrestricted_structural_identity_of_existsWitness
    godel_dp_admitsUnrestrictedWitness

/-! ### Phase P4A: classification predicate and equivalence theorem -/

example : True := by
  have :=
    admitsUnrestrictedWitness_iff
      OperatorKO7.LCELSchema.godel1931LCELInstance
      OperatorKO7.LCELDpInstance.dpEmitterLCELInstance
  trivial

example : True := by
  have := godel_dp_classificationData
  trivial

example : True := by
  have := godel_benchmark_classificationData
  trivial

/-- Forward / backward equivalence on the canonical pair: admission of
an unrestricted witness is equivalent to having the three classification
Nonempties. -/
example :
    AdmitsLCELUnrestrictedWitness
        OperatorKO7.LCELSchema.godel1931LCELInstance
        OperatorKO7.LCELDpInstance.dpEmitterLCELInstance
      ↔ Nonempty
            (OperatorKO7.LCELSchema.RealizesLCELSchema
              OperatorKO7.LCELSchema.godel1931LCELInstance.toSlotProfile)
          ∧ Nonempty
            (OperatorKO7.LCELSchema.RealizesLCELSchema
              OperatorKO7.LCELDpInstance.dpEmitterLCELInstance.toSlotProfile)
          ∧ Nonempty
            (OperatorKO7.LCELMathematical.LCELMathematicalSupportWitness
              OperatorKO7.LCELSchema.godel1931LCELInstance
              OperatorKO7.LCELDpInstance.dpEmitterLCELInstance) :=
  admitsUnrestrictedWitness_iff
    OperatorKO7.LCELSchema.godel1931LCELInstance
    OperatorKO7.LCELDpInstance.dpEmitterLCELInstance

/-- The forward classification extraction on the canonical witness. -/
example :
    Nonempty
        (OperatorKO7.LCELSchema.RealizesLCELSchema
          OperatorKO7.LCELSchema.godel1931LCELInstance.toSlotProfile)
      ∧ Nonempty
        (OperatorKO7.LCELSchema.RealizesLCELSchema
          OperatorKO7.LCELDpInstance.dpEmitterLCELInstance.toSlotProfile)
      ∧ Nonempty
        (OperatorKO7.LCELMathematical.LCELMathematicalSupportWitness
          OperatorKO7.LCELSchema.godel1931LCELInstance
          OperatorKO7.LCELDpInstance.dpEmitterLCELInstance) :=
  classification_of_admitsUnrestrictedWitness godel_dp_admitsUnrestrictedWitness

/-- Residual-obligation alias on the canonical pair. -/
example :
    LCELWitnessFreeResidualObligation
      OperatorKO7.LCELSchema.godel1931LCELInstance
      OperatorKO7.LCELDpInstance.dpEmitterLCELInstance :=
  classification_of_admitsUnrestrictedWitness godel_dp_admitsUnrestrictedWitness

/-! ### Phase P4B: classification-scoped witness-free theorem -/

example : True := by
  have := godel_dp_witness_free_structural_identity
  trivial

example : True := by
  have := godel_benchmark_witness_free_structural_identity
  trivial

example : True := by
  have :=
    lcel_witness_free_structural_identity_of_classificationData
      godel_dp_classificationData
  trivial

example : True := by
  have :=
    lcel_witness_free_structural_identity_of_residualObligation
      (classification_of_admitsUnrestrictedWitness godel_dp_admitsUnrestrictedWitness)
  trivial

/-- The classification-scoped witness-free theorem genuinely closes on
the canonical Gödel ↔ DP classification data. -/
example :
    ∃ A₁ A₂ : OperatorKO7.LCELUniversalTheorem.AdmissibleLCELInstance,
      A₁.instance_ = OperatorKO7.LCELSchema.godel1931LCELInstance
        ∧ A₂.instance_ = OperatorKO7.LCELDpInstance.dpEmitterLCELInstance
        ∧ Nonempty
            (OperatorKO7.LCELUniversalTheorem.LCELUniversalQuasiFunctor A₁ A₂) :=
  lcel_witness_free_structural_identity_of_classificationData
    godel_dp_classificationData

/-! ### Refined classification via LCELRawPairBridgeData

These tests exercise the strictly weaker classification route: a bridge
data + two admissibility data packages suffice to discharge
`AdmitsLCELUnrestrictedWitness`. No `Nonempty (LCELMathematicalSupportWitness)`
is ever taken as a hypothesis. -/

example : True := by
  have := @LCELRawPairBridgeData
  trivial

example : True := by
  have := godel_dp_bridgeData
  trivial

example : True := by
  have := godel_benchmark_bridgeData
  trivial

example : True := by
  have :=
    LCELMathematicalSupportWitness.ofBridgeData
      godel1931LCELAdmissibilityData
      dpEmitterLCELAdmissibilityData
      godel_dp_bridgeData
  trivial

example : True := by
  have :=
    LCELUnrestrictedMathematicalWitness.ofAdmissibilityDataAndBridge
      godel1931LCELAdmissibilityData
      dpEmitterLCELAdmissibilityData
      godel_dp_bridgeData
  trivial

example :
    AdmitsLCELUnrestrictedWitness
      OperatorKO7.LCELSchema.godel1931LCELInstance
      OperatorKO7.LCELDpInstance.dpEmitterLCELInstance :=
  admitsUnrestrictedWitness_of_bridgeData
    godel1931LCELAdmissibilityData
    dpEmitterLCELAdmissibilityData
    godel_dp_bridgeData

example :
    AdmitsLCELUnrestrictedWitness
      OperatorKO7.LCELSchema.godel1931LCELInstance
      OperatorKO7.LCELSchema.benchmarkTransportLCELInstance :=
  admitsUnrestrictedWitness_of_bridgeData
    godel1931LCELAdmissibilityData
    benchmarkTransportLCELAdmissibilityData
    godel_benchmark_bridgeData

/-- The refined witness-free theorem closes on the canonical bridge data
on the Gödel ↔ DP pair. -/
example :
    ∃ A₁ A₂ : OperatorKO7.LCELUniversalTheorem.AdmissibleLCELInstance,
      A₁.instance_ = OperatorKO7.LCELSchema.godel1931LCELInstance
        ∧ A₂.instance_ = OperatorKO7.LCELDpInstance.dpEmitterLCELInstance
        ∧ Nonempty
            (OperatorKO7.LCELUniversalTheorem.LCELUniversalQuasiFunctor A₁ A₂) :=
  lcel_witness_free_structural_identity_of_bridgeData
    godel1931LCELAdmissibilityData
    dpEmitterLCELAdmissibilityData
    godel_dp_bridgeData

example :
    ∃ A₁ A₂ : OperatorKO7.LCELUniversalTheorem.AdmissibleLCELInstance,
      A₁.instance_ = OperatorKO7.LCELSchema.godel1931LCELInstance
        ∧ A₂.instance_ = OperatorKO7.LCELSchema.benchmarkTransportLCELInstance
        ∧ Nonempty
            (OperatorKO7.LCELUniversalTheorem.LCELUniversalQuasiFunctor A₁ A₂) :=
  lcel_witness_free_structural_identity_of_bridgeData
    godel1931LCELAdmissibilityData
    benchmarkTransportLCELAdmissibilityData
    godel_benchmark_bridgeData

example : True := by
  have := godel_dp_witness_free_structural_identity_viaBridge
  trivial

example : True := by
  have := godel_benchmark_witness_free_structural_identity_viaBridge
  trivial

example : True := by
  have := benchmark_dp_witness_free_structural_identity_viaBridge
  trivial

/-! ### Strong transport-bridge route: reachability, admissions, corollaries -/

example : True := by
  have := godel_dp_transportBridgeData
  trivial

example : True := by
  have := godel_benchmark_transportBridgeData
  trivial

example : True := by
  have := godel_dp_admitsUnrestrictedWitness_viaTransportBridge
  trivial

example : True := by
  have := godel_benchmark_admitsUnrestrictedWitness_viaTransportBridge
  trivial

example : True := by
  have := benchmark_dp_admitsUnrestrictedWitness_viaTransportBridge
  trivial

example : True := by
  have := godel_dp_witness_free_structural_identity_viaTransportBridge
  trivial

example : True := by
  have := godel_benchmark_witness_free_structural_identity_viaTransportBridge
  trivial

example : True := by
  have := benchmark_dp_witness_free_structural_identity_viaTransportBridge
  trivial

/-! ### Strong transport-bridge classification iff and downgrade comparisons -/

example :
    AdmitsLCELUnrestrictedWitness
        OperatorKO7.LCELSchema.godel1931LCELInstance
        OperatorKO7.LCELDpInstance.dpEmitterLCELInstance
      ↔ ∃ A₁ : LCELAdmissibilityData OperatorKO7.LCELSchema.godel1931LCELInstance,
          ∃ A₂ : LCELAdmissibilityData OperatorKO7.LCELDpInstance.dpEmitterLCELInstance,
            Nonempty (LCELTransportBridgeData A₁ A₂) :=
  admitsUnrestrictedWitness_iff_transportBridgeData
    OperatorKO7.LCELSchema.godel1931LCELInstance
    OperatorKO7.LCELDpInstance.dpEmitterLCELInstance

example :
    ∃ A₁ : LCELAdmissibilityData OperatorKO7.LCELSchema.godel1931LCELInstance,
      ∃ A₂ : LCELAdmissibilityData OperatorKO7.LCELDpInstance.dpEmitterLCELInstance,
        Nonempty (LCELTransportBridgeData A₁ A₂) :=
  transportBridgeClassification_of_admitsUnrestrictedWitness
    godel_dp_admitsUnrestrictedWitness

example :
    godel_dp_transportBridgeData.toRawPairBridgeData = godel_dp_bridgeData :=
  godel_dp_transportBridgeData_toRawPairBridgeData_eq_bridgeData

example :
    godel_benchmark_transportBridgeData.toRawPairBridgeData
      = godel_benchmark_bridgeData :=
  godel_benchmark_transportBridgeData_toRawPairBridgeData_eq_bridgeData

example :
    benchmark_dp_unrestrictedMathematicalWitness.toTransportBridgeData.toRawPairBridgeData
      = benchmark_dp_unrestrictedMathematicalWitness.toBridgeData :=
  LCELUnrestrictedMathematicalWitness.toTransportBridgeData_toRawPairBridgeData_eq_toBridgeData
    benchmark_dp_unrestrictedMathematicalWitness

/-- The strong route's `transportBase` reduces to the bridge's own
transport, not to a constant target closure. -/
example
    (bridge : LCELTransportBridgeData godel1931LCELAdmissibilityData
      dpEmitterLCELAdmissibilityData)
    (T : OperatorKO7.LCELSubstrateMathematics.BaseReversibilityTheorem
            OperatorKO7.LCELSchema.godel1931LCELInstance) :
    (LCELMathematicalSupportWitness.ofTransportBridgeData
        godel1931LCELAdmissibilityData
        dpEmitterLCELAdmissibilityData
        bridge).transportBase T
      = bridge.transportBase T :=
  ofTransportBridgeData_transportBase_fromBridge
    godel1931LCELAdmissibilityData
    dpEmitterLCELAdmissibilityData
    bridge T

/-- Audit: the weak route's `transportBase` is constant regardless of
the input theorem. -/
example
    (bridge : LCELRawPairBridgeData OperatorKO7.LCELSchema.godel1931LCELInstance
      OperatorKO7.LCELDpInstance.dpEmitterLCELInstance)
    (T : OperatorKO7.LCELSubstrateMathematics.BaseReversibilityTheorem
            OperatorKO7.LCELSchema.godel1931LCELInstance) :
    (LCELMathematicalSupportWitness.ofBridgeData
        godel1931LCELAdmissibilityData
        dpEmitterLCELAdmissibilityData
        bridge).transportBase T
      = OperatorKO7.LCELSubstrateMathematics.baseReversibilityTheorem_of_support
          dpEmitterLCELAdmissibilityData.baseSupport :=
  ofBridgeData_transportBase_constant
    godel1931LCELAdmissibilityData
    dpEmitterLCELAdmissibilityData
    bridge T

example : True := by
  have := godel_dp_admitsUnrestrictedWitness_viaBridge
  trivial

example : True := by
  have := godel_benchmark_admitsUnrestrictedWitness_viaBridge
  trivial

/-! ### Reverse direction of refined classification and bridge-data extraction -/

example : True := by
  have :=
    LCELUnrestrictedMathematicalWitness.toSourceAdmissibilityData
      godel_dp_unrestrictedMathematicalWitness
  trivial

example : True := by
  have :=
    LCELUnrestrictedMathematicalWitness.toTargetAdmissibilityData
      godel_dp_unrestrictedMathematicalWitness
  trivial

example : True := by
  have :=
    LCELUnrestrictedMathematicalWitness.toBridgeData
      godel_dp_unrestrictedMathematicalWitness
  trivial

/-- The extracted source-admissibility data lifts to the canonical
source-admissible instance of the unrestricted witness. -/
example :
    godel_dp_unrestrictedMathematicalWitness.sourceAdmissibleInstance
      = godel_dp_unrestrictedMathematicalWitness.toSourceAdmissibilityData.toAdmissibleInstance :=
  LCELUnrestrictedMathematicalWitness.sourceAdmissibleInstance_eq_toSourceAdmissibilityData
    godel_dp_unrestrictedMathematicalWitness

example :
    godel_dp_unrestrictedMathematicalWitness.targetAdmissibleInstance
      = godel_dp_unrestrictedMathematicalWitness.toTargetAdmissibilityData.toAdmissibleInstance :=
  LCELUnrestrictedMathematicalWitness.targetAdmissibleInstance_eq_toTargetAdmissibilityData
    godel_dp_unrestrictedMathematicalWitness

/-- The refined classification iff is real: we exhibit both directions
on the canonical Gödel ↔ DP pair. -/
example :
    AdmitsLCELUnrestrictedWitness
        OperatorKO7.LCELSchema.godel1931LCELInstance
        OperatorKO7.LCELDpInstance.dpEmitterLCELInstance
      ↔ Nonempty
            (LCELAdmissibilityData OperatorKO7.LCELSchema.godel1931LCELInstance)
          ∧ Nonempty
            (LCELAdmissibilityData OperatorKO7.LCELDpInstance.dpEmitterLCELInstance)
          ∧ Nonempty
            (LCELRawPairBridgeData
              OperatorKO7.LCELSchema.godel1931LCELInstance
              OperatorKO7.LCELDpInstance.dpEmitterLCELInstance) :=
  admitsUnrestrictedWitness_iff_bridgeData
    OperatorKO7.LCELSchema.godel1931LCELInstance
    OperatorKO7.LCELDpInstance.dpEmitterLCELInstance

example :
    Nonempty
        (LCELAdmissibilityData OperatorKO7.LCELSchema.godel1931LCELInstance)
      ∧ Nonempty
        (LCELAdmissibilityData OperatorKO7.LCELDpInstance.dpEmitterLCELInstance)
      ∧ Nonempty
        (LCELRawPairBridgeData
          OperatorKO7.LCELSchema.godel1931LCELInstance
          OperatorKO7.LCELDpInstance.dpEmitterLCELInstance) :=
  bridgeClassification_of_admitsUnrestrictedWitness godel_dp_admitsUnrestrictedWitness

end LCELWitnessFreeStructuralIdentityReach
