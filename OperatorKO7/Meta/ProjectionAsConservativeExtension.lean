import OperatorKO7.Meta.ClassicalAscentProfile

/-!
# One-way proof-language projection

The module defines an implication from `HasWitness` at one level to `HasWitness` at another. The benchmark instance ignores its source proposition and returns an independently available transformed-call proposition. It proves target availability; source-dependent transport and reflection require stronger assumptions.
-/

namespace OperatorKO7.ProjectionAsConservativeExtension

open OperatorKO7.WitnessOrder
open OperatorKO7.ProofTheoreticRegister
open OperatorKO7.ClassicalAscentProfile

private theorem iff_of_true {P Q : Prop} (hP : P) (hQ : Q) : P ↔ Q := by
  constructor
  · intro _
    exact hQ
  · intro _
    exact hP

/-- A language label paired with its `WLevel`. -/
structure WitnessLanguage where
  label : String
  level : WLevel

/-- One-way implication between proof-existence propositions at two levels. This structure stores no reverse implication or equivalence. -/
structure ConservativeExtension (T : WitnessTower)
    (base ext : WitnessLanguage) where
  lifts : HasWitness T base.level → HasWitness T ext.level

/-- Apply the stored implication to a source-level proof. -/
theorem ConservativeExtension.transports_hasWitness
    {T : WitnessTower} {base ext : WitnessLanguage}
    (hExt : ConservativeExtension T base ext)
    (hBase : HasWitness T base.level) :
    HasWitness T ext.level :=
  hExt.lifts hBase

/-- Construct a `kappaLe` proof at a target level at least as high as `ext`. -/
theorem ConservativeExtension.transports_kappaLe
    {T : WitnessTower} {base ext target : WitnessLanguage}
    (hExt : ConservativeExtension T base ext)
    (hLe : ext.level.toNat ≤ target.level.toNat)
    (hBase : HasWitness T base.level) :
    kappaLe T target.level := by
  exact ⟨ext.level, hLe, hExt.lifts hBase⟩

/-- Imported-whole language profile. -/
def importedWholeLanguage : WitnessLanguage where
  label := "imported whole-term"
  level := WLevel.importedWhole

/-- Transformed-call language profile. -/
def transformedCallLanguage : WitnessLanguage where
  label := "transformed call"
  level := WLevel.transformedCall

/-- The benchmark lift returns the transformed-call proposition independently of its source proof. It records target availability rather than source-dependent transport. -/
def benchmarkContractProjectionExtension :
    ConservativeExtension (contractTower ko7Tower benchmarkContract)
      importedWholeLanguage transformedCallLanguage where
  lifts := by
    intro _
    simpa [HasWitness, contractTower, transformedCallLanguage] using
      (show benchmarkContract.admissible WLevel.transformedCall
          ∧ HasWitness ko7Tower WLevel.transformedCall from
        ⟨by simp [benchmarkContract], ko7_has_transformedCall_witness⟩)

/-- Given an imported-whole proof, the benchmark contract also admits a transformed-call proof. -/
theorem benchmarkContract_projection_extension_sound
    (hBase : HasWitness (contractTower ko7Tower benchmarkContract)
      importedWholeLanguage.level) :
    HasWitness (contractTower ko7Tower benchmarkContract)
      transformedCallLanguage.level :=
  benchmarkContractProjectionExtension.lifts hBase

/-- The benchmark contract yields `kappaLe` for the transformed-call level given an imported-whole proof. -/
theorem benchmarkContract_projection_extension_kappaLe
    (hBase : HasWitness (contractTower ko7Tower benchmarkContract)
      importedWholeLanguage.level) :
    kappaLe (contractTower ko7Tower benchmarkContract)
      transformedCallLanguage.level := by
  exact ConservativeExtension.transports_kappaLe benchmarkContractProjectionExtension
    (by decide) hBase

/-- Concrete comparison profile for the benchmark contract's transformed-call proof. -/
def benchmarkTransportAscentProfile : AscentProfile where
  shape := {
    hasBaseSystem := True
    hasSelfObstruction := True
    blockedInBase := ¬ HasWitness ko7Tower WLevel.directWhole
    hasStrongerFramework := Nonempty
      (ConservativeExtension (contractTower ko7Tower benchmarkContract)
        importedWholeLanguage transformedCallLanguage)
    resolvedInFramework := kappaLe (contractTower ko7Tower benchmarkContract)
      WLevel.transformedCall
    licensedReimport := kappaLe (contractTower ko7Tower benchmarkContract)
      WLevel.transformedCall
  }
  family := AscentFamily.reflection

/-- Named benchmark-contract transport comparison object. -/
def benchmarkTransportComparison : ConcreteComparisonProfile where
  profile := benchmarkTransportAscentProfile
  baseSystemLabel := "benchmark contract over KO7"
  obstructionLabel := "contract blocks imported-whole witnesses"
  blockedLabel := "no direct whole-term witness"
  strongerFrameworkLabel := "conservative importedWhole → transformedCall transport"
  resolutionLabel := "first admissible witness at transformed-call"
  licensedReimportLabel := "transported transformed-call admission"

/-- Classification tags attached to the benchmark transport comparison layer. -/
def benchmarkTransportHistoricalAnnotation :
    OperatorKO7.ClassicalAscentProfile.HistoricalComparisonAnnotation where
  baseKind := HistoricalBaseKind.benchmarkContractKO7
  obstructionKind := HistoricalObstructionKind.noDirectWholeWitness
  frameworkKind := HistoricalFrameworkKind.transformedCallTransport
  resolutionKind := HistoricalResolutionKind.transformedCallWitness
  reimportKind := HistoricalReimportKind.contractLicensedWitness

theorem benchmarkTransportAscentProfile_realizesSixStep :
    RealizesSixStepShape benchmarkTransportAscentProfile.shape := by
  refine ⟨trivial, trivial, ?_, ?_, ?_, ?_⟩
  · exact ko7_no_directWhole_witness
  · exact ⟨benchmarkContractProjectionExtension⟩
  · exact ko7_kappaContract_le_transformedCall
  · exact ko7_kappaContract_le_transformedCall

/-- The benchmark comparison profile satisfies its six stipulated propositions
and carries the reflection family tag. -/
theorem benchmarkContractProjectionExtension_instantiates_concreteComparison :
    RealizesSixStepShape benchmarkTransportAscentProfile.shape
      ∧ benchmarkTransportAscentProfile.family = AscentFamily.reflection := by
  exact ⟨benchmarkTransportAscentProfile_realizesSixStep, rfl⟩

/-- Concrete theorem-backed transport-side profile instantiation compatible with
the mechanized DP ascent profile. -/
theorem benchmarkTransportAscentProfile_compatible :
    CompatibleWithDp benchmarkTransportAscentProfile := by
  rcases OperatorKO7.ProofTheoreticRegister.structural_identity with
    ⟨hBase, hSelf, hBlocked, hStronger, hResolved, hLicensed⟩
  constructor
  · intro s
    cases s with
    | baseSystem =>
        exact iff_of_true trivial hBase
    | selfObstruction =>
        exact iff_of_true trivial hSelf
    | blockedInBase =>
        exact iff_of_true ko7_no_directWhole_witness hBlocked
    | strongerFramework =>
        exact iff_of_true ⟨benchmarkContractProjectionExtension⟩ hStronger
    | resolvedInFramework =>
        exact iff_of_true ko7_kappaContract_le_transformedCall hResolved
    | licensedReimport =>
        exact iff_of_true ko7_kappaContract_le_transformedCall hLicensed
  · rfl

end OperatorKO7.ProjectionAsConservativeExtension
