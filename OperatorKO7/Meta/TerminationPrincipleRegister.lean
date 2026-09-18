import OperatorKO7.Meta.ReverseMathFramework

/-!
# Termination-Principle Register

Registry layer sitting on top of `ReverseMathFramework`.

This file records the named termination principles and soundness principles
used by the paper stack, together with their currently available calibration
profiles. The goal is to make comparisons explicit and machine-visible without
pretending that every calibration is already theorem-level exact.
-/

namespace OperatorKO7.TerminationPrincipleRegister

open Ordinal
open OperatorKO7.ProofTheoreticRegister
open OperatorKO7.ReverseMathSupport
open OperatorKO7.ReverseMathFramework

/-- Named termination / soundness principles tracked by the paper stack. -/
inductive TerminationPrinciple
  | sizeChangeTermination
  | dependencyPairSoundness
  | artsGieslSoundness
  | importedWellFoundedOrder
  deriving DecidableEq, Repr

/-- Public registry entry for one principle. -/
structure TerminationPrincipleEntry where
  principle : TerminationPrinciple
  profile : PrincipleProfile
  calibrationStatus : CalibrationStatus
  targetTheory? : Option FormalTheory := none
  targetOrdinal? : Option Ordinal := none

/-- Registry entry for SCT. -/
noncomputable def sctEntry : TerminationPrincipleEntry where
  principle := TerminationPrinciple.sizeChangeTermination
  profile := sctPrincipleProfile
  calibrationStatus := CalibrationStatus.exact
  targetTheory? := some FormalTheory.RCA0_WO_omega3
  targetOrdinal? := some omegaPowThree

/-- Registry entry for Arts--Giesl soundness. -/
noncomputable def artsGieslEntry : TerminationPrincipleEntry where
  principle := TerminationPrinciple.artsGieslSoundness
  profile := artsGieslPrincipleProfile
  calibrationStatus := CalibrationStatus.conjectural
  targetTheory? := some FormalTheory.RCA0_WO_omega3
  targetOrdinal? := some omegaPowThree

/-- Registry entry for the general dependency-pair soundness route. The
artifact currently tracks its proof-theoretic family and formula class, but not
an exact reverse-mathematical target distinct from the Arts--Giesl license.
-/
def dependencyPairEntry : TerminationPrincipleEntry where
  principle := TerminationPrinciple.dependencyPairSoundness
  profile := artsGieslPrincipleProfile
  calibrationStatus := CalibrationStatus.boundedUpper

/-- Registry entry for imported well-founded order soundness routes. -/
def importedWellFoundedOrderEntry : TerminationPrincipleEntry where
  principle := TerminationPrinciple.importedWellFoundedOrder
  profile := {
    label := "Imported well-founded order"
  }
  calibrationStatus := CalibrationStatus.boundedUpper

/-- Alignment object between two registered principles. -/
structure PrincipleAlignment
    (left right : TerminationPrincipleEntry) where
  sharedTheoryTarget? : Option FormalTheory := none
  sharedOrdinalTarget? : Option Ordinal := none
  evidenceStatus : EvidenceStatus

/-- The exact missing bridge for the Arts--Giesl/SCT calibration program: a
theorem-level alignment, not merely a profile-level shared target note. -/
structure ArtsGieslSctTheoremAlignment extends PrincipleAlignment artsGieslEntry sctEntry where
  sharedTheoryExact :
    sharedTheoryTarget? = some FormalTheory.RCA0_WO_omega3
  sharedOrdinalExact :
    sharedOrdinalTarget? = some omegaPowThree
  theoremLevel :
    evidenceStatus = EvidenceStatus.theoremLevel

/-- Current AG/SCT alignment used in the paper's reverse-mathematical
discussion: exact on the SCT side, conjectural on the AG side, with a shared
candidate target. -/
noncomputable def artsGieslSctAlignment :
    PrincipleAlignment artsGieslEntry sctEntry where
  sharedTheoryTarget? := some FormalTheory.RCA0_WO_omega3
  sharedOrdinalTarget? := some omegaPowThree
  evidenceStatus := EvidenceStatus.profileLevel

@[simp] theorem artsGieslSctAlignment_status :
    artsGieslSctAlignment.evidenceStatus = EvidenceStatus.profileLevel := rfl

/-- The current AG/SCT alignment is only profile-level, not theorem-level. -/
theorem artsGieslSctAlignment_not_theoremLevel :
    artsGieslSctAlignment.evidenceStatus ≠ EvidenceStatus.theoremLevel := by
  simp [artsGieslSctAlignment]

/-- The current alignment object is not yet an inhabitant of the stronger
theorem-level alignment schema. -/
theorem artsGieslSctAlignment_still_below_theoremAlignment :
    artsGieslSctAlignment.evidenceStatus ≠ EvidenceStatus.theoremLevel := by
  exact artsGieslSctAlignment_not_theoremLevel

@[simp] theorem sctEntry_status :
    sctEntry.calibrationStatus = CalibrationStatus.exact := by
  simp [sctEntry]

@[simp] theorem artsGieslEntry_status :
    artsGieslEntry.calibrationStatus = CalibrationStatus.conjectural := by
  simp [artsGieslEntry]

@[simp] theorem artsGieslEntry_family :
    artsGieslEntry.profile.family? = some AscentFamily.reflection := by
  simp [artsGieslEntry, artsGieslPrincipleProfile, artsGieslLicenseProfile]

@[simp] theorem artsGieslEntry_complexity :
    artsGieslEntry.profile.complexity? = some FormulaClass.pi02 := by
  simp [artsGieslEntry, artsGieslPrincipleProfile, artsGieslLicenseProfile]

/-- The registry-level AG/SCT alignment shares the same candidate target
theory. -/
theorem artsGiesl_and_sct_share_registry_target_theory :
    artsGieslEntry.targetTheory? = sctEntry.targetTheory? := by
  simp [artsGieslEntry, sctEntry]

/-- The registry-level AG/SCT alignment shares the same candidate target
ordinal. -/
theorem artsGiesl_and_sct_share_registry_target_ordinal :
    artsGieslEntry.targetOrdinal? = sctEntry.targetOrdinal? := by
  rfl

/-- The alignment object agrees with the two concrete registry entries. -/
theorem artsGieslSctAlignment_sound :
    artsGieslSctAlignment.sharedTheoryTarget? = artsGieslEntry.targetTheory?
      ∧ artsGieslSctAlignment.sharedTheoryTarget? = sctEntry.targetTheory?
      ∧ artsGieslSctAlignment.sharedOrdinalTarget? = artsGieslEntry.targetOrdinal?
      ∧ artsGieslSctAlignment.sharedOrdinalTarget? = sctEntry.targetOrdinal? := by
  constructor
  · simp [artsGieslSctAlignment, artsGieslEntry]
  constructor
  · simp [artsGieslSctAlignment, sctEntry]
  constructor <;> rfl

/-! ## Generic transfer -> theorem-alignment bridge

Given an `ExactCalibrationTransfer sctPrincipleProfile artsGieslPrincipleProfile`
whose source calibration hits the `RCA₀ + WO(ω^3)` target, we can
canonically produce an `ArtsGieslSctTheoremAlignment`. The construction
uses the transfer's source-calibration target data (not hard-coded
constants), with the theory and ordinal equality hypotheses acting as
the bridge from the transfer's source-side data to the alignment
schema's required exact-target values. The `theoremLevel` evidence
status is forced by the schema and is discharged by `rfl`; the
transfer's `upperTheoremLevel` / `lowerTheoremLevel` fields certify that
the transfer's destination packages are already at that level, making
the schematic alignment a genuine summary of the transfer. -/
noncomputable def ArtsGieslSctTheoremAlignment.ofExactCalibrationTransfer
    (T : ExactCalibrationTransfer sctPrincipleProfile artsGieslPrincipleProfile)
    (hTheory : T.sourceCalibration.targetProfile.theory =
      FormalTheory.RCA0_WO_omega3)
    (hOrdinal : T.sourceCalibration.targetProfile.ordinalCeiling? =
      some omegaPowThree) :
    ArtsGieslSctTheoremAlignment where
  sharedTheoryTarget? := some T.sourceCalibration.targetProfile.theory
  sharedOrdinalTarget? := T.sourceCalibration.targetProfile.ordinalCeiling?
  evidenceStatus := EvidenceStatus.theoremLevel
  sharedTheoryExact := by rw [hTheory]
  sharedOrdinalExact := hOrdinal
  theoremLevel := rfl

/-- Projection: the generic bridge's theory target is always
`some FormalTheory.RCA0_WO_omega3`. -/
theorem ArtsGieslSctTheoremAlignment.ofExactCalibrationTransfer_theory
    (T : ExactCalibrationTransfer sctPrincipleProfile artsGieslPrincipleProfile)
    (hTheory : T.sourceCalibration.targetProfile.theory =
      FormalTheory.RCA0_WO_omega3)
    (hOrdinal : T.sourceCalibration.targetProfile.ordinalCeiling? =
      some omegaPowThree) :
    (ArtsGieslSctTheoremAlignment.ofExactCalibrationTransfer
        T hTheory hOrdinal).sharedTheoryTarget? =
      some FormalTheory.RCA0_WO_omega3 := by
  rw [show (ArtsGieslSctTheoremAlignment.ofExactCalibrationTransfer
      T hTheory hOrdinal).sharedTheoryTarget? =
      some T.sourceCalibration.targetProfile.theory from rfl, hTheory]

/-- Projection: the generic bridge's ordinal target is always
`some omegaPowThree`. -/
theorem ArtsGieslSctTheoremAlignment.ofExactCalibrationTransfer_ordinal
    (T : ExactCalibrationTransfer sctPrincipleProfile artsGieslPrincipleProfile)
    (hTheory : T.sourceCalibration.targetProfile.theory =
      FormalTheory.RCA0_WO_omega3)
    (hOrdinal : T.sourceCalibration.targetProfile.ordinalCeiling? =
      some omegaPowThree) :
    (ArtsGieslSctTheoremAlignment.ofExactCalibrationTransfer
        T hTheory hOrdinal).sharedOrdinalTarget? =
      some omegaPowThree := hOrdinal

/-- Projection: the generic bridge's evidence status is always
`EvidenceStatus.theoremLevel`. -/
@[simp] theorem ArtsGieslSctTheoremAlignment.ofExactCalibrationTransfer_theoremLevel
    (T : ExactCalibrationTransfer sctPrincipleProfile artsGieslPrincipleProfile)
    (hTheory : T.sourceCalibration.targetProfile.theory =
      FormalTheory.RCA0_WO_omega3)
    (hOrdinal : T.sourceCalibration.targetProfile.ordinalCeiling? =
      some omegaPowThree) :
    (ArtsGieslSctTheoremAlignment.ofExactCalibrationTransfer
        T hTheory hOrdinal).evidenceStatus =
      EvidenceStatus.theoremLevel := rfl

end OperatorKO7.TerminationPrincipleRegister
