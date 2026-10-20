import OperatorKO7.Meta.ArtsGiesl_ReverseMathCalibration

/-!
# Arts-Giesl Reverse-Math Calibration Reach Tests

Dedicated regression surface for the named concrete Arts-Giesl
SCT-sharp transfer layer and the named concrete
`ArtsGieslExactTheoremCalibration` object. Each `#check` pins a public
name so that renames/removals break this file; each `rfl`-based
regression pins the definitional content of the key projection theorems
without triggering universe unification on the polymorphic `Ordinal`
parameter (the `Test/CrossPaperAPIReach.lean` AG block uses the same
strategy).
-/

namespace ArtsGieslReverseMathCalibrationReach

open OperatorKO7
open OperatorKO7.ArtsGieslReverseMathCalibration
open OperatorKO7.ArtsGieslUpperBound
open OperatorKO7.ArtsGieslLowerBound
open OperatorKO7.ReverseMathSupport
open OperatorKO7.ReverseMathFramework
open OperatorKO7.ProofTheoreticRegister
open OperatorKO7.TerminationPrincipleRegister

/-! ### Named SCT-sharp transfer inhabitants -/

#check @artsGieslConcreteSctSharpUpperTransfer
#print axioms artsGieslConcreteSctSharpUpperTransfer
#check @artsGieslConcreteSctSharpLowerTransfer
#print axioms artsGieslConcreteSctSharpLowerTransfer
#check @artsGieslConcreteSctSharpTransferPair
#print axioms artsGieslConcreteSctSharpTransferPair
#check @artsGieslConcreteSctSharpTransferPair_yields_exactTheoremCalibration
#print axioms artsGieslConcreteSctSharpTransferPair_yields_exactTheoremCalibration

/-! ### Named concrete sharp-theorem bounds -/

#check @artsGieslConcreteSharpTheoremUpperBound
#print axioms artsGieslConcreteSharpTheoremUpperBound
#check @artsGieslConcreteSharpTheoremLowerBound
#print axioms artsGieslConcreteSharpTheoremLowerBound

/-! ### Named concrete exact-theorem-calibration object -/

#check @artsGieslConcreteExactTheoremCalibration
#print axioms artsGieslConcreteExactTheoremCalibration

/-! ### Theorem-facing projection lemmas on the concrete exact object -/

#check @artsGieslConcreteExactTheoremCalibration_status
#print axioms artsGieslConcreteExactTheoremCalibration_status
#check @artsGieslConcreteExactTheoremCalibration_targetTheory
#print axioms artsGieslConcreteExactTheoremCalibration_targetTheory
#check @artsGieslConcreteExactTheoremCalibration_targetOrdinal
#print axioms artsGieslConcreteExactTheoremCalibration_targetOrdinal
#check @artsGieslConcreteExactTheoremCalibration_upperTheory
#print axioms artsGieslConcreteExactTheoremCalibration_upperTheory
#check @artsGieslConcreteExactTheoremCalibration_upperOrdinal
#print axioms artsGieslConcreteExactTheoremCalibration_upperOrdinal
#check @artsGieslConcreteExactTheoremCalibration_upperTheoremLevel
#print axioms artsGieslConcreteExactTheoremCalibration_upperTheoremLevel
#check @artsGieslConcreteExactTheoremCalibration_lowerTheoremLevel
#print axioms artsGieslConcreteExactTheoremCalibration_lowerTheoremLevel

/-! ### Extraction theorems -/

#check @artsGieslConcreteExactTheoremCalibration_toSharpUpper_eq
#print axioms artsGieslConcreteExactTheoremCalibration_toSharpUpper_eq
#check @artsGieslConcreteExactTheoremCalibration_toSharpLower_eq
#print axioms artsGieslConcreteExactTheoremCalibration_toSharpLower_eq

/-! ### Paper-facing aliases and strengthened endpoint -/

#check @artsGieslConcreteExactTheoremCalibration_isExact
#print axioms artsGieslConcreteExactTheoremCalibration_isExact
#check @artsGieslConcreteExactTheoremCalibration_hitsTarget
#print axioms artsGieslConcreteExactTheoremCalibration_hitsTarget
#check @artsGieslConcreteSctSharpTransferPair_yields_exactTheoremCalibrationObject
#print axioms artsGieslConcreteSctSharpTransferPair_yields_exactTheoremCalibrationObject

/-! ### Definitional regressions (rfl-based, universe-agnostic)

Each example below pins the same definitional equation as the
corresponding `@[simp]` projection theorem, but via a direct `rfl` so
that the example's own universe context absorbs the `Ordinal` universe
rather than leaving it as a free metavariable in a polymorphic lemma
application. -/

example :
    artsGieslConcreteSctSharpUpperTransfer.bound.evidenceStatus =
      EvidenceStatus.theoremLevel := rfl

example :
    artsGieslConcreteSctSharpUpperTransfer.bound.theoryProfile.theory =
      FormalTheory.RCA0_WO_omega3 := rfl

example :
    artsGieslConcreteSctSharpUpperTransfer.bound.theoryProfile.ordinalCeiling? =
      some omegaPowThree := rfl

example :
    artsGieslConcreteSctSharpLowerTransfer.bound.evidenceStatus =
      EvidenceStatus.theoremLevel := rfl

example :
    artsGieslConcreteSctSharpLowerTransfer.bound.theoryProfile.theory =
      FormalTheory.RCA0_WO_omega3 := rfl

example :
    artsGieslConcreteSctSharpLowerTransfer.bound.theoryProfile.ordinalCeiling? =
      some omegaPowThree := rfl

example :
    artsGieslConcreteSctSharpTransferPair.upper.bound.evidenceStatus =
      EvidenceStatus.theoremLevel := rfl

example :
    artsGieslConcreteSctSharpTransferPair.lower.bound.evidenceStatus =
      EvidenceStatus.theoremLevel := rfl

example :
    (artsGieslExactTheoremCalibrationOfSctSharpTransfers
        artsGieslConcreteSctSharpTransferPair).calibration.status =
      CalibrationStatus.exact := rfl

example :
    artsGieslConcreteExactTheoremCalibration.calibration.status =
      CalibrationStatus.exact := rfl

example :
    artsGieslConcreteExactTheoremCalibration.calibration.targetProfile.theory =
      FormalTheory.RCA0_WO_omega3 := rfl

example :
    artsGieslConcreteExactTheoremCalibration.calibration.targetProfile.ordinalCeiling? =
      some omegaPowThree := rfl

example :
    artsGieslConcreteExactTheoremCalibration.calibration.upperBound.theoryProfile.theory =
      FormalTheory.RCA0_WO_omega3 := rfl

example :
    artsGieslConcreteExactTheoremCalibration.calibration.upperBound.theoryProfile.ordinalCeiling? =
      some omegaPowThree := rfl

example :
    artsGieslConcreteExactTheoremCalibration.calibration.upperBound.evidenceStatus =
      EvidenceStatus.theoremLevel := rfl

/-! ### Extraction regression

The upper extraction is definitionally the named concrete sharp-theorem
upper-bound; the lower extraction's `.bound` is only propositionally
equal (via `Classical.choose` on the lower-bound existential) and is
exercised via the named theorem, which itself proves the proposition.
-/

example :
    artsGieslConcreteExactTheoremCalibration.toSharpUpperBound =
      artsGieslConcreteSharpTheoremUpperBound := rfl

example :
    artsGieslConcreteExactTheoremCalibration.toSharpLowerBound.bound =
      artsGieslConcreteSharpTheoremLowerBound.bound :=
  artsGieslConcreteExactTheoremCalibration_toSharpLower_eq

/-! ### Lower-bound evidence-status regression (extraction via
`Classical.choose`; proved by the dedicated theorem) -/

example :
    artsGieslConcreteExactTheoremCalibration.toSharpLowerBound.bound.evidenceStatus =
      EvidenceStatus.theoremLevel :=
  artsGieslConcreteExactTheoremCalibration_lowerTheoremLevel

/-! ### Path C: named concrete theorem-alignment route -/

#check @artsGieslConcreteSctTheoremAlignment
#print axioms artsGieslConcreteSctTheoremAlignment
#check @artsGieslConcreteSctTheoremAlignment_theory
#print axioms artsGieslConcreteSctTheoremAlignment_theory
#check @artsGieslConcreteSctTheoremAlignment_ordinal
#print axioms artsGieslConcreteSctTheoremAlignment_ordinal
#check @artsGieslConcreteSctTheoremAlignment_theoremLevel
#print axioms artsGieslConcreteSctTheoremAlignment_theoremLevel
#check @artsGieslConcreteSctTheoremAlignment_supported
#print axioms artsGieslConcreteSctTheoremAlignment_supported
#check @artsGieslConcreteSctTheoremAlignment_isTheoremLevel
#print axioms artsGieslConcreteSctTheoremAlignment_isTheoremLevel

#check @artsGieslConcreteSctSharpTransferPair_viaTheoremAlignment
#print axioms artsGieslConcreteSctSharpTransferPair_viaTheoremAlignment
#check @artsGieslConcreteSharpTheoremUpperBound_viaTheoremAlignment
#print axioms artsGieslConcreteSharpTheoremUpperBound_viaTheoremAlignment
#check @artsGieslConcreteSharpTheoremLowerBound_viaTheoremAlignment
#print axioms artsGieslConcreteSharpTheoremLowerBound_viaTheoremAlignment
#check @artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment
#print axioms artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment

#check @artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment_status
#print axioms artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment_status
#check @artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment_targetTheory
#print axioms artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment_targetTheory
#check @artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment_targetOrdinal
#print axioms artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment_targetOrdinal
#check @artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment_upperTheoremLevel
#print axioms artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment_upperTheoremLevel
#check @artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment_lowerTheoremLevel
#print axioms artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment_lowerTheoremLevel

#check @artsGieslConcreteSctTheoremAlignment_yields_exactTheoremCalibration
#print axioms artsGieslConcreteSctTheoremAlignment_yields_exactTheoremCalibration
#check @artsGieslConcreteSctTheoremAlignment_yields_exactTheoremCalibrationObject
#print axioms artsGieslConcreteSctTheoremAlignment_yields_exactTheoremCalibrationObject

#check @artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment_isExact
#print axioms artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment_isExact
#check @artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment_hitsTarget
#print axioms artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment_hitsTarget

/-! ### Path C projection regressions via direct `rfl` -/

example :
    artsGieslConcreteSctTheoremAlignment.sharedTheoryTarget? =
      some FormalTheory.RCA0_WO_omega3 := rfl

example :
    artsGieslConcreteSctTheoremAlignment.sharedOrdinalTarget? =
      some omegaPowThree := rfl

example :
    artsGieslConcreteSctTheoremAlignment.evidenceStatus =
      EvidenceStatus.theoremLevel := rfl

example :
    artsGieslConcreteSctSharpTransferPair_viaTheoremAlignment.upper.bound.evidenceStatus =
      EvidenceStatus.theoremLevel := rfl

example :
    artsGieslConcreteSctSharpTransferPair_viaTheoremAlignment.lower.bound.evidenceStatus =
      EvidenceStatus.theoremLevel := rfl

example :
    artsGieslConcreteSctSharpTransferPair_viaTheoremAlignment.upper.bound.theoryProfile.theory =
      FormalTheory.RCA0_WO_omega3 := rfl

example :
    artsGieslConcreteSctSharpTransferPair_viaTheoremAlignment.lower.bound.theoryProfile.theory =
      FormalTheory.RCA0_WO_omega3 := rfl

example :
    artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment.calibration.status =
      CalibrationStatus.exact := rfl

example :
    artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment.calibration.targetProfile.theory =
      FormalTheory.RCA0_WO_omega3 := rfl

example :
    artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment.calibration.targetProfile.ordinalCeiling? =
      some omegaPowThree := rfl

example :
    artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment.calibration.upperBound.theoryProfile.theory =
      FormalTheory.RCA0_WO_omega3 := rfl

example :
    artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment.calibration.upperBound.evidenceStatus =
      EvidenceStatus.theoremLevel := rfl

example :
    artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment.toSharpLowerBound.bound.evidenceStatus =
      EvidenceStatus.theoremLevel :=
  artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment_lowerTheoremLevel

/-! ### Route-comparison reach and regressions -/

#check @artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment_sameTarget
#print axioms artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment_sameTarget
#check @artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment_sameUpperTheory
#print axioms artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment_sameUpperTheory
#check @artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment_sameUpperOrdinal
#print axioms artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment_sameUpperOrdinal
#check @artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment_sameUpperStatus
#print axioms artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment_sameUpperStatus
#check @artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment_sameLowerStatus
#print axioms artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment_sameLowerStatus
#check @artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment_sameStatus
#print axioms artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment_sameStatus

#check @artsGieslConcreteSctSharpTransferPair_viaTheoremAlignment_upper_status
#print axioms artsGieslConcreteSctSharpTransferPair_viaTheoremAlignment_upper_status
#check @artsGieslConcreteSctSharpTransferPair_viaTheoremAlignment_lower_status
#print axioms artsGieslConcreteSctSharpTransferPair_viaTheoremAlignment_lower_status
#check @artsGieslConcreteSctSharpTransferPair_viaTheoremAlignment_supported
#print axioms artsGieslConcreteSctSharpTransferPair_viaTheoremAlignment_supported
#check @artsGieslConcreteSctSharpTransferPair_routeComparison_upperStatus
#print axioms artsGieslConcreteSctSharpTransferPair_routeComparison_upperStatus
#check @artsGieslConcreteSctSharpTransferPair_routeComparison_lowerStatus
#print axioms artsGieslConcreteSctSharpTransferPair_routeComparison_lowerStatus
#check @artsGieslConcreteSctSharpTransferPair_routeComparison_upperTheory
#print axioms artsGieslConcreteSctSharpTransferPair_routeComparison_upperTheory
#check @artsGieslConcreteSctSharpTransferPair_routeComparison_lowerTheory
#print axioms artsGieslConcreteSctSharpTransferPair_routeComparison_lowerTheory

example :
    artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment.calibration.targetProfile =
      artsGieslConcreteExactTheoremCalibration.calibration.targetProfile := rfl

example :
    artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment.calibration.upperBound.theoryProfile.theory =
      artsGieslConcreteExactTheoremCalibration.calibration.upperBound.theoryProfile.theory := rfl

example :
    artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment.calibration.upperBound.evidenceStatus =
      artsGieslConcreteExactTheoremCalibration.calibration.upperBound.evidenceStatus := rfl

example :
    artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment.calibration.status =
      artsGieslConcreteExactTheoremCalibration.calibration.status := rfl

example :
    artsGieslConcreteSctSharpTransferPair_viaTheoremAlignment.upper.bound.evidenceStatus =
      artsGieslConcreteSctSharpTransferPair.upper.bound.evidenceStatus := rfl

example :
    artsGieslConcreteSctSharpTransferPair_viaTheoremAlignment.lower.bound.evidenceStatus =
      artsGieslConcreteSctSharpTransferPair.lower.bound.evidenceStatus := rfl

example :
    artsGieslConcreteSctSharpTransferPair_viaTheoremAlignment.upper.bound.theoryProfile.theory =
      artsGieslConcreteSctSharpTransferPair.upper.bound.theoryProfile.theory := rfl

example :
    artsGieslConcreteSctSharpTransferPair_viaTheoremAlignment.lower.bound.theoryProfile.theory =
      artsGieslConcreteSctSharpTransferPair.lower.bound.theoryProfile.theory := rfl

/-! ### Generic transfer -> theorem-alignment bridge -/

#check @ArtsGieslSctTheoremAlignment.ofExactCalibrationTransfer
#print axioms ArtsGieslSctTheoremAlignment.ofExactCalibrationTransfer
#check @ArtsGieslSctTheoremAlignment.ofExactCalibrationTransfer_theory
#print axioms ArtsGieslSctTheoremAlignment.ofExactCalibrationTransfer_theory
#check @ArtsGieslSctTheoremAlignment.ofExactCalibrationTransfer_ordinal
#print axioms ArtsGieslSctTheoremAlignment.ofExactCalibrationTransfer_ordinal
#check @ArtsGieslSctTheoremAlignment.ofExactCalibrationTransfer_theoremLevel
#print axioms ArtsGieslSctTheoremAlignment.ofExactCalibrationTransfer_theoremLevel

/-! ### Concrete exact-transfer-induced theorem-alignment object -/

#check @artsGieslExactCalibrationTransferFromSct_toTheoremAlignment
#print axioms artsGieslExactCalibrationTransferFromSct_toTheoremAlignment
#check @artsGieslExactCalibrationTransferFromSct_toTheoremAlignment_supported
#print axioms artsGieslExactCalibrationTransferFromSct_toTheoremAlignment_supported
#check @artsGieslExactCalibrationTransferFromSct_toTheoremAlignment_eq_concrete
#print axioms artsGieslExactCalibrationTransferFromSct_toTheoremAlignment_eq_concrete
#check @artsGieslExactCalibrationTransferFromSct_toTheoremAlignment_sameTheory
#print axioms artsGieslExactCalibrationTransferFromSct_toTheoremAlignment_sameTheory
#check @artsGieslExactCalibrationTransferFromSct_toTheoremAlignment_sameOrdinal
#print axioms artsGieslExactCalibrationTransferFromSct_toTheoremAlignment_sameOrdinal
#check @artsGieslExactCalibrationTransferFromSct_toTheoremAlignment_sameStatus
#print axioms artsGieslExactCalibrationTransferFromSct_toTheoremAlignment_sameStatus

/-- The exact-transfer route induces the Path C concrete
theorem-alignment object via the generic bridge. -/
example :
    artsGieslExactCalibrationTransferFromSct_toTheoremAlignment =
      artsGieslConcreteSctTheoremAlignment :=
  artsGieslExactCalibrationTransferFromSct_toTheoremAlignment_eq_concrete

example :
    artsGieslExactCalibrationTransferFromSct_toTheoremAlignment.evidenceStatus =
      EvidenceStatus.theoremLevel := rfl

/-! ### Tag-insensitive erasure and route equivalence -/

#check @ReverseMathUpperBound.eraseJustificationTag
#print axioms ReverseMathUpperBound.eraseJustificationTag
#check @ReverseMathLowerBound.eraseJustificationTag
#print axioms ReverseMathLowerBound.eraseJustificationTag
#check @ReverseMathCalibration.eraseJustificationTags
#print axioms ReverseMathCalibration.eraseJustificationTags

#check @artsGieslConcreteSharpTheoremUpperBound_eraseTags_eq_viaTheoremAlignment
#print axioms artsGieslConcreteSharpTheoremUpperBound_eraseTags_eq_viaTheoremAlignment
#check @artsGieslConcreteSharpTheoremLowerBound_eraseTags_eq_viaTheoremAlignment
#print axioms artsGieslConcreteSharpTheoremLowerBound_eraseTags_eq_viaTheoremAlignment
#check @artsGieslConcreteExactTheoremCalibration_eraseTags_eq_viaTheoremAlignment
#print axioms artsGieslConcreteExactTheoremCalibration_eraseTags_eq_viaTheoremAlignment
#check @artsGieslConcreteExactTheoremCalibration_sameMathematicalContent_as_viaTheoremAlignment
#print axioms artsGieslConcreteExactTheoremCalibration_sameMathematicalContent_as_viaTheoremAlignment

example :
    artsGieslConcreteSharpTheoremUpperBound.bound.eraseJustificationTag =
      artsGieslConcreteSharpTheoremUpperBound_viaTheoremAlignment.bound.eraseJustificationTag :=
  artsGieslConcreteSharpTheoremUpperBound_eraseTags_eq_viaTheoremAlignment

example :
    artsGieslConcreteSharpTheoremLowerBound.bound.eraseJustificationTag =
      artsGieslConcreteSharpTheoremLowerBound_viaTheoremAlignment.bound.eraseJustificationTag :=
  artsGieslConcreteSharpTheoremLowerBound_eraseTags_eq_viaTheoremAlignment

example :
    artsGieslConcreteExactTheoremCalibration.calibration.eraseJustificationTags =
      artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment.calibration.eraseJustificationTags :=
  artsGieslConcreteExactTheoremCalibration_eraseTags_eq_viaTheoremAlignment

/-! ### Extended route-comparison: lower theory / lower ordinal -/

#check @artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment_sameLowerTheory
#print axioms artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment_sameLowerTheory
#check @artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment_sameLowerOrdinal
#print axioms artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment_sameLowerOrdinal

example :
    artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment.toSharpLowerBound.bound.theoryProfile.theory =
      artsGieslConcreteExactTheoremCalibration.toSharpLowerBound.bound.theoryProfile.theory :=
  artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment_sameLowerTheory

example :
    artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment.toSharpLowerBound.bound.theoryProfile.ordinalCeiling? =
      artsGieslConcreteExactTheoremCalibration.toSharpLowerBound.bound.theoryProfile.ordinalCeiling? :=
  artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment_sameLowerOrdinal

/-! ### Generic upper/lower route-comparison theorems -/

#check @ArtsGieslSharpTheoremUpperBound.ofExactCalibrationTransfer_sameTheory
#print axioms ArtsGieslSharpTheoremUpperBound.ofExactCalibrationTransfer_sameTheory
#check @ArtsGieslSharpTheoremUpperBound.ofExactCalibrationTransfer_sameOrdinal
#print axioms ArtsGieslSharpTheoremUpperBound.ofExactCalibrationTransfer_sameOrdinal
#check @ArtsGieslSharpTheoremUpperBound.ofExactCalibrationTransfer_sameStatus
#print axioms ArtsGieslSharpTheoremUpperBound.ofExactCalibrationTransfer_sameStatus
#check @ArtsGieslSharpTheoremUpperBound.ofExactCalibrationTransfer_eraseTags_eq_ofTheoremAlignment
#print axioms ArtsGieslSharpTheoremUpperBound.ofExactCalibrationTransfer_eraseTags_eq_ofTheoremAlignment
#check @ArtsGieslSharpTheoremLowerBound.ofExactCalibrationTransfer_sameTheory
#print axioms ArtsGieslSharpTheoremLowerBound.ofExactCalibrationTransfer_sameTheory
#check @ArtsGieslSharpTheoremLowerBound.ofExactCalibrationTransfer_sameOrdinal
#print axioms ArtsGieslSharpTheoremLowerBound.ofExactCalibrationTransfer_sameOrdinal
#check @ArtsGieslSharpTheoremLowerBound.ofExactCalibrationTransfer_sameStatus
#print axioms ArtsGieslSharpTheoremLowerBound.ofExactCalibrationTransfer_sameStatus
#check @ArtsGieslSharpTheoremLowerBound.ofExactCalibrationTransfer_eraseTags_eq_ofTheoremAlignment
#print axioms ArtsGieslSharpTheoremLowerBound.ofExactCalibrationTransfer_eraseTags_eq_ofTheoremAlignment

/-! ### Generic exact-calibration builders and route-equivalence theorems -/

#check @artsGieslExactTheoremCalibrationOfExactCalibrationTransfer
#print axioms artsGieslExactTheoremCalibrationOfExactCalibrationTransfer
#check @artsGieslExactTheoremCalibrationOfTheoremAlignmentFromExactTransfer
#print axioms artsGieslExactTheoremCalibrationOfTheoremAlignmentFromExactTransfer
#check @artsGieslSharpTheoremUpperBound_ofTheoremAlignmentRoute
#print axioms artsGieslSharpTheoremUpperBound_ofTheoremAlignmentRoute
#check @artsGieslSharpTheoremLowerBound_ofTheoremAlignmentRoute
#print axioms artsGieslSharpTheoremLowerBound_ofTheoremAlignmentRoute
#check @artsGieslExactTheoremCalibrationOfExactCalibrationTransfer_status
#print axioms artsGieslExactTheoremCalibrationOfExactCalibrationTransfer_status
#check @artsGieslExactTheoremCalibrationOfTheoremAlignmentFromExactTransfer_status
#print axioms artsGieslExactTheoremCalibrationOfTheoremAlignmentFromExactTransfer_status

#check @artsGieslExactTheoremCalibrationOfExactCalibrationTransfer_sameTargetProfile
#print axioms artsGieslExactTheoremCalibrationOfExactCalibrationTransfer_sameTargetProfile
#check @artsGieslExactTheoremCalibrationOfExactCalibrationTransfer_sameUpperTheory
#print axioms artsGieslExactTheoremCalibrationOfExactCalibrationTransfer_sameUpperTheory
#check @artsGieslExactTheoremCalibrationOfExactCalibrationTransfer_sameUpperOrdinal
#print axioms artsGieslExactTheoremCalibrationOfExactCalibrationTransfer_sameUpperOrdinal
#check @artsGieslExactTheoremCalibrationOfExactCalibrationTransfer_sameUpperStatus
#print axioms artsGieslExactTheoremCalibrationOfExactCalibrationTransfer_sameUpperStatus
#check @artsGieslExactTheoremCalibrationOfExactCalibrationTransfer_sameStatus
#print axioms artsGieslExactTheoremCalibrationOfExactCalibrationTransfer_sameStatus
#check @artsGieslExactTheoremCalibrationOfExactCalibrationTransfer_sameLowerTheory
#print axioms artsGieslExactTheoremCalibrationOfExactCalibrationTransfer_sameLowerTheory
#check @artsGieslExactTheoremCalibrationOfExactCalibrationTransfer_sameLowerOrdinal
#print axioms artsGieslExactTheoremCalibrationOfExactCalibrationTransfer_sameLowerOrdinal
#check @artsGieslExactTheoremCalibrationOfExactCalibrationTransfer_sameLowerStatus
#print axioms artsGieslExactTheoremCalibrationOfExactCalibrationTransfer_sameLowerStatus
#check @artsGieslExactTheoremCalibrationOfExactCalibrationTransfer_eraseTags_eq_ofTheoremAlignment_upperBound
#print axioms artsGieslExactTheoremCalibrationOfExactCalibrationTransfer_eraseTags_eq_ofTheoremAlignment_upperBound
#check @artsGieslExactTheoremCalibrationOfExactCalibrationTransfer_eraseTags_eq_ofTheoremAlignment_lowerBound
#print axioms artsGieslExactTheoremCalibrationOfExactCalibrationTransfer_eraseTags_eq_ofTheoremAlignment_lowerBound
#check @artsGieslExactTheoremCalibrationOfExactCalibrationTransfer_sameMathematicalContent_as_ofTheoremAlignment
#print axioms artsGieslExactTheoremCalibrationOfExactCalibrationTransfer_sameMathematicalContent_as_ofTheoremAlignment

/-! ### Canonical instantiation of the generic route-equivalence
surface

Reachability `#check`s for the generic theorems applied to the
canonical exact-calibration transfer. These pin the generic names
through the test file without forcing universe unification at the
module top level (the generic theorems carry `Ordinal`-universe
polymorphism; `#check` handles this automatically). -/

#check ArtsGieslSharpTheoremUpperBound.ofExactCalibrationTransfer_sameTheory
  artsGieslExactCalibrationTransferFromSct rfl rfl
#print axioms ArtsGieslSharpTheoremUpperBound.ofExactCalibrationTransfer_sameTheory
#check ArtsGieslSharpTheoremLowerBound.ofExactCalibrationTransfer_sameTheory
  artsGieslExactCalibrationTransferFromSct rfl rfl
#print axioms ArtsGieslSharpTheoremLowerBound.ofExactCalibrationTransfer_sameTheory
#check ArtsGieslSharpTheoremUpperBound.ofExactCalibrationTransfer_eraseTags_eq_ofTheoremAlignment
  artsGieslExactCalibrationTransferFromSct rfl rfl rfl
#print axioms ArtsGieslSharpTheoremUpperBound.ofExactCalibrationTransfer_eraseTags_eq_ofTheoremAlignment
#check ArtsGieslSharpTheoremLowerBound.ofExactCalibrationTransfer_eraseTags_eq_ofTheoremAlignment
  artsGieslExactCalibrationTransferFromSct rfl rfl rfl
#print axioms ArtsGieslSharpTheoremLowerBound.ofExactCalibrationTransfer_eraseTags_eq_ofTheoremAlignment
#check artsGieslExactTheoremCalibrationOfExactCalibrationTransfer
  artsGieslExactCalibrationTransferFromSct rfl rfl
#print axioms artsGieslExactTheoremCalibrationOfExactCalibrationTransfer
#check artsGieslExactTheoremCalibrationOfTheoremAlignmentFromExactTransfer
  artsGieslExactCalibrationTransferFromSct rfl rfl
#print axioms artsGieslExactTheoremCalibrationOfTheoremAlignmentFromExactTransfer
#check artsGieslExactTheoremCalibrationOfExactCalibrationTransfer_sameMathematicalContent_as_ofTheoremAlignment
  artsGieslExactCalibrationTransferFromSct rfl rfl
#print axioms artsGieslExactTheoremCalibrationOfExactCalibrationTransfer_sameMathematicalContent_as_ofTheoremAlignment

/-! ### Semantic / presentation-erasure layer -/

#check @SecondOrderTheoryProfile.erasePresentationMetadata
#print axioms SecondOrderTheoryProfile.erasePresentationMetadata
#check @SecondOrderTheoryProfile.erasePresentationMetadata_label
#print axioms SecondOrderTheoryProfile.erasePresentationMetadata_label
#check @SecondOrderTheoryProfile.erasePresentationMetadata_theory
#print axioms SecondOrderTheoryProfile.erasePresentationMetadata_theory
#check @SecondOrderTheoryProfile.erasePresentationMetadata_ordinal
#print axioms SecondOrderTheoryProfile.erasePresentationMetadata_ordinal
#check @SecondOrderTheoryProfile.erasePresentationMetadata_complexity
#print axioms SecondOrderTheoryProfile.erasePresentationMetadata_complexity
#check @SecondOrderTheoryProfile.erasePresentationMetadata_congr
#print axioms SecondOrderTheoryProfile.erasePresentationMetadata_congr

#check @ReverseMathUpperBound.erasePresentationMetadata
#print axioms ReverseMathUpperBound.erasePresentationMetadata
#check @ReverseMathLowerBound.erasePresentationMetadata
#print axioms ReverseMathLowerBound.erasePresentationMetadata
#check @ReverseMathUpperBound.erasePresentationMetadata_congr
#print axioms ReverseMathUpperBound.erasePresentationMetadata_congr
#check @ReverseMathLowerBound.erasePresentationMetadata_congr
#print axioms ReverseMathLowerBound.erasePresentationMetadata_congr

/-! ### Stronger generic presentation-erased route theorems (only
`hTheory` and `hOrdinal` needed) -/

#check @ArtsGieslSharpTheoremUpperBound.ofExactCalibrationTransfer_erasePresentation_eq_ofTheoremAlignment
#print axioms ArtsGieslSharpTheoremUpperBound.ofExactCalibrationTransfer_erasePresentation_eq_ofTheoremAlignment
#check @ArtsGieslSharpTheoremLowerBound.ofExactCalibrationTransfer_erasePresentation_eq_ofTheoremAlignment
#print axioms ArtsGieslSharpTheoremLowerBound.ofExactCalibrationTransfer_erasePresentation_eq_ofTheoremAlignment
#check @artsGieslExactTheoremCalibrationOfExactCalibrationTransfer_erasePresentation_eq_ofTheoremAlignment_upperBound
#print axioms artsGieslExactTheoremCalibrationOfExactCalibrationTransfer_erasePresentation_eq_ofTheoremAlignment_upperBound
#check @artsGieslExactTheoremCalibrationOfExactCalibrationTransfer_erasePresentation_eq_ofTheoremAlignment_lowerBound
#print axioms artsGieslExactTheoremCalibrationOfExactCalibrationTransfer_erasePresentation_eq_ofTheoremAlignment_lowerBound

/-! ### Stronger packaged generic route-equivalence layer -/

#check @artsGieslExactTheoremCalibrationOfExactCalibrationTransfer_sameSemanticContent_as_ofTheoremAlignment
#print axioms artsGieslExactTheoremCalibrationOfExactCalibrationTransfer_sameSemanticContent_as_ofTheoremAlignment

/-! ### Canonical instantiations of the stronger layer on
`artsGieslExactCalibrationTransferFromSct` -/

#check ArtsGieslSharpTheoremUpperBound.ofExactCalibrationTransfer_erasePresentation_eq_ofTheoremAlignment
  artsGieslExactCalibrationTransferFromSct rfl rfl
#print axioms ArtsGieslSharpTheoremUpperBound.ofExactCalibrationTransfer_erasePresentation_eq_ofTheoremAlignment
#check ArtsGieslSharpTheoremLowerBound.ofExactCalibrationTransfer_erasePresentation_eq_ofTheoremAlignment
  artsGieslExactCalibrationTransferFromSct rfl rfl
#print axioms ArtsGieslSharpTheoremLowerBound.ofExactCalibrationTransfer_erasePresentation_eq_ofTheoremAlignment
#check artsGieslExactTheoremCalibrationOfExactCalibrationTransfer_erasePresentation_eq_ofTheoremAlignment_upperBound
  artsGieslExactCalibrationTransferFromSct rfl rfl
#print axioms artsGieslExactTheoremCalibrationOfExactCalibrationTransfer_erasePresentation_eq_ofTheoremAlignment_upperBound
#check artsGieslExactTheoremCalibrationOfExactCalibrationTransfer_erasePresentation_eq_ofTheoremAlignment_lowerBound
  artsGieslExactCalibrationTransferFromSct rfl rfl
#print axioms artsGieslExactTheoremCalibrationOfExactCalibrationTransfer_erasePresentation_eq_ofTheoremAlignment_lowerBound
#check artsGieslExactTheoremCalibrationOfExactCalibrationTransfer_sameSemanticContent_as_ofTheoremAlignment
  artsGieslExactCalibrationTransferFromSct rfl rfl
#print axioms artsGieslExactTheoremCalibrationOfExactCalibrationTransfer_sameSemanticContent_as_ofTheoremAlignment

end ArtsGieslReverseMathCalibrationReach
