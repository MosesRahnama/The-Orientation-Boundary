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
#check @artsGieslConcreteSctSharpLowerTransfer
#check @artsGieslConcreteSctSharpTransferPair
#check @artsGieslConcreteSctSharpTransferPair_yields_exactTheoremCalibration

/-! ### Named concrete sharp-theorem bounds -/

#check @artsGieslConcreteSharpTheoremUpperBound
#check @artsGieslConcreteSharpTheoremLowerBound

/-! ### Named concrete exact-theorem-calibration object -/

#check @artsGieslConcreteExactTheoremCalibration

/-! ### Theorem-facing projection lemmas on the concrete exact object -/

#check @artsGieslConcreteExactTheoremCalibration_status
#check @artsGieslConcreteExactTheoremCalibration_targetTheory
#check @artsGieslConcreteExactTheoremCalibration_targetOrdinal
#check @artsGieslConcreteExactTheoremCalibration_upperTheory
#check @artsGieslConcreteExactTheoremCalibration_upperOrdinal
#check @artsGieslConcreteExactTheoremCalibration_upperTheoremLevel
#check @artsGieslConcreteExactTheoremCalibration_lowerTheoremLevel

/-! ### Extraction theorems -/

#check @artsGieslConcreteExactTheoremCalibration_toSharpUpper_eq
#check @artsGieslConcreteExactTheoremCalibration_toSharpLower_eq

/-! ### Paper-facing aliases and strengthened endpoint -/

#check @artsGieslConcreteExactTheoremCalibration_isExact
#check @artsGieslConcreteExactTheoremCalibration_hitsTarget
#check @artsGieslConcreteSctSharpTransferPair_yields_exactTheoremCalibrationObject

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
#check @artsGieslConcreteSctTheoremAlignment_theory
#check @artsGieslConcreteSctTheoremAlignment_ordinal
#check @artsGieslConcreteSctTheoremAlignment_theoremLevel
#check @artsGieslConcreteSctTheoremAlignment_supported
#check @artsGieslConcreteSctTheoremAlignment_isTheoremLevel

#check @artsGieslConcreteSctSharpTransferPair_viaTheoremAlignment
#check @artsGieslConcreteSharpTheoremUpperBound_viaTheoremAlignment
#check @artsGieslConcreteSharpTheoremLowerBound_viaTheoremAlignment
#check @artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment

#check @artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment_status
#check @artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment_targetTheory
#check @artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment_targetOrdinal
#check @artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment_upperTheoremLevel
#check @artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment_lowerTheoremLevel

#check @artsGieslConcreteSctTheoremAlignment_yields_exactTheoremCalibration
#check @artsGieslConcreteSctTheoremAlignment_yields_exactTheoremCalibrationObject

#check @artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment_isExact
#check @artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment_hitsTarget

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
#check @artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment_sameUpperTheory
#check @artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment_sameUpperOrdinal
#check @artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment_sameUpperStatus
#check @artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment_sameLowerStatus
#check @artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment_sameStatus

#check @artsGieslConcreteSctSharpTransferPair_viaTheoremAlignment_upper_status
#check @artsGieslConcreteSctSharpTransferPair_viaTheoremAlignment_lower_status
#check @artsGieslConcreteSctSharpTransferPair_viaTheoremAlignment_supported
#check @artsGieslConcreteSctSharpTransferPair_routeComparison_upperStatus
#check @artsGieslConcreteSctSharpTransferPair_routeComparison_lowerStatus
#check @artsGieslConcreteSctSharpTransferPair_routeComparison_upperTheory
#check @artsGieslConcreteSctSharpTransferPair_routeComparison_lowerTheory

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
#check @ArtsGieslSctTheoremAlignment.ofExactCalibrationTransfer_theory
#check @ArtsGieslSctTheoremAlignment.ofExactCalibrationTransfer_ordinal
#check @ArtsGieslSctTheoremAlignment.ofExactCalibrationTransfer_theoremLevel

/-! ### Concrete exact-transfer-induced theorem-alignment object -/

#check @artsGieslExactCalibrationTransferFromSct_toTheoremAlignment
#check @artsGieslExactCalibrationTransferFromSct_toTheoremAlignment_supported
#check @artsGieslExactCalibrationTransferFromSct_toTheoremAlignment_eq_concrete
#check @artsGieslExactCalibrationTransferFromSct_toTheoremAlignment_sameTheory
#check @artsGieslExactCalibrationTransferFromSct_toTheoremAlignment_sameOrdinal
#check @artsGieslExactCalibrationTransferFromSct_toTheoremAlignment_sameStatus

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
#check @ReverseMathLowerBound.eraseJustificationTag
#check @ReverseMathCalibration.eraseJustificationTags

#check @artsGieslConcreteSharpTheoremUpperBound_eraseTags_eq_viaTheoremAlignment
#check @artsGieslConcreteSharpTheoremLowerBound_eraseTags_eq_viaTheoremAlignment
#check @artsGieslConcreteExactTheoremCalibration_eraseTags_eq_viaTheoremAlignment
#check @artsGieslConcreteExactTheoremCalibration_sameMathematicalContent_as_viaTheoremAlignment

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
#check @artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment_sameLowerOrdinal

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
#check @ArtsGieslSharpTheoremUpperBound.ofExactCalibrationTransfer_sameOrdinal
#check @ArtsGieslSharpTheoremUpperBound.ofExactCalibrationTransfer_sameStatus
#check @ArtsGieslSharpTheoremUpperBound.ofExactCalibrationTransfer_eraseTags_eq_ofTheoremAlignment
#check @ArtsGieslSharpTheoremLowerBound.ofExactCalibrationTransfer_sameTheory
#check @ArtsGieslSharpTheoremLowerBound.ofExactCalibrationTransfer_sameOrdinal
#check @ArtsGieslSharpTheoremLowerBound.ofExactCalibrationTransfer_sameStatus
#check @ArtsGieslSharpTheoremLowerBound.ofExactCalibrationTransfer_eraseTags_eq_ofTheoremAlignment

/-! ### Generic exact-calibration builders and route-equivalence theorems -/

#check @artsGieslExactTheoremCalibrationOfExactCalibrationTransfer
#check @artsGieslExactTheoremCalibrationOfTheoremAlignmentFromExactTransfer
#check @artsGieslSharpTheoremUpperBound_ofTheoremAlignmentRoute
#check @artsGieslSharpTheoremLowerBound_ofTheoremAlignmentRoute
#check @artsGieslExactTheoremCalibrationOfExactCalibrationTransfer_status
#check @artsGieslExactTheoremCalibrationOfTheoremAlignmentFromExactTransfer_status

#check @artsGieslExactTheoremCalibrationOfExactCalibrationTransfer_sameTargetProfile
#check @artsGieslExactTheoremCalibrationOfExactCalibrationTransfer_sameUpperTheory
#check @artsGieslExactTheoremCalibrationOfExactCalibrationTransfer_sameUpperOrdinal
#check @artsGieslExactTheoremCalibrationOfExactCalibrationTransfer_sameUpperStatus
#check @artsGieslExactTheoremCalibrationOfExactCalibrationTransfer_sameStatus
#check @artsGieslExactTheoremCalibrationOfExactCalibrationTransfer_sameLowerTheory
#check @artsGieslExactTheoremCalibrationOfExactCalibrationTransfer_sameLowerOrdinal
#check @artsGieslExactTheoremCalibrationOfExactCalibrationTransfer_sameLowerStatus
#check @artsGieslExactTheoremCalibrationOfExactCalibrationTransfer_eraseTags_eq_ofTheoremAlignment_upperBound
#check @artsGieslExactTheoremCalibrationOfExactCalibrationTransfer_eraseTags_eq_ofTheoremAlignment_lowerBound
#check @artsGieslExactTheoremCalibrationOfExactCalibrationTransfer_sameMathematicalContent_as_ofTheoremAlignment

/-! ### Canonical instantiation of the generic route-equivalence
surface

Reachability `#check`s for the generic theorems applied to the
canonical exact-calibration transfer. These pin the generic names
through the test file without forcing universe unification at the
module top level (the generic theorems carry `Ordinal`-universe
polymorphism; `#check` handles this automatically). -/

#check ArtsGieslSharpTheoremUpperBound.ofExactCalibrationTransfer_sameTheory
  artsGieslExactCalibrationTransferFromSct rfl rfl
#check ArtsGieslSharpTheoremLowerBound.ofExactCalibrationTransfer_sameTheory
  artsGieslExactCalibrationTransferFromSct rfl rfl
#check ArtsGieslSharpTheoremUpperBound.ofExactCalibrationTransfer_eraseTags_eq_ofTheoremAlignment
  artsGieslExactCalibrationTransferFromSct rfl rfl rfl
#check ArtsGieslSharpTheoremLowerBound.ofExactCalibrationTransfer_eraseTags_eq_ofTheoremAlignment
  artsGieslExactCalibrationTransferFromSct rfl rfl rfl
#check artsGieslExactTheoremCalibrationOfExactCalibrationTransfer
  artsGieslExactCalibrationTransferFromSct rfl rfl
#check artsGieslExactTheoremCalibrationOfTheoremAlignmentFromExactTransfer
  artsGieslExactCalibrationTransferFromSct rfl rfl
#check artsGieslExactTheoremCalibrationOfExactCalibrationTransfer_sameMathematicalContent_as_ofTheoremAlignment
  artsGieslExactCalibrationTransferFromSct rfl rfl

/-! ### Semantic / presentation-erasure layer -/

#check @SecondOrderTheoryProfile.erasePresentationMetadata
#check @SecondOrderTheoryProfile.erasePresentationMetadata_label
#check @SecondOrderTheoryProfile.erasePresentationMetadata_theory
#check @SecondOrderTheoryProfile.erasePresentationMetadata_ordinal
#check @SecondOrderTheoryProfile.erasePresentationMetadata_complexity
#check @SecondOrderTheoryProfile.erasePresentationMetadata_congr

#check @ReverseMathUpperBound.erasePresentationMetadata
#check @ReverseMathLowerBound.erasePresentationMetadata
#check @ReverseMathUpperBound.erasePresentationMetadata_congr
#check @ReverseMathLowerBound.erasePresentationMetadata_congr

/-! ### Stronger generic presentation-erased route theorems (only
`hTheory` and `hOrdinal` needed) -/

#check @ArtsGieslSharpTheoremUpperBound.ofExactCalibrationTransfer_erasePresentation_eq_ofTheoremAlignment
#check @ArtsGieslSharpTheoremLowerBound.ofExactCalibrationTransfer_erasePresentation_eq_ofTheoremAlignment
#check @artsGieslExactTheoremCalibrationOfExactCalibrationTransfer_erasePresentation_eq_ofTheoremAlignment_upperBound
#check @artsGieslExactTheoremCalibrationOfExactCalibrationTransfer_erasePresentation_eq_ofTheoremAlignment_lowerBound

/-! ### Stronger packaged generic route-equivalence layer -/

#check @artsGieslExactTheoremCalibrationOfExactCalibrationTransfer_sameSemanticContent_as_ofTheoremAlignment

/-! ### Canonical instantiations of the stronger layer on
`artsGieslExactCalibrationTransferFromSct` -/

#check ArtsGieslSharpTheoremUpperBound.ofExactCalibrationTransfer_erasePresentation_eq_ofTheoremAlignment
  artsGieslExactCalibrationTransferFromSct rfl rfl
#check ArtsGieslSharpTheoremLowerBound.ofExactCalibrationTransfer_erasePresentation_eq_ofTheoremAlignment
  artsGieslExactCalibrationTransferFromSct rfl rfl
#check artsGieslExactTheoremCalibrationOfExactCalibrationTransfer_erasePresentation_eq_ofTheoremAlignment_upperBound
  artsGieslExactCalibrationTransferFromSct rfl rfl
#check artsGieslExactTheoremCalibrationOfExactCalibrationTransfer_erasePresentation_eq_ofTheoremAlignment_lowerBound
  artsGieslExactCalibrationTransferFromSct rfl rfl
#check artsGieslExactTheoremCalibrationOfExactCalibrationTransfer_sameSemanticContent_as_ofTheoremAlignment
  artsGieslExactCalibrationTransferFromSct rfl rfl

end ArtsGieslReverseMathCalibrationReach
