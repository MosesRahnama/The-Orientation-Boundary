import OperatorKO7.Meta.ArtsGiesl_UpperBound
import OperatorKO7.Meta.ReverseMathOmega3WellOrdering

/-!
# Arts-Giesl Lower-Bound Profile Records

Profile records for proposed reverse-mathematical lower bounds on Arts-Giesl
soundness.

`ReverseMathLowerBound` stores only a theory profile, an evidence-status tag,
and a justification string. The theorems in this module establish record
equalities, comparisons in the finite `FormalTheory` register, and independent
well-ordering facts about the canonical `ω^3` carrier. A second-order
derivability relation and an Arts-Giesl reduction lie outside these records.

The initial profile stores:

- the `RCA₀` theory tag;
- the `Π⁰₂` formula-class tag copied from the imported proof-theoretic register.
-/

namespace OperatorKO7.ArtsGieslLowerBound

open OperatorKO7.ProofTheoreticRegister
open OperatorKO7.ReverseMathFramework
open OperatorKO7.TerminationPrincipleRegister

/-- Metadata profile assigning the `RCA₀` theory tag and the `Π⁰₂`
formula-class tag. Its Lean content is limited to those assignments. -/
def artsGieslPi02FloorProfile : SecondOrderTheoryProfile where
  label := "RCA₀ with Π⁰₂ floor"
  theory := FormalTheory.RCA0
  complexityFloor? := some FormulaClass.pi02

/-- Lower-bound metadata record carrying the `theoremLevel` evidence tag. The
record type enforces only its stored profile, status, and justification fields. -/
def artsGieslTheoremLowerBound : ReverseMathLowerBound artsGieslPrincipleProfile where
  theoryProfile := artsGieslPi02FloorProfile
  evidenceStatus := EvidenceStatus.theoremLevel
  justificationTag := "Pi02 soundness floor over RCA0"

@[simp] theorem artsGieslTheoremLowerBound_status :
    artsGieslTheoremLowerBound.evidenceStatus = EvidenceStatus.theoremLevel := rfl

@[simp] theorem artsGieslPi02FloorProfile_theory :
    artsGieslPi02FloorProfile.theory = FormalTheory.RCA0 := rfl

@[simp] theorem artsGieslPi02FloorProfile_complexity :
    artsGieslPi02FloorProfile.complexityFloor? = some FormulaClass.pi02 := rfl

/-- The profile's complexity tag equals the Arts-Giesl registry's formula-class tag. -/
theorem artsGieslPi02FloorProfile_supported :
    artsGieslPi02FloorProfile.complexityFloor? =
      some artsGieslLicenseProfile.complexity := by
  simp [artsGieslPi02FloorProfile, artsGieslLicenseProfile]

/-- Constructor-order comparison between the `RCA₀` and
`RCA₀ + WO(ω^3)` entries of `FormalTheory`. -/
theorem artsGieslTheoremLowerBound_le_target :
    artsGieslTheoremLowerBound.theoryProfile.theory ≤
      rca0WoOmega3TheoryProfile.theory := by
  decide

/-- The registry principle profile and lower-bound record carry the same
formula-class tag. -/
theorem artsGiesl_registry_profile_matches_lowerBound_floor :
    artsGieslEntry.profile.complexity? = artsGieslTheoremLowerBound.theoryProfile.complexityFloor? := by
  simp [artsGieslEntry, artsGieslTheoremLowerBound, artsGieslPi02FloorProfile,
    artsGieslPrincipleProfile, artsGieslLicenseProfile]

/-- Projection summary for the lower-bound metadata record. -/
theorem artsGieslTheoremLowerBound_supported :
    artsGieslTheoremLowerBound.evidenceStatus = EvidenceStatus.theoremLevel
      ∧ artsGieslTheoremLowerBound.theoryProfile.theory = FormalTheory.RCA0
      ∧ artsGieslTheoremLowerBound.theoryProfile.complexityFloor? = some FormulaClass.pi02
      ∧ artsGieslTheoremLowerBound.theoryProfile.theory ≤ rca0WoOmega3TheoryProfile.theory := by
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  · exact artsGieslTheoremLowerBound_le_target

/-- The coarse profile's theory field differs from the proposed target field. -/
theorem artsGieslTheoremLowerBound_theory_ne_target :
    artsGieslTheoremLowerBound.theoryProfile.theory ≠ FormalTheory.RCA0_WO_omega3 := by
  simp [artsGieslTheoremLowerBound, artsGieslPi02FloorProfile]

/-- The coarse profile's absent ordinal field differs from the proposed `ω^3` target. -/
theorem artsGieslTheoremLowerBound_ordinal_ne_target :
    artsGieslTheoremLowerBound.theoryProfile.ordinalCeiling? ≠ some OperatorKO7.ReverseMathSupport.omegaPowThree := by
  simp [artsGieslTheoremLowerBound, artsGieslPi02FloorProfile]

/-- Profile package for a lower-bound claim at the `ω^3` target.

Mechanized content: `omega3Backing` carries well-foundedness of the canonical
`Ordinal.toType ω^3` carrier and its order-type identity.

External content: an Arts-Giesl-to-well-ordering bridge and an `RCA₀`
provability predicate lie outside the structure. Its theory and evidence-status
fields record the calibration attributed to Moser-Schnabl and
Frittaion-Pelupessy-Steila-Yokoyama. -/
structure ArtsGieslSharpTheoremLowerBound where
  bound : ReverseMathLowerBound artsGieslPrincipleProfile
  theoryEq : bound.theoryProfile.theory = FormalTheory.RCA0_WO_omega3
  ordinalEq :
    bound.theoryProfile.ordinalCeiling? =
      some OperatorKO7.ReverseMathSupport.omegaPowThree
  theoremLevel : bound.evidenceStatus = EvidenceStatus.theoremLevel
  /-- Well-foundedness and order-type identity for the canonical `ω^3` carrier.
  This field is independent of the Arts-Giesl principle. -/
  omega3Backing : OperatorKO7.ReverseMathOmega3.WOOmega3Backing :=
    OperatorKO7.ReverseMathOmega3.wo_omega3_backing

/-- Projection of the three profile/status fields from the package. -/
theorem ArtsGieslSharpTheoremLowerBound.supported
    (L : ArtsGieslSharpTheoremLowerBound) :
    L.bound.theoryProfile.theory = FormalTheory.RCA0_WO_omega3
      ∧ L.bound.theoryProfile.ordinalCeiling? =
          some OperatorKO7.ReverseMathSupport.omegaPowThree
      ∧ L.bound.evidenceStatus = EvidenceStatus.theoremLevel := by
  exact ⟨L.theoryEq, L.ordinalEq, L.theoremLevel⟩

/-- Project the independent `ω^3` well-ordering witness stored in the package. -/
theorem ArtsGieslSharpTheoremLowerBound.carries_genuine_wo_omega3
    (L : ArtsGieslSharpTheoremLowerBound) :
    OperatorKO7.ReverseMathOmega3.WOOmega3Backing :=
  L.omega3Backing

/-- Pair the SCT profile's `ω^3` field equality with the independent canonical
`ω^3` well-ordering witness. The conclusion contains only this conjunction. -/
theorem sctExactCalibration_omega3_genuinely_wellOrdered :
    sctExactCalibration.targetProfile.ordinalCeiling?
        = some OperatorKO7.ReverseMathOmega3.omega3
      ∧ OperatorKO7.ReverseMathOmega3.WOOmega3Backing :=
  ⟨rfl, OperatorKO7.ReverseMathOmega3.wo_omega3_backing⟩

/-- Theory-tag inequality excludes the coarse lower-bound record from the
target-profile package. -/
theorem artsGieslTheoremLowerBound_not_sharp :
    ¬ ∃ L : ArtsGieslSharpTheoremLowerBound, L.bound = artsGieslTheoremLowerBound := by
  rintro ⟨L, hL⟩
  have hTheory := L.theoryEq
  rw [hL] at hTheory
  simp [artsGieslTheoremLowerBound, artsGieslPi02FloorProfile] at hTheory

/-- Record comparing two lower-bound profile values. -/
structure ArtsGieslTheoremLowerBoundGap where
  current : ReverseMathLowerBound artsGieslPrincipleProfile
  target : SecondOrderTheoryProfile
  currentLeTarget : current.theoryProfile.theory ≤ target.theory
  theoryNeTarget : current.theoryProfile.theory ≠ target.theory
  ordinalNeTarget : current.theoryProfile.ordinalCeiling? ≠ target.ordinalCeiling?

/-- Profile comparison between the coarse record and the proposed
`RCA₀ + WO(ω^3)` target. -/
noncomputable def artsGieslCurrentTheoremLowerBoundGap : ArtsGieslTheoremLowerBoundGap where
  current := artsGieslTheoremLowerBound
  target := rca0WoOmega3TheoryProfile
  currentLeTarget := artsGieslTheoremLowerBound_le_target
  theoryNeTarget := artsGieslTheoremLowerBound_theory_ne_target
  ordinalNeTarget := artsGieslTheoremLowerBound_ordinal_ne_target

/-- Projection summary for the lower-bound profile comparison. -/
theorem artsGieslCurrentTheoremLowerBoundGap_supported :
    artsGieslCurrentTheoremLowerBoundGap.current.evidenceStatus = EvidenceStatus.theoremLevel
      ∧ artsGieslCurrentTheoremLowerBoundGap.current.theoryProfile.theory ≤
          artsGieslCurrentTheoremLowerBoundGap.target.theory
      ∧ artsGieslCurrentTheoremLowerBoundGap.current.theoryProfile.theory ≠
          artsGieslCurrentTheoremLowerBoundGap.target.theory
      ∧ artsGieslCurrentTheoremLowerBoundGap.current.theoryProfile.ordinalCeiling? ≠
          artsGieslCurrentTheoremLowerBoundGap.target.ordinalCeiling? := by
  constructor
  · rfl
  constructor
  · exact artsGieslCurrentTheoremLowerBoundGap.currentLeTarget
  constructor
  · exact artsGieslCurrentTheoremLowerBoundGap.theoryNeTarget
  · exact artsGieslCurrentTheoremLowerBoundGap.ordinalNeTarget

/-- Record requiring a lower-bound profile to match the SCT target profile and
carry the `theoremLevel` status tag. Its fields contain profile and status
equalities; an SCT-to-Arts-Giesl reduction lies outside this record. -/
structure ArtsGieslSctSharpLowerTransfer where
  bound : ReverseMathLowerBound artsGieslPrincipleProfile
  theoryEqSct :
    bound.theoryProfile.theory = sctExactCalibration.targetProfile.theory
  ordinalEqSct :
    bound.theoryProfile.ordinalCeiling? = sctExactCalibration.targetProfile.ordinalCeiling?
  theoremLevel : bound.evidenceStatus = EvidenceStatus.theoremLevel

/-- Convert the matching-profile record into the corresponding target-profile package. -/
noncomputable def ArtsGieslSctSharpLowerTransfer.toSharpTheoremLowerBound
    (T : ArtsGieslSctSharpLowerTransfer) :
    ArtsGieslSharpTheoremLowerBound where
  bound := T.bound
  theoryEq := by simpa using T.theoryEqSct
  ordinalEq := by simpa using T.ordinalEqSct
  theoremLevel := T.theoremLevel

/-- Projection summary for the SCT-matching lower-bound profile. -/
theorem ArtsGieslSctSharpLowerTransfer.supported
    (T : ArtsGieslSctSharpLowerTransfer) :
    T.bound.theoryProfile.theory = FormalTheory.RCA0_WO_omega3
      ∧ T.bound.theoryProfile.ordinalCeiling? =
          some OperatorKO7.ReverseMathSupport.omegaPowThree
      ∧ T.bound.evidenceStatus = EvidenceStatus.theoremLevel := by
  exact T.toSharpTheoremLowerBound.supported

/-- A matching-profile record yields an inhabitant of the target-profile package. -/
theorem artsGiesl_sharpLowerBound_exists_if_sctTransfer
    (T : ArtsGieslSctSharpLowerTransfer) :
    ∃ L : ArtsGieslSharpTheoremLowerBound, L.bound = T.bound := by
  exact ⟨T.toSharpTheoremLowerBound, rfl⟩

/-- Build an SCT-matching lower-bound profile from the target and
evidence-status fields of an AG/SCT alignment record. The formal result is
profile bookkeeping. -/
noncomputable def ArtsGieslSctSharpLowerTransfer.ofTheoremAlignment
    (A : ArtsGieslSctTheoremAlignment) :
    ArtsGieslSctSharpLowerTransfer where
  bound := {
    theoryProfile := sctExactLowerBound.theoryProfile
    evidenceStatus := A.evidenceStatus
    justificationTag := "theorem-level AG/SCT exact-target lower transfer"
  }
  theoryEqSct := by
    rfl
  ordinalEqSct := by
    rfl
  theoremLevel := A.theoremLevel

/-- A target-alignment record yields a target-profile package. -/
theorem artsGiesl_sharpLowerBound_exists_if_theoremAlignment
    (A : ArtsGieslSctTheoremAlignment) :
    ∃ L : ArtsGieslSharpTheoremLowerBound,
      L.bound = (ArtsGieslSctSharpLowerTransfer.ofTheoremAlignment A).bound := by
  exact artsGiesl_sharpLowerBound_exists_if_sctTransfer
    (ArtsGieslSctSharpLowerTransfer.ofTheoremAlignment A)

/-- Within the repository's coarse calibration framework, copy the destination
lower-bound record and source-target equalities from an
`ExactCalibrationTransfer` into a sharp-profile package. The generic
`witnessTransport` field is a cost-shape record; the construction copies profile
fields between the two records. -/
noncomputable def ArtsGieslSharpTheoremLowerBound.ofExactCalibrationTransfer
    (T : ExactCalibrationTransfer sctPrincipleProfile artsGieslPrincipleProfile)
    (hTheory : T.sourceCalibration.targetProfile.theory = FormalTheory.RCA0_WO_omega3)
    (hOrdinal :
      T.sourceCalibration.targetProfile.ordinalCeiling? =
        some OperatorKO7.ReverseMathSupport.omegaPowThree) :
    ArtsGieslSharpTheoremLowerBound where
  bound := T.dstLower
  theoryEq := by
    rw [T.lowerMatchesSourceTarget]
    exact hTheory
  ordinalEq := by
    rw [T.lowerMatchesSourceTarget]
    simpa [OperatorKO7.ReverseMathSupport.omegaPowThree] using hOrdinal
  theoremLevel := T.lowerTheoremLevel

/-- The copied destination record inhabits the sharp-profile package. -/
theorem artsGiesl_sharpLowerBound_exists_if_exactTransfer
    (T : ExactCalibrationTransfer sctPrincipleProfile artsGieslPrincipleProfile)
    (hTheory : T.sourceCalibration.targetProfile.theory = FormalTheory.RCA0_WO_omega3)
    (hOrdinal :
      T.sourceCalibration.targetProfile.ordinalCeiling? =
        some OperatorKO7.ReverseMathSupport.omegaPowThree) :
    ∃ L : ArtsGieslSharpTheoremLowerBound, L.bound = T.dstLower := by
  exact ⟨ArtsGieslSharpTheoremLowerBound.ofExactCalibrationTransfer T hTheory hOrdinal, rfl⟩

/-- Direct profile package at the proposed `ω^3` lower-bound target.

The profile fields record an externally attributed `RCA₀ + WO(ω^3)` calibration.
The independent `omega3Backing` field proves that the canonical `ω^3` carrier
is well-founded and has order type `ω^3`. The formal scope ends at this carrier
fact and the stored profile fields. -/
noncomputable def artsGieslDirectSharpTheoremLowerBound :
    ArtsGieslSharpTheoremLowerBound where
  bound := {
    theoryProfile := rca0WoOmega3TheoryProfile
    evidenceStatus := EvidenceStatus.theoremLevel
    justificationTag := "exact-target theorem lower package"
  }
  theoryEq := rfl
  ordinalEq := by
    rfl
  theoremLevel := rfl

@[simp] theorem artsGieslDirectSharpTheoremLowerBound_status :
    artsGieslDirectSharpTheoremLowerBound.bound.evidenceStatus =
      EvidenceStatus.theoremLevel := rfl

theorem artsGieslDirectSharpTheoremLowerBound_supported :
    artsGieslDirectSharpTheoremLowerBound.bound.theoryProfile.theory =
        FormalTheory.RCA0_WO_omega3
      ∧ artsGieslDirectSharpTheoremLowerBound.bound.theoryProfile.ordinalCeiling? =
          some OperatorKO7.ReverseMathSupport.omegaPowThree
      ∧ artsGieslDirectSharpTheoremLowerBound.bound.evidenceStatus =
          EvidenceStatus.theoremLevel := by
  constructor
  · rfl
  constructor
  · rfl
  · rfl

/-- The direct profile record inhabits the target-profile package. The
conclusion is a record-existence proposition. -/
theorem artsGiesl_sharpLowerBound_exists_directly :
    ∃ L : ArtsGieslSharpTheoremLowerBound, L = artsGieslDirectSharpTheoremLowerBound := by
  exact ⟨artsGieslDirectSharpTheoremLowerBound, rfl⟩

/-! ## Profile-construction comparison theorems

The calibration-record construction
`ArtsGieslSharpTheoremLowerBound.ofExactCalibrationTransfer` and the
alignment-record construction
`(ArtsGieslSctSharpLowerTransfer.ofTheoremAlignment ...).toSharpTheoremLowerBound`
agree on selected metadata fields. With an additional source-profile equality,
their justification-tag-erased records agree. -/

/-- The two profile constructions produce the same theory field. -/
theorem ArtsGieslSharpTheoremLowerBound.ofExactCalibrationTransfer_sameTheory
    (T : ExactCalibrationTransfer sctPrincipleProfile artsGieslPrincipleProfile)
    (hTheory : T.sourceCalibration.targetProfile.theory =
      FormalTheory.RCA0_WO_omega3)
    (hOrdinal : T.sourceCalibration.targetProfile.ordinalCeiling? =
      some OperatorKO7.ReverseMathSupport.omegaPowThree) :
    (ArtsGieslSharpTheoremLowerBound.ofExactCalibrationTransfer
        T hTheory hOrdinal).bound.theoryProfile.theory =
      ((ArtsGieslSctSharpLowerTransfer.ofTheoremAlignment
          (ArtsGieslSctTheoremAlignment.ofExactCalibrationTransfer
            T hTheory hOrdinal)
        ).toSharpTheoremLowerBound).bound.theoryProfile.theory := by
  rw [(ArtsGieslSharpTheoremLowerBound.ofExactCalibrationTransfer
        T hTheory hOrdinal).theoryEq,
    ((ArtsGieslSctSharpLowerTransfer.ofTheoremAlignment
        (ArtsGieslSctTheoremAlignment.ofExactCalibrationTransfer
          T hTheory hOrdinal)
      ).toSharpTheoremLowerBound).theoryEq]

/-- The two profile constructions produce the same ordinal field. -/
theorem ArtsGieslSharpTheoremLowerBound.ofExactCalibrationTransfer_sameOrdinal
    (T : ExactCalibrationTransfer sctPrincipleProfile artsGieslPrincipleProfile)
    (hTheory : T.sourceCalibration.targetProfile.theory =
      FormalTheory.RCA0_WO_omega3)
    (hOrdinal : T.sourceCalibration.targetProfile.ordinalCeiling? =
      some OperatorKO7.ReverseMathSupport.omegaPowThree) :
    (ArtsGieslSharpTheoremLowerBound.ofExactCalibrationTransfer
        T hTheory hOrdinal).bound.theoryProfile.ordinalCeiling? =
      ((ArtsGieslSctSharpLowerTransfer.ofTheoremAlignment
          (ArtsGieslSctTheoremAlignment.ofExactCalibrationTransfer
            T hTheory hOrdinal)
        ).toSharpTheoremLowerBound).bound.theoryProfile.ordinalCeiling? := by
  rw [(ArtsGieslSharpTheoremLowerBound.ofExactCalibrationTransfer
        T hTheory hOrdinal).ordinalEq,
    ((ArtsGieslSctSharpLowerTransfer.ofTheoremAlignment
        (ArtsGieslSctTheoremAlignment.ofExactCalibrationTransfer
          T hTheory hOrdinal)
      ).toSharpTheoremLowerBound).ordinalEq]

/-- The two profile constructions produce the same evidence-status field. -/
theorem ArtsGieslSharpTheoremLowerBound.ofExactCalibrationTransfer_sameStatus
    (T : ExactCalibrationTransfer sctPrincipleProfile artsGieslPrincipleProfile)
    (hTheory : T.sourceCalibration.targetProfile.theory =
      FormalTheory.RCA0_WO_omega3)
    (hOrdinal : T.sourceCalibration.targetProfile.ordinalCeiling? =
      some OperatorKO7.ReverseMathSupport.omegaPowThree) :
    (ArtsGieslSharpTheoremLowerBound.ofExactCalibrationTransfer
        T hTheory hOrdinal).bound.evidenceStatus =
      ((ArtsGieslSctSharpLowerTransfer.ofTheoremAlignment
          (ArtsGieslSctTheoremAlignment.ofExactCalibrationTransfer
            T hTheory hOrdinal)
        ).toSharpTheoremLowerBound).bound.evidenceStatus := by
  rw [(ArtsGieslSharpTheoremLowerBound.ofExactCalibrationTransfer
        T hTheory hOrdinal).theoremLevel,
    ((ArtsGieslSctSharpLowerTransfer.ofTheoremAlignment
        (ArtsGieslSctTheoremAlignment.ofExactCalibrationTransfer
          T hTheory hOrdinal)
      ).toSharpTheoremLowerBound).theoremLevel]

/-- Equality after erasing justification tags, assuming the source target
profile equals the SCT lower-bound profile. -/
theorem ArtsGieslSharpTheoremLowerBound.ofExactCalibrationTransfer_eraseTags_eq_ofTheoremAlignment
    (T : ExactCalibrationTransfer sctPrincipleProfile artsGieslPrincipleProfile)
    (hTheory : T.sourceCalibration.targetProfile.theory =
      FormalTheory.RCA0_WO_omega3)
    (hOrdinal : T.sourceCalibration.targetProfile.ordinalCeiling? =
      some OperatorKO7.ReverseMathSupport.omegaPowThree)
    (hSource : T.sourceCalibration.targetProfile =
      sctExactLowerBound.theoryProfile) :
    (ArtsGieslSharpTheoremLowerBound.ofExactCalibrationTransfer
        T hTheory hOrdinal).bound.eraseJustificationTag =
      ((ArtsGieslSctSharpLowerTransfer.ofTheoremAlignment
          (ArtsGieslSctTheoremAlignment.ofExactCalibrationTransfer
            T hTheory hOrdinal)
        ).toSharpTheoremLowerBound).bound.eraseJustificationTag := by
  apply ReverseMathLowerBound.eraseJustificationTag_congr
  · show T.dstLower.theoryProfile = sctExactLowerBound.theoryProfile
    rw [T.lowerMatchesSourceTarget, hSource]
  · show T.dstLower.evidenceStatus = EvidenceStatus.theoremLevel
    exact T.lowerTheoremLevel

/-- Equality after erasing presentation metadata, using only the displayed
theory, ordinal, and evidence-status equalities. -/
theorem ArtsGieslSharpTheoremLowerBound.ofExactCalibrationTransfer_erasePresentation_eq_ofTheoremAlignment
    (T : ExactCalibrationTransfer sctPrincipleProfile artsGieslPrincipleProfile)
    (hTheory : T.sourceCalibration.targetProfile.theory =
      FormalTheory.RCA0_WO_omega3)
    (hOrdinal : T.sourceCalibration.targetProfile.ordinalCeiling? =
      some OperatorKO7.ReverseMathSupport.omegaPowThree) :
    (ArtsGieslSharpTheoremLowerBound.ofExactCalibrationTransfer
        T hTheory hOrdinal).bound.erasePresentationMetadata =
      ((ArtsGieslSctSharpLowerTransfer.ofTheoremAlignment
          (ArtsGieslSctTheoremAlignment.ofExactCalibrationTransfer
            T hTheory hOrdinal)
        ).toSharpTheoremLowerBound).bound.erasePresentationMetadata := by
  apply ReverseMathLowerBound.erasePresentationMetadata_congr
  · show T.dstLower.theoryProfile.theory = FormalTheory.RCA0_WO_omega3
    rw [T.lowerMatchesSourceTarget]
    exact hTheory
  · show T.dstLower.theoryProfile.ordinalCeiling? =
      some OperatorKO7.ReverseMathSupport.omegaPowThree
    rw [T.lowerMatchesSourceTarget]
    exact hOrdinal
  · show T.dstLower.evidenceStatus = EvidenceStatus.theoremLevel
    exact T.lowerTheoremLevel

end OperatorKO7.ArtsGieslLowerBound
