import OperatorKO7.Meta.ReverseMathSupport

/-!
This module defines reverse-mathematics profile records, finite-register comparisons, and
presentation-metadata erasures. Evidence and calibration statuses are stored fields. Semantic
upper and lower bounds for a principle require proof-bearing data beyond these records.















-/

namespace OperatorKO7.ReverseMathFramework

open Ordinal
open OperatorKO7.ProofTheoreticRegister
open OperatorKO7.ReverseMathSupport

/-- Carrier with the constructors displayed below. -/
inductive EvidenceStatus
  | theoremLevel
  | profileLevel
  | conjectural
  deriving DecidableEq, Repr

/-- Data record whose requirements are the fields displayed below.



-/
structure SecondOrderTheoryProfile where
  label : String
  theory : FormalTheory
  ordinalCeiling? : Option Ordinal := none
  complexityFloor? : Option FormulaClass := none

/-- Data record whose requirements are the fields displayed below.


-/
structure PrincipleProfile where
  label : String
  family? : Option AscentFamily := none
  complexity? : Option FormulaClass := none

/-- Data record whose requirements are the fields displayed below.

-/
structure TheoryImplication (src dst : SecondOrderTheoryProfile) where
  carries : src.theory ≤ dst.theory

/-- Data record whose requirements are the fields displayed below.





-/
structure TheoryConservativity (src dst : SecondOrderTheoryProfile) where
  extensionLe : src.theory ≤ dst.theory
  preservesOrdinalCeiling :
    match src.ordinalCeiling?, dst.ordinalCeiling? with
    | some α, some β => α = β
    | _, _ => True

/-- Data record whose requirements are the fields displayed below. -/
structure TheoryEquivalence (left right : SecondOrderTheoryProfile) where
  forward : TheoryImplication left right
  backward : TheoryImplication right left

/-- Data record whose requirements are the fields displayed below.


-/
structure ReverseMathUpperBound (P : PrincipleProfile) where
  theoryProfile : SecondOrderTheoryProfile
  evidenceStatus : EvidenceStatus
  justificationTag : String

/-- Data record whose requirements are the fields displayed below. -/
structure ReverseMathLowerBound (P : PrincipleProfile) where
  theoryProfile : SecondOrderTheoryProfile
  evidenceStatus : EvidenceStatus
  justificationTag : String

/-- Data record whose requirements are the fields displayed below.


-/
structure ReverseMathCalibration (P : PrincipleProfile) where
  targetProfile : SecondOrderTheoryProfile
  upperBound : ReverseMathUpperBound P
  lowerBound? : Option (ReverseMathLowerBound P) := none
  targetLeUpper : targetProfile.theory ≤ upperBound.theoryProfile.theory
  lowerLeTarget :
    match lowerBound? with
    | none => True
    | some lb => lb.theoryProfile.theory ≤ targetProfile.theory
  status : CalibrationStatus

/-- Data record whose requirements are the fields displayed below.











-/
structure ExactCalibrationTransfer
    (src dst : PrincipleProfile) where
  sourceCalibration : ReverseMathCalibration src
  sourceExact : sourceCalibration.status = CalibrationStatus.exact
  witnessTransport : ConstantOverheadTransformation
  dstUpper : ReverseMathUpperBound dst
  dstLower : ReverseMathLowerBound dst
  upperMatchesSourceTarget : dstUpper.theoryProfile = sourceCalibration.targetProfile
  lowerMatchesSourceTarget : dstLower.theoryProfile = sourceCalibration.targetProfile
  upperTheoremLevel : dstUpper.evidenceStatus = EvidenceStatus.theoremLevel
  lowerTheoremLevel : dstLower.evidenceStatus = EvidenceStatus.theoremLevel

namespace SecondOrderTheoryProfile

@[simp] theorem theoryImplication_refl (A : SecondOrderTheoryProfile) :
    TheoryImplication A A := ⟨Nat.le_refl _⟩

@[simp] theorem theoryEquivalence_refl (A : SecondOrderTheoryProfile) :
    TheoryEquivalence A A := ⟨theoryImplication_refl A, theoryImplication_refl A⟩

end SecondOrderTheoryProfile

namespace ReverseMathCalibration

/-- The displayed proposition follows from the stated hypotheses. -/
theorem has_upperBound {P : PrincipleProfile} (C : ReverseMathCalibration P) :
    C.targetProfile.theory ≤ C.upperBound.theoryProfile.theory :=
  C.targetLeUpper

end ReverseMathCalibration

namespace ExactCalibrationTransfer

/-- Definition with formal content given by the displayed type and body.
-/
noncomputable def transferredCalibration
    {src dst : PrincipleProfile}
    (T : ExactCalibrationTransfer src dst) :
    ReverseMathCalibration dst where
  targetProfile := T.sourceCalibration.targetProfile
  upperBound := T.dstUpper
  lowerBound? := some T.dstLower
  targetLeUpper := by
    rw [T.upperMatchesSourceTarget]
    cases T.sourceCalibration.targetProfile.theory <;> decide
  lowerLeTarget := by
    change T.dstLower.theoryProfile.theory ≤ T.sourceCalibration.targetProfile.theory
    rw [T.lowerMatchesSourceTarget]
    cases T.sourceCalibration.targetProfile.theory <;> decide
  status := CalibrationStatus.exact

@[simp] theorem transferredCalibration_status
    {src dst : PrincipleProfile}
    (T : ExactCalibrationTransfer src dst) :
    T.transferredCalibration.status = CalibrationStatus.exact := rfl

@[simp] theorem transferredCalibration_targetProfile
    {src dst : PrincipleProfile}
    (T : ExactCalibrationTransfer src dst) :
    T.transferredCalibration.targetProfile = T.sourceCalibration.targetProfile := rfl

@[simp] theorem transferredCalibration_upperBound
    {src dst : PrincipleProfile}
    (T : ExactCalibrationTransfer src dst) :
    T.transferredCalibration.upperBound = T.dstUpper := rfl

@[simp] theorem transferredCalibration_lowerBound
    {src dst : PrincipleProfile}
    (T : ExactCalibrationTransfer src dst) :
    T.transferredCalibration.lowerBound? = some T.dstLower := rfl

theorem transferredCalibration_supported
    {src dst : PrincipleProfile}
    (T : ExactCalibrationTransfer src dst) :
    T.transferredCalibration.status = CalibrationStatus.exact
      ∧ T.transferredCalibration.upperBound.evidenceStatus = EvidenceStatus.theoremLevel
      ∧ (match T.transferredCalibration.lowerBound? with
          | some lb => lb.evidenceStatus = EvidenceStatus.theoremLevel
          | none => False) := by
  constructor
  · rfl
  constructor
  · simpa using T.upperTheoremLevel
  · simpa using T.lowerTheoremLevel

end ExactCalibrationTransfer

/-! Declarations for the section below. -/

/-- Definition with formal content given by the displayed type and body. -/
def praTheoryProfile : SecondOrderTheoryProfile where
  label := "PRA"
  theory := FormalTheory.PRA

/-- Definition with formal content given by the displayed type and body. -/
def iSigma1TheoryProfile : SecondOrderTheoryProfile where
  label := "IΣ₁"
  theory := FormalTheory.ISigma1
  complexityFloor? := some FormulaClass.pi02

/-- Definition with formal content given by the displayed type and body. -/
def rca0TheoryProfile : SecondOrderTheoryProfile where
  label := "RCA₀"
  theory := FormalTheory.RCA0

/-- Definition with formal content given by the displayed type and body. -/
noncomputable def rca0WoOmega3TheoryProfile : SecondOrderTheoryProfile where
  label := "RCA₀ + WO(ω^3)"
  theory := FormalTheory.RCA0_WO_omega3
  ordinalCeiling? := some omegaPowThree

/-- Definition with formal content given by the displayed type and body. -/
noncomputable def woEpsilon0TheoryProfile : SecondOrderTheoryProfile where
  label := "WO(ε₀)"
  theory := FormalTheory.WO_epsilon0
  ordinalCeiling? := some ε₀

/-- Definition with formal content given by the displayed type and body. -/
def artsGieslPrincipleProfile : PrincipleProfile where
  label := "Arts--Giesl soundness"
  family? := some artsGieslLicenseProfile.family
  complexity? := some artsGieslLicenseProfile.complexity

/-- Definition with formal content given by the displayed type and body.


-/
def sctPrincipleProfile : PrincipleProfile where
  label := "Size-change termination"

/-- Definition with formal content given by the displayed type and body. -/
noncomputable def sctExactUpperBound : ReverseMathUpperBound sctPrincipleProfile where
  theoryProfile := rca0WoOmega3TheoryProfile
  evidenceStatus := EvidenceStatus.theoremLevel
  justificationTag := "sctReverseMathProfile"

/-- Definition with formal content given by the displayed type and body. -/
noncomputable def sctExactLowerBound : ReverseMathLowerBound sctPrincipleProfile where
  theoryProfile := rca0WoOmega3TheoryProfile
  evidenceStatus := EvidenceStatus.theoremLevel
  justificationTag := "sctReverseMathProfile"

/-- Definition with formal content given by the displayed type and body. -/
noncomputable def sctExactCalibration : ReverseMathCalibration sctPrincipleProfile where
  targetProfile := rca0WoOmega3TheoryProfile
  upperBound := sctExactUpperBound
  lowerBound? := some sctExactLowerBound
  targetLeUpper := by
    show FormalTheory.RCA0_WO_omega3 ≤ FormalTheory.RCA0_WO_omega3
    decide
  lowerLeTarget := by
    show FormalTheory.RCA0_WO_omega3 ≤ FormalTheory.RCA0_WO_omega3
    decide
  status := CalibrationStatus.exact

/-- Definition with formal content given by the displayed type and body.


-/
noncomputable def artsGieslCandidateUpperBound :
    ReverseMathUpperBound artsGieslPrincipleProfile where
  theoryProfile := woEpsilon0TheoryProfile
  evidenceStatus := EvidenceStatus.conjectural
  justificationTag := "artsGieslReverseMathCalibration.upperBenchmark"

/-- Definition with formal content given by the displayed type and body.

-/
noncomputable def artsGieslCandidateLowerBound :
    ReverseMathLowerBound artsGieslPrincipleProfile where
  theoryProfile := rca0WoOmega3TheoryProfile
  evidenceStatus := EvidenceStatus.conjectural
  justificationTag := "artsGieslReverseMathCalibration.target"

/-- Definition with formal content given by the displayed type and body. -/
noncomputable def artsGieslConjecturalCalibration :
    ReverseMathCalibration artsGieslPrincipleProfile where
  targetProfile := rca0WoOmega3TheoryProfile
  upperBound := artsGieslCandidateUpperBound
  lowerBound? := some artsGieslCandidateLowerBound
  targetLeUpper := by
    show FormalTheory.RCA0_WO_omega3 ≤ FormalTheory.WO_epsilon0
    decide
  lowerLeTarget := by
    show FormalTheory.RCA0_WO_omega3 ≤ FormalTheory.RCA0_WO_omega3
    decide
  status := CalibrationStatus.conjectural

/-- Field requirements are given by the displayed type. -/
@[simp] theorem sctExactCalibration_status :
    sctExactCalibration.status = CalibrationStatus.exact := rfl

/-- Field requirements are given by the displayed type. -/
@[simp] theorem artsGieslConjecturalCalibration_status :
    artsGieslConjecturalCalibration.status = CalibrationStatus.conjectural := rfl

/-- The displayed proposition follows from the stated hypotheses.
-/
theorem artsGiesl_and_sct_share_framework_target_theory :
    artsGieslConjecturalCalibration.targetProfile.theory =
      sctExactCalibration.targetProfile.theory := by
  simp [artsGieslConjecturalCalibration, sctExactCalibration,
    rca0WoOmega3TheoryProfile]

/-- The displayed proposition follows from the stated hypotheses. -/
theorem artsGiesl_and_sct_share_framework_target_ordinal :
    artsGieslConjecturalCalibration.targetProfile.ordinalCeiling? =
      sctExactCalibration.targetProfile.ordinalCeiling? := by
  rfl

/-- Definition with formal content given by the displayed type and body.
-/
noncomputable def sctIntoEpsilon0Implication :
    TheoryImplication rca0WoOmega3TheoryProfile woEpsilon0TheoryProfile where
  carries := by decide

/-- The displayed proposition follows from the stated hypotheses.
-/
theorem artsGiesl_framework_target_below_benchmark :
    artsGieslConjecturalCalibration.targetProfile.theory ≤
      artsGieslConjecturalCalibration.upperBound.theoryProfile.theory := by
  show FormalTheory.RCA0_WO_omega3 ≤ FormalTheory.WO_epsilon0
  decide

/-! Declarations for the section below.






-/

/-- Definition with formal content given by the displayed type and body. -/
def ReverseMathUpperBound.eraseJustificationTag {P : PrincipleProfile}
    (U : ReverseMathUpperBound P) : ReverseMathUpperBound P where
  theoryProfile := U.theoryProfile
  evidenceStatus := U.evidenceStatus
  justificationTag := ""

/-- Definition with formal content given by the displayed type and body. -/
def ReverseMathLowerBound.eraseJustificationTag {P : PrincipleProfile}
    (L : ReverseMathLowerBound P) : ReverseMathLowerBound P where
  theoryProfile := L.theoryProfile
  evidenceStatus := L.evidenceStatus
  justificationTag := ""

@[simp] theorem ReverseMathUpperBound.eraseJustificationTag_theoryProfile
    {P : PrincipleProfile} (U : ReverseMathUpperBound P) :
    U.eraseJustificationTag.theoryProfile = U.theoryProfile := rfl

@[simp] theorem ReverseMathUpperBound.eraseJustificationTag_evidenceStatus
    {P : PrincipleProfile} (U : ReverseMathUpperBound P) :
    U.eraseJustificationTag.evidenceStatus = U.evidenceStatus := rfl

@[simp] theorem ReverseMathUpperBound.eraseJustificationTag_tag
    {P : PrincipleProfile} (U : ReverseMathUpperBound P) :
    U.eraseJustificationTag.justificationTag = "" := rfl

@[simp] theorem ReverseMathLowerBound.eraseJustificationTag_theoryProfile
    {P : PrincipleProfile} (L : ReverseMathLowerBound P) :
    L.eraseJustificationTag.theoryProfile = L.theoryProfile := rfl

@[simp] theorem ReverseMathLowerBound.eraseJustificationTag_evidenceStatus
    {P : PrincipleProfile} (L : ReverseMathLowerBound P) :
    L.eraseJustificationTag.evidenceStatus = L.evidenceStatus := rfl

@[simp] theorem ReverseMathLowerBound.eraseJustificationTag_tag
    {P : PrincipleProfile} (L : ReverseMathLowerBound P) :
    L.eraseJustificationTag.justificationTag = "" := rfl

/-- The displayed proposition follows from the stated hypotheses.
-/
theorem ReverseMathUpperBound.eraseJustificationTag_congr
    {P : PrincipleProfile} {U V : ReverseMathUpperBound P}
    (hTheory : U.theoryProfile = V.theoryProfile)
    (hStatus : U.evidenceStatus = V.evidenceStatus) :
    U.eraseJustificationTag = V.eraseJustificationTag := by
  cases U
  cases V
  simp only [ReverseMathUpperBound.eraseJustificationTag]
  congr 1

/-- The displayed proposition follows from the stated hypotheses.
-/
theorem ReverseMathLowerBound.eraseJustificationTag_congr
    {P : PrincipleProfile} {L M : ReverseMathLowerBound P}
    (hTheory : L.theoryProfile = M.theoryProfile)
    (hStatus : L.evidenceStatus = M.evidenceStatus) :
    L.eraseJustificationTag = M.eraseJustificationTag := by
  cases L
  cases M
  simp only [ReverseMathLowerBound.eraseJustificationTag]
  congr 1

/-- Definition with formal content given by the displayed type and body.

-/
noncomputable def ReverseMathCalibration.eraseJustificationTags {P : PrincipleProfile}
    (C : ReverseMathCalibration P) : ReverseMathCalibration P where
  targetProfile := C.targetProfile
  upperBound := C.upperBound.eraseJustificationTag
  lowerBound? := C.lowerBound?.map ReverseMathLowerBound.eraseJustificationTag
  targetLeUpper := by
    change C.targetProfile.theory ≤ C.upperBound.theoryProfile.theory
    exact C.targetLeUpper
  lowerLeTarget := by
    cases hLB : C.lowerBound? with
    | none => exact True.intro
    | some lb =>
      change lb.theoryProfile.theory ≤ C.targetProfile.theory
      have hC := C.lowerLeTarget
      rw [hLB] at hC
      exact hC
  status := C.status

@[simp] theorem ReverseMathCalibration.eraseJustificationTags_status
    {P : PrincipleProfile} (C : ReverseMathCalibration P) :
    C.eraseJustificationTags.status = C.status := rfl

@[simp] theorem ReverseMathCalibration.eraseJustificationTags_targetProfile
    {P : PrincipleProfile} (C : ReverseMathCalibration P) :
    C.eraseJustificationTags.targetProfile = C.targetProfile := rfl

@[simp] theorem ReverseMathCalibration.eraseJustificationTags_upperBound
    {P : PrincipleProfile} (C : ReverseMathCalibration P) :
    C.eraseJustificationTags.upperBound = C.upperBound.eraseJustificationTag := rfl

@[simp] theorem ReverseMathCalibration.eraseJustificationTags_lowerBound
    {P : PrincipleProfile} (C : ReverseMathCalibration P) :
    C.eraseJustificationTags.lowerBound? =
      C.lowerBound?.map ReverseMathLowerBound.eraseJustificationTag := rfl

/-! Declarations for the section below.











-/

/-- Definition with formal content given by the displayed type and body.

-/
def SecondOrderTheoryProfile.erasePresentationMetadata
    (p : SecondOrderTheoryProfile) : SecondOrderTheoryProfile where
  label := ""
  theory := p.theory
  ordinalCeiling? := p.ordinalCeiling?
  complexityFloor? := none

@[simp] theorem SecondOrderTheoryProfile.erasePresentationMetadata_label
    (p : SecondOrderTheoryProfile) :
    p.erasePresentationMetadata.label = "" := rfl

@[simp] theorem SecondOrderTheoryProfile.erasePresentationMetadata_theory
    (p : SecondOrderTheoryProfile) :
    p.erasePresentationMetadata.theory = p.theory := rfl

@[simp] theorem SecondOrderTheoryProfile.erasePresentationMetadata_ordinal
    (p : SecondOrderTheoryProfile) :
    p.erasePresentationMetadata.ordinalCeiling? = p.ordinalCeiling? := rfl

@[simp] theorem SecondOrderTheoryProfile.erasePresentationMetadata_complexity
    (p : SecondOrderTheoryProfile) :
    p.erasePresentationMetadata.complexityFloor? = none := rfl

/-- The displayed proposition follows from the stated hypotheses.
-/
theorem SecondOrderTheoryProfile.erasePresentationMetadata_congr
    {p q : SecondOrderTheoryProfile}
    (hTheory : p.theory = q.theory)
    (hOrdinal : p.ordinalCeiling? = q.ordinalCeiling?) :
    p.erasePresentationMetadata = q.erasePresentationMetadata := by
  unfold SecondOrderTheoryProfile.erasePresentationMetadata
  congr 1

/-- Definition with formal content given by the displayed type and body.


-/
def ReverseMathUpperBound.erasePresentationMetadata
    {P : PrincipleProfile} (U : ReverseMathUpperBound P) :
    ReverseMathUpperBound P where
  theoryProfile := U.theoryProfile.erasePresentationMetadata
  evidenceStatus := U.evidenceStatus
  justificationTag := ""

/-- Definition with formal content given by the displayed type and body. -/
def ReverseMathLowerBound.erasePresentationMetadata
    {P : PrincipleProfile} (L : ReverseMathLowerBound P) :
    ReverseMathLowerBound P where
  theoryProfile := L.theoryProfile.erasePresentationMetadata
  evidenceStatus := L.evidenceStatus
  justificationTag := ""

@[simp] theorem ReverseMathUpperBound.erasePresentationMetadata_theoryProfile
    {P : PrincipleProfile} (U : ReverseMathUpperBound P) :
    U.erasePresentationMetadata.theoryProfile =
      U.theoryProfile.erasePresentationMetadata := rfl

@[simp] theorem ReverseMathUpperBound.erasePresentationMetadata_evidenceStatus
    {P : PrincipleProfile} (U : ReverseMathUpperBound P) :
    U.erasePresentationMetadata.evidenceStatus = U.evidenceStatus := rfl

@[simp] theorem ReverseMathUpperBound.erasePresentationMetadata_tag
    {P : PrincipleProfile} (U : ReverseMathUpperBound P) :
    U.erasePresentationMetadata.justificationTag = "" := rfl

@[simp] theorem ReverseMathLowerBound.erasePresentationMetadata_theoryProfile
    {P : PrincipleProfile} (L : ReverseMathLowerBound P) :
    L.erasePresentationMetadata.theoryProfile =
      L.theoryProfile.erasePresentationMetadata := rfl

@[simp] theorem ReverseMathLowerBound.erasePresentationMetadata_evidenceStatus
    {P : PrincipleProfile} (L : ReverseMathLowerBound P) :
    L.erasePresentationMetadata.evidenceStatus = L.evidenceStatus := rfl

@[simp] theorem ReverseMathLowerBound.erasePresentationMetadata_tag
    {P : PrincipleProfile} (L : ReverseMathLowerBound P) :
    L.erasePresentationMetadata.justificationTag = "" := rfl

/-- The displayed proposition follows from the stated hypotheses.
-/
theorem ReverseMathUpperBound.erasePresentationMetadata_congr
    {P : PrincipleProfile} {U V : ReverseMathUpperBound P}
    (hTheory : U.theoryProfile.theory = V.theoryProfile.theory)
    (hOrdinal : U.theoryProfile.ordinalCeiling? = V.theoryProfile.ordinalCeiling?)
    (hStatus : U.evidenceStatus = V.evidenceStatus) :
    U.erasePresentationMetadata = V.erasePresentationMetadata := by
  unfold ReverseMathUpperBound.erasePresentationMetadata
  congr 1
  exact SecondOrderTheoryProfile.erasePresentationMetadata_congr hTheory hOrdinal

/-- The displayed proposition follows from the stated hypotheses.
-/
theorem ReverseMathLowerBound.erasePresentationMetadata_congr
    {P : PrincipleProfile} {L M : ReverseMathLowerBound P}
    (hTheory : L.theoryProfile.theory = M.theoryProfile.theory)
    (hOrdinal : L.theoryProfile.ordinalCeiling? = M.theoryProfile.ordinalCeiling?)
    (hStatus : L.evidenceStatus = M.evidenceStatus) :
    L.erasePresentationMetadata = M.erasePresentationMetadata := by
  unfold ReverseMathLowerBound.erasePresentationMetadata
  congr 1
  exact SecondOrderTheoryProfile.erasePresentationMetadata_congr hTheory hOrdinal

end OperatorKO7.ReverseMathFramework
