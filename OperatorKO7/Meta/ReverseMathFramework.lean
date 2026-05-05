import OperatorKO7.Meta.ReverseMathSupport

/-!
# Reverse-Mathematical Calibration Framework

Shared abstraction layer for the broader reverse-mathematical expansion
program in Paper 2.

This file does **not** prove a new calibration theorem by itself. Instead it
provides the reusable objects needed to express:

- theory profiles;
- principle profiles;
- implication / conservativity / equivalence relations between theory profiles;
- upper-bound / lower-bound / calibration records with explicit evidence
  status;
- concrete framework-level instances for SCT and the Arts--Giesl license.

The key design constraint is honesty: the framework must distinguish
theorem-level results from profile-level support and from conjectural
candidate calibrations.
-/

namespace OperatorKO7.ReverseMathFramework

open Ordinal
open OperatorKO7.ProofTheoreticRegister
open OperatorKO7.ReverseMathSupport

/-- Evidence status attached to a calibration claim. -/
inductive EvidenceStatus
  | theoremLevel
  | profileLevel
  | conjectural
  deriving DecidableEq, Repr

/-- Coarse second-order theory profile used by the reverse-mathematical layer.

`ordinalCeiling?` is optional because not every paper-facing theory datum in
this repository is currently tied to an exact ordinal assignment.
-/
structure SecondOrderTheoryProfile where
  label : String
  theory : FormalTheory
  ordinalCeiling? : Option Ordinal := none
  complexityFloor? : Option FormulaClass := none

/-- Abstract proof-principle profile. This stays intentionally lightweight:
it records only the paper-facing identity, family, and complexity tags that
are already part of the mechanized register.
-/
structure PrincipleProfile where
  label : String
  family? : Option AscentFamily := none
  complexity? : Option FormulaClass := none

/-- A coarse implication witness between theory profiles: the source theory is
no stronger than the target theory on the existing formal-theory register.
-/
structure TheoryImplication (src dst : SecondOrderTheoryProfile) where
  carries : src.theory ≤ dst.theory

/-- A coarse conservativity witness between theory profiles. At the current
artifact level this means:

- the source theory embeds into the target theory on the paper's register; and
- no new ordinal ceiling is claimed beyond the one already attached to the
  source profile.
-/
structure TheoryConservativity (src dst : SecondOrderTheoryProfile) where
  extensionLe : src.theory ≤ dst.theory
  preservesOrdinalCeiling :
    match src.ordinalCeiling?, dst.ordinalCeiling? with
    | some α, some β => α = β
    | _, _ => True

/-- Bidirectional coarse equivalence between theory profiles. -/
structure TheoryEquivalence (left right : SecondOrderTheoryProfile) where
  forward : TheoryImplication left right
  backward : TheoryImplication right left

/-- A reverse-mathematical upper bound for a principle profile. The evidence
status makes explicit whether the bound is theorem-level, profile-level, or
still conjectural.
-/
structure ReverseMathUpperBound (P : PrincipleProfile) where
  theoryProfile : SecondOrderTheoryProfile
  evidenceStatus : EvidenceStatus
  justificationTag : String

/-- Lower-bound companion to `ReverseMathUpperBound`. -/
structure ReverseMathLowerBound (P : PrincipleProfile) where
  theoryProfile : SecondOrderTheoryProfile
  evidenceStatus : EvidenceStatus
  justificationTag : String

/-- General calibration package. This is the reusable object the roadmap was
calling for: it allows exact, profile-level, and conjectural calibrations to
be represented without pretending they are all theorem-level closures.
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

/-- Witness-bearing exact-calibration transport between proof principles.

This is intentionally stronger than a shared-target or status-only note: it
packages

- a source exact calibration,
- an explicit witness-preserving constant-overhead transport, and
- theorem-level destination upper/lower packages whose theory profiles match
  the source target exactly.

Within the coarse reverse-mathematical framework used by this repository, such
an object is enough to transfer exact calibration from the source principle to
the destination principle without appealing to external prose. -/
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

/-- Every calibration package already contains an upper bound by construction. -/
theorem has_upperBound {P : PrincipleProfile} (C : ReverseMathCalibration P) :
    C.targetProfile.theory ≤ C.upperBound.theoryProfile.theory :=
  C.targetLeUpper

end ReverseMathCalibration

namespace ExactCalibrationTransfer

/-- Assemble an exact destination calibration from a witness-bearing exact
transport object. -/
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

/-! ## Concrete framework-level profiles already supported by the artifact -/

/-- Base theory profile for `PRA`. -/
def praTheoryProfile : SecondOrderTheoryProfile where
  label := "PRA"
  theory := FormalTheory.PRA

/-- Base theory profile for `IΣ₁`. -/
def iSigma1TheoryProfile : SecondOrderTheoryProfile where
  label := "IΣ₁"
  theory := FormalTheory.ISigma1
  complexityFloor? := some FormulaClass.pi02

/-- Base theory profile for `RCA₀`. -/
def rca0TheoryProfile : SecondOrderTheoryProfile where
  label := "RCA₀"
  theory := FormalTheory.RCA0

/-- Base theory profile for `RCA₀ + WO(ω^3)`. -/
noncomputable def rca0WoOmega3TheoryProfile : SecondOrderTheoryProfile where
  label := "RCA₀ + WO(ω^3)"
  theory := FormalTheory.RCA0_WO_omega3
  ordinalCeiling? := some omegaPowThree

/-- Base theory profile for the current `ε₀` benchmark. -/
noncomputable def woEpsilon0TheoryProfile : SecondOrderTheoryProfile where
  label := "WO(ε₀)"
  theory := FormalTheory.WO_epsilon0
  ordinalCeiling? := some ε₀

/-- Principle profile for the Arts--Giesl soundness license. -/
def artsGieslPrincipleProfile : PrincipleProfile where
  label := "Arts--Giesl soundness"
  family? := some artsGieslLicenseProfile.family
  complexity? := some artsGieslLicenseProfile.complexity

/-- Principle profile for SCT as the adjacent exact calibration point used in
the paper. The family and formula-class tags are intentionally left absent
because they are not currently proved in this repository.
-/
def sctPrincipleProfile : PrincipleProfile where
  label := "Size-change termination"

/-- Theorem-level exact upper bound for SCT. -/
noncomputable def sctExactUpperBound : ReverseMathUpperBound sctPrincipleProfile where
  theoryProfile := rca0WoOmega3TheoryProfile
  evidenceStatus := EvidenceStatus.theoremLevel
  justificationTag := "sctReverseMathProfile"

/-- Theorem-level exact lower bound for SCT. -/
noncomputable def sctExactLowerBound : ReverseMathLowerBound sctPrincipleProfile where
  theoryProfile := rca0WoOmega3TheoryProfile
  evidenceStatus := EvidenceStatus.theoremLevel
  justificationTag := "sctReverseMathProfile"

/-- Exact SCT calibration package. -/
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

/-- Candidate upper bound package for the Arts--Giesl target. This is
intentionally marked conjectural: the framework distinguishes the current
support profile from a proved semantic upper-bound theorem.
-/
noncomputable def artsGieslCandidateUpperBound :
    ReverseMathUpperBound artsGieslPrincipleProfile where
  theoryProfile := woEpsilon0TheoryProfile
  evidenceStatus := EvidenceStatus.conjectural
  justificationTag := "artsGieslReverseMathCalibration.upperBenchmark"

/-- Candidate lower bound package for the Arts--Giesl target. This matches the
paper's current target object rather than a proved theorem.
-/
noncomputable def artsGieslCandidateLowerBound :
    ReverseMathLowerBound artsGieslPrincipleProfile where
  theoryProfile := rca0WoOmega3TheoryProfile
  evidenceStatus := EvidenceStatus.conjectural
  justificationTag := "artsGieslReverseMathCalibration.target"

/-- Conjectural Arts--Giesl calibration package in framework form. -/
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

/-- The framework-level SCT calibration is exact. -/
@[simp] theorem sctExactCalibration_status :
    sctExactCalibration.status = CalibrationStatus.exact := rfl

/-- The framework-level AG calibration remains conjectural. -/
@[simp] theorem artsGieslConjecturalCalibration_status :
    artsGieslConjecturalCalibration.status = CalibrationStatus.conjectural := rfl

/-- The AG target theory matches the SCT exact target at the current framework
level. -/
theorem artsGiesl_and_sct_share_framework_target_theory :
    artsGieslConjecturalCalibration.targetProfile.theory =
      sctExactCalibration.targetProfile.theory := by
  simp [artsGieslConjecturalCalibration, sctExactCalibration,
    rca0WoOmega3TheoryProfile]

/-- The AG and SCT framework profiles share the same explicit ordinal target. -/
theorem artsGiesl_and_sct_share_framework_target_ordinal :
    artsGieslConjecturalCalibration.targetProfile.ordinalCeiling? =
      sctExactCalibration.targetProfile.ordinalCeiling? := by
  rfl

/-- The theorem-level SCT exact calibration sits below the current `ε₀`
benchmark profile on the coarse theory register. -/
noncomputable def sctIntoEpsilon0Implication :
    TheoryImplication rca0WoOmega3TheoryProfile woEpsilon0TheoryProfile where
  carries := by decide

/-- The conjectural Arts--Giesl target sits below its current benchmark on the
coarse theory register. -/
theorem artsGiesl_framework_target_below_benchmark :
    artsGieslConjecturalCalibration.targetProfile.theory ≤
      artsGieslConjecturalCalibration.upperBound.theoryProfile.theory := by
  show FormalTheory.RCA0_WO_omega3 ≤ FormalTheory.WO_epsilon0
  decide

/-! ## Tag-insensitive erasure layer

Calibration packages carry a free-form `justificationTag : String` on
both upper and lower bounds. Two calibrations can describe exactly the
same mathematical content (same theory profile, same evidence status,
same status) while disagreeing on their tag strings. The helpers below
erase the tag strings, giving a canonical tag-insensitive representative
that ignores the prose-level justification text. -/

/-- Erase the free-form justification tag from an upper-bound package. -/
def ReverseMathUpperBound.eraseJustificationTag {P : PrincipleProfile}
    (U : ReverseMathUpperBound P) : ReverseMathUpperBound P where
  theoryProfile := U.theoryProfile
  evidenceStatus := U.evidenceStatus
  justificationTag := ""

/-- Erase the free-form justification tag from a lower-bound package. -/
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

/-- Two upper-bound packages with the same theory profile and evidence
status agree after tag erasure. -/
theorem ReverseMathUpperBound.eraseJustificationTag_congr
    {P : PrincipleProfile} {U V : ReverseMathUpperBound P}
    (hTheory : U.theoryProfile = V.theoryProfile)
    (hStatus : U.evidenceStatus = V.evidenceStatus) :
    U.eraseJustificationTag = V.eraseJustificationTag := by
  cases U
  cases V
  simp only [ReverseMathUpperBound.eraseJustificationTag]
  congr 1

/-- Two lower-bound packages with the same theory profile and evidence
status agree after tag erasure. -/
theorem ReverseMathLowerBound.eraseJustificationTag_congr
    {P : PrincipleProfile} {L M : ReverseMathLowerBound P}
    (hTheory : L.theoryProfile = M.theoryProfile)
    (hStatus : L.evidenceStatus = M.evidenceStatus) :
    L.eraseJustificationTag = M.eraseJustificationTag := by
  cases L
  cases M
  simp only [ReverseMathLowerBound.eraseJustificationTag]
  congr 1

/-- Erase both upper and lower justification tags from a calibration
package. Preserves theory profile, target profile, evidence statuses,
and calibration status. -/
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

/-! ## Semantic / presentation erasure for theory profiles

The `SecondOrderTheoryProfile` record carries two genuinely load-bearing
fields (`theory`, `ordinalCeiling?`) and two presentation-level fields
(`label`, `complexityFloor?`) that are not required for theory-target
comparison at the reverse-math level. `erasePresentationMetadata`
zeroes out the presentation fields, leaving a "semantic core" containing
only the theory and ordinal ceiling. The lifted helpers on
`ReverseMathUpperBound` / `ReverseMathLowerBound` also zero the
`justificationTag` string, giving a combined presentation + tag erasure
that is the right equivalence for comparing two route constructions
whose source-calibration target profiles agree only on theory and
ordinal ceiling (not on label or complexity floor). -/

/-- Erase presentation-only metadata from a theory profile. The `label`
and `complexityFloor?` fields are collapsed to their default/empty
values; `theory` and `ordinalCeiling?` are preserved. -/
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

/-- Two theory profiles agree after presentation-metadata erasure iff
their `theory` and `ordinalCeiling?` fields agree. -/
theorem SecondOrderTheoryProfile.erasePresentationMetadata_congr
    {p q : SecondOrderTheoryProfile}
    (hTheory : p.theory = q.theory)
    (hOrdinal : p.ordinalCeiling? = q.ordinalCeiling?) :
    p.erasePresentationMetadata = q.erasePresentationMetadata := by
  unfold SecondOrderTheoryProfile.erasePresentationMetadata
  congr 1

/-- Erase both presentation-level theory-profile metadata and the
free-form justification tag from an upper-bound package. This is the
combined comparison normal form for route-unification theorems that
only require theory / ordinal / evidence-status agreement. -/
def ReverseMathUpperBound.erasePresentationMetadata
    {P : PrincipleProfile} (U : ReverseMathUpperBound P) :
    ReverseMathUpperBound P where
  theoryProfile := U.theoryProfile.erasePresentationMetadata
  evidenceStatus := U.evidenceStatus
  justificationTag := ""

/-- Lower-bound companion of `ReverseMathUpperBound.erasePresentationMetadata`. -/
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

/-- Two upper-bound packages agree after presentation + tag erasure iff
their `theory`, `ordinalCeiling?`, and `evidenceStatus` fields agree. -/
theorem ReverseMathUpperBound.erasePresentationMetadata_congr
    {P : PrincipleProfile} {U V : ReverseMathUpperBound P}
    (hTheory : U.theoryProfile.theory = V.theoryProfile.theory)
    (hOrdinal : U.theoryProfile.ordinalCeiling? = V.theoryProfile.ordinalCeiling?)
    (hStatus : U.evidenceStatus = V.evidenceStatus) :
    U.erasePresentationMetadata = V.erasePresentationMetadata := by
  unfold ReverseMathUpperBound.erasePresentationMetadata
  congr 1
  exact SecondOrderTheoryProfile.erasePresentationMetadata_congr hTheory hOrdinal

/-- Two lower-bound packages agree after presentation + tag erasure iff
their `theory`, `ordinalCeiling?`, and `evidenceStatus` fields agree. -/
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
