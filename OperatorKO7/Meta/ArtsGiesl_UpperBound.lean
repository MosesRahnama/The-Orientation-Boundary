import OperatorKO7.Meta.ReverseMathFramework
import OperatorKO7.Meta.TerminationPrincipleRegister
import OperatorKO7.Meta.ReverseMathOmega3WellOrdering

/-!
# Arts-Giesl Upper-Bound Packages

This module separates three formal layers:

- finite-register comparisons between the `RCA0_WO_omega3` and `WO_epsilon0`
  theory profiles;
- genuine Lean backing for the well-ordering of `omega^3`;
- constructors that turn an explicitly supplied alignment or exact-calibration
  transfer into an Arts-Giesl upper-bound package.

The theory and evidence-status fields are metadata. No theorem in this module
derives the Arts-Giesl principle from `RCA0 + WO(omega^3)` or proves the reverse
reduction. Such a semantic calibration requires an explicit transport theorem.
-/

namespace OperatorKO7.ArtsGieslUpperBound

open Ordinal
open OperatorKO7.ProofTheoreticRegister
open OperatorKO7.ReverseMathSupport
open OperatorKO7.ReverseMathFramework
open OperatorKO7.TerminationPrincipleRegister

/-- Broad registry package placing the Arts-Giesl profile under the
`WO(epsilon0)` benchmark. The evidence-status field is a recorded tag; the
package does not itself prove a reduction of principles. -/
noncomputable def artsGieslTheoremUpperBound : ReverseMathUpperBound artsGieslPrincipleProfile where
  theoryProfile := woEpsilon0TheoryProfile
  evidenceStatus := EvidenceStatus.theoremLevel
  justificationTag := "target sits below existing epsilon0 benchmark"

@[simp] theorem artsGieslTheoremUpperBound_status :
    artsGieslTheoremUpperBound.evidenceStatus = EvidenceStatus.theoremLevel := rfl

@[simp] theorem artsGieslTheoremUpperBound_theory :
    artsGieslTheoremUpperBound.theoryProfile.theory = FormalTheory.WO_epsilon0 := rfl

@[simp] theorem artsGieslTheoremUpperBound_ordinal :
    artsGieslTheoremUpperBound.theoryProfile.ordinalCeiling? = some ε₀ := rfl

/-- The finite theory register orders `RCA0_WO_omega3` below `WO_epsilon0`. -/
theorem artsGiesl_targetTheory_le_theoremUpperBound :
    rca0WoOmega3TheoryProfile.theory ≤ artsGieslTheoremUpperBound.theoryProfile.theory := by
  decide

/-- The ordinal target `omega^3` is strictly below `epsilon0`. -/
theorem artsGiesl_targetOrdinal_lt_theoremUpperBound :
    omegaPowThree < ε₀ :=
  omegaPowThree_lt_epsilon0

/-- The Arts-Giesl registry entry names the `RCA0_WO_omega3` target profile. -/
theorem artsGiesl_registry_target_agrees_with_upperBound_target :
    artsGieslEntry.targetTheory? = some rca0WoOmega3TheoryProfile.theory := by
  simp [artsGieslEntry, rca0WoOmega3TheoryProfile]

/-- The registered recursor transformation adds its fixed overhead to the
input cost. -/
theorem artsGiesl_recursor_constant_overhead (n : Nat) :
    agRecursorTransformation.transformedCost n = n + agRecursorTransformation.overhead :=
  agRecursorTransformation_preserves_linear_growth n

/-- Summary of the broad package: theorem-level status, theory-register
inclusion, and the strict ordinal inequality. -/
theorem artsGieslTheoremUpperBound_supported :
    artsGieslTheoremUpperBound.evidenceStatus = EvidenceStatus.theoremLevel
      ∧ rca0WoOmega3TheoryProfile.theory ≤ artsGieslTheoremUpperBound.theoryProfile.theory
      ∧ omegaPowThree < ε₀ := by
  constructor
  · rfl
  constructor
  · exact artsGiesl_targetTheory_le_theoremUpperBound
  · exact artsGiesl_targetOrdinal_lt_theoremUpperBound

/-- The broad package's `WO_epsilon0` theory field is not the exact
`RCA0_WO_omega3` target. -/
theorem artsGieslTheoremUpperBound_theory_ne_target :
    artsGieslTheoremUpperBound.theoryProfile.theory ≠ FormalTheory.RCA0_WO_omega3 := by
  simp [artsGieslTheoremUpperBound, woEpsilon0TheoryProfile]

/-- The broad package's `epsilon0` ordinal ceiling is not `omega^3`. -/
theorem artsGieslTheoremUpperBound_ordinal_ne_target :
    artsGieslTheoremUpperBound.theoryProfile.ordinalCeiling? ≠ some omegaPowThree := by
  intro h
  have h' : ε₀ = omegaPowThree := by
    simpa [artsGieslTheoremUpperBound, woEpsilon0TheoryProfile] using h
  exact omegaPowThree_lt_epsilon0.ne h'.symm

/-- Exact-target upper-bound package. Besides exact theory, ordinal, and status
fields, an inhabitant carries the Lean theorem backing `WO(omega^3)`. The
package still does not supply a semantic Arts-Giesl reduction. -/
structure ArtsGieslSharpTheoremUpperBound where
  bound : ReverseMathUpperBound artsGieslPrincipleProfile
  theoryEq : bound.theoryProfile.theory = FormalTheory.RCA0_WO_omega3
  ordinalEq :
    bound.theoryProfile.ordinalCeiling? =
      some OperatorKO7.ReverseMathSupport.omegaPowThree
  theoremLevel : bound.evidenceStatus = EvidenceStatus.theoremLevel
  /-- Genuine well-ordering backing for the `omega^3` ordinal field. -/
  omega3Backing : OperatorKO7.ReverseMathOmega3.WOOmega3Backing :=
    OperatorKO7.ReverseMathOmega3.wo_omega3_backing

/-- Project the exact theory, ordinal, and theorem-status fields from a sharp
package. -/
theorem ArtsGieslSharpTheoremUpperBound.supported
    (U : ArtsGieslSharpTheoremUpperBound) :
    U.bound.theoryProfile.theory = FormalTheory.RCA0_WO_omega3
      ∧ U.bound.theoryProfile.ordinalCeiling? =
          some OperatorKO7.ReverseMathSupport.omegaPowThree
      ∧ U.bound.evidenceStatus = EvidenceStatus.theoremLevel := by
  exact ⟨U.theoryEq, U.ordinalEq, U.theoremLevel⟩

/-- Project the genuine `WO(omega^3)` backing carried by a sharp package. -/
theorem ArtsGieslSharpTheoremUpperBound.carries_genuine_wo_omega3
    (U : ArtsGieslSharpTheoremUpperBound) :
    OperatorKO7.ReverseMathOmega3.WOOmega3Backing :=
  U.omega3Backing

/-- The broad `WO(epsilon0)` package cannot be equal to an exact-target sharp
package because their theory fields differ. -/
theorem artsGieslTheoremUpperBound_not_sharp :
    ¬ ∃ U : ArtsGieslSharpTheoremUpperBound, U.bound = artsGieslTheoremUpperBound := by
  rintro ⟨U, hU⟩
  have hTheory := U.theoryEq
  rw [hU] at hTheory
  simp [artsGieslTheoremUpperBound, woEpsilon0TheoryProfile] at hTheory

/-- Exact data describing the gap between a registered upper package and a
target profile. -/
structure ArtsGieslTheoremUpperBoundGap where
  current : ReverseMathUpperBound artsGieslPrincipleProfile
  target : SecondOrderTheoryProfile
  targetLeCurrent : target.theory ≤ current.theoryProfile.theory
  theoryNeTarget : current.theoryProfile.theory ≠ target.theory
  ordinalNeTarget : current.theoryProfile.ordinalCeiling? ≠ target.ordinalCeiling?

/-- Gap witness from the broad `WO(epsilon0)` package to the
`RCA0_WO_omega3` target. -/
noncomputable def artsGieslCurrentTheoremUpperBoundGap : ArtsGieslTheoremUpperBoundGap where
  current := artsGieslTheoremUpperBound
  target := rca0WoOmega3TheoryProfile
  targetLeCurrent := artsGiesl_targetTheory_le_theoremUpperBound
  theoryNeTarget := artsGieslTheoremUpperBound_theory_ne_target
  ordinalNeTarget := artsGieslTheoremUpperBound_ordinal_ne_target

/-- Project the status, register inclusion, and two unequal target fields from
the broad-package gap witness. -/
theorem artsGieslCurrentTheoremUpperBoundGap_supported :
    artsGieslCurrentTheoremUpperBoundGap.current.evidenceStatus = EvidenceStatus.theoremLevel
      ∧ artsGieslCurrentTheoremUpperBoundGap.target.theory ≤
          artsGieslCurrentTheoremUpperBoundGap.current.theoryProfile.theory
      ∧ artsGieslCurrentTheoremUpperBoundGap.current.theoryProfile.theory ≠
          artsGieslCurrentTheoremUpperBoundGap.target.theory
      ∧ artsGieslCurrentTheoremUpperBoundGap.current.theoryProfile.ordinalCeiling? ≠
          artsGieslCurrentTheoremUpperBoundGap.target.ordinalCeiling? := by
  constructor
  · rfl
  constructor
  · exact artsGieslCurrentTheoremUpperBoundGap.targetLeCurrent
  constructor
  · exact artsGieslCurrentTheoremUpperBoundGap.theoryNeTarget
  · exact artsGieslCurrentTheoremUpperBoundGap.ordinalNeTarget

/-- Conditional Arts-Giesl upper package whose theory and ordinal fields agree
with the exact SCT calibration and whose evidence status is theorem-level. -/
structure ArtsGieslSctSharpUpperTransfer where
  bound : ReverseMathUpperBound artsGieslPrincipleProfile
  theoryEqSct :
    bound.theoryProfile.theory = sctExactCalibration.targetProfile.theory
  ordinalEqSct :
    bound.theoryProfile.ordinalCeiling? = sctExactCalibration.targetProfile.ordinalCeiling?
  theoremLevel : bound.evidenceStatus = EvidenceStatus.theoremLevel

/-- Convert an SCT-aligned conditional transfer into the exact-target sharp
package. -/
noncomputable def ArtsGieslSctSharpUpperTransfer.toSharpTheoremUpperBound
    (T : ArtsGieslSctSharpUpperTransfer) :
    ArtsGieslSharpTheoremUpperBound where
  bound := T.bound
  theoryEq := by simpa using T.theoryEqSct
  ordinalEq := by simpa using T.ordinalEqSct
  theoremLevel := T.theoremLevel

/-- Project the exact target fields supplied by an SCT-aligned transfer. -/
theorem ArtsGieslSctSharpUpperTransfer.supported
    (T : ArtsGieslSctSharpUpperTransfer) :
    T.bound.theoryProfile.theory = FormalTheory.RCA0_WO_omega3
      ∧ T.bound.theoryProfile.ordinalCeiling? =
          some OperatorKO7.ReverseMathSupport.omegaPowThree
      ∧ T.bound.evidenceStatus = EvidenceStatus.theoremLevel := by
  exact T.toSharpTheoremUpperBound.supported

/-- A supplied SCT-aligned transfer yields a sharp upper-bound package with
the same bound. -/
theorem artsGiesl_sharpUpperBound_exists_if_sctTransfer
    (T : ArtsGieslSctSharpUpperTransfer) :
    ∃ U : ArtsGieslSharpTheoremUpperBound, U.bound = T.bound := by
  exact ⟨T.toSharpTheoremUpperBound, rfl⟩

/-- Build the SCT-aligned transfer from a supplied theorem-alignment record.
The evidence status is copied from that record, and its `theoremLevel` field
establishes the required status equality. -/
noncomputable def ArtsGieslSctSharpUpperTransfer.ofTheoremAlignment
    (A : ArtsGieslSctTheoremAlignment) :
    ArtsGieslSctSharpUpperTransfer where
  bound := {
    theoryProfile := sctExactUpperBound.theoryProfile
    evidenceStatus := A.evidenceStatus
    justificationTag := "theorem-level AG/SCT exact-target upper transfer"
  }
  theoryEqSct := by rfl
  ordinalEqSct := by rfl
  theoremLevel := A.theoremLevel

/-- A supplied theorem-alignment record yields a sharp package through the
SCT-aligned transfer. -/
theorem artsGiesl_sharpUpperBound_exists_if_theoremAlignment
    (A : ArtsGieslSctTheoremAlignment) :
    ∃ U : ArtsGieslSharpTheoremUpperBound,
      U.bound = (ArtsGieslSctSharpUpperTransfer.ofTheoremAlignment A).bound := by
  exact artsGiesl_sharpUpperBound_exists_if_sctTransfer
    (ArtsGieslSctSharpUpperTransfer.ofTheoremAlignment A)

/-- Build a sharp package from an exact-calibration transfer whose source
target has the required theory and ordinal fields. -/
noncomputable def ArtsGieslSharpTheoremUpperBound.ofExactCalibrationTransfer
    (T : ExactCalibrationTransfer sctPrincipleProfile artsGieslPrincipleProfile)
    (hTheory : T.sourceCalibration.targetProfile.theory = FormalTheory.RCA0_WO_omega3)
    (hOrdinal :
      T.sourceCalibration.targetProfile.ordinalCeiling? =
        some OperatorKO7.ReverseMathSupport.omegaPowThree) :
    ArtsGieslSharpTheoremUpperBound where
  bound := T.dstUpper
  theoryEq := by
    rw [T.upperMatchesSourceTarget]
    exact hTheory
  ordinalEq := by
    rw [T.upperMatchesSourceTarget]
    exact hOrdinal
  theoremLevel := T.upperTheoremLevel

/-- An exact-calibration transfer with the required source target yields a
sharp package over its destination upper bound. -/
theorem artsGiesl_sharpUpperBound_exists_if_exactTransfer
    (T : ExactCalibrationTransfer sctPrincipleProfile artsGieslPrincipleProfile)
    (hTheory : T.sourceCalibration.targetProfile.theory = FormalTheory.RCA0_WO_omega3)
    (hOrdinal :
      T.sourceCalibration.targetProfile.ordinalCeiling? =
        some OperatorKO7.ReverseMathSupport.omegaPowThree) :
    ∃ U : ArtsGieslSharpTheoremUpperBound, U.bound = T.dstUpper := by
  exact ⟨ArtsGieslSharpTheoremUpperBound.ofExactCalibrationTransfer T hTheory hOrdinal, rfl⟩

/-- Direct exact-target record backed by the Lean theorem `WO(omega^3)`. This
constructs the upper-bound data package; it does not prove the Arts-Giesl
principle reduction represented by that package. -/
noncomputable def artsGieslDirectSharpTheoremUpperBound :
    ArtsGieslSharpTheoremUpperBound where
  bound := {
    theoryProfile := rca0WoOmega3TheoryProfile
    evidenceStatus := EvidenceStatus.theoremLevel
    justificationTag := "exact-target theorem upper package"
  }
  theoryEq := rfl
  ordinalEq := rfl
  theoremLevel := rfl

@[simp] theorem artsGieslDirectSharpTheoremUpperBound_status :
    artsGieslDirectSharpTheoremUpperBound.bound.evidenceStatus =
      EvidenceStatus.theoremLevel := rfl

theorem artsGieslDirectSharpTheoremUpperBound_supported :
    artsGieslDirectSharpTheoremUpperBound.bound.theoryProfile.theory =
        FormalTheory.RCA0_WO_omega3
      ∧ artsGieslDirectSharpTheoremUpperBound.bound.theoryProfile.ordinalCeiling? =
          some OperatorKO7.ReverseMathSupport.omegaPowThree
      ∧ artsGieslDirectSharpTheoremUpperBound.bound.evidenceStatus =
          EvidenceStatus.theoremLevel := by
  constructor
  · rfl
  constructor
  · rfl
  · rfl

/-- The direct exact-target data package is inhabited by its canonical
construction. -/
theorem artsGiesl_sharpUpperBound_exists_directly :
    ∃ U : ArtsGieslSharpTheoremUpperBound, U = artsGieslDirectSharpTheoremUpperBound := by
  exact ⟨artsGieslDirectSharpTheoremUpperBound, rfl⟩

/-! ## Comparison of conditional construction routes

The exact-calibration and theorem-alignment routes agree on theory, ordinal,
and evidence status. Equality after erasing only the justification tag also
requires equality of the full source theory profile. Equality after erasing
all presentation metadata needs only the theory and ordinal equalities.
-/

/-- The exact-calibration and induced theorem-alignment routes have the same
upper-bound theory field. -/
theorem ArtsGieslSharpTheoremUpperBound.ofExactCalibrationTransfer_sameTheory
    (T : ExactCalibrationTransfer sctPrincipleProfile artsGieslPrincipleProfile)
    (hTheory : T.sourceCalibration.targetProfile.theory =
      FormalTheory.RCA0_WO_omega3)
    (hOrdinal : T.sourceCalibration.targetProfile.ordinalCeiling? =
      some OperatorKO7.ReverseMathSupport.omegaPowThree) :
    (ArtsGieslSharpTheoremUpperBound.ofExactCalibrationTransfer
        T hTheory hOrdinal).bound.theoryProfile.theory =
      ((ArtsGieslSctSharpUpperTransfer.ofTheoremAlignment
          (ArtsGieslSctTheoremAlignment.ofExactCalibrationTransfer
            T hTheory hOrdinal)
        ).toSharpTheoremUpperBound).bound.theoryProfile.theory := by
  rw [(ArtsGieslSharpTheoremUpperBound.ofExactCalibrationTransfer
        T hTheory hOrdinal).theoryEq,
    ((ArtsGieslSctSharpUpperTransfer.ofTheoremAlignment
        (ArtsGieslSctTheoremAlignment.ofExactCalibrationTransfer
          T hTheory hOrdinal)
      ).toSharpTheoremUpperBound).theoryEq]

/-- The exact-calibration and induced theorem-alignment routes have the same
ordinal-ceiling field. -/
theorem ArtsGieslSharpTheoremUpperBound.ofExactCalibrationTransfer_sameOrdinal
    (T : ExactCalibrationTransfer sctPrincipleProfile artsGieslPrincipleProfile)
    (hTheory : T.sourceCalibration.targetProfile.theory =
      FormalTheory.RCA0_WO_omega3)
    (hOrdinal : T.sourceCalibration.targetProfile.ordinalCeiling? =
      some OperatorKO7.ReverseMathSupport.omegaPowThree) :
    (ArtsGieslSharpTheoremUpperBound.ofExactCalibrationTransfer
        T hTheory hOrdinal).bound.theoryProfile.ordinalCeiling? =
      ((ArtsGieslSctSharpUpperTransfer.ofTheoremAlignment
          (ArtsGieslSctTheoremAlignment.ofExactCalibrationTransfer
            T hTheory hOrdinal)
        ).toSharpTheoremUpperBound).bound.theoryProfile.ordinalCeiling? := by
  rw [(ArtsGieslSharpTheoremUpperBound.ofExactCalibrationTransfer
        T hTheory hOrdinal).ordinalEq,
    ((ArtsGieslSctSharpUpperTransfer.ofTheoremAlignment
        (ArtsGieslSctTheoremAlignment.ofExactCalibrationTransfer
          T hTheory hOrdinal)
      ).toSharpTheoremUpperBound).ordinalEq]

/-- The exact-calibration and induced theorem-alignment routes have the same
evidence-status field. -/
theorem ArtsGieslSharpTheoremUpperBound.ofExactCalibrationTransfer_sameStatus
    (T : ExactCalibrationTransfer sctPrincipleProfile artsGieslPrincipleProfile)
    (hTheory : T.sourceCalibration.targetProfile.theory =
      FormalTheory.RCA0_WO_omega3)
    (hOrdinal : T.sourceCalibration.targetProfile.ordinalCeiling? =
      some OperatorKO7.ReverseMathSupport.omegaPowThree) :
    (ArtsGieslSharpTheoremUpperBound.ofExactCalibrationTransfer
        T hTheory hOrdinal).bound.evidenceStatus =
      ((ArtsGieslSctSharpUpperTransfer.ofTheoremAlignment
          (ArtsGieslSctTheoremAlignment.ofExactCalibrationTransfer
            T hTheory hOrdinal)
        ).toSharpTheoremUpperBound).bound.evidenceStatus := by
  rw [(ArtsGieslSharpTheoremUpperBound.ofExactCalibrationTransfer
        T hTheory hOrdinal).theoremLevel,
    ((ArtsGieslSctSharpUpperTransfer.ofTheoremAlignment
        (ArtsGieslSctTheoremAlignment.ofExactCalibrationTransfer
          T hTheory hOrdinal)
      ).toSharpTheoremUpperBound).theoremLevel]

/-- If the source target profile equals the SCT exact profile, the two routes
agree after erasing only their justification tags. -/
theorem ArtsGieslSharpTheoremUpperBound.ofExactCalibrationTransfer_eraseTags_eq_ofTheoremAlignment
    (T : ExactCalibrationTransfer sctPrincipleProfile artsGieslPrincipleProfile)
    (hTheory : T.sourceCalibration.targetProfile.theory =
      FormalTheory.RCA0_WO_omega3)
    (hOrdinal : T.sourceCalibration.targetProfile.ordinalCeiling? =
      some OperatorKO7.ReverseMathSupport.omegaPowThree)
    (hSource : T.sourceCalibration.targetProfile =
      sctExactUpperBound.theoryProfile) :
    (ArtsGieslSharpTheoremUpperBound.ofExactCalibrationTransfer
        T hTheory hOrdinal).bound.eraseJustificationTag =
      ((ArtsGieslSctSharpUpperTransfer.ofTheoremAlignment
          (ArtsGieslSctTheoremAlignment.ofExactCalibrationTransfer
            T hTheory hOrdinal)
        ).toSharpTheoremUpperBound).bound.eraseJustificationTag := by
  apply ReverseMathUpperBound.eraseJustificationTag_congr
  · show T.dstUpper.theoryProfile = sctExactUpperBound.theoryProfile
    rw [T.upperMatchesSourceTarget, hSource]
  · show T.dstUpper.evidenceStatus = EvidenceStatus.theoremLevel
    exact T.upperTheoremLevel

/-- With only theory and ordinal agreement, the two routes agree after erasing
the theory-profile presentation fields and justification tag. -/
theorem ArtsGieslSharpTheoremUpperBound.ofExactCalibrationTransfer_erasePresentation_eq_ofTheoremAlignment
    (T : ExactCalibrationTransfer sctPrincipleProfile artsGieslPrincipleProfile)
    (hTheory : T.sourceCalibration.targetProfile.theory =
      FormalTheory.RCA0_WO_omega3)
    (hOrdinal : T.sourceCalibration.targetProfile.ordinalCeiling? =
      some OperatorKO7.ReverseMathSupport.omegaPowThree) :
    (ArtsGieslSharpTheoremUpperBound.ofExactCalibrationTransfer
        T hTheory hOrdinal).bound.erasePresentationMetadata =
      ((ArtsGieslSctSharpUpperTransfer.ofTheoremAlignment
          (ArtsGieslSctTheoremAlignment.ofExactCalibrationTransfer
            T hTheory hOrdinal)
        ).toSharpTheoremUpperBound).bound.erasePresentationMetadata := by
  apply ReverseMathUpperBound.erasePresentationMetadata_congr
  · show T.dstUpper.theoryProfile.theory = FormalTheory.RCA0_WO_omega3
    rw [T.upperMatchesSourceTarget]
    exact hTheory
  · show T.dstUpper.theoryProfile.ordinalCeiling? =
      some OperatorKO7.ReverseMathSupport.omegaPowThree
    rw [T.upperMatchesSourceTarget]
    exact hOrdinal
  · show T.dstUpper.evidenceStatus = EvidenceStatus.theoremLevel
    exact T.upperTheoremLevel

end OperatorKO7.ArtsGieslUpperBound
