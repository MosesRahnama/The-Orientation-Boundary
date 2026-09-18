import OperatorKO7.Meta.ProofTheoreticRegister

/-!
# Six-field profile comparison

`SixStepStructuralProfile` supplies six proposition-valued fields.
`StageHolds` selects one field, `StagewiseEquivalent` is pointwise logical
equivalence across the six selectors, and the transport theorems project those
equivalences. `dpStagewiseRealization` is derived from the imported
`structural_identity` proof for `dpSixStepStructuralProfile`. The formal scope
is proposition-level field comparison.
-/

namespace OperatorKO7.ReflectionSchema

open OperatorKO7.ProofTheoreticRegister

/-- Named stages in the paper's six-step structural profile. -/
inductive StructuralStage
  | baseSystem
  | selfObstruction
  | blockedInBase
  | strongerFramework
  | resolvedInFramework
  | licensedReimport
  deriving DecidableEq, Repr

/-- Stagewise view of a `SixStepStructuralProfile`. -/
def StageHolds (P : SixStepStructuralProfile) : StructuralStage → Prop
  | .baseSystem => P.hasBaseSystem
  | .selfObstruction => P.hasSelfObstruction
  | .blockedInBase => P.blockedInBase
  | .strongerFramework => P.hasStrongerFramework
  | .resolvedInFramework => P.resolvedInFramework
  | .licensedReimport => P.licensedReimport

/-- Pointwise realization of all six stages. -/
structure StagewiseRealization (P : SixStepStructuralProfile) where
  realizes : ∀ s, StageHolds P s

/-- Stagewise agreement between two structural profiles. -/
def StagewiseEquivalent (P Q : SixStepStructuralProfile) : Prop :=
  ∀ s, StageHolds P s ↔ StageHolds Q s

theorem StagewiseEquivalent.symm
    {P Q : SixStepStructuralProfile}
    (hEQ : StagewiseEquivalent P Q) :
    StagewiseEquivalent Q P := by
  intro s
  exact (hEQ s).symm

/-- A package containing pointwise equivalence of the six profile fields. -/
structure ReflectionComparisonSchema (P Q : SixStepStructuralProfile) where
  stagewiseAgreement : StagewiseEquivalent P Q

@[simp] theorem realizesSixStepShape_iff_stagewise (P : SixStepStructuralProfile) :
    RealizesSixStepShape P ↔ Nonempty (StagewiseRealization P) := by
  constructor
  · intro h
    rcases h with ⟨h1, h2, h3, h4, h5, h6⟩
    refine ⟨⟨?_⟩⟩
    intro s
    cases s <;> assumption
  · intro h
    rcases h with ⟨hR⟩
    refine ⟨hR.realizes .baseSystem, hR.realizes .selfObstruction,
      hR.realizes .blockedInBase, hR.realizes .strongerFramework,
      hR.realizes .resolvedInFramework, hR.realizes .licensedReimport⟩

/-- Stagewise agreement preserves realization of the six-step shape. -/
theorem StagewiseEquivalent.preserves_realization
    {P Q : SixStepStructuralProfile}
    (hEQ : StagewiseEquivalent P Q)
    (hP : RealizesSixStepShape P) :
    RealizesSixStepShape Q := by
  rcases (realizesSixStepShape_iff_stagewise P).1 hP with ⟨hR⟩
  refine (realizesSixStepShape_iff_stagewise Q).2 ?_
  refine ⟨⟨?_⟩⟩
  intro s
  exact (hEQ s).1 (hR.realizes s)

/-- The stored pointwise equivalence transports a realization from left to right. -/
theorem ReflectionComparisonSchema.sound
    {P Q : SixStepStructuralProfile}
    (C : ReflectionComparisonSchema P Q)
    (hP : RealizesSixStepShape P) :
    RealizesSixStepShape Q :=
  C.stagewiseAgreement.preserves_realization hP

/-- Converts the imported `structural_identity` conjunction into a stage-indexed function. -/
def dpStagewiseRealization : StagewiseRealization dpSixStepStructuralProfile := by
  rcases (realizesSixStepShape_iff_stagewise dpSixStepStructuralProfile).1 structural_identity with
    ⟨hR⟩
  exact hR

/-- Self-comparison for the mechanized DP profile. -/
def dpReflectionComparison : ReflectionComparisonSchema
    dpSixStepStructuralProfile dpSixStepStructuralProfile where
  stagewiseAgreement := by intro s; rfl

end OperatorKO7.ReflectionSchema
