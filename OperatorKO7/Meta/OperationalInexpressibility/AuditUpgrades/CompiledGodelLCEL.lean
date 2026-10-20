import OperatorKO7.Meta.LCELStructuralIdentity
import OperatorKO7.Meta.GodelSideAscentProfile
import OperatorKO7.Meta.DistinctionBoundary.GodelFixedPointSemantics

/-!
# Compiled Gödel side: fixed-point profile and LCEL instance

Proves: the compiled Gödel profile whose second stage is the Gödel fixed point of the compiled
Robinson-Q checker realizes the six-step shape and is compatible with the dependency-pair
profile; a formal comparison object built from the compiled checker, with the Gödel sentence as
the blocked sentence, the theory of the standard model as the stronger framework and admission
by truth as the reimport, yields an LCEL instance that realizes the LCEL schema; this instance
and the dependency-pair LCEL instance admit six-clause comparisons in both directions.
Relation: provability `Provable` of the compiled checker; truth `evalForm env0` in the standard model.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: every slot is filled by a compiled formula or a theorem of the compiled stack; no slot is
stipulated `True`.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.OperationalInexpressibility.AuditUpgrades.CompiledGodelLCEL

open OperatorKO7.ClassicalAscentProfile
open OperatorKO7.LCELTypedSigmaGamma
open OperatorKO7.LCELSchema
open OperatorKO7.LCELStructuralIdentity
open OperatorKO7.LCELDpInstance
open OperatorKO7.ProofTheoreticRegister
open OperatorKO7.ReflectionSchema
open OperatorKO7.Meta.DistinctionBoundary.GodelArith

/-- The Gödel sentence of the compiled checker is unprovable. -/
theorem arithGodelSentence_not_provable : ¬ Provable arithGodelSentence :=
  godel_first_incompleteness_Q_unconditional.1

/-- The Gödel sentence of the compiled checker is true in the standard model. -/
theorem arithGodelSentence_true : evalForm env0 arithGodelSentence :=
  arithGodelFixedPointSemantics_holds.2 arithGodelSentence_not_provable

/-! ## Six-step profile with the fixed point at stage two -/

/-- The compiled Gödel profile with the Gödel fixed point at stage two. -/
def godelFixedPointAscentProfile : AscentProfile where
  shape := {
    hasBaseSystem := ∃ φ : Formula, Provable φ
    hasSelfObstruction := ∃ G : Formula, (evalForm env0 G ↔ ¬ Provable G) ∧ ¬ Provable G
    blockedInBase := ¬ Provable ConQ
    hasStrongerFramework := ModelsQ ModelInf
    resolvedInFramework := ¬ evalFormIn ModelInf env0Inf ConQ
    licensedReimport := ¬ Provable (Formula.not ConQ)
  }
  family := AscentFamily.reflection

theorem godelFixedPointAscentProfile_realizes :
    RealizesSixStepShape godelFixedPointAscentProfile.shape :=
  ⟨⟨Formula.eq Term.zero Term.zero, eq_refl_is_provable⟩,
    ⟨arithGodelSentence, arithGodelFixedPointSemantics_holds, arithGodelSentence_not_provable⟩,
    godel_second_incompleteness_Q_unconditional,
    modelInf_qAxioms,
    modelInf_not_conQ,
    not_provable_not_conQ_unconditional⟩

theorem godelFixedPointAscentProfile_compatible :
    CompatibleWithDp godelFixedPointAscentProfile :=
  (OperatorKO7.Meta.SafeStep.AscentProfileDegeneracy.compatibleWithDp_iff_realizes
    godelFixedPointAscentProfile).2 ⟨godelFixedPointAscentProfile_realizes, rfl⟩

/-! ## Formal comparison object of the compiled checker -/

def compiledBaseTheory : FormalHistoricalBaseTheory where
  label := "Robinson Q, compiled checker"
  Sentence := Formula
  provesBaseSystem := Provable
  witness := Formula.eq Term.zero Term.zero
  witness_provesBaseSystem := eq_refl_is_provable

def compiledObstruction : FormalHistoricalObstruction where
  label := "Gödel sentence of the compiled checker"
  Witness := Formula
  isSelfObstruction := fun G => (evalForm env0 G ↔ ¬ Provable G)
  blocksBase := fun G => ¬ Provable G
  witness := arithGodelSentence
  witness_isSelfObstruction := arithGodelFixedPointSemantics_holds
  witness_blocksBase := arithGodelSentence_not_provable

def compiledFramework : FormalHistoricalFramework where
  label := "theory of the standard model"
  Framework := Formula → Prop
  resolves := fun T => (∀ φ, Provable φ → T φ) ∧ T arithGodelSentence
  availableWitness := fun φ => evalForm env0 φ
  resolver := fun φ => evalForm env0 φ
  resolver_resolves := ⟨fun _ h => provable_sound h env0, arithGodelSentence_true⟩

def compiledReimport : FormalHistoricalReimport where
  label := "admission of the Gödel sentence by truth"
  Admission := Unit
  certified := fun _ => evalForm env0 arithGodelSentence ∧ ¬ Provable arithGodelSentence
  witness := ()
  witness_certified := ⟨arithGodelSentence_true, arithGodelSentence_not_provable⟩

def compiledBaseContent : FormalBaseTheorySemantics where
  Sentence := Formula
  proves := Provable
  trueInReferenceModel := evalForm env0
  baseSentence := Formula.eq Term.zero Term.zero
  baseSentence_proves := eq_refl_is_provable

def compiledObstructionContent : FormalObstructionSemantics compiledBaseContent where
  Witness := Formula
  obstructs := fun w s => s = w
  selfReferential := fun G => (evalForm env0 G ↔ ¬ Provable G)
  blockedBy := id
  witness := arithGodelSentence
  witness_selfReferential := arithGodelFixedPointSemantics_holds
  witness_obstructs_blocked := rfl
  blocked_not_provable := arithGodelSentence_not_provable
  blocked_true := arithGodelSentence_true

def compiledReflectionContent : FormalReflectionOperatorSemantics compiledBaseContent where
  Framework := Formula → Prop
  extendsBase := fun T => ∀ φ, Provable φ → T φ
  reflects := fun T φ => T φ
  licensedAdmission := fun φ => evalForm env0 φ
  blockedSentence := arithGodelSentence
  blocked_not_provable := arithGodelSentence_not_provable
  blocked_true := arithGodelSentence_true
  strongerFramework := fun φ => evalForm env0 φ
  stronger_extendsBase := fun _ h => provable_sound h env0
  stronger_reflects_blocked := arithGodelSentence_true
  blocked_licensedAdmission := arithGodelSentence_true

def compiledReimportContent : FormalReimportSemantics compiledBaseContent where
  Admission := Unit
  certifies := fun _ φ => evalForm env0 φ
  importedSentence := arithGodelSentence
  witness := ()
  witness_certifies_imported := arithGodelSentence_true
  imported_true := arithGodelSentence_true

def compiledCoherence :
    FormalSemanticCoherence compiledObstructionContent compiledReflectionContent
      compiledReimportContent where
  obstruction_blocked_eq_reflection_blocked := rfl
  reflection_blocked_eq_reimported := rfl
  reflection_covers_obstruction := arithGodelSentence_true
  reimport_certifies_reflection_blocked := arithGodelSentence_true

/-- The comparison profile read off the compiled semantics. -/
def compiledComparisonProfile : AscentProfile where
  shape := {
    hasBaseSystem := compiledBaseTheory.hasBaseSystem
    hasSelfObstruction := compiledObstruction.hasSelfObstruction
    blockedInBase := compiledObstruction.blockedInBase
    hasStrongerFramework := compiledFramework.frameworkAvailable
    resolvedInFramework := compiledFramework.resolvesInFramework
    licensedReimport := compiledReimport.licensedReimport
  }
  family := AscentFamily.reflection

theorem compiledComparisonProfile_realizes :
    RealizesSixStepShape compiledComparisonProfile.shape :=
  ⟨compiledBaseTheory.realizesBaseSystem,
    compiledObstruction.realizesSelfObstruction,
    compiledObstruction.realizesBlockedInBase,
    compiledFramework.realizesAvailability,
    compiledFramework.realizesResolution,
    compiledReimport.realizesLicensedReimport⟩

def compiledGodelComparisonObject : FormalExternalClassicalComparisonObject where
  baseSemantics := compiledBaseTheory
  obstructionSemantics := compiledObstruction
  frameworkSemantics := compiledFramework
  reimportSemantics := compiledReimport
  baseTheoryContent := compiledBaseContent
  obstructionContent := compiledObstructionContent
  reflectionContent := compiledReflectionContent
  reimportContent := compiledReimportContent
  semanticCoherence := compiledCoherence
  family := AscentFamily.reflection
  profile := compiledComparisonProfile
  profileShape := rfl
  profileFamily := rfl
  compatible :=
    (OperatorKO7.Meta.SafeStep.AscentProfileDegeneracy.compatibleWithDp_iff_realizes
      compiledComparisonProfile).2 ⟨compiledComparisonProfile_realizes, rfl⟩

/-! ## LCEL instance of the compiled checker -/

def compiledBoundaryObject : LCELBoundaryObject compiledBaseContent where
  BoundaryWitness := Unit
  boundarySentence := fun _ => arithGodelSentence
  designated := ()
  designated_not_provable := arithGodelSentence_not_provable
  designated_true := arithGodelSentence_true

def compiledAnnotationFunctor :
    LCELAnnotationFunctor compiledBaseContent compiledReimportContent where
  Annotation := Formula
  annotate := fun _ => arithGodelSentence
  decode := id
  witness_decodes_to_imported := rfl
  witness_certifies_decoded := arithGodelSentence_true
  witness_decoded_true := arithGodelSentence_true

/-- The LCEL instance built from the compiled Robinson-Q checker. -/
def compiledGodelLCELInstance : FormalLCELInstance where
  comparison := compiledGodelComparisonObject
  boundaryObject := compiledBoundaryObject
  boundaryMatchesProfile :=
    iff_of_true compiledBoundaryObject.designated_realizes
      compiledObstruction.realizesSelfObstruction
  externalLicenseObject := defaultExternalLicenseObject compiledGodelComparisonObject
  externalLicenseWitness := compiledReflectionContent.hasReflectionOperator
  externalLicenseHolds := ⟨_, compiledReflectionContent.stronger_extendsBase⟩
  externalLicenseMatchesWitness :=
    defaultExternalLicenseObject_realized_iff_hasReflectionOperator compiledGodelComparisonObject
  reimportClassObject := defaultReimportClassObject compiledGodelComparisonObject
  reimportClassWitness := compiledReimportContent.hasSemanticReimport
  reimportClassHolds := compiledReimportContent.realizesSemanticReimport
  reimportClassMatchesWitness :=
    defaultReimportClassObject_realized_iff_hasSemanticReimport compiledGodelComparisonObject
  annotationFunctor := compiledAnnotationFunctor
  annotationMatchesProfile :=
    iff_of_true compiledAnnotationFunctor.witness_realizes
      compiledReimport.realizesLicensedReimport

/-- The compiled Gödel LCEL instance realizes the LCEL schema. -/
theorem compiledGodelLCELInstance_realizesSchema :
    RealizesLCELSchema compiledGodelLCELInstance.toSlotProfile :=
  compiledGodelLCELInstance.realizesLCELSchema compiledBaseTheory.realizesBaseSystem
    compiledFramework.realizesAvailability

/-- The boundary sentence of the compiled instance is independent of the checker and true. -/
theorem compiledGodelLCELInstance_boundary_independent_and_true :
    ¬ Provable arithGodelSentence ∧ ¬ Provable (Formula.not arithGodelSentence) ∧
      evalForm env0 arithGodelSentence :=
  ⟨godel_first_incompleteness_Q_unconditional.1, godel_first_incompleteness_Q_unconditional.2,
    arithGodelSentence_true⟩

/-- The compiled Gödel instance and the dependency-pair LCEL instance admit six-clause
comparisons in both directions. -/
theorem compiledGodel_dp_lcel_comparison :
    Nonempty (LCELQuasiFunctor compiledGodelLCELInstance dpEmitterLCELInstance) ∧
      Nonempty (LCELQuasiFunctor dpEmitterLCELInstance compiledGodelLCELInstance) :=
  lcel_structural_identity_bidirectional
    (fun s => (compiledGodelComparisonObject.compatible.1 s).trans
      (dpEmitterLCELInstance.comparison.compatible.1 s).symm)
    (iff_of_true compiledGodelLCELInstance.externalLicenseHolds
      dpEmitterLCELInstance.externalLicenseHolds)
    (iff_of_true compiledGodelLCELInstance.reimportClassHolds
      dpEmitterLCELInstance.reimportClassHolds)

end OperatorKO7.Meta.OperationalInexpressibility.AuditUpgrades.CompiledGodelLCEL
