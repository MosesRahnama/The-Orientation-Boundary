import OperatorKO7.Meta.WitnessOrder
import OperatorKO7.Meta.OperationalIncompleteness
import OperatorKO7.Meta.ConfessionMethod_DP
import OperatorKO7.Meta.ConfessionMethod_Unification
import OperatorKO7.Meta.DependencyPairs_Works
import OperatorKO7.Meta.LawvereYanofskySeparation
import OperatorKO7.Meta.SchemaConfessionDominance
import OperatorKO7.Meta.ArtsGiesl_DerivationalComplexity
import Mathlib.Tactic

/-!
# Proof-theoretic ascent register

This module records six-step ascent profiles and diagonal or reflection classifications, registers the Arts--Giesl license at `Π⁰₂` complexity and `IΣ₁` formalizability with `PRA` for each fixed finite TRS, stores a reverse-mathematical target as a conjecture object, and states a constant-overhead recursor-side bound.

The dependency-pair confession realizes the six-step shape and is classified as a reflection ascent, not a diagonal ascent. Its profile carries the `artsGiesl2000` soundness license.

-/

namespace OperatorKO7.ProofTheoreticRegister

open OperatorKO7
open OperatorKO7.Trace
open OperatorKO7.WitnessOrder
open OperatorKO7.MetaOperationalIncompleteness
open OperatorKO7.ConfessionMethodFamily
open OperatorKO7.LawvereYanofskySeparation
open OperatorKO7.MetaDependencyPairs
open OperatorKO7.StepDuplicating.StepDuplicatingSchema.BaseDuplicatingSystem

/-- The two ascent families in this register. -/
inductive AscentFamily
  | diagonal
  | reflection
  deriving DecidableEq, Repr

/-- The formula class used for license complexity. -/
inductive FormulaClass
  | pi02
  deriving DecidableEq, Repr

/-- The formal theories represented in the register. -/
inductive FormalTheory
  | PRA
  | ISigma1
  | RCA0
  | RCA0_WO_omega3
  | WO_epsilon0
  deriving DecidableEq, Repr

namespace FormalTheory

/-- An explicit coarse ordering for the proof-theoretic register. -/
def toNat : FormalTheory → Nat
  | PRA => 0
  | ISigma1 => 1
  | RCA0 => 2
  | RCA0_WO_omega3 => 3
  | WO_epsilon0 => 4

instance : LE FormalTheory := ⟨fun a b => a.toNat ≤ b.toNat⟩
instance : LT FormalTheory := ⟨fun a b => a.toNat < b.toNat⟩

instance (a b : FormalTheory) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.toNat ≤ b.toNat))

instance (a b : FormalTheory) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.toNat < b.toNat))

end FormalTheory

/-- Six-step structural profile for a confession-style ascent. -/
structure SixStepStructuralProfile where
  hasBaseSystem : Prop
  hasSelfObstruction : Prop
  blockedInBase : Prop
  hasStrongerFramework : Prop
  resolvedInFramework : Prop
  licensedReimport : Prop

/-- Realization predicate for the six-step profile. -/
def RealizesSixStepShape (P : SixStepStructuralProfile) : Prop :=
  P.hasBaseSystem
    ∧ P.hasSelfObstruction
    ∧ P.blockedInBase
    ∧ P.hasStrongerFramework
    ∧ P.resolvedInFramework
    ∧ P.licensedReimport

/-- Six-step profile for the dependency-pair confession on the duplicator. -/
def dpSixStepStructuralProfile : SixStepStructuralProfile where
  hasBaseSystem := True
  hasSelfObstruction :=
    ∃ b s n : Trace, Step (recΔ b s (delta n)) (app s (recΔ b s n))
  blockedInBase := ¬ HasWitness ko7Tower WLevel.directWhole
  hasStrongerFramework :=
    ∃ C : ConfessionMethod OperatorKO7.CompositionalImpossibility.ko7Schema,
      C.license = SoundnessLicense.artsGiesl2000
  resolvedInFramework := HasWitness ko7Tower WLevel.transformedCall
  licensedReimport :=
    ∃ fw : CertifiedForgettingWitness,
      fw = CertifiedForgettingWitness.ofConfessionMethod dpConfession

/-- The dependency-pair confession on the duplicator realizes the six-step ascent profile. -/
theorem structural_identity :
    RealizesSixStepShape dpSixStepStructuralProfile := by
  refine ⟨trivial, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨Trace.void, Trace.void, Trace.void, ?_⟩
    simpa using (rec_succ_extracts_dependency_pair Trace.void Trace.void Trace.void).1
  · exact ko7_no_directWhole_witness
  · exact ⟨dpConfession, rfl⟩
  · exact ko7_has_transformedCall_witness
  · exact ⟨CertifiedForgettingWitness.ofConfessionMethod dpConfession, rfl⟩

/-- Reflection-family evidence: the base layer is blocked, the transformed
problem is resolved only after admitting an external license, and the admitted
license is tracked together with its proof-theoretic class. -/
structure ReflectionFamilyEvidence where
  blockedInBase : Prop
  externalLicense : SoundnessLicense
  transformedResolution : Prop
  conservativeClass : FormulaClass

/-- A reflection-family ascent record carrying the six-step profile, soundness license, and proof-theoretic class. -/
structure ReflectionFamilyAscentWitness where
  hasBaseSystem : Prop
  hasSelfObstruction : Prop
  blockedInBase : Prop
  hasStrongerFramework : Prop
  resolvedInFramework : Prop
  licensedReimport : Prop
  externalLicense : SoundnessLicense
  conservativeClass : FormulaClass
  holdsBaseSystem : hasBaseSystem
  holdsSelfObstruction : hasSelfObstruction
  holdsBlockedInBase : blockedInBase
  holdsStrongerFramework : hasStrongerFramework
  holdsResolvedInFramework : resolvedInFramework
  holdsLicensedReimport : licensedReimport

/-- A diagonal-family record stores propositions for an internal code object, evaluation map, and contradiction-driven fixed-point-free step. -/
structure DiagonalFamilyEvidence where
  hasInternalCodeObject : Prop
  hasEvaluationMap : Prop
  contradictionDriven : Prop

/-- Proof-theoretic classification object. -/
inductive AscentFamilyEvidence
  | diagonal (d : DiagonalFamilyEvidence)
  | reflection (r : ReflectionFamilyEvidence)

/-- The dependency-pair confession is classified by the reflection-family
register. -/
def dpReflectionEvidence : ReflectionFamilyEvidence where
  blockedInBase := dpSixStepStructuralProfile.blockedInBase
  externalLicense := SoundnessLicense.artsGiesl2000
  transformedResolution := dpSixStepStructuralProfile.resolvedInFramework
  conservativeClass := FormulaClass.pi02

/-- Reflection-family ascent data for the dependency-pair confession on the primitive duplicator. -/
def dpReflectionAscentWitness : ReflectionFamilyAscentWitness := by
  rcases structural_identity with
    ⟨hBase, hSelf, hBlocked, hStronger, hResolved, hLicensed⟩
  exact
    { hasBaseSystem := dpSixStepStructuralProfile.hasBaseSystem
      hasSelfObstruction := dpSixStepStructuralProfile.hasSelfObstruction
      blockedInBase := dpSixStepStructuralProfile.blockedInBase
      hasStrongerFramework := dpSixStepStructuralProfile.hasStrongerFramework
      resolvedInFramework := dpSixStepStructuralProfile.resolvedInFramework
      licensedReimport := dpSixStepStructuralProfile.licensedReimport
      externalLicense := SoundnessLicense.artsGiesl2000
      conservativeClass := FormulaClass.pi02
      holdsBaseSystem := hBase
      holdsSelfObstruction := hSelf
      holdsBlockedInBase := hBlocked
      holdsStrongerFramework := hStronger
      holdsResolvedInFramework := hResolved
      holdsLicensedReimport := hLicensed }

/-- The proof-theoretic register attached to the DP confession. -/
def dpProofTheoreticRegister : AscentFamilyEvidence :=
  .reflection dpReflectionEvidence

/-- The dependency-pair confession is not classified by the Lawvere--Yanofsky diagonal branch. -/
theorem dp_confession_not_lawvere_yanofsky_diagonal :
    ¬ ∃ d, dpProofTheoreticRegister = .diagonal d := by
  intro h
  rcases h with ⟨d, hd⟩
  cases hd

/-- The dependency-pair confession has a reflection-family ascent. -/
theorem dp_confession_is_reflection_family_ascent :
    ∃ r, dpProofTheoreticRegister = .reflection r := by
  exact ⟨dpReflectionEvidence, rfl⟩

/-- The dependency-pair confession has a reflection-family witness object with the six-step profile, soundness license, and proof-theoretic class. -/
def dp_confession_reflection_family_witness : ReflectionFamilyAscentWitness :=
  dpReflectionAscentWitness

/-- A nonempty reflection-family ascent record exists for the dependency-pair confession. -/
theorem dp_confession_has_reflection_family_witness :
    Nonempty ReflectionFamilyAscentWitness :=
  ⟨dp_confession_reflection_family_witness⟩

/-- The primitive-duplicator dependency-pair confession has a singleton extracted-pair certificate, well-founded `DPPairRev`, the `artsGiesl2000` license, and semantic separation from Lawvere--Yanofsky diagonal coding. -/
theorem dp_confession_semantic_lawvere_yanofsky_separation :
    Fintype.card primitiveDuplicatorDpConfessionStructure.pairCertificate.Node = 1
      ∧ WellFounded MetaDependencyPairs.DPPairRev
      ∧ primitiveDuplicatorDpConfessionStructure.externalLicense =
          SoundnessLicense.artsGiesl2000
      ∧ primitiveDuplicatorDpConfessionStructure.SemanticallySeparatedFromLawvereYanofsky := by
  exact primitive_duplicator_dp_confession_semantic_profile

/-- The certificate summary establishes one extracted-pair node, well-founded `DPPairRev`, and the `artsGiesl2000` license. -/
theorem dp_confession_has_singleton_finite_graph_certificate :
    Fintype.card primitiveDuplicatorDpConfessionStructure.pairCertificate.Node = 1
      ∧ WellFounded MetaDependencyPairs.DPPairRev
      ∧ primitiveDuplicatorDpConfessionStructure.externalLicense =
          SoundnessLicense.artsGiesl2000 := by
  exact ⟨dp_confession_semantic_lawvere_yanofsky_separation.1,
    dp_confession_semantic_lawvere_yanofsky_separation.2.1,
    dp_confession_semantic_lawvere_yanofsky_separation.2.2.1⟩

@[simp] theorem dpReflectionAscentWitness_externalLicense :
    dpReflectionAscentWitness.externalLicense = SoundnessLicense.artsGiesl2000 := by
  unfold dpReflectionAscentWitness
  rcases structural_identity with
    ⟨_hBase, _hSelf, _hBlocked, _hStronger, _hResolved, _hLicensed⟩
  rfl

@[simp] theorem dpReflectionAscentWitness_conservativeClass :
    dpReflectionAscentWitness.conservativeClass = FormulaClass.pi02 := by
  unfold dpReflectionAscentWitness
  rcases structural_identity with
    ⟨_hBase, _hSelf, _hBlocked, _hStronger, _hResolved, _hLicensed⟩
  rfl

/-- Proof-theoretic fields associated with the Arts--Giesl soundness license. -/
structure SoundnessLicenseProfile where
  family : AscentFamily
  complexity : FormulaClass
  formalizableIn : FormalTheory
  fixedFiniteProvableIn : FormalTheory

/-- The Arts--Giesl license register records a reflection family, `Π⁰₂` complexity, `IΣ₁` formalizability, and `PRA` provability for fixed finite TRSs. -/
def artsGieslLicenseProfile : SoundnessLicenseProfile where
  family := AscentFamily.reflection
  complexity := FormulaClass.pi02
  formalizableIn := FormalTheory.ISigma1
  fixedFiniteProvableIn := FormalTheory.PRA

/-- The Arts--Giesl license register assigns `Π⁰₂` complexity. -/
@[simp] theorem arts_giesl_soundness_is_pi02 :
    artsGieslLicenseProfile.complexity = FormulaClass.pi02 := rfl

/-- The Arts--Giesl license register assigns `IΣ₁` formalizability. -/
@[simp] theorem arts_giesl_formalizable_in_ISigma1 :
    artsGieslLicenseProfile.formalizableIn = FormalTheory.ISigma1 := rfl

/-- The register assigns `PRA` for each fixed finite TRS. -/
@[simp] theorem arts_giesl_fixed_finite_TRS_in_PRA :
    artsGieslLicenseProfile.fixedFiniteProvableIn = FormalTheory.PRA := rfl

/-- Conjectural reverse-mathematical calibration target for the Arts--Giesl
license. This is a formalized statement object, not a proved theorem. -/
structure ReverseMathConjecture where
  target : FormalTheory
  upperBenchmark : FormalTheory
  targetBelowUpper : target < upperBenchmark

/-- The named calibration target is `RCA0_WO_omega3` below `WO_epsilon0`. -/
def artsGieslReverseMathCalibration : ReverseMathConjecture where
  target := FormalTheory.RCA0_WO_omega3
  upperBenchmark := FormalTheory.WO_epsilon0
  targetBelowUpper := by decide

@[simp] theorem arts_giesl_reverse_math_target :
    artsGieslReverseMathCalibration.target = FormalTheory.RCA0_WO_omega3 := rfl

@[simp] theorem arts_giesl_reverse_math_target_below_epsilon0 :
    artsGieslReverseMathCalibration.target < artsGieslReverseMathCalibration.upperBenchmark :=
  artsGieslReverseMathCalibration.targetBelowUpper

/-! ## Constant-overhead recursor-side Arts--Giesl bound -/

/-- Rule count of the primitive duplicator. -/
abbrev recursorRuleCount : Nat :=
  ArtsGieslDerivationalComplexity.recursorRuleCount

/-- Signature size for the recursor-side bound. -/
abbrev recursorSignatureSize : Nat :=
  ArtsGieslDerivationalComplexity.recursorSignatureSize

/-- The extracted dependency-pair count for the primitive duplicator. -/
abbrev recursorDependencyPairCount : Nat :=
  ArtsGieslDerivationalComplexity.recursorDependencyPairCount

/-- Construction-cost bound for the dependency-pair graph. -/
abbrev agGraphConstructionCost : Nat :=
  ArtsGieslDerivationalComplexity.agGraphConstructionCost

/-- Base-order check cost for the single extracted pair. -/
abbrev agBaseOrderCost : Nat :=
  ArtsGieslDerivationalComplexity.agBaseOrderCost

/-- Constant schematic cost of one Arts--Giesl soundness invocation. -/
abbrev agSchematicInvocationCost : Nat :=
  ArtsGieslDerivationalComplexity.agSchematicInvocationCost

/-- Total constant license overhead on the primitive duplicator. -/
abbrev agLicenseOverhead : Nat :=
  ArtsGieslDerivationalComplexity.agLicenseOverhead

@[simp] theorem ag_license_overhead_eq : agLicenseOverhead = 18 :=
  ArtsGieslDerivationalComplexity.ag_license_overhead_eq

/-- The transformed-call residual proof work on the primitive duplicator is
linear in the counter height, with constant license overhead. -/
theorem ag_proof_length_on_step_duplicating_recursor (K : Nat) :
    residualProofWork K + agLicenseOverhead = K + agLicenseOverhead :=
  ArtsGieslDerivationalComplexity.ag_proof_length_on_step_duplicating_recursor K

end OperatorKO7.ProofTheoreticRegister
