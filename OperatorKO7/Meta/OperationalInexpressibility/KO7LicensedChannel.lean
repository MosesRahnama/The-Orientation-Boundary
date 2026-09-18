import OperatorKO7.Meta.OperationalInexpressibility.FiniteProbabilityChannel
import OperatorKO7.Meta.OperationalInexpressibility.KO7ObservationVerdict
import OperatorKO7.Meta.OperationalInexpressibility.ResponseProvenance

/-!
# Concrete normalized KO7 licensed channel

The source carrier is exactly B-02's two relation systems with a uniform
prior. The direct observation is the complete proved `directProfile`, whose
codomain is `Candidate -> Prop`; it is not replaced by a constant or an
existential bit. The licensed decision is generated from a proof-backed
certificate/refutation split. Its accepting certificate contains B-03's
checked transformed call, transformed termination, rule-extracted projection
receipt, proof-valued source license, and exact source relation.

The self-embedding system is rejected because any such certificate would use
its license to prove source termination and relation exactness would transport
that result to the self-embedding relation, contradicting B-02's independent
nontermination theorem. `terminationVerdict` is never inspected to construct
the licensed decision. Channel separation and B-03 rule provenance remain
separate propositions. The direct and licensed posterior kernels are supplied
normalized models. The theorems below prove their calibration on this exact
two-system instance, but do not derive them as Bayes conditionals from a joint
probability law.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace OperatorKO7.Meta.OperationalInexpressibility.KO7LicensedChannel

open OperatorKO7
open OperatorKO7.Trace
open OperatorKO7.MetaDependencyPairs
open OperatorKO7.Meta.InformationalIncompleteness.ShannonFinite
open OperatorKO7.Meta.OperationalInexpressibility.FiniteProbabilityChannel
open OperatorKO7.Meta.OperationalInexpressibility.KO7ObservationVerdict
open OperatorKO7.Meta.OperationalInexpressibility.ResponseProvenance
open OperatorKO7.Meta.Recursor.MassProfileIdentity

/-! ## Exact source carrier and uniform prior -/

/-- The recursor system carries the actual KO7 root-step relation. -/
theorem ko7_recursor_relation_eq_step :
    RelationSystem.recursor.relation = Step :=
  rfl

/-- The comparison system carries the actual self-embedding relation. -/
theorem ko7_selfEmbedding_relation_eq_selfEmbeddingStep :
    RelationSystem.selfEmbedding.relation = SelfEmbeddingStep :=
  rfl

/-- The exact B-02 source carrier has two elements. -/
theorem relationSystem_card_eq_two :
    Fintype.card RelationSystem = 2 := by
  decide

/-- Uniform prior on the exact recursor/self-embedding carrier. -/
def ko7UniformPrior : FiniteDistribution RelationSystem where
  mass := fun _ => (1 : Real) / 2
  nonnegative := by
    intro system
    norm_num
  total := by
    rw [Finset.sum_const, Finset.card_univ,
      relationSystem_card_eq_two, nsmul_eq_mul]
    norm_num

/-- Named total-mass-one law for the two-system prior. -/
theorem ko7UniformPrior_total :
    Finset.univ.sum ko7UniformPrior.mass = 1 :=
  ko7UniformPrior.total

/-- Named nonnegativity law for the two-system prior. -/
theorem ko7UniformPrior_nonnegative
    (system : RelationSystem) :
    0 <= ko7UniformPrior.mass system :=
  ko7UniformPrior.nonnegative system

/-- Both actual systems have positive prior mass. -/
theorem ko7UniformPrior_positive :
    0 < ko7UniformPrior.mass RelationSystem.recursor
      ∧ 0 < ko7UniformPrior.mass RelationSystem.selfEmbedding := by
  norm_num [ko7UniformPrior]

/-! ## Direct channel on the full proved profile -/

/-- The direct posterior is fair on verdicts at every complete candidate
profile. The input type itself is the full B-02 profile. -/
def ko7DirectPosterior :
    ConditionalKernel (Candidate -> Prop) Bool :=
  ConditionalKernel.fairBinary (Candidate -> Prop)

/-- The direct channel exposes `directProfile` literally. -/
def ko7DirectChannel :
    FiniteChannel RelationSystem (Candidate -> Prop) Bool where
  prior := ko7UniformPrior
  target := terminationVerdict
  observe := directProfile
  posterior := ko7DirectPosterior

/-- Public receipt that the direct observation is the full profile, not a
surrogate finite tag. -/
theorem ko7DirectChannel_observe_eq_directProfile :
    ko7DirectChannel.observe = directProfile :=
  rfl

/-- Required B-02 collision, re-exported under the D-04 paper-facing name. -/
theorem ko7_directProfile_eq :
    directProfile RelationSystem.recursor =
      directProfile RelationSystem.selfEmbedding :=
  directProfile_recursor_eq_selfEmbedding

/-- The common full-profile fiber. This is the actual B-02 predicate-valued
observation, not a surrogate tag. -/
def ko7CommonDirectProfile : Candidate -> Prop :=
  directProfile RelationSystem.recursor

/-- Every source system lies in the same full-profile fiber. The nontrivial
branch is exactly the B-02 direct-profile equality. -/
theorem ko7_everySource_has_common_directProfile
    (system : RelationSystem) :
    directProfile system = ko7CommonDirectProfile := by
  cases system with
  | recursor => rfl
  | selfEmbedding =>
      simpa [ko7CommonDirectProfile] using ko7_directProfile_eq.symm

/-- The direct channel therefore sends every source to the same observation
fiber. -/
theorem ko7DirectChannel_everySource_commonFiber
    (system : RelationSystem) :
    ko7DirectChannel.observe system = ko7CommonDirectProfile := by
  simpa [ko7DirectChannel] using
    ko7_everySource_has_common_directProfile system

/-- Required independent target split, re-exported under the D-04 name. -/
theorem ko7_terminationVerdict_ne :
    terminationVerdict RelationSystem.recursor ≠
      terminationVerdict RelationSystem.selfEmbedding :=
  terminationVerdict_recursor_ne_selfEmbedding

/-- Every direct posterior row is normalized. -/
theorem ko7DirectPosterior_total
    (profile : Candidate -> Prop) :
    Finset.univ.sum (ko7DirectPosterior.mass profile) = 1 :=
  ko7DirectPosterior.total profile

/-- Named nonnegativity law for every direct posterior row. -/
theorem ko7DirectPosterior_nonnegative
    (profile : Candidate -> Prop) (verdict : Bool) :
    0 <= ko7DirectPosterior.mass profile verdict :=
  ko7DirectPosterior.nonnegative profile verdict

/-- The target law induced by the two equally weighted systems and their
distinct Boolean verdicts. -/
def ko7UniformTargetDistribution : FiniteDistribution Bool :=
  fairBinaryDistribution

/-- The uniform target law agrees with the two uniform source atoms at their
independently defined B-02 verdicts. -/
theorem ko7UniformTargetDistribution_matches_uniformPrior :
    ko7UniformTargetDistribution.mass
        (terminationVerdict RelationSystem.recursor) =
        ko7UniformPrior.mass RelationSystem.recursor
      ∧ ko7UniformTargetDistribution.mass
        (terminationVerdict RelationSystem.selfEmbedding) =
        ko7UniformPrior.mass RelationSystem.selfEmbedding := by
  constructor <;> rfl

/-- On the common direct-profile fiber, the fair posterior is exactly the
uniform target distribution. -/
theorem ko7DirectPosterior_commonFiber_calibrated
    (verdict : Bool) :
    ko7DirectPosterior.mass ko7CommonDirectProfile verdict =
      ko7UniformTargetDistribution.mass verdict :=
  rfl

/-- Source-indexed calibration, derived through the common B-02 profile
fiber. -/
theorem ko7DirectPosterior_calibrated
    (system : RelationSystem) (verdict : Bool) :
    ko7DirectPosterior.mass (directProfile system) verdict =
      ko7UniformTargetDistribution.mass verdict := by
  rw [ko7_everySource_has_common_directProfile system]
  exact ko7DirectPosterior_commonFiber_calibrated verdict

/-- Under the direct profile, either actual target receives mass one half. -/
theorem ko7DirectPosterior_target_mass_half
    (system : RelationSystem) :
    ko7DirectPosterior.mass (directProfile system)
      (terminationVerdict system) = (1 : Real) / 2 :=
  rfl

/-! ## Checked licensed certificate and non-circular rejection -/

/-- A concrete nontrivial instance of the displayed `rec_succ` rule. -/
def ko7ChannelRecSuccRule : RecSuccRule where
  base := void
  stepTerm := void
  counter := void

/-- A licensed certificate for a named system. Every field is proof content;
there is no stored desired verdict. -/
structure LicensedTerminationCertificate
    (rule : RecSuccRule) (system : RelationSystem) : Prop where
  transformedCall : TransformedCallCertificate rule
  transformedTerminates : KO7TransformedTermination
  projectionRuleExtracted :
    RuleDetermined (fun r : RecSuccRule => r) extractProjection
  sourceLicense :
    SoundnessLicense KO7TransformedTermination KO7SourceRootTermination
  relationExact : system.relation = Step

/-- The concrete D-04 certificate type. -/
abbrev KO7LicensedCertificate (system : RelationSystem) : Prop :=
  LicensedTerminationCertificate ko7ChannelRecSuccRule system

/-- The recursor has the checked transformed call and proof-valued source
license required by the certificate. -/
def recursorLicensedCertificate :
    KO7LicensedCertificate RelationSystem.recursor where
  transformedCall :=
    ko7CheckedTransformedCallCertificate ko7ChannelRecSuccRule
  transformedTerminates := wf_DPPairRev
  projectionRuleExtracted := ko7Projection_ruleDetermined
  sourceLicense := ko7DPSoundnessLicense
  relationExact := ko7_recursor_relation_eq_step

/-- The self-embedding system cannot carry the certificate: certificate
soundness would force strong normalization, contradicting the independently
proved self-embedding chain. -/
theorem selfEmbedding_rejected_by_licenseSoundness_and_nontermination :
    Not (KO7LicensedCertificate RelationSystem.selfEmbedding) := by
  intro certificate
  apply selfEmbedding_not_strongNormalizationVerdict
  have sourceTermination : KO7SourceRootTermination :=
    certificate.sourceLicense.bridge certificate.transformedTerminates
  unfold StrongNormalizationVerdict StronglyNormalizing
  rw [certificate.relationExact]
  exact sourceTermination

/-- Proof-backed result of checking the licensed certificate interface. -/
inductive LicensedDecision (system : RelationSystem)
  | accepted (certificate : KO7LicensedCertificate system)
  | rejected (refutation : Not (KO7LicensedCertificate system))

/-- Check the two exact systems by their certificate evidence. This definition
does not inspect `terminationVerdict`. -/
def licensedDecision :
    (system : RelationSystem) -> LicensedDecision system
  | .recursor => .accepted recursorLicensedCertificate
  | .selfEmbedding =>
      .rejected selfEmbedding_rejected_by_licenseSoundness_and_nontermination

/-- Boolean projection of the proof-backed licensed decision. -/
def licensedAccept (system : RelationSystem) : Bool :=
  match licensedDecision system with
  | .accepted _ => true
  | .rejected _ => false

/-- Required certificate-based separation. -/
theorem ko7_licensedCertificate_separates :
    licensedAccept RelationSystem.recursor = true
      ∧ licensedAccept RelationSystem.selfEmbedding = false :=
  ⟨rfl, rfl⟩

/-- Agreement with the independently defined B-02 target is derived only
after the certificate/refutation decision has been constructed. It is not
used in the definition of `licensedAccept`. -/
theorem ko7_licensedAccept_eq_terminationVerdict
    (system : RelationSystem) :
    licensedAccept system = terminationVerdict system := by
  cases system with
  | recursor =>
      simpa [terminationVerdict] using
        ko7_licensedCertificate_separates.1
  | selfEmbedding =>
      simpa [terminationVerdict] using
        ko7_licensedCertificate_separates.2

/-! ## Normalized licensed channel and exact residuals -/

/-- The licensed posterior is determinate at the certificate decision. -/
def ko7LicensedPosterior : ConditionalKernel Bool Bool :=
  ConditionalKernel.deterministic id

/-- The licensed channel uses the proof-backed certificate decision as its
observation. Its target remains the independently defined B-02 verdict. -/
def ko7LicensedChannel :
    FiniteChannel RelationSystem Bool Bool where
  prior := ko7UniformPrior
  target := terminationVerdict
  observe := licensedAccept
  posterior := ko7LicensedPosterior

/-- Every licensed posterior row is normalized. -/
theorem ko7LicensedPosterior_total (decision : Bool) :
    Finset.univ.sum (ko7LicensedPosterior.mass decision) = 1 :=
  ko7LicensedPosterior.total decision

/-- Named nonnegativity law for every licensed posterior row. -/
theorem ko7LicensedPosterior_nonnegative
    (decision verdict : Bool) :
    0 <= ko7LicensedPosterior.mass decision verdict :=
  ko7LicensedPosterior.nonnegative decision verdict

/-- After certificate construction, the licensed posterior assigns mass one
to the independently defined target verdict. This is a derived calibration
theorem, not the definition of `licensedAccept`. -/
theorem ko7LicensedPosterior_target_mass_one
    (system : RelationSystem) :
    ko7LicensedPosterior.mass (licensedAccept system)
      (terminationVerdict system) = 1 := by
  have hCalibration := ko7_licensedAccept_eq_terminationVerdict system
  change pointMass (licensedAccept system) (terminationVerdict system) = 1
  rw [← hCalibration]
  simp [pointMass]

/-- Each direct-profile cell has fair binary target entropy. -/
theorem ko7DirectChannel_cellEntropy_eq_log_two
    (system : RelationSystem) :
    H (ko7DirectChannel.posterior.mass
      (ko7DirectChannel.observe system)) = Real.log 2 := by
  change H (ko7DirectPosterior.mass (directProfile system)) = Real.log 2
  have hPosterior :
      ko7DirectPosterior.mass (directProfile system) =
        ko7UniformTargetDistribution.mass := by
    funext verdict
    exact ko7DirectPosterior_calibrated system verdict
  rw [hPosterior]
  simpa [ko7UniformTargetDistribution, fairBinaryDistribution] using
    fairBinaryMass_entropy

/-- Each licensed-decision cell has determinate target entropy. -/
theorem ko7LicensedChannel_cellEntropy_eq_zero
    (system : RelationSystem) :
    H (ko7LicensedChannel.posterior.mass
      (ko7LicensedChannel.observe system)) = 0 := by
  have hCalibration := ko7_licensedAccept_eq_terminationVerdict system
  change H (pointMass (licensedAccept system)) = 0
  rw [hCalibration]
  exact H_pointMass (terminationVerdict system)

/-- Residual target uncertainty after the full direct profile. -/
noncomputable def directResidual : Real :=
  ko7DirectChannel.residual

/-- Residual target uncertainty after the licensed certificate channel. -/
noncomputable def licensedResidual : Real :=
  ko7LicensedChannel.residual

/-- Licensed-channel deficit in natural-log units. -/
noncomputable def ko7LicensedDeficit : Real :=
  directResidual - licensedResidual

/-- The full-profile collision leaves exactly `log 2` residual uncertainty
under the uniform two-system prior. -/
theorem ko7_direct_residual_eq_log_two :
    directResidual = Real.log 2 := by
  unfold directResidual FiniteChannel.residual
  calc
    (∑ system, ko7DirectChannel.prior.mass system *
        H (ko7DirectChannel.posterior.mass
          (ko7DirectChannel.observe system))) =
        ∑ system, ko7DirectChannel.prior.mass system * Real.log 2 := by
          apply Finset.sum_congr rfl
          intro system hSystem
          rw [ko7DirectChannel_cellEntropy_eq_log_two system]
    _ = (∑ system, ko7DirectChannel.prior.mass system) * Real.log 2 := by
          rw [Finset.sum_mul]
    _ = Real.log 2 := by
          rw [ko7DirectChannel.prior.total, one_mul]

/-- The proof-backed licensed channel leaves zero residual uncertainty. -/
theorem ko7_licensed_residual_eq_zero :
    licensedResidual = 0 := by
  unfold licensedResidual FiniteChannel.residual
  apply Finset.sum_eq_zero
  intro system hSystem
  rw [ko7LicensedChannel_cellEntropy_eq_zero system, mul_zero]

/-- The exact licensed deficit is `log 2` in natural-log units. -/
theorem ko7_licensed_deficit_eq_log_two :
    ko7LicensedDeficit = Real.log 2 := by
  unfold ko7LicensedDeficit
  rw [ko7_direct_residual_eq_log_two, ko7_licensed_residual_eq_zero, sub_zero]

/-! ## Separate channel and provenance conclusions -/

/-- Channel separation and B-03 rule provenance are separate conjuncts. The
second statement concerns factorization through the declared rule view; it is
not inferred from the first statement's varying channel cells. -/
theorem ko7_channelSeparation_with_separate_licenseProvenance :
    (licensedAccept RelationSystem.recursor = true
      ∧ licensedAccept RelationSystem.selfEmbedding = false)
      ∧ Not (RuleDetermined licenseSupplyRuleView licenseAvailable) :=
  ⟨ko7_licensedCertificate_separates,
    ko7SoundnessLicense_outside_declaredExtractorLanguage⟩

/-- The D-04 headline is theorem-level composition of independently named
results, not a structure whose fields store the desired conclusions. Its
residual and deficit equalities are under the stated normalized posterior
model; this theorem does not derive a Bayes posterior from a joint law. -/
theorem ko7_licensedChannel_headline :
    ko7DirectChannel.observe = directProfile
      ∧ (forall system : RelationSystem,
        directProfile system = ko7CommonDirectProfile)
      ∧ terminationVerdict RelationSystem.recursor ≠
        terminationVerdict RelationSystem.selfEmbedding
      ∧ (licensedAccept RelationSystem.recursor = true
        ∧ licensedAccept RelationSystem.selfEmbedding = false)
      ∧ (forall (system : RelationSystem) (verdict : Bool),
        ko7DirectPosterior.mass (directProfile system) verdict =
          ko7UniformTargetDistribution.mass verdict)
      ∧ (forall system : RelationSystem,
        licensedAccept system = terminationVerdict system)
      ∧ directResidual = Real.log 2
      ∧ licensedResidual = 0
      ∧ ko7LicensedDeficit = Real.log 2
      ∧ Not (RuleDetermined licenseSupplyRuleView licenseAvailable) := by
  exact
    ⟨ko7DirectChannel_observe_eq_directProfile,
      ko7_everySource_has_common_directProfile,
      ko7_terminationVerdict_ne,
      ko7_licensedCertificate_separates,
      ko7DirectPosterior_calibrated,
      ko7_licensedAccept_eq_terminationVerdict,
      ko7_direct_residual_eq_log_two,
      ko7_licensed_residual_eq_zero,
      ko7_licensed_deficit_eq_log_two,
      ko7SoundnessLicense_outside_declaredExtractorLanguage⟩

/-- Non-vacuity: the systems are distinct and positively weighted, the
recursor certificate is inhabited, the self-embedding certificate is refuted,
and the resulting natural-log deficit is strictly positive. -/
theorem ko7_licensedChannel_nonvacuous :
    RelationSystem.recursor ≠ RelationSystem.selfEmbedding
      ∧ 0 < ko7UniformPrior.mass RelationSystem.recursor
      ∧ 0 < ko7UniformPrior.mass RelationSystem.selfEmbedding
      ∧ KO7LicensedCertificate RelationSystem.recursor
      ∧ Not (KO7LicensedCertificate RelationSystem.selfEmbedding)
      ∧ 0 < ko7LicensedDeficit := by
  refine ⟨by decide, ?_, ?_, recursorLicensedCertificate,
    selfEmbedding_rejected_by_licenseSoundness_and_nontermination, ?_⟩
  · norm_num [ko7UniformPrior]
  · norm_num [ko7UniformPrior]
  · rw [ko7_licensed_deficit_eq_log_two]
    exact Real.log_pos (by norm_num)

end OperatorKO7.Meta.OperationalInexpressibility.KO7LicensedChannel
