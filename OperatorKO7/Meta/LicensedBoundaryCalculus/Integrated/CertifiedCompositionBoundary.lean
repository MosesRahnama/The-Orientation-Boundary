import OperatorKO7.Meta.LicensedBoundaryCalculus.Integrated.Composition
import OperatorKO7.Meta.LicensedBoundaryCalculus.Quantitative.KO7SemanticAdequacy

/-!
# Certified semantic composition boundary

Structural morphisms and event accounting form the universal categorical
backbone.  Semantic data can decorate a composite only through a supplied
adequacy certificate.  The KO7 fixture proves that no rule determined solely
by the two factor decorations can equal every adequate composite decoration:
the same composed relation admits distinct certified witness-language grades.

## Audit slots

Relation: partial licensed-reduction composition.
Closure: morphism identity/associativity and list append.
Trust: kernel-only; semantic output is never inferred without adequacy.
Scope: structural/accounting category with domain-specific semantic decoration.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.LicensedBoundaryCalculus

universe u v w d a d₁ a₁ d₂ a₂

/-- Semantic construction data together with complete relation-derived
adequacy for one partial licensed-reduction morphism. -/
structure CertifiedSemanticCapability
    {A : ARS.{u}} {B : ARS.{v}}
    [Fintype A.Carrier] [Fintype B.Carrier]
    (F : PartialLicensedReductionMorphism A B)
    (Defect : Type d) (Action : Type a)
    [DecidableEq Defect] [Fintype Action] [DecidableEq Action] where
  data : SemanticConstructionData A Defect Action
  adequate : SemanticAdequacyCertificate F data

namespace CertifiedSemanticCapability

/-- Forget only the adequacy witness to use the compatibility composition
builder.  The semantic relation remains pinned to the exact composite. -/
def toComposite
    {A : ARS.{u}} {B : ARS.{v}} {C : ARS.{w}}
    [Fintype A.Carrier] [Fintype B.Carrier] [Fintype C.Carrier]
    {Defect : Type d} {Action : Type a}
    [DecidableEq Defect] [Fintype Action] [DecidableEq Action]
    {F : PartialLicensedReductionMorphism A B}
    {G : PartialLicensedReductionMorphism B C}
    (capability : CertifiedSemanticCapability
      (PartialLicensedReductionMorphism.comp F G) Defect Action) :
    CompositeSemanticCapability F G Defect Action where
  semantics := capability.data
  relation_iff := capability.adequate.relationExact

end CertifiedSemanticCapability

namespace IntegratedBoundaryTransaction

/-- Certified semantic composition.  The output profile is computed from a
complete adequacy certificate for the exact composite relation. -/
def certifiedComp
    {A : ARS.{u}} {B : ARS.{v}} {C : ARS.{w}}
    [Fintype A.Carrier] [Fintype B.Carrier] [Fintype C.Carrier]
    {Defect₁ : Type d₁} {Action₁ : Type a₁}
    [DecidableEq Defect₁] [Fintype Action₁] [DecidableEq Action₁]
    {Defect₂ : Type d₂} {Action₂ : Type a₂}
    [DecidableEq Defect₂] [Fintype Action₂] [DecidableEq Action₂]
    {Defect : Type d} {Action : Type a}
    [DecidableEq Defect] [Fintype Action] [DecidableEq Action]
    (first : IntegratedBoundaryTransaction A B Defect₁ Action₁)
    (second : IntegratedBoundaryTransaction B C Defect₂ Action₂)
    (semantic : CertifiedSemanticCapability
      (PartialLicensedReductionMorphism.comp first.morphism second.morphism)
      Defect Action) :
    IntegratedBoundaryTransaction A C Defect Action :=
  comp first second semantic.toComposite

/-- Left identity holds for the full universal backbone: morphism, trace, and
ledger.  Semantic equality is deliberately not asserted. -/
theorem integrated_id_comp
    {A : ARS.{u}} {B : ARS.{v}}
    [Fintype A.Carrier] [Fintype B.Carrier]
    {Defect₁ : Type d₁} {Action₁ : Type a₁}
    [DecidableEq Defect₁] [Fintype Action₁] [DecidableEq Action₁]
    {Defect₂ : Type d₂} {Action₂ : Type a₂}
    [DecidableEq Defect₂] [Fintype Action₂] [DecidableEq Action₂]
    (identitySemantics : SemanticConstructionData A Defect₁ Action₁)
    (identityRelation : ∀ x y,
      identitySemantics.scope.relation x y ↔ A.step x y)
    (transaction : IntegratedBoundaryTransaction A B Defect₂ Action₂) :
    PartialLicensedReductionMorphism.comp
        (identity identitySemantics identityRelation).morphism
        transaction.morphism = transaction.morphism ∧
      (identity identitySemantics identityRelation).eventTrace ++
          transaction.eventTrace = transaction.eventTrace ∧
      countEvents
          ((identity identitySemantics identityRelation).eventTrace ++
            transaction.eventTrace) = transaction.ledger := by
  refine ⟨PartialLicensedReductionMorphism.id_comp transaction.morphism, ?_, ?_⟩
  · rfl
  · rfl

/-- Right identity holds for morphism, trace, and ledger. -/
theorem integrated_comp_id
    {A : ARS.{u}} {B : ARS.{v}}
    [Fintype A.Carrier] [Fintype B.Carrier]
    {Defect₁ : Type d₁} {Action₁ : Type a₁}
    [DecidableEq Defect₁] [Fintype Action₁] [DecidableEq Action₁]
    {Defect₂ : Type d₂} {Action₂ : Type a₂}
    [DecidableEq Defect₂] [Fintype Action₂] [DecidableEq Action₂]
    (transaction : IntegratedBoundaryTransaction A B Defect₁ Action₁)
    (identitySemantics : SemanticConstructionData B Defect₂ Action₂)
    (identityRelation : ∀ x y,
      identitySemantics.scope.relation x y ↔ B.step x y) :
    PartialLicensedReductionMorphism.comp transaction.morphism
        (identity identitySemantics identityRelation).morphism =
          transaction.morphism ∧
      transaction.eventTrace ++
          (identity identitySemantics identityRelation).eventTrace =
            transaction.eventTrace ∧
      countEvents
          (transaction.eventTrace ++
            (identity identitySemantics identityRelation).eventTrace) =
          transaction.ledger := by
  refine ⟨PartialLicensedReductionMorphism.comp_id transaction.morphism, ?_, ?_⟩
  · exact List.append_nil _
  · change countEvents (transaction.eventTrace ++ []) =
      countEvents transaction.eventTrace
    rw [List.append_nil]

/-- Associativity holds exactly for the structural/accounting backbone. -/
theorem integrated_comp_assoc
    {A : ARS.{u}} {B : ARS.{v}} {C : ARS.{w}} {D : ARS}
    [Fintype A.Carrier] [Fintype B.Carrier]
    [Fintype C.Carrier] [Fintype D.Carrier]
    {Defect₁ : Type d₁} {Action₁ : Type a₁}
    [DecidableEq Defect₁] [Fintype Action₁] [DecidableEq Action₁]
    {Defect₂ : Type d₂} {Action₂ : Type a₂}
    [DecidableEq Defect₂] [Fintype Action₂] [DecidableEq Action₂]
    {Defect : Type d} {Action : Type a}
    [DecidableEq Defect] [Fintype Action] [DecidableEq Action]
    (first : IntegratedBoundaryTransaction A B Defect₁ Action₁)
    (second : IntegratedBoundaryTransaction B C Defect₂ Action₂)
    (third : IntegratedBoundaryTransaction C D Defect Action) :
    PartialLicensedReductionMorphism.comp
        (PartialLicensedReductionMorphism.comp first.morphism second.morphism)
        third.morphism =
      PartialLicensedReductionMorphism.comp first.morphism
        (PartialLicensedReductionMorphism.comp second.morphism third.morphism) ∧
    (first.eventTrace ++ second.eventTrace) ++ third.eventTrace =
      first.eventTrace ++ (second.eventTrace ++ third.eventTrace) ∧
    countEvents ((first.eventTrace ++ second.eventTrace) ++ third.eventTrace) =
      countEvents (first.eventTrace ++ (second.eventTrace ++ third.eventTrace)) := by
  refine ⟨PartialLicensedReductionMorphism.comp_assoc
      first.morphism second.morphism third.morphism, List.append_assoc _ _ _, ?_⟩
  rw [List.append_assoc]

/-- The composed semantic profile is derived from the certified decoration. -/
theorem integrated_comp_semanticProfile
    {A : ARS.{u}} {B : ARS.{v}} {C : ARS.{w}}
    [Fintype A.Carrier] [Fintype B.Carrier] [Fintype C.Carrier]
    {Defect₁ : Type d₁} {Action₁ : Type a₁}
    [DecidableEq Defect₁] [Fintype Action₁] [DecidableEq Action₁]
    {Defect₂ : Type d₂} {Action₂ : Type a₂}
    [DecidableEq Defect₂] [Fintype Action₂] [DecidableEq Action₂]
    {Defect : Type d} {Action : Type a}
    [DecidableEq Defect] [Fintype Action] [DecidableEq Action]
    (first : IntegratedBoundaryTransaction A B Defect₁ Action₁)
    (second : IntegratedBoundaryTransaction B C Defect₂ Action₂)
    (semantic : CertifiedSemanticCapability
      (PartialLicensedReductionMorphism.comp first.morphism second.morphism)
      Defect Action) :
    (certifiedComp first second semantic).semanticProfile =
      OperatorKO7.Meta.LicensedBoundaryCalculus.semanticProfile semantic.data :=
  rfl

/-- Trace composition is exact. -/
theorem integrated_comp_trace
    {A : ARS.{u}} {B : ARS.{v}} {C : ARS.{w}}
    [Fintype A.Carrier] [Fintype B.Carrier] [Fintype C.Carrier]
    {Defect₁ : Type d₁} {Action₁ : Type a₁}
    [DecidableEq Defect₁] [Fintype Action₁] [DecidableEq Action₁]
    {Defect₂ : Type d₂} {Action₂ : Type a₂}
    [DecidableEq Defect₂] [Fintype Action₂] [DecidableEq Action₂]
    {Defect : Type d} {Action : Type a}
    [DecidableEq Defect] [Fintype Action] [DecidableEq Action]
    (first : IntegratedBoundaryTransaction A B Defect₁ Action₁)
    (second : IntegratedBoundaryTransaction B C Defect₂ Action₂)
    (semantic : CertifiedSemanticCapability
      (PartialLicensedReductionMorphism.comp first.morphism second.morphism)
      Defect Action) :
    (certifiedComp first second semantic).eventTrace =
      first.eventTrace ++ second.eventTrace :=
  rfl

/-- Ledger composition is exact. -/
theorem integrated_comp_ledger
    {A : ARS.{u}} {B : ARS.{v}} {C : ARS.{w}}
    [Fintype A.Carrier] [Fintype B.Carrier] [Fintype C.Carrier]
    {Defect₁ : Type d₁} {Action₁ : Type a₁}
    [DecidableEq Defect₁] [Fintype Action₁] [DecidableEq Action₁]
    {Defect₂ : Type d₂} {Action₂ : Type a₂}
    [DecidableEq Defect₂] [Fintype Action₂] [DecidableEq Action₂]
    {Defect : Type d} {Action : Type a}
    [DecidableEq Defect] [Fintype Action] [DecidableEq Action]
    (first : IntegratedBoundaryTransaction A B Defect₁ Action₁)
    (second : IntegratedBoundaryTransaction B C Defect₂ Action₂)
    (semantic : CertifiedSemanticCapability
      (PartialLicensedReductionMorphism.comp first.morphism second.morphism)
      Defect Action) :
    (certifiedComp first second semantic).ledger =
      first.ledger + second.ledger :=
  comp_ledger first second semantic.toComposite

/-- Composite scope cannot widen the first morphism's state domain. -/
theorem integrated_comp_scope_no_widen
    {A : ARS.{u}} {B : ARS.{v}} {C : ARS.{w}}
    (F : PartialLicensedReductionMorphism A B)
    (G : PartialLicensedReductionMorphism B C)
    {x : A.Carrier} (hx : (PartialLicensedReductionMorphism.comp F G).domain x) :
    F.domain x :=
  hx.1

/-- A certified composition carries exactly the supplied adequacy; no trust
level is synthesized or upgraded by composition. -/
theorem integrated_comp_trust_no_upgrade
    {A : ARS.{u}} {B : ARS.{v}} {C : ARS.{w}}
    [Fintype A.Carrier] [Fintype B.Carrier] [Fintype C.Carrier]
    {Defect : Type d} {Action : Type a}
    [DecidableEq Defect] [Fintype Action] [DecidableEq Action]
    {F : PartialLicensedReductionMorphism A B}
    {G : PartialLicensedReductionMorphism B C}
    (semantic : CertifiedSemanticCapability
      (PartialLicensedReductionMorphism.comp F G) Defect Action)
    (x y : A.Carrier) :
    semantic.data.scope.relation x y ↔
      (PartialLicensedReductionMorphism.comp F G).admitted x y :=
  semantic.adequate.relationExact x y

end IntegratedBoundaryTransaction

/-! ## Calibration transport -/

/-- Change only the declared repair-cost calibration. -/
def repriceSemanticData
    {A : ARS.{u}} [Fintype A.Carrier]
    {Defect : Type d} {Action : Type a}
    [DecidableEq Defect] [Fintype Action] [DecidableEq Action]
    (data : SemanticConstructionData A Defect Action)
    (cost : Action → Nat) : SemanticConstructionData A Defect Action :=
  { data with actionCost := cost }

namespace DefectAdequacy

/-- Defect adequacy is invariant under repair-cost recalibration. -/
def reprice
    {A : ARS.{u}} [Fintype A.Carrier]
    {Defect : Type d} {Action : Type a}
    [DecidableEq Defect] [Fintype Action] [DecidableEq Action]
    {data : SemanticConstructionData A Defect Action}
    (certificate : DefectAdequacy data) (cost : Action → Nat) :
    DefectAdequacy (repriceSemanticData data cost) where
  endpoints := certificate.endpoints
  sound := certificate.sound
  complete := certificate.complete
  irredundant := certificate.irredundant

end DefectAdequacy

namespace RepairSemantics

/-- Repair relation semantics is invariant under repair-cost recalibration. -/
def reprice
    {A : ARS.{u}} [Fintype A.Carrier]
    {Defect : Type d} {Action : Type a}
    [DecidableEq Defect] [Fintype Action] [DecidableEq Action]
    {data : SemanticConstructionData A Defect Action}
    {defects : DefectAdequacy data}
    (certificate : RepairSemantics data defects) (cost : Action → Nat) :
    RepairSemantics (repriceSemanticData data cost) (defects.reprice cost) where
  repairedRelation := certificate.repairedRelation
  protectedRelation := certificate.protectedRelation
  protected_sub_scope := certificate.protected_sub_scope
  repaired_sub_scope := certificate.repaired_sub_scope
  preserves_protected := certificate.preserves_protected
  closes_sound := certificate.closes_sound
  closes_complete := certificate.closes_complete

end RepairSemantics

namespace WitnessLanguageAdequacy

/-- Witness-language adequacy is invariant under repair-cost recalibration. -/
def reprice
    {A : ARS.{u}} [Fintype A.Carrier]
    {Defect : Type d} {Action : Type a}
    [DecidableEq Defect] [Fintype Action] [DecidableEq Action]
    {data : SemanticConstructionData A Defect Action}
    (certificate : WitnessLanguageAdequacy data) (cost : Action → Nat) :
    WitnessLanguageAdequacy (repriceSemanticData data cost) where
  model := certificate.model
  language_kind_eq := certificate.language_kind_eq
  adequate_iff := certificate.adequate_iff
  scope_grade_eq := certificate.scope_grade_eq

end WitnessLanguageAdequacy

namespace AlternativeCarrier

/-- Concrete terminal alternatives are invariant under repair-cost
recalibration. -/
def reprice
    {A : ARS.{u}} [Fintype A.Carrier]
    {Defect : Type d} {Action : Type a}
    [DecidableEq Defect] [Fintype Action] [DecidableEq Action]
    {data : SemanticConstructionData A Defect Action}
    (certificate : AlternativeCarrier data) (cost : Action → Nat) :
    AlternativeCarrier (repriceSemanticData data cost) where
  Alternative := certificate.Alternative
  alternativeFintype := certificate.alternativeFintype
  terminalEquiv := certificate.terminalEquiv
  fixed_count_eq := certificate.fixed_count_eq
  prefix_count_eq := certificate.prefix_count_eq
  prefixCode := certificate.prefixCode
  prefixCode_injective := certificate.prefixCode_injective
  prefixCode_prefixFree := certificate.prefixCode_prefixFree

end AlternativeCarrier

namespace SemanticAdequacyCertificate

/-- Full semantic adequacy transports across a pure repair-cost
recalibration.  This theorem does not certify the new calibration itself. -/
def reprice
    {A : ARS.{u}} {B : ARS.{v}}
    [Fintype A.Carrier] [Fintype B.Carrier]
    {Defect : Type d} {Action : Type a}
    [DecidableEq Defect] [Fintype Action] [DecidableEq Action]
    {F : PartialLicensedReductionMorphism A B}
    {data : SemanticConstructionData A Defect Action}
    (certificate : SemanticAdequacyCertificate F data)
    (cost : Action → Nat) :
    SemanticAdequacyCertificate F (repriceSemanticData data cost) where
  relationExact := certificate.relationExact
  normalizing := certificate.normalizing
  defects := certificate.defects.reprice cost
  repairs := certificate.repairs.reprice cost
  witnesses := certificate.witnesses.reprice cost
  alternatives := certificate.alternatives.reprice cost

end SemanticAdequacyCertificate

/-! ## Exact obstruction to an unlicensed semantic composer -/

namespace KO7DistinctionAdapter

open OperatorKO7.Meta.DistinctionBoundary.Quantitative
open OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7LocalCone

noncomputable section

/-- Same raw relation, defects, repairs, witnesses, and alternatives, but with
an uncalibrated zero-cost action schedule. -/
def rawZeroCostData :
    SemanticConstructionData rawARS CanonicalDefect RepairAction :=
  repriceSemanticData rawData (fun _ => 0)

/-- Action-cost calibration is not part of relation-derived adequacy.  The
zero-cost decoration therefore remains fully adequate at the semantic level. -/
def ko7RawZeroCostAdequacy :
    SemanticAdequacyCertificate rawIdentityMorphism rawZeroCostData :=
  SemanticAdequacyCertificate.reprice ko7RawSemanticAdequacy (fun _ => 0)

theorem rawZeroCost_minimumRepairCost_eq_zero :
    (semanticProfile rawZeroCostData).minimumRepairCost = 0 := by
  change minimumRepairCoverCost
    OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7RepairCover.bad
    OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7RepairCover.closes
    (fun _ : RepairAction => 0)
    OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7RepairCover.coverable = 0
  apply Nat.eq_zero_of_le_zero
  have hchosen : IsRepairCover
      OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7RepairCover.bad
      OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7RepairCover.closes
      ({.guardDiff} : Finset RepairAction) := by
    intro defect hdefect
    simp [OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7RepairCover.closes]
  have hle := minimumRepairCoverCost_le
    (cost := fun _ : RepairAction => 0)
    OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7RepairCover.coverable
    hchosen
  simpa [repairCoverCost] using hle

/-- Universe-pinned KO7 semantic capability. -/
abbrev KO7CertifiedCapability
    (F : PartialLicensedReductionMorphism rawARS rawARS) :=
  CertifiedSemanticCapability.{0, 0, 0, 0, 0, 0}
    F CanonicalDefect RepairAction

noncomputable def ko7RawCapability :
    KO7CertifiedCapability rawIdentityMorphism :=
  ⟨rawData, ko7RawSemanticAdequacy⟩

noncomputable def ko7RawZeroCostCapability :
    KO7CertifiedCapability rawIdentityMorphism :=
  ⟨rawZeroCostData, ko7RawZeroCostAdequacy⟩

/-- Original raw decoration re-certified against the identity composite. -/
noncomputable def ko7RawCompositeCapability :
    KO7CertifiedCapability
      (PartialLicensedReductionMorphism.comp
        rawIdentityMorphism rawIdentityMorphism) where
  data := rawData
  adequate :=
    (PartialLicensedReductionMorphism.id_comp rawIdentityMorphism).symm ▸
      ko7RawSemanticAdequacy

/-- Zero-cost decoration re-certified against the same identity composite. -/
noncomputable def ko7RawZeroCostCompositeCapability :
    KO7CertifiedCapability
      (PartialLicensedReductionMorphism.comp
        rawIdentityMorphism rawIdentityMorphism) where
  data := rawZeroCostData
  adequate :=
    (PartialLicensedReductionMorphism.id_comp rawIdentityMorphism).symm ▸
      ko7RawZeroCostAdequacy

theorem ko7_certified_composite_profiles_differ :
    semanticProfile ko7RawCompositeCapability.data ≠
      semanticProfile ko7RawZeroCostCompositeCapability.data := by
  intro heq
  have hcost := congrArg SemanticProfile.minimumRepairCost heq
  have horiginal :
      (semanticProfile ko7RawCompositeCapability.data).minimumRepairCost = 1 := by
    change (semanticProfile rawData).minimumRepairCost = 1
    exact raw_minimumRepairCost_exact
  have hzero :
      (semanticProfile ko7RawZeroCostCompositeCapability.data
        ).minimumRepairCost = 0 := by
    change (semanticProfile rawZeroCostData).minimumRepairCost = 0
    exact rawZeroCost_minimumRepairCost_eq_zero
  rw [horiginal, hzero] at hcost
  omega

/-- A proposed composer is universally exact only if its one output profile
equals every adequate semantic decoration of that exact composite. -/
def KO7UniversalCompositeProfileRule
    (rule :
      KO7CertifiedCapability rawIdentityMorphism →
        KO7CertifiedCapability rawIdentityMorphism → SemanticProfile) : Prop :=
  ∀ first second
    (output : KO7CertifiedCapability
      (PartialLicensedReductionMorphism.comp
        rawIdentityMorphism rawIdentityMorphism)),
    rule first second = semanticProfile output.data

/-- Exact obstruction: factor decorations do not select a unique adequate
composite decoration.  A domain law choosing witness language and calibration
is therefore load-bearing. -/
theorem no_universal_semantic_composer_without_domain_law :
    ¬ (∃ rule :
        KO7CertifiedCapability rawIdentityMorphism →
          KO7CertifiedCapability rawIdentityMorphism → SemanticProfile,
      KO7UniversalCompositeProfileRule rule) := by
  rintro ⟨rule, huniversal⟩
  have horiginal := huniversal ko7RawCapability ko7RawCapability
    ko7RawCompositeCapability
  have hzero := huniversal ko7RawCapability ko7RawCapability
    ko7RawZeroCostCompositeCapability
  exact ko7_certified_composite_profiles_differ
    (horiginal.symm.trans hzero)

end
end KO7DistinctionAdapter

#check @IntegratedBoundaryTransaction.integrated_id_comp
#check @IntegratedBoundaryTransaction.integrated_comp_id
#check @IntegratedBoundaryTransaction.integrated_comp_assoc
#check @IntegratedBoundaryTransaction.integrated_comp_semanticProfile
#check @IntegratedBoundaryTransaction.integrated_comp_trace
#check @IntegratedBoundaryTransaction.integrated_comp_ledger
#check @IntegratedBoundaryTransaction.integrated_comp_scope_no_widen
#check @IntegratedBoundaryTransaction.integrated_comp_trust_no_upgrade
#check KO7DistinctionAdapter.no_universal_semantic_composer_without_domain_law
#print axioms IntegratedBoundaryTransaction.integrated_id_comp
#print axioms IntegratedBoundaryTransaction.integrated_comp_id
#print axioms IntegratedBoundaryTransaction.integrated_comp_assoc
#print axioms IntegratedBoundaryTransaction.integrated_comp_semanticProfile
#print axioms IntegratedBoundaryTransaction.integrated_comp_trace
#print axioms IntegratedBoundaryTransaction.integrated_comp_ledger
#print axioms IntegratedBoundaryTransaction.integrated_comp_scope_no_widen
#print axioms IntegratedBoundaryTransaction.integrated_comp_trust_no_upgrade
#print axioms KO7DistinctionAdapter.ko7_certified_composite_profiles_differ
#print axioms KO7DistinctionAdapter.no_universal_semantic_composer_without_domain_law

end OperatorKO7.Meta.LicensedBoundaryCalculus
