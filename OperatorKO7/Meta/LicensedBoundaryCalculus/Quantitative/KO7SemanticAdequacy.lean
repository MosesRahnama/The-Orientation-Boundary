import OperatorKO7.Meta.LicensedBoundaryCalculus.Quantitative.SemanticAdequacyCertificate
import OperatorKO7.Meta.LicensedBoundaryCalculus.Quantitative.KO7ExactProfile

/-!
# Certified semantic adequacy for the KO7 distinction cone

The raw and licensed three-node systems receive complete adequacy
certificates.  Their defect vocabularies are proved sound and complete for
actual local peaks, every repair action resolves the represented peak while
preserving the licensed branch, witness grades come from concrete witness
carriers, and both certificate counts come from the reachable terminal
support with explicit prefix-free codes.

## Audit slots

Relation: `LocalRaw` and `LocalLicensed` at `eqW(void,void)`.
Closure: root-local reachability and peak resolution by branch guarding.
Trust: kernel-only finite proofs.
Scope: the canonical three-node local cone, not global context closure.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.LicensedBoundaryCalculus
namespace KO7DistinctionAdapter

open OperatorKO7.Meta.DistinctionBoundary.Quantitative
open OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7LocalCone

noncomputable section

namespace KTerminal

open OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7TerminalMultiplicity

/-- The two raw verdict branches cannot join. -/
theorem raw_refl_diff_not_joinable :
    ¬ Joinable LocalRaw .reflVerdict .diffVerdict := by
  rintro ⟨z, hzRefl, hzDiff⟩
  have hzEqRefl : z = .reflVerdict :=
    eq_of_normalForm_reach raw_refl_normal hzRefl
  have hzEqDiff : z = .diffVerdict :=
    eq_of_normalForm_reach raw_diff_normal hzDiff
  cases hzEqRefl.symm.trans hzEqDiff

/-- Exact raw terminal-support equation in the LBC scope. -/
theorem raw_terminalSupport_eq :
    SemanticScope.terminalSupport rawData.scope =
      ({.reflVerdict, .diffVerdict} : Finset EqWBreakerNode) :=
  OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7TerminalMultiplicity.raw_terminalSupport_eq

/-- Exact licensed terminal-support equation in the LBC scope. -/
theorem licensed_terminalSupport_eq :
    SemanticScope.terminalSupport licensedData.scope =
      ({.reflVerdict} : Finset EqWBreakerNode) :=
  OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7TerminalMultiplicity.licensed_terminalSupport_eq

#print axioms raw_refl_diff_not_joinable
#print axioms raw_terminalSupport_eq
#print axioms licensed_terminalSupport_eq

end KTerminal

namespace KDefect

open OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7RepairCover

/-- The singleton raw defect vocabulary is exactly the actual diagonal peak. -/
def rawDefectAdequacy : DefectAdequacy rawData where
  endpoints
    | .diagonal => (.reflVerdict, .diffVerdict)
  sound := by
    intro d _hd
    cases d
    exact
      ⟨{ left := .reflVerdict
         right := .diffVerdict
         source_to_left := LocalRaw.refl
         source_to_right := LocalRaw.diff
         branches_not_joinable := KTerminal.raw_refl_diff_not_joinable }, rfl⟩
  complete := by
    intro actual
    rcases actual with ⟨left, right, hleft, hright, hnot⟩
    cases hleft with
    | refl =>
        cases hright with
        | refl =>
            exact False.elim
              (hnot
                ⟨.reflVerdict,
                  OperatorKO7.Meta.DistinctionBoundary.Quantitative.reach_refl _,
                  OperatorKO7.Meta.DistinctionBoundary.Quantitative.reach_refl _⟩)
        | diff =>
            exact ⟨.diagonal, by simp [rawData, bad], Or.inl rfl⟩
    | diff =>
        cases hright with
        | refl =>
            exact ⟨.diagonal, by simp [rawData, bad], Or.inr rfl⟩
        | diff =>
            exact False.elim
              (hnot
                ⟨.diffVerdict,
                  OperatorKO7.Meta.DistinctionBoundary.Quantitative.reach_refl _,
                  OperatorKO7.Meta.DistinctionBoundary.Quantitative.reach_refl _⟩)
  irredundant := by
    intro d₁ d₂ _ _ _
    cases d₁
    cases d₂
    rfl

/-- The empty licensed defect vocabulary is complete because the only source
branch is the reflexive verdict branch. -/
def licensedDefectAdequacy : DefectAdequacy licensedData where
  endpoints
    | .diagonal => (.reflVerdict, .diffVerdict)
  sound := by
    intro d hd
    simp [licensedData] at hd
  complete := by
    intro actual
    rcases actual with ⟨left, right, hleft, hright, hnot⟩
    cases hleft
    cases hright
    exact False.elim
      (hnot
        ⟨.reflVerdict,
          OperatorKO7.Meta.DistinctionBoundary.Quantitative.reach_refl _,
          OperatorKO7.Meta.DistinctionBoundary.Quantitative.reach_refl _⟩)
  irredundant := by
    intro d₁ d₂ hd₁ _ _
    simp [licensedData] at hd₁

#check rawDefectAdequacy
#check licensedDefectAdequacy

end KDefect

namespace KRepairSemantics

open OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7RepairCover

/-- Every listed raw repair is interpreted by the semantics-preserving guarded
relation.  The distinction among costs remains in `actionCost`. -/
def rawRepairSemantics : RepairSemantics rawData KDefect.rawDefectAdequacy where
  repairedRelation := fun _ => LocalLicensed
  protectedRelation := LocalLicensed
  protected_sub_scope := by
    intro x y h
    exact licensed_subrelation h
  repaired_sub_scope := by
    intro a x y h
    exact licensed_subrelation h
  preserves_protected := by
    intro a x y h
    exact h
  closes_sound := by
    intro a d _hd _hcloses
    cases d
    apply RepairSemantics.peakResolved_of_not_right
    intro h
    cases h
  closes_complete := by
    intro a d _hd _hresolved
    cases a <;> cases d <;> simp [rawData, closes]

/-- With no licensed defects, every action preserves the already-licensed
relation and the closure table is extensionally empty. -/
def licensedRepairSemantics :
    RepairSemantics licensedData KDefect.licensedDefectAdequacy where
  repairedRelation := fun _ => LocalLicensed
  protectedRelation := LocalLicensed
  protected_sub_scope := by
    intro x y h
    exact h
  repaired_sub_scope := by
    intro a x y h
    exact h
  preserves_protected := by
    intro a x y h
    exact h
  closes_sound := by
    intro a d hd _
    simp [licensedData] at hd
  closes_complete := by
    intro a d hd _
    simp [licensedData] at hd

#check rawRepairSemantics
#check licensedRepairSemantics

end KRepairSemantics

namespace KWitness

open OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7WitnessRank

/-- A single external comparator witness first available at grade one. -/
def rawWitnessModel : WitnessLanguageModel where
  Witness := PUnit
  kind := .external
  grade := fun _ => 1
  adequateWitness := fun _ => True
  inhabited := ⟨PUnit.unit, trivial⟩

/-- The licensed language needs no additional witness grade. -/
def licensedWitnessModel : WitnessLanguageModel where
  Witness := PUnit
  kind := .licensed
  grade := fun _ => 0
  adequateWitness := fun _ => True
  inhabited := ⟨PUnit.unit, trivial⟩

/-- Raw witness rank and language metadata are extensionally exact. -/
def rawWitnessAdequacy : WitnessLanguageAdequacy rawData where
  model := rawWitnessModel
  language_kind_eq := rfl
  adequate_iff := by
    intro n
    simp [rawData, ko7Adequacy, WitnessLanguageModel.adequateAt,
      rawWitnessModel]
  scope_grade_eq := by
    change 1 = witnessRank ko7Adequacy
    exact ko7_distinction_witnessRank_eq_one.symm

/-- Licensed witness rank and language metadata are extensionally exact. -/
def licensedWitnessAdequacy : WitnessLanguageAdequacy licensedData where
  model := licensedWitnessModel
  language_kind_eq := rfl
  adequate_iff := by
    intro n
    simp [licensedData, baseAdequacy,
      WitnessLanguageModel.adequateAt, licensedWitnessModel]
  scope_grade_eq := by
    change 0 = witnessRank baseAdequacy
    exact baseAdequacy_rank_zero.symm

#check rawWitnessAdequacy
#check licensedWitnessAdequacy

end KWitness

namespace KAlternative

/-- An injective code on all three local nodes.  Restriction to either
terminal support is therefore injective. -/
def nodeCode : EqWBreakerNode → List Bool
  | .source => [false, false]
  | .reflVerdict => [false]
  | .diffVerdict => [true]

theorem nodeCode_injective : Function.Injective nodeCode := by
  intro x y h
  cases x <;> cases y <;> simp_all [nodeCode]

theorem raw_prefixFree :
    IsPrefixFree
      (fun x : {x // x ∈ SemanticScope.terminalSupport rawData.scope} =>
        nodeCode x.1) := by
  intro a b hab hp
  rcases a with ⟨a, ha⟩
  rcases b with ⟨b, hb⟩
  have ha' : a = .reflVerdict ∨ a = .diffVerdict := by
    rw [KTerminal.raw_terminalSupport_eq] at ha
    simpa using ha
  have hb' : b = .reflVerdict ∨ b = .diffVerdict := by
    rw [KTerminal.raw_terminalSupport_eq] at hb
    simpa using hb
  rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
  · exact hab rfl
  · simp [BitListPrefix, nodeCode] at hp
  · simp [BitListPrefix, nodeCode] at hp
  · exact hab rfl

theorem licensed_prefixFree :
    IsPrefixFree
      (fun x : {x // x ∈ SemanticScope.terminalSupport licensedData.scope} =>
        nodeCode x.1) := by
  intro a b hab _hp
  rcases a with ⟨a, ha⟩
  rcases b with ⟨b, hb⟩
  have ha' : a = .reflVerdict := by
    rw [KTerminal.licensed_terminalSupport_eq] at ha
    simpa using ha
  have hb' : b = .reflVerdict := by
    rw [KTerminal.licensed_terminalSupport_eq] at hb
    simpa using hb
  subst a
  subst b
  exact hab rfl

/-- Raw alternatives are exactly the two reachable terminal verdicts. -/
def rawAlternativeCarrier : AlternativeCarrier rawData where
  Alternative := {x // x ∈ SemanticScope.terminalSupport rawData.scope}
  alternativeFintype := inferInstance
  terminalEquiv := Equiv.refl _
  fixed_count_eq := by
    rw [Fintype.card_coe]
    change 2 = SemanticScope.terminalMultiplicity rawData.scope
    exact raw_terminalMultiplicity_exact.symm
  prefix_count_eq := by
    rw [Fintype.card_coe]
    change 2 = SemanticScope.terminalMultiplicity rawData.scope
    exact raw_terminalMultiplicity_exact.symm
  prefixCode := fun x => nodeCode x.1
  prefixCode_injective := by
    intro a b h
    apply Subtype.ext
    exact nodeCode_injective h
  prefixCode_prefixFree := raw_prefixFree

/-- Licensed alternatives are exactly the single surviving terminal verdict. -/
def licensedAlternativeCarrier : AlternativeCarrier licensedData where
  Alternative := {x // x ∈ SemanticScope.terminalSupport licensedData.scope}
  alternativeFintype := inferInstance
  terminalEquiv := Equiv.refl _
  fixed_count_eq := by
    rw [Fintype.card_coe]
    change 1 = SemanticScope.terminalMultiplicity licensedData.scope
    exact licensed_terminalMultiplicity_exact.symm
  prefix_count_eq := by
    rw [Fintype.card_coe]
    change 1 = SemanticScope.terminalMultiplicity licensedData.scope
    exact licensed_terminalMultiplicity_exact.symm
  prefixCode := fun x => nodeCode x.1
  prefixCode_injective := by
    intro a b h
    apply Subtype.ext
    exact nodeCode_injective h
  prefixCode_prefixFree := licensed_prefixFree

#print axioms nodeCode_injective
#print axioms raw_prefixFree
#print axioms licensed_prefixFree

end KAlternative

/-- Fully certified raw semantic model for the equality-witness cone. -/
def ko7RawSemanticAdequacy :
    SemanticAdequacyCertificate rawIdentityMorphism rawData where
  relationExact := by
    intro x y
    rfl
  normalizing := rawScope_normalizing
  defects := KDefect.rawDefectAdequacy
  repairs := KRepairSemantics.rawRepairSemantics
  witnesses := KWitness.rawWitnessAdequacy
  alternatives := KAlternative.rawAlternativeCarrier

/-- Fully certified licensed semantic model after the diagonal branch guard. -/
def ko7LicensedSemanticAdequacy :
    SemanticAdequacyCertificate licenseMorphism licensedData where
  relationExact := by
    intro x y
    rfl
  normalizing := licensedScope_normalizing
  defects := KDefect.licensedDefectAdequacy
  repairs := KRepairSemantics.licensedRepairSemantics
  witnesses := KWitness.licensedWitnessAdequacy
  alternatives := KAlternative.licensedAlternativeCarrier

/-- Non-vacuity: the raw certificate counts two actual terminal alternatives. -/
theorem ko7_raw_semantic_adequacy_fixture :
    Fintype.card ko7RawSemanticAdequacy.alternatives.Alternative = 2 := by
  rw [← SemanticAdequacyCertificate.terminalMultiplicity_eq_alternative_card
    ko7RawSemanticAdequacy]
  exact raw_terminalMultiplicity_exact

/-- Non-vacuity: the licensed certificate counts one actual terminal
alternative. -/
theorem ko7_licensed_semantic_adequacy_fixture :
    Fintype.card ko7LicensedSemanticAdequacy.alternatives.Alternative = 1 := by
  rw [← SemanticAdequacyCertificate.terminalMultiplicity_eq_alternative_card
    ko7LicensedSemanticAdequacy]
  exact licensed_terminalMultiplicity_exact

#check ko7RawSemanticAdequacy
#check ko7LicensedSemanticAdequacy
#check ko7_raw_semantic_adequacy_fixture
#check ko7_licensed_semantic_adequacy_fixture
#print axioms ko7_raw_semantic_adequacy_fixture
#print axioms ko7_licensed_semantic_adequacy_fixture

end
end KO7DistinctionAdapter
end OperatorKO7.Meta.LicensedBoundaryCalculus
