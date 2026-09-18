import OperatorKO7.Meta.LicensedBoundaryCalculus.Quantitative.SemanticAdequacyCertificate
import OperatorKO7.Meta.DistinctionBoundary.MinimalForkQuantitativeKO7Transport
import Mathlib.Data.List.OfFn

/-!
# Binary-fork profiles and transport

Relation: `Fork3Step` and its one-edge subrelation `Fork3LicensedStep`.
Closure: reflexive-transitive reachability at `Fork3.source`.
Strategy: both root exits, followed by deletion of the difference exit.
Trust: kernel proofs using the foundational axiom baseline.

Profiles transport with their construction data. The relation alone determines terminal
support, but not supplied repair prices. Witness grades here count binary identification
words for actual terminal states; they are not an external-comparator language.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile

open OperatorKO7.Meta.LicensedBoundaryCalculus
open OperatorKO7.Meta.DistinctionBoundary.Quantitative
open OperatorKO7.Meta.DistinctionBoundary.MinimalFork

universe u v w z

noncomputable section

local notation "ForkRelIso" => OperatorKO7.Meta.DistinctionBoundary.MinimalFork.RelIso
local notation "QNormalForm" => OperatorKO7.Meta.DistinctionBoundary.Quantitative.NormalForm

/-- Transport the relation and source; retain the declared audit metadata. -/
def transportScope {A : ARS.{u}} {B : ARS.{v}} (S : SemanticScope A)
    (R : B.Carrier → B.Carrier → Prop) (e : ForkRelIso S.relation R) : SemanticScope B where
  relation := R
  source := e.toEquiv S.source
  audit := S.audit
  normalization := S.normalization
  witnessLanguage := S.witnessLanguage
  witnessGrade := S.witnessGrade

/-- Transport one construction, including its costs, witnesses, and coding alternatives. -/
def transportData {A : ARS.{u}} {B : ARS.{v}}
    [Fintype A.Carrier] [Fintype B.Carrier]
    {D : Type w} {J : Type z} [DecidableEq D] [Fintype J] [DecidableEq J]
    (data : SemanticConstructionData A D J)
    (R : B.Carrier → B.Carrier → Prop) (e : ForkRelIso data.scope.relation R) :
    SemanticConstructionData B D J where
  scope := transportScope data.scope R e
  defects := data.defects
  closes := data.closes
  coverable := data.coverable
  actionCost := data.actionCost
  witnessAdequacy := data.witnessAdequacy
  fixedLengthAlternatives := data.fixedLengthAlternatives
  prefixCodeAlternatives := data.prefixCodeAlternatives

/-- Every coordinate is preserved by transport of the complete construction. -/
theorem semanticProfile_invariant_under_relationIso
    {A : ARS.{u}} {B : ARS.{v}} [Fintype A.Carrier] [Fintype B.Carrier]
    {D : Type w} {J : Type z} [DecidableEq D] [Fintype J] [DecidableEq J]
    (data : SemanticConstructionData A D J)
    (R : B.Carrier → B.Carrier → Prop) (e : ForkRelIso data.scope.relation R) :
    semanticProfile (transportData data R e) = semanticProfile data := by
  have hm : SemanticScope.terminalMultiplicity (transportScope data.scope R e) =
      SemanticScope.terminalMultiplicity data.scope :=
    (e.terminalMultiplicity_eq data.scope.source).symm
  apply SemanticProfile.ext
  · exact hm
  · change SemanticScope.terminalHartley? (transportScope data.scope R e) =
      SemanticScope.terminalHartley? data.scope
    simp only [SemanticScope.terminalHartley?, hm]
  all_goals rfl

theorem joinable_transport_iff {X : Type u} {Y : Type v}
    {R : X → X → Prop} {S : Y → Y → Prop} (e : ForkRelIso R S) {x y : X} :
    Joinable R x y ↔ Joinable S (e.toEquiv x) (e.toEquiv y) := by
  constructor
  · rintro ⟨z, hx, hy⟩
    exact ⟨e.toEquiv z, e.reach_map hx, e.reach_map hy⟩
  · rintro ⟨z, hx, hy⟩
    refine ⟨e.toEquiv.symm z, e.reach_iff.mpr ?_, e.reach_iff.mpr ?_⟩
    · simpa only [Equiv.apply_symm_apply] using hx
    · simpa only [Equiv.apply_symm_apply] using hy

theorem normalizing_transport {X : Type u} {Y : Type v}
    {R : X → X → Prop} {S : Y → Y → Prop} (e : ForkRelIso R S) {x : X}
    (hn : NormalizingAt R x) : NormalizingAt S (e.toEquiv x) := by
  intro y hy
  have hback : Reach R x (e.toEquiv.symm y) :=
    e.reach_iff.mpr (by simpa only [Equiv.apply_symm_apply] using hy)
  obtain ⟨z, hz, hnormal⟩ := hn _ hback
  refine ⟨e.toEquiv z, ?_, e.normalForm_iff.mp hnormal⟩
  simpa only [Equiv.apply_symm_apply] using e.reach_map hz

/-- The relation obtained by renaming both endpoints through a carrier equivalence. -/
def imageRelation {X : Type u} {Y : Type v} (e : X ≃ Y)
    (R : X → X → Prop) (x y : Y) : Prop := R (e.symm x) (e.symm y)

def imageRelationIso {X : Type u} {Y : Type v} (e : X ≃ Y)
    (R : X → X → Prop) : ForkRelIso R (imageRelation e R) where
  toEquiv := e
  map_rel_iff := by intros; simp only [imageRelation, Equiv.symm_apply_apply]

section CertificateTransport

variable {A : ARS.{u}} {B : ARS.{v}} [Fintype A.Carrier] [Fintype B.Carrier]
variable {D : Type w} {J : Type z} [DecidableEq D] [Fintype J] [DecidableEq J]
variable (data : SemanticConstructionData A D J)
variable (R : B.Carrier → B.Carrier → Prop) (e : ForkRelIso data.scope.relation R)

/-- Actual local peaks, including completeness and absence of duplicates, transport. -/
def transportDefectAdequacy (C : DefectAdequacy data) :
    DefectAdequacy (transportData data R e) where
  endpoints := fun d => (e.toEquiv (C.endpoints d).1, e.toEquiv (C.endpoints d).2)
  sound := by
    intro d hd
    obtain ⟨a, ha⟩ := C.sound d hd
    refine ⟨{ left := e.toEquiv a.left
              right := e.toEquiv a.right
              source_to_left := e.map_rel_iff.mp a.source_to_left
              source_to_right := e.map_rel_iff.mp a.source_to_right
              branches_not_joinable := fun h => a.branches_not_joinable
                ((joinable_transport_iff e).mpr h) }, ?_⟩
    simp only [ha]
  complete := by
    intro a
    let back : ActualLocalDefect data.scope :=
      { left := e.toEquiv.symm a.left
        right := e.toEquiv.symm a.right
        source_to_left := e.map_rel_iff.mpr (by
          simpa only [Equiv.apply_symm_apply] using a.source_to_left)
        source_to_right := e.map_rel_iff.mpr (by
          simpa only [Equiv.apply_symm_apply] using a.source_to_right)
        branches_not_joinable := by
          intro h
          apply a.branches_not_joinable
          simpa only [Equiv.apply_symm_apply] using (joinable_transport_iff e).mp h }
    obtain ⟨d, hd, heq⟩ := C.complete back
    refine ⟨d, hd, ?_⟩
    rcases heq with heq | heq
    · left
      simpa only [back, Equiv.apply_symm_apply] using
        congrArg (fun p => (e.toEquiv p.1, e.toEquiv p.2)) heq
    · right
      simpa only [back, Equiv.apply_symm_apply] using
        congrArg (fun p => (e.toEquiv p.1, e.toEquiv p.2)) heq
  irredundant := by
    intro d₁ d₂ h₁ h₂ heq
    apply C.irredundant d₁ d₂ h₁ h₂
    rcases heq with h | h
    · left
      exact Prod.ext (e.toEquiv.injective (congrArg Prod.fst h))
        (e.toEquiv.injective (congrArg Prod.snd h))
    · right
      exact Prod.ext (e.toEquiv.injective (congrArg Prod.fst h))
        (e.toEquiv.injective (congrArg Prod.snd h))

omit [Fintype B.Carrier] in
theorem peakResolved_image_iff (S : A.Carrier → A.Carrier → Prop) (a b c : A.Carrier) :
    PeakResolved (imageRelation e.toEquiv S) (e.toEquiv a) (e.toEquiv b) (e.toEquiv c) ↔
      PeakResolved S a b c := by
  have hj : Joinable S b c ↔
      Joinable (imageRelation e.toEquiv S) (e.toEquiv b) (e.toEquiv c) :=
    joinable_transport_iff (imageRelationIso e.toEquiv S)
  simp only [PeakResolved, imageRelation, Equiv.symm_apply_apply, ← hj]

/-- Repair actions preserve their coverage table and the actual protected/repaired relations. -/
def transportRepairSemantics {C : DefectAdequacy data} (rep : RepairSemantics data C) :
    RepairSemantics (transportData data R e) (transportDefectAdequacy data R e C) where
  repairedRelation := fun j => imageRelation e.toEquiv (rep.repairedRelation j)
  protectedRelation := imageRelation e.toEquiv rep.protectedRelation
  protected_sub_scope := by
    intro x y h
    simpa only [Equiv.apply_symm_apply] using e.map_rel_iff.mp (rep.protected_sub_scope h)
  repaired_sub_scope := by
    intro j x y h
    simpa only [Equiv.apply_symm_apply] using e.map_rel_iff.mp (rep.repaired_sub_scope j h)
  preserves_protected := by
    intro j x y h
    exact rep.preserves_protected j h
  closes_sound := by
    intro j d hd hc
    exact (peakResolved_image_iff data R e (rep.repairedRelation j) _ _ _).mpr
      (rep.closes_sound j d hd hc)
  closes_complete := by
    intro j d hd h
    exact rep.closes_complete j d hd
      ((peakResolved_image_iff data R e (rep.repairedRelation j) _ _ _).mp h)

def transportWitnessLanguageAdequacy (C : WitnessLanguageAdequacy data) :
    WitnessLanguageAdequacy (transportData data R e) where
  model := C.model
  language_kind_eq := C.language_kind_eq
  adequate_iff := C.adequate_iff
  scope_grade_eq := C.scope_grade_eq

/-- Alternatives are identified with transported terminal states by the proved support equivalence. -/
def transportAlternativeCarrier (C : AlternativeCarrier data) :
    AlternativeCarrier (transportData data R e) where
  Alternative := C.Alternative
  alternativeFintype := C.alternativeFintype
  terminalEquiv := C.terminalEquiv.trans (e.terminalSupportEquiv data.scope.source)
  fixed_count_eq := C.fixed_count_eq
  prefix_count_eq := C.prefix_count_eq
  prefixCode := C.prefixCode
  prefixCode_injective := C.prefixCode_injective
  prefixCode_prefixFree := C.prefixCode_prefixFree

end CertificateTransport

/-- The whole semantic certificate, not only its numeric profile, transports. -/
def transportSemanticAdequacy
    {A : ARS.{u}} {B : ARS.{v}} {A' B' : ARS}
    [Fintype A.Carrier] [Fintype B.Carrier] [Fintype A'.Carrier] [Fintype B'.Carrier]
    {D : Type w} {J : Type z} [DecidableEq D] [Fintype J] [DecidableEq J]
    {F : PartialLicensedReductionMorphism A A'}
    {data : SemanticConstructionData A D J} (C : SemanticAdequacyCertificate F data)
    (G : PartialLicensedReductionMorphism B B') (e : ForkRelIso data.scope.relation G.admitted) :
    SemanticAdequacyCertificate G (transportData data G.admitted e) where
  relationExact := fun _ _ => Iff.rfl
  normalizing := normalizing_transport e C.normalizing
  defects := transportDefectAdequacy data G.admitted e C.defects
  repairs := transportRepairSemantics data G.admitted e C.repairs
  witnesses := transportWitnessLanguageAdequacy data G.admitted e C.witnesses
  alternatives := transportAlternativeCarrier data G.admitted e C.alternatives

/-- A grade contains an injective binary word assignment, not a stipulated threshold. -/
def binaryWitnessAdequacy (E : Type u) [Fintype E] : GradedAdequacy where
  adequate := fun n => Nonempty (E ↪ BitWord n)
  upward := by
    intro i j hij hi
    obtain ⟨f⟩ := hi
    apply Function.Embedding.nonempty_of_card_le
    rw [bitWord_card]
    have h := Fintype.card_le_of_embedding f
    rw [bitWord_card] at h
    exact h.trans (Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) hij)
  inhabited := by
    refine ⟨Nat.clog 2 (Fintype.card E), Function.Embedding.nonempty_of_card_le ?_⟩
    rw [bitWord_card]
    exact (Nat.le_pow_iff_clog_le (by decide : 1 < (2 : Nat))).2 le_rfl

/-- The minimum grade equals the optimal fixed-length binary capacity for every finite type. -/
theorem binaryWitnessAdequacy_rank (E : Type u) [Fintype E] :
    witnessRank (binaryWitnessAdequacy E) = Nat.clog 2 (Fintype.card E) := by
  apply le_antisymm
  · apply witnessRank_le_of_adequate
    apply Function.Embedding.nonempty_of_card_le
    rw [bitWord_card]
    exact (Nat.le_pow_iff_clog_le (by decide : 1 < (2 : Nat))).2 le_rfl
  · obtain ⟨f⟩ := witnessRank_adequate (binaryWitnessAdequacy E)
    apply (Nat.le_pow_iff_clog_le (by decide : 1 < (2 : Nat))).1
    simpa only [bitWord_card] using Fintype.card_le_of_embedding f

def forkARS : ARS where
  Carrier := Fork3
  step := Fork3Step
  scope :=
    { location := .root
      closure := .reflexiveTransitive
      admission := .full
      layer := .original }

instance forkARS_fintype : Fintype forkARS.Carrier := inferInstanceAs (Fintype Fork3)

def rawScope : SemanticScope forkARS :=
  SemanticScope.raw forkARS .source .local .base 1

def licensedScope : SemanticScope forkARS where
  relation := Fork3LicensedStep
  source := .source
  audit := { forkARS.scope with admission := .guarded }
  normalization := .local
  witnessLanguage := .licensed
  witnessGrade := 0

def rawCloses (_ : Fin 1) : Finset (Fin 1) := Finset.univ

theorem raw_coverable : IsRepairCover Finset.univ rawCloses Finset.univ := by
  intro d _
  exact Finset.mem_biUnion.mpr ⟨0, Finset.mem_univ _, Finset.mem_univ _⟩

def licensedCloses (_ : Fin 1) : Finset (Fin 1) := ∅

theorem licensed_coverable :
    IsRepairCover (∅ : Finset (Fin 1)) licensedCloses Finset.univ := by
  intro d hd
  simp at hd

/-- Alternative counts and witness types are computed from the reachable terminal support. -/
def rawData (cost : Nat) : SemanticConstructionData forkARS (Fin 1) (Fin 1) where
  scope := rawScope
  defects := Finset.univ
  closes := rawCloses
  coverable := raw_coverable
  actionCost := fun _ => cost
  witnessAdequacy := binaryWitnessAdequacy {x // x ∈ terminalSupport Fork3Step .source}
  fixedLengthAlternatives := terminalMultiplicity Fork3Step .source
  prefixCodeAlternatives := terminalMultiplicity Fork3Step .source

def licensedData (cost : Nat) : SemanticConstructionData forkARS (Fin 1) (Fin 1) where
  scope := licensedScope
  defects := ∅
  closes := licensedCloses
  coverable := licensed_coverable
  actionCost := fun _ => cost
  witnessAdequacy := binaryWitnessAdequacy
    {x // x ∈ terminalSupport Fork3LicensedStep .source}
  fixedLengthAlternatives := terminalMultiplicity Fork3LicensedStep .source
  prefixCodeAlternatives := terminalMultiplicity Fork3LicensedStep .source

theorem raw_repairCandidates_exact :
    repairCandidates (Finset.univ : Finset (Fin 1)) rawCloses = {Finset.univ} := by
  classical
  ext chosen
  rw [mem_repairCandidates_iff, Finset.mem_singleton]
  constructor
  · intro hc
    have hm := hc (Finset.mem_univ (0 : Fin 1))
    obtain ⟨a, ha, _⟩ := Finset.mem_biUnion.mp hm
    apply Finset.eq_univ_of_forall
    intro b
    simpa only [Subsingleton.elim b a] using ha
  · rintro rfl
    exact raw_coverable

theorem raw_repair_cover_exact : repairCoverNumber Finset.univ rawCloses raw_coverable = 1 := by
  simp only [repairCoverNumber, raw_repairCandidates_exact, Finset.inf'_singleton]
  decide

theorem raw_repair_cost_exact (cost : Nat) :
    minimumRepairCoverCost Finset.univ rawCloses (fun _ => cost) raw_coverable = cost := by
  simp only [minimumRepairCoverCost, raw_repairCandidates_exact, Finset.inf'_singleton]
  simp [repairCoverCost]

def rawExactProfile (cost : Nat) : SemanticProfile where
  terminalMultiplicity := 2
  terminalHartley := some 1
  criticalPairDefect := 1
  minimumRepairCover := 1
  minimumRepairCost := cost
  witnessRank := 1
  fixedLengthCertificateFloor := 1
  prefixCodeCertificateFloor := 1

def licensedExactProfile : SemanticProfile where
  terminalMultiplicity := 1
  terminalHartley := some 0
  criticalPairDefect := 0
  minimumRepairCover := 0
  minimumRepairCost := 0
  witnessRank := 0
  fixedLengthCertificateFloor := 0
  prefixCodeCertificateFloor := 0

theorem raw_binaryWitness_rank :
    witnessRank (binaryWitnessAdequacy {x // x ∈ terminalSupport Fork3Step .source}) = 1 := by
  rw [binaryWitnessAdequacy_rank, Fintype.card_coe]
  change Nat.clog 2 (terminalMultiplicity Fork3Step .source) = 1
  rw [fork3_raw_terminalMultiplicity_eq_two]
  norm_num [Nat.clog]

theorem licensed_binaryWitness_rank :
    witnessRank (binaryWitnessAdequacy
      {x // x ∈ terminalSupport Fork3LicensedStep .source}) = 0 := by
  rw [binaryWitnessAdequacy_rank, Fintype.card_coe]
  change Nat.clog 2 (terminalMultiplicity Fork3LicensedStep .source) = 0
  rw [fork3_licensed_terminalMultiplicity_eq_one]
  norm_num [Nat.clog]

theorem binaryFork_raw_profile_exact (cost : Nat) :
    semanticProfile (rawData cost) = rawExactProfile cost := by
  apply SemanticProfile.ext
  · exact fork3_raw_terminalMultiplicity_eq_two
  · change SemanticScope.terminalHartley? rawScope = some 1
    rw [SemanticScope.terminalHartley?_eq_some_of_normalizingAt
      rawScope fork3_raw_normalizingAt_source]
    exact congrArg some fork3_raw_terminalHartleyEntropy_eq_one
  · change (Finset.univ : Finset (Fin 1)).card = 1
    decide
  · exact raw_repair_cover_exact
  · exact raw_repair_cost_exact cost
  · exact raw_binaryWitness_rank
  · change Nat.clog 2 (terminalMultiplicity Fork3Step .source) = 1
    rw [fork3_raw_terminalMultiplicity_eq_two]
    norm_num [Nat.clog]
  · change Nat.clog 2 (terminalMultiplicity Fork3Step .source) = 1
    rw [fork3_raw_terminalMultiplicity_eq_two]
    norm_num [Nat.clog]

theorem binaryFork_licensed_profile_exact (cost : Nat) :
    semanticProfile (licensedData cost) = licensedExactProfile := by
  apply SemanticProfile.ext
  · exact fork3_licensed_terminalMultiplicity_eq_one
  · change SemanticScope.terminalHartley? licensedScope = some 0
    rw [SemanticScope.terminalHartley?_eq_some_of_normalizingAt
      licensedScope fork3_licensed_normalizingAt_source]
    exact congrArg some fork3_licensed_terminalHartleyEntropy_eq_zero
  · rfl
  · exact repairCoverNumber_empty_eq_zero licensedCloses licensed_coverable
  · exact minimumRepairCoverCost_empty_eq_zero licensedCloses (fun _ => cost)
      licensed_coverable
  · exact licensed_binaryWitness_rank
  · change Nat.clog 2 (terminalMultiplicity Fork3LicensedStep .source) = 0
    rw [fork3_licensed_terminalMultiplicity_eq_one]
    norm_num [Nat.clog]
  · change Nat.clog 2 (terminalMultiplicity Fork3LicensedStep .source) = 0
    rw [fork3_licensed_terminalMultiplicity_eq_one]
    norm_num [Nat.clog]

/-- Unit-cost repair reduces each natural coordinate by one and Hartley support from one to zero. -/
theorem binaryFork_profile_drop_exact :
    semanticProfile (rawData 1) = rawExactProfile 1 ∧
      semanticProfile (licensedData 1) = licensedExactProfile :=
  ⟨binaryFork_raw_profile_exact 1, binaryFork_licensed_profile_exact 1⟩

/-- Changing the price changes the profile without changing any relation, source, or witness. -/
theorem raw_profile_cost_injective :
    Function.Injective (fun cost => semanticProfile (rawData cost)) := by
  intro c d h
  have hc := congrArg SemanticProfile.minimumRepairCost h
  simpa only [binaryFork_raw_profile_exact, rawExactProfile] using hc

theorem same_relation_different_repair_cost_profiles :
    (rawData 0).scope = (rawData 1).scope ∧
      semanticProfile (rawData 0) ≠ semanticProfile (rawData 1) :=
  ⟨rfl, fun h => Nat.zero_ne_one (raw_profile_cost_injective h)⟩

/-- The raw and licensed relations use one carrier equivalence and the same source. -/
structure BinaryForkPresentation (A : ARS.{u}) where
  rawIso : ForkRelIso Fork3Step A.step
  licensed : A.Carrier → A.Carrier → Prop
  licensed_iff : ∀ {x y}, Fork3LicensedStep x y ↔
    licensed (rawIso.toEquiv x) (rawIso.toEquiv y)

def BinaryForkPresentation.licensedIso {A : ARS.{u}} (P : BinaryForkPresentation A) :
    ForkRelIso Fork3LicensedStep P.licensed where
  toEquiv := P.rawIso.toEquiv
  map_rel_iff := P.licensed_iff

def BinaryForkPresentation.rawData {A : ARS.{u}} [Fintype A.Carrier]
    (P : BinaryForkPresentation A) (cost : Nat) :
    SemanticConstructionData A (Fin 1) (Fin 1) :=
  transportData (BinaryForkExactProfile.rawData cost) A.step P.rawIso

def BinaryForkPresentation.licensedData {A : ARS.{u}} [Fintype A.Carrier]
    (P : BinaryForkPresentation A) (cost : Nat) :
    SemanticConstructionData A (Fin 1) (Fin 1) :=
  transportData (BinaryForkExactProfile.licensedData cost) P.licensed P.licensedIso

/-- All represented binary forks have these profiles, for every declared repair price. -/
theorem binaryForkPresentation_profile_drop_exact {A : ARS.{u}} [Fintype A.Carrier]
    (P : BinaryForkPresentation A) (cost : Nat) :
    semanticProfile (P.rawData cost) = rawExactProfile cost ∧
      semanticProfile (P.licensedData cost) = licensedExactProfile := by
  constructor
  · exact (semanticProfile_invariant_under_relationIso (rawData cost) A.step P.rawIso).trans
      (binaryFork_raw_profile_exact cost)
  · exact (semanticProfile_invariant_under_relationIso (licensedData cost)
      P.licensed P.licensedIso).trans (binaryFork_licensed_profile_exact cost)

def canonicalPresentation : BinaryForkPresentation forkARS where
  rawIso := { toEquiv := Equiv.refl _, map_rel_iff := Iff.rfl }
  licensed := Fork3LicensedStep
  licensed_iff := Iff.rfl

/-- Finiteness is supplied by the presentation itself. -/
def BinaryForkPresentation.fintype {A : ARS.{u}} (P : BinaryForkPresentation A) :
    Fintype A.Carrier := Fintype.ofEquiv Fork3 P.rawIso.toEquiv

theorem binaryForkPresentation_profile_exact_unconditional {A : ARS.{u}}
    (P : BinaryForkPresentation A) (cost : Nat) :
    letI : Fintype A.Carrier := P.fintype
    semanticProfile (P.rawData cost) = rawExactProfile cost ∧
      semanticProfile (P.licensedData cost) = licensedExactProfile := by
  letI : Fintype A.Carrier := P.fintype
  exact binaryForkPresentation_profile_drop_exact P cost

/-! ## The profile fields denote actual defects, repairs, and witnesses -/

def rawDefectAdequacy (cost : Nat) : DefectAdequacy (rawData cost) where
  endpoints := fun _ => (.equal, .different)
  sound := by
    intro _ _
    refine ⟨{ left := .equal
              right := .different
              source_to_left := Fork3Step.toEqual
              source_to_right := Fork3Step.toDifferent
              branches_not_joinable := fork3_verdicts_unjoinable }, rfl⟩
  complete := by
    rintro ⟨left, right, hl, hr, hn⟩
    cases hl <;> cases hr
    · exact (hn ⟨_, reach_refl _, reach_refl _⟩).elim
    · exact ⟨0, Finset.mem_univ _, Or.inl rfl⟩
    · exact ⟨0, Finset.mem_univ _, Or.inr rfl⟩
    · exact (hn ⟨_, reach_refl _, reach_refl _⟩).elim
  irredundant := fun _ _ _ _ _ => Subsingleton.elim _ _

def licensedDefectAdequacy (cost : Nat) : DefectAdequacy (licensedData cost) where
  endpoints := fun _ => (.equal, .different)
  sound := by
    intro d hd
    simp [licensedData] at hd
  complete := by
    rintro ⟨left, right, hl, hr, hn⟩
    cases hl
    cases hr
    exact (hn ⟨_, reach_refl _, reach_refl _⟩).elim
  irredundant := fun _ _ _ _ _ => Subsingleton.elim _ _

def rawRepairSemantics (cost : Nat) :
    RepairSemantics (rawData cost) (rawDefectAdequacy cost) where
  repairedRelation := fun _ => Fork3LicensedStep
  protectedRelation := Fork3LicensedStep
  protected_sub_scope := by
    intro x y h
    exact fork3Licensed_sub_raw h
  repaired_sub_scope := by
    intro a x y h
    exact fork3Licensed_sub_raw h
  preserves_protected := by
    intro a x y h
    exact h
  closes_sound := by
    intro a d _ _
    exact RepairSemantics.peakResolved_of_not_right (fun h => by cases h)
  closes_complete := fun _ _ _ _ => Finset.mem_univ _

def licensedRepairSemantics (cost : Nat) :
    RepairSemantics (licensedData cost) (licensedDefectAdequacy cost) where
  repairedRelation := fun _ => Fork3LicensedStep
  protectedRelation := Fork3LicensedStep
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

/-- A witness stores its word length and a proved injective code at that length. -/
def binaryWitnessModel (E : Type u) [Fintype E] (kind : WitnessLanguageKind) :
    WitnessLanguageModel where
  Witness := Σ n : Nat, E ↪ BitWord n
  kind := kind
  grade := Sigma.fst
  adequateWitness := fun _ => True
  inhabited := by
    obtain ⟨n, ⟨f⟩⟩ := (binaryWitnessAdequacy E).inhabited
    exact ⟨⟨n, f⟩, trivial⟩

theorem binaryWitnessModel_adequate_iff (E : Type u) [Fintype E]
    (kind : WitnessLanguageKind) (n : Nat) :
    (binaryWitnessAdequacy E).adequate n ↔ (binaryWitnessModel E kind).adequateAt n := by
  constructor
  · rintro ⟨f⟩
    exact ⟨⟨n, f⟩, trivial, le_rfl⟩
  · rintro ⟨⟨k, f⟩, _, hkn⟩
    exact (binaryWitnessAdequacy E).upward hkn ⟨f⟩

def rawWitnessLanguageAdequacy (cost : Nat) : WitnessLanguageAdequacy (rawData cost) where
  model := binaryWitnessModel {x // x ∈ terminalSupport Fork3Step .source} .base
  language_kind_eq := rfl
  adequate_iff := binaryWitnessModel_adequate_iff _ .base
  scope_grade_eq := raw_binaryWitness_rank.symm

def licensedWitnessLanguageAdequacy (cost : Nat) :
    WitnessLanguageAdequacy (licensedData cost) where
  model := binaryWitnessModel {x // x ∈ terminalSupport Fork3LicensedStep .source} .licensed
  language_kind_eq := rfl
  adequate_iff := binaryWitnessModel_adequate_iff _ .licensed
  scope_grade_eq := licensed_binaryWitness_rank.symm

/-- Every finite alternative type has a minimum-length injective binary code. -/
def optimalBinaryCode (E : Type u) [Fintype E] : E ↪ BitWord (Nat.clog 2 (Fintype.card E)) :=
  Classical.choice (Function.Embedding.nonempty_of_card_le (by
    rw [bitWord_card]
    exact (Nat.le_pow_iff_clog_le (by decide : 1 < (2 : Nat))).2 le_rfl))

def decodeBinaryCode (E : Type u) [Fintype E]
    (word : BitWord (Nat.clog 2 (Fintype.card E))) : Option E :=
  if h : ∃ x, optimalBinaryCode E x = word then some (Classical.choose h) else none

theorem decodeBinaryCode_encode (E : Type u) [Fintype E] (x : E) :
    decodeBinaryCode E (optimalBinaryCode E x) = some x := by
  unfold decodeBinaryCode
  rw [dif_pos ⟨x, rfl⟩]
  congr 1
  exact (optimalBinaryCode E).injective (Classical.choose_spec
    (show ∃ z : E, optimalBinaryCode E z = optimalBinaryCode E x from ⟨x, rfl⟩))

def transportedBinaryCode {E : Type u} {F : Type v} [Fintype E]
    (e : E ≃ F) (y : F) : BitWord (Nat.clog 2 (Fintype.card E)) :=
  optimalBinaryCode E (e.symm y)

def transportedBinaryDecode {E : Type u} {F : Type v} [Fintype E]
    (e : E ≃ F) (word : BitWord (Nat.clog 2 (Fintype.card E))) : Option F :=
  (decodeBinaryCode E word).map e

theorem transportedBinaryCode_eq_iff {E : Type u} {F : Type v} [Fintype E]
    (e : E ≃ F) (x y : F) : transportedBinaryCode e x = transportedBinaryCode e y ↔ x = y := by
  constructor
  · intro h
    exact e.symm.injective ((optimalBinaryCode E).injective h)
  · rintro rfl
    rfl

theorem transportedBinaryDecode_encode {E : Type u} {F : Type v} [Fintype E]
    (e : E ≃ F) (y : F) :
    transportedBinaryDecode e (transportedBinaryCode e y) = some y := by
  simp only [transportedBinaryDecode, transportedBinaryCode, decodeBinaryCode_encode,
    Option.map_some, Equiv.apply_symm_apply]

def optimalPrefixCode (E : Type u) [Fintype E] (x : E) : List Bool :=
  List.ofFn (optimalBinaryCode E x)

theorem optimalPrefixCode_injective (E : Type u) [Fintype E] :
    Function.Injective (optimalPrefixCode E) := by
  intro x y h
  exact (optimalBinaryCode E).injective (List.ofFn_injective h)

theorem optimalPrefixCode_prefixFree (E : Type u) [Fintype E] :
    IsPrefixFree (optimalPrefixCode E) := by
  intro a b hab hprefix
  obtain ⟨suffix, heq⟩ := hprefix
  have hlen := congrArg List.length heq
  simp only [List.length_append, optimalPrefixCode, List.length_ofFn] at hlen
  have hempty : suffix = [] := List.length_eq_zero_iff.mp (by omega)
  subst suffix
  simp only [List.append_nil] at heq
  exact hab (optimalPrefixCode_injective E heq)

def rawAlternativeCarrier (cost : Nat) : AlternativeCarrier (rawData cost) where
  Alternative := {x // x ∈ terminalSupport Fork3Step .source}
  alternativeFintype := inferInstance
  terminalEquiv := Equiv.refl _
  fixed_count_eq := by simp only [Fintype.card_coe]; rfl
  prefix_count_eq := by simp only [Fintype.card_coe]; rfl
  prefixCode := optimalPrefixCode _
  prefixCode_injective := optimalPrefixCode_injective _
  prefixCode_prefixFree := optimalPrefixCode_prefixFree _

def licensedAlternativeCarrier (cost : Nat) : AlternativeCarrier (licensedData cost) where
  Alternative := {x // x ∈ terminalSupport Fork3LicensedStep .source}
  alternativeFintype := inferInstance
  terminalEquiv := Equiv.refl _
  fixed_count_eq := by simp only [Fintype.card_coe]; rfl
  prefix_count_eq := by simp only [Fintype.card_coe]; rfl
  prefixCode := optimalPrefixCode _
  prefixCode_injective := optimalPrefixCode_injective _
  prefixCode_prefixFree := optimalPrefixCode_prefixFree _

def rawMorphism : PartialLicensedReductionMorphism forkARS forkARS :=
  PartialLicensedReductionMorphism.id forkARS

def licenseMorphism : PartialLicensedReductionMorphism forkARS forkARS where
  domain := fun _ => True
  admitted := Fork3LicensedStep
  admitted_sub_raw := by
    intro x y h
    exact fork3Licensed_sub_raw h
  admitted_source_domain := fun _ => trivial
  admitted_target_domain := fun _ => trivial
  map := Subtype.val
  map_step := by
    intro x y h
    exact fork3Licensed_sub_raw h

def rawSemanticAdequacy (cost : Nat) :
    SemanticAdequacyCertificate rawMorphism (rawData cost) where
  relationExact := fun _ _ => Iff.rfl
  normalizing := fork3_raw_normalizingAt_source
  defects := rawDefectAdequacy cost
  repairs := rawRepairSemantics cost
  witnesses := rawWitnessLanguageAdequacy cost
  alternatives := rawAlternativeCarrier cost

def licensedSemanticAdequacy (cost : Nat) :
    SemanticAdequacyCertificate licenseMorphism (licensedData cost) where
  relationExact := fun _ _ => Iff.rfl
  normalizing := fork3_licensed_normalizingAt_source
  defects := licensedDefectAdequacy cost
  repairs := licensedRepairSemantics cost
  witnesses := licensedWitnessLanguageAdequacy cost
  alternatives := licensedAlternativeCarrier cost

theorem BinaryForkPresentation.licensed_sub_raw {A : ARS.{u}}
    (P : BinaryForkPresentation A) {x y : A.Carrier} (h : P.licensed x y) : A.step x y := by
  have hback : Fork3LicensedStep (P.rawIso.toEquiv.symm x) (P.rawIso.toEquiv.symm y) :=
    P.licensedIso.map_rel_iff.mpr (by
      simpa only [BinaryForkPresentation.licensedIso, Equiv.apply_symm_apply] using h)
  simpa only [Equiv.apply_symm_apply] using
    P.rawIso.map_rel_iff.mp (fork3Licensed_sub_raw hback)

def BinaryForkPresentation.rawMorphism {A : ARS.{u}} (_P : BinaryForkPresentation A) :
    PartialLicensedReductionMorphism A A := PartialLicensedReductionMorphism.id A

def BinaryForkPresentation.licenseMorphism {A : ARS.{u}} (P : BinaryForkPresentation A) :
    PartialLicensedReductionMorphism A A where
  domain := fun _ => True
  admitted := P.licensed
  admitted_sub_raw := P.licensed_sub_raw
  admitted_source_domain := fun _ => trivial
  admitted_target_domain := fun _ => trivial
  map := Subtype.val
  map_step := by
    intro x y h
    exact P.licensed_sub_raw h

/-- Both represented relations carry transported defects, repairs, codes, and normalization proofs. -/
def BinaryForkPresentation.rawSemanticAdequacy {A : ARS.{u}} [Fintype A.Carrier]
    (P : BinaryForkPresentation A) (cost : Nat) :
    SemanticAdequacyCertificate P.rawMorphism (P.rawData cost) :=
  transportSemanticAdequacy (BinaryForkExactProfile.rawSemanticAdequacy cost)
    P.rawMorphism P.rawIso

def BinaryForkPresentation.licensedSemanticAdequacy {A : ARS.{u}} [Fintype A.Carrier]
    (P : BinaryForkPresentation A) (cost : Nat) :
    SemanticAdequacyCertificate P.licenseMorphism (P.licensedData cost) :=
  transportSemanticAdequacy (BinaryForkExactProfile.licensedSemanticAdequacy cost)
    P.licenseMorphism P.licensedIso

theorem binaryForkPresentation_certified_profiles {A : ARS.{u}}
    (P : BinaryForkPresentation A) (cost : Nat) :
    letI : Fintype A.Carrier := P.fintype
    Nonempty (SemanticAdequacyCertificate.{u, u, 0, 0, 0, 0}
      P.rawMorphism (P.rawData cost)) ∧
    Nonempty (SemanticAdequacyCertificate.{u, u, 0, 0, 0, 0}
      P.licenseMorphism (P.licensedData cost)) ∧
    semanticProfile (P.rawData cost) = rawExactProfile cost ∧
    semanticProfile (P.licensedData cost) = licensedExactProfile := by
  letI : Fintype A.Carrier := P.fintype
  exact ⟨⟨P.rawSemanticAdequacy cost⟩, ⟨P.licensedSemanticAdequacy cost⟩,
    binaryForkPresentation_profile_drop_exact P cost⟩

/-- The same relation and complete semantic certificates permit different declared prices. -/
theorem certified_same_relation_different_prices :
    Nonempty (SemanticAdequacyCertificate.{0, 0, 0, 0, 0, 0} rawMorphism (rawData 0)) ∧
      Nonempty (SemanticAdequacyCertificate.{0, 0, 0, 0, 0, 0} rawMorphism (rawData 1)) ∧
      (rawData 0).scope = (rawData 1).scope ∧
      semanticProfile (rawData 0) ≠ semanticProfile (rawData 1) :=
  ⟨⟨rawSemanticAdequacy 0⟩, ⟨rawSemanticAdequacy 1⟩,
    same_relation_different_repair_cost_profiles⟩

/-! ## Finite closed parts of arbitrary ambient systems -/

/-- Every ambient successor of an image point remains in the image. -/
structure ClosedRelationEmbedding {X : Type u} {Y : Type v}
    (R : X → X → Prop) (S : Y → Y → Prop) where
  map : X ↪ Y
  step_iff : ∀ {x y}, R x y ↔ S (map x) (map y)
  forward_closed : ∀ {x y}, S (map x) y → ∃ z, map z = y

theorem ClosedRelationEmbedding.steps_map {X : Type u} {Y : Type v}
    {R : X → X → Prop} {S : Y → Y → Prop} (e : ClosedRelationEmbedding R S)
    {n x y} (h : Steps R n x y) : Steps S n (e.map x) (e.map y) := by
  induction h with
  | zero => exact Steps.zero _
  | succ hs ht ih => exact Steps.succ (e.step_iff.mp hs) ih

theorem ClosedRelationEmbedding.steps_pull {X : Type u} {Y : Type v}
    {R : X → X → Prop} {S : Y → Y → Prop} (e : ClosedRelationEmbedding R S)
    {n : Nat} {x : X} {y : Y} (h : Steps S n (e.map x) y) :
    ∃ z, e.map z = y ∧ Steps R n x z := by
  induction n generalizing x y with
  | zero =>
      cases h
      exact ⟨x, rfl, Steps.zero _⟩
  | succ n ih =>
      cases h with
      | succ hs ht =>
          obtain ⟨m, rfl⟩ := e.forward_closed hs
          obtain ⟨z, hz, hrest⟩ := ih ht
          exact ⟨z, hz, Steps.succ (e.step_iff.mpr hs) hrest⟩

theorem ClosedRelationEmbedding.reach_map {X : Type u} {Y : Type v}
    {R : X → X → Prop} {S : Y → Y → Prop} (e : ClosedRelationEmbedding R S)
    {x y} (h : Reach R x y) : Reach S (e.map x) (e.map y) := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, e.steps_map hn⟩

theorem ClosedRelationEmbedding.reach_pull {X : Type u} {Y : Type v}
    {R : X → X → Prop} {S : Y → Y → Prop} (e : ClosedRelationEmbedding R S)
    {x : X} {y : Y} (h : Reach S (e.map x) y) :
    ∃ z, e.map z = y ∧ Reach R x z := by
  obtain ⟨n, hn⟩ := h
  obtain ⟨z, hz, hr⟩ := e.steps_pull hn
  exact ⟨z, hz, n, hr⟩

theorem ClosedRelationEmbedding.normalForm_iff {X : Type u} {Y : Type v}
    {R : X → X → Prop} {S : Y → Y → Prop} (e : ClosedRelationEmbedding R S) (x : X) :
    QNormalForm R x ↔ QNormalForm S (e.map x) := by
  constructor
  · intro hn y hy
    obtain ⟨z, rfl⟩ := e.forward_closed hy
    exact hn z (e.step_iff.mpr hy)
  · intro hn y hy
    exact hn _ (e.step_iff.mp hy)

/-- The ambient carrier need not be finite; only the represented terminal support is finite. -/
def ClosedRelationEmbedding.terminalEquiv {X : Type u} {Y : Type v} [Fintype X]
    {R : X → X → Prop} {S : Y → Y → Prop} (e : ClosedRelationEmbedding R S) (x : X) :
    {z // z ∈ terminalSupport R x} ≃ {y // Reach S (e.map x) y ∧ QNormalForm S y} where
  toFun z := ⟨e.map z.1, e.reach_map (mem_terminalSupport.mp z.2).1,
    (e.normalForm_iff z.1).mp (mem_terminalSupport.mp z.2).2⟩
  invFun y :=
    let h := e.reach_pull y.2.1
    ⟨Classical.choose h, mem_terminalSupport.mpr
      ⟨(Classical.choose_spec h).2, (e.normalForm_iff _).mpr
        ((Classical.choose_spec h).1.symm ▸ y.2.2)⟩⟩
  left_inv z := by
    apply Subtype.ext
    apply e.map.injective
    exact (Classical.choose_spec (e.reach_pull (e.reach_map (mem_terminalSupport.mp z.2).1))).1
  right_inv y := by
    apply Subtype.ext
    exact (Classical.choose_spec (e.reach_pull y.2.1)).1

def ClosedRelationEmbedding.terminalFintype {X : Type u} {Y : Type v} [Fintype X]
    {R : X → X → Prop} {S : Y → Y → Prop} (e : ClosedRelationEmbedding R S) (x : X) :
    Fintype {y // Reach S (e.map x) y ∧ QNormalForm S y} :=
  Fintype.ofEquiv _ (e.terminalEquiv x)

theorem ClosedRelationEmbedding.terminal_card {X : Type u} {Y : Type v} [Fintype X]
    {R : X → X → Prop} {S : Y → Y → Prop} (e : ClosedRelationEmbedding R S) (x : X) :
    letI := e.terminalFintype x
    Fintype.card {y // Reach S (e.map x) y ∧ QNormalForm S y} = terminalMultiplicity R x := by
  letI := e.terminalFintype x
  have h := Fintype.card_congr (e.terminalEquiv x)
  simpa only [Fintype.card_coe, terminalMultiplicity] using h.symm

/-- One closed binary fork inside an arbitrary system, with an edge-restricting repair. -/
structure AmbientBinaryFork (A : ARS.{u}) where
  raw : ClosedRelationEmbedding Fork3Step A.step
  licensed : A.Carrier → A.Carrier → Prop
  licensed_iff : ∀ {x y}, Fork3LicensedStep x y ↔ licensed (raw.map x) (raw.map y)
  licensed_sub_raw : ∀ {x y}, licensed x y → A.step x y

def AmbientBinaryFork.licensedEmbedding {A : ARS.{u}} (P : AmbientBinaryFork A) :
    ClosedRelationEmbedding Fork3LicensedStep P.licensed where
  map := P.raw.map
  step_iff := P.licensed_iff
  forward_closed := fun h => P.raw.forward_closed (P.licensed_sub_raw h)

/-- The restricted system uses finite point names; its steps are the ambient steps. -/
def AmbientBinaryFork.localARS {A : ARS.{u}} (P : AmbientBinaryFork A) : ARS where
  Carrier := Fork3
  step := fun x y => A.step (P.raw.map x) (P.raw.map y)
  scope := A.scope

instance AmbientBinaryFork.localFintype {A : ARS.{u}} (P : AmbientBinaryFork A) :
    Fintype P.localARS.Carrier := inferInstanceAs (Fintype Fork3)

def AmbientBinaryFork.presentation {A : ARS.{u}} (P : AmbientBinaryFork A) :
    BinaryForkPresentation P.localARS where
  rawIso := { toEquiv := Equiv.refl _, map_rel_iff := P.raw.step_iff }
  licensed := fun x y => P.licensed (P.raw.map x) (P.raw.map y)
  licensed_iff := P.licensed_iff

theorem ambientBinaryFork_profile_exact {A : ARS.{u}} (P : AmbientBinaryFork A) (cost : Nat) :
    semanticProfile (P.presentation.rawData cost) = rawExactProfile cost ∧
    semanticProfile (P.presentation.licensedData cost) = licensedExactProfile :=
  binaryForkPresentation_profile_drop_exact P.presentation cost

theorem ambientBinaryFork_terminal_counts {A : ARS.{u}} (P : AmbientBinaryFork A) :
    letI := P.raw.terminalFintype .source
    letI : Fintype {y // Reach P.licensed (P.raw.map .source) y ∧ QNormalForm P.licensed y} :=
      P.licensedEmbedding.terminalFintype .source
    Fintype.card {y // Reach A.step (P.raw.map .source) y ∧ QNormalForm A.step y} = 2 ∧
    Fintype.card {y // Reach P.licensed (P.raw.map .source) y ∧ QNormalForm P.licensed y} = 1 := by
  letI := P.raw.terminalFintype .source
  letI : Fintype {y // Reach P.licensed (P.raw.map .source) y ∧ QNormalForm P.licensed y} :=
    P.licensedEmbedding.terminalFintype .source
  exact ⟨(P.raw.terminal_card .source).trans fork3_raw_terminalMultiplicity_eq_two,
    (P.licensedEmbedding.terminal_card .source).trans fork3_licensed_terminalMultiplicity_eq_one⟩

/-! ## The live KO7 instance -/

def ko7AmbientARS : ARS where
  Carrier := OperatorKO7.Trace
  step := OperatorKO7.Step
  scope := forkARS.scope

def ko7AmbientBinaryFork : AmbientBinaryFork ko7AmbientARS where
  raw :=
    { map := ⟨KO7LocalConeBridge.fork3ToTrace, KO7LocalConeBridge.fork3ToTrace_injective⟩
      step_iff := KO7LocalConeBridge.fork3Step_iff_ko7Step
      forward_closed := by
        intro x y h
        cases x with
        | source =>
            change OperatorKO7.Step (.eqW .void .void) y at h
            cases h with
            | R_eq_refl a => exact ⟨.equal, rfl⟩
            | R_eq_diff a b => exact ⟨.different, rfl⟩
        | equal =>
            change OperatorKO7.Step .void y at h
            cases h
        | different =>
            change OperatorKO7.Step (.integrate (.merge .void .void)) y at h
            cases h }
  licensed := MetaSN_KO7.SafeStep
  licensed_iff := KO7LocalConeBridge.fork3LicensedStep_iff_ko7SafeStep
  licensed_sub_raw := by
    intro x y h
    cases h <;> constructor

/-- These profiles use live kernel and SafeStep edges, through the proved closed local part. -/
theorem ko7_binaryFork_profile_recovery (cost : Nat) :
    semanticProfile (ko7AmbientBinaryFork.presentation.rawData cost) = rawExactProfile cost ∧
    semanticProfile (ko7AmbientBinaryFork.presentation.licensedData cost) = licensedExactProfile :=
  ambientBinaryFork_profile_exact ko7AmbientBinaryFork cost

theorem ko7_binaryFork_ambient_terminals :
    letI : Fintype {y : OperatorKO7.Trace // Reach OperatorKO7.Step (.eqW .void .void) y ∧
      QNormalForm OperatorKO7.Step y} := ko7AmbientBinaryFork.raw.terminalFintype .source
    letI : Fintype {y : OperatorKO7.Trace // Reach MetaSN_KO7.SafeStep (.eqW .void .void) y ∧
      QNormalForm MetaSN_KO7.SafeStep y} :=
      ko7AmbientBinaryFork.licensedEmbedding.terminalFintype .source
    Fintype.card {y // Reach OperatorKO7.Step (.eqW .void .void) y ∧
      QNormalForm OperatorKO7.Step y} = 2 ∧
    Fintype.card {y // Reach MetaSN_KO7.SafeStep (.eqW .void .void) y ∧
      QNormalForm MetaSN_KO7.SafeStep y} = 1 :=
  ambientBinaryFork_terminal_counts ko7AmbientBinaryFork

end
end OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile
