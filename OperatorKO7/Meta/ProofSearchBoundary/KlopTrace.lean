/-
Copyright (c) 2026 Moses Rahnama. All rights reserved.
Source-available; see the file LICENSE. Free for individual research;
departmental academic use and commercial use require a paid license.
Authors: Moses Rahnama
-/
import OperatorKO7.Meta.ProofSearchBoundary
import OperatorKO7.Meta.ProofSearchBoundary.GroundedSupport
import OperatorKO7.Meta.UniqueNormalization.Lemma36

/-!
# Proof-search states for transitivity of `Down R`

The target is transitivity of `Down R`. Under its stated assumptions, `lemma36_at_down_needs_only_transitivity` discharges the symmetry and constructor-compatibility premises of `lemma36`, leaving transitivity as the remaining premise.

The model includes open proposals, a certified closing proposal, its withdrawal, and a subsequent recommendation. The theorem `celebration_target_underivable` shows that the certified proposal's support does not derive transitivity or closure even when the same-rule join is supplied.

Two boundary predicates differ on the same path. The `Licensed` boundary is the edge `s1 → s2` (`firstPromotion`). The `Consumes` boundary is the edge `s0 → s1` (`consumptionFailure`); its first failing state `s1` is open and licensed.

Trust: kernel only, Mathlib baseline.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.ProofSearchBoundary.KlopTrace

open OperatorKO7.Meta.DistinctionBoundary.PersistentLicense
open OperatorKO7.Meta.LicensedBoundaryCalculus
open OperatorKO7.Meta.ProofSearchBoundary
open OperatorKO7.Meta.ProofSearchBoundary.GroundedSupport

/-- The target is transitivity of `Down R`. -/
inductive Target where
  | section7DownTransitivity
  deriving DecidableEq, Repr

/-- The two obligations the episode leaves unhandled. -/
inductive Constraint where
  /-- `lemma36` at `S := Down R` takes transitivity of `Down R`, the target,
  as a premise. -/
  | htransObligation
  /-- The uniform separating construction is owed; none is supplied. -/
  | uniformConstructionOwed
  deriving DecidableEq, Repr

/-- The open obligations of the episode. -/
inductive Obligation where
  | proveDownTransitivity
  | constructUniformSeparatingModel
  deriving DecidableEq, Repr

/-- The modeled proposals. -/
inductive Proposal where
  | proposeTwoLevelShift
  | buildCrossRuleRefutation
  | celebrateKlopClosed
  | recommendRationalTree
  deriving DecidableEq, Repr

/-- Proof-search states of the episode. -/
abbrev State := ProofSearchState Target Constraint Obligation Proposal

/-- The transitivity obligation applies to the two proposals that route
cross-rule peaks through `lemma36` at `S := Down R`; the construction
obligation applies to the recommendation. -/
def Applicable : Constraint → Target → List Obligation → Proposal → Prop
  | .htransObligation, _, _, .buildCrossRuleRefutation => True
  | .htransObligation, _, _, .celebrateKlopClosed => True
  | .uniformConstructionOwed, _, _, .recommendRationalTree => True
  | _, _, _, _ => False

/-- No proposal of the episode supplies an independent transitivity proof or
the uniform construction. -/
def Handles : Constraint → Target → List Obligation → Proposal → Prop :=
  fun _ _ _ _ => False

/-- The audit rejects each proposal under each applicable obligation. -/
def AuditRejects : Constraint → Target → List Obligation → Proposal → Prop
  | .htransObligation, _, _, .buildCrossRuleRefutation => True
  | .htransObligation, _, _, .celebrateKlopClosed => True
  | .uniformConstructionOwed, _, _, .recommendRationalTree => True
  | _, _, _, _ => False

/-- The two obligations on record throughout the episode. -/
def blockers : List Constraint :=
  [.htransObligation, .uniformConstructionOwed]

/-- The initial state carries open obligations. -/
def obligations : List Obligation :=
  [.proveDownTransitivity, .constructUniformSeparatingModel]

/-- The initial state proposes a two-level shift and remains open. -/
def s0 : State where
  target := .section7DownTransitivity
  known := blockers
  openObligations := obligations
  proposal := .proposeTwoLevelShift
  status := .«open»

/-- The cross-rule refutation proposal remains open with both obligations outstanding. -/
def s1 : State where
  target := .section7DownTransitivity
  known := blockers
  openObligations := obligations
  proposal := .buildCrossRuleRefutation
  status := .«open»

/-- The state with `celebrateKlopClosed` has certified status. -/
def s2 : State where
  target := .section7DownTransitivity
  known := blockers
  openObligations := obligations
  proposal := .celebrateKlopClosed
  status := .certified

/-- The state `s2withdraw` retains the proposal from `s2` and has withdrawn status. -/
def s2withdraw : State := { s2 with status := .withdrawn }

/-- The rational-tree recommendation state is open. -/
def s3 : State where
  target := .section7DownTransitivity
  known := blockers
  openObligations := obligations
  proposal := .recommendRationalTree
  status := .«open»

/-- The `NextProposal` path from `s0` to `s2`. -/
inductive NextProposal : State → State → Prop
  | first : NextProposal s0 s1
  | second : NextProposal s1 s2

/-- The episode transition relation includes the proposal path, withdrawal, and recommendation edges. -/
inductive EpisodeStep : State → State → Prop
  | first : EpisodeStep s0 s1
  | second : EpisodeStep s1 s2
  | retract : EpisodeStep s2 s2withdraw
  | recommend : EpisodeStep s2withdraw s3

noncomputable instance : DecidablePred (Consumes Applicable Handles) := by
  intro s
  exact Classical.propDecidable _

theorem s0_consumes : Consumes Applicable Handles s0 := by
  intro k hk happ
  simp only [s0, blockers, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl <;> exact happ.elim

theorem s1_not_consumes : ¬ Consumes Applicable Handles s1 :=
  fun h => h .htransObligation (by simp [s1, blockers]) trivial

theorem s2_not_consumes : ¬ Consumes Applicable Handles s2 :=
  fun h => h .htransObligation (by simp [s2, blockers]) trivial

theorem s2withdraw_not_consumes : ¬ Consumes Applicable Handles s2withdraw :=
  fun h => h .htransObligation (by simp [s2withdraw, s2, blockers]) trivial

theorem s3_not_consumes : ¬ Consumes Applicable Handles s3 :=
  fun h => h .uniformConstructionOwed (by simp [s3, blockers]) trivial

theorem s0_licensed : Licensed Applicable Handles s0 := fun _ => s0_consumes

theorem s1_licensed : Licensed Applicable Handles s1 :=
  licensed_of_not_commits _ _ (by simp [Commits, s1])

theorem s2withdraw_licensed : Licensed Applicable Handles s2withdraw :=
  licensed_of_not_commits _ _ (by simp [Commits, s2withdraw, s2])

theorem s3_licensed : Licensed Applicable Handles s3 :=
  licensed_of_not_commits _ _ (by simp [Commits, s3])

/-- The audit is sound: nothing is handled, so every rejection is sound. -/
theorem auditRejects_sound : AuditSound Handles AuditRejects :=
  fun _ _ _ _ _ hh => hh

/-- State `s1` has a self-application gap caused by the unhandled transitivity obligation and has no promotion. -/
theorem s1_selfApplicationGap : SelfApplicationGap Applicable AuditRejects s1 :=
  ⟨.htransObligation, by simp [s1, blockers], trivial, trivial⟩

theorem s2_selfApplicationGap : SelfApplicationGap Applicable AuditRejects s2 :=
  ⟨.htransObligation, by simp [s2, blockers], trivial, trivial⟩

/-- The certified state `s2` is an unsupported promotion because it does not consume. -/
theorem s2_unsupportedPromotion :
    UnsupportedPromotion Applicable Handles s2 :=
  ⟨rfl, s2_not_consumes⟩

/-- The `NextProposal` path from `s0` to `s2`. -/
def trace : FinitePath NextProposal s0 s2 :=
  .cons NextProposal.first
    (.cons NextProposal.second (.refl s2))

/-- The path determines a `FailureObject` for `Consumes` between `s0` and `s2`. -/
theorem extracted_failure :
    Nonempty
      (FailureObject NextProposal (Consumes Applicable Handles) s0 s2 trace) :=
  FailureObject.of_explicit_path trace s0_consumes s2_not_consumes

/-- The consumption boundary lies on the transition from `s0` to `s1`; `s0` consumes and `s1` does not. -/
def consumptionFailure :
    FailureObject NextProposal (Consumes Applicable Handles) s0 s2 trace where
  lastSafe := s0
  firstFail := s1
  sourceSafe := s0_consumes
  endpointFails := s2_not_consumes
  safePrefix := .refl s0
  safePrefixProof := .refl s0_consumes
  crossing := ⟨NextProposal.first, s0_consumes, s1_not_consumes⟩
  suffix := .cons NextProposal.second (.refl s2)
  decomposition := rfl

theorem consumptionFailure_lastSafe : consumptionFailure.lastSafe = s0 := rfl

theorem consumptionFailure_firstFail : consumptionFailure.firstFail = s1 := rfl

/-- The consumption boundary lands on an open, licensed state. -/
theorem consumptionFailure_lands_on_licensed_open :
    consumptionFailure.firstFail.status = ClaimStatus.«open» ∧
      Licensed Applicable Handles consumptionFailure.firstFail :=
  ⟨rfl, s1_licensed⟩

/-- The `Licensed` boundary is the certification edge `s1 → s2`. -/
def firstPromotion :
    FailureObject NextProposal (Licensed Applicable Handles) s0 s2 trace where
  lastSafe := s1
  firstFail := s2
  sourceSafe := s0_licensed
  endpointFails :=
    (unsupportedPromotion_iff_not_licensed _ _ s2).mp s2_unsupportedPromotion
  safePrefix := .cons NextProposal.first (.refl s1)
  safePrefixProof := .cons s0_licensed (.refl s1_licensed)
  crossing := ⟨NextProposal.second, s1_licensed,
    (unsupportedPromotion_iff_not_licensed _ _ s2).mp s2_unsupportedPromotion⟩
  suffix := .refl s2
  decomposition := rfl

theorem firstPromotion_lastSafe : firstPromotion.lastSafe = s1 := rfl

theorem firstPromotion_firstFail : firstPromotion.firstFail = s2 := rfl

theorem firstPromotion_unsupported :
    UnsupportedPromotion Applicable Handles firstPromotion.firstFail :=
  s2_unsupportedPromotion

/-- The two boundaries differ on this trace, and the consumption boundary's
failing state is licensed. -/
theorem consumption_and_license_boundaries_differ :
    BoundaryEdge NextProposal (Consumes Applicable Handles) s0 s1 ∧
      BoundaryEdge NextProposal (Licensed Applicable Handles) s1 s2 ∧
      Licensed Applicable Handles s1 :=
  ⟨consumptionFailure.crossing, firstPromotion.crossing, s1_licensed⟩

theorem prescription_not_persistent :
    ¬ PrescriptionPersistent Applicable Handles NextProposal s0 :=
  FailureObject.not_box consumptionFailure

theorem not_persistentLicensed :
    ¬ PersistentLicensed Applicable Handles NextProposal s0 :=
  FailureObject.not_box firstPromotion

/-- The episode path runs from `s0` to `s3` through proposal, certification, withdrawal, and recommendation. -/
def history : FinitePath EpisodeStep s0 s3 :=
  .cons EpisodeStep.first (.cons EpisodeStep.second
    (.cons EpisodeStep.retract (.cons EpisodeStep.recommend (.refl s3))))

/-- Withdrawal makes `s2withdraw` and `s3` licensed, but the full episode path is not persistently licensed. -/
theorem correction_restores_license_not_history :
    Licensed Applicable Handles s2withdraw ∧ Licensed Applicable Handles s3 ∧
      ¬ PersistentLicensed Applicable Handles EpisodeStep s0 :=
  ⟨s2withdraw_licensed, s3_licensed,
    reachable_unsupportedPromotion_not_persistentLicensed _ _ _
      (Relation.ReflTransGen.head EpisodeStep.first
        (Relation.ReflTransGen.single EpisodeStep.second))
      s2_unsupportedPromotion⟩

/-- The recommendation state leaves the construction obligation open, is licensed, and is not an unsupported promotion. -/
theorem recommendation_open_research :
    ¬ Consumes Applicable Handles s3 ∧ Licensed Applicable Handles s3 ∧
      ¬ UnsupportedPromotion Applicable Handles s3 :=
  ⟨s3_not_consumes, s3_licensed,
    not_unsupportedPromotion_of_not_commits _ _ (by simp [Commits, s3])⟩

/-! ## Transitivity premise for `lemma36` -/

section Lemma36Link

open OperatorKO7.Meta.Rewriting
open OperatorKO7.Meta.UniqueNormalization

universe u v

/-- For `S := Down R`, the hypotheses `Down.symm` and `Down.constructorCompatible` discharge the symmetry and constructor-compatibility premises of `lemma36`; transitivity of `Down R` remains. The closing proposal uses that premise without a derivation. -/
theorem lemma36_at_down_needs_only_transitivity
    {sigma : Type u} {nu : Type v}
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    {F : sigma} {ps qs : List (Term (sigma ⊕ sigma) nu)}
    (hps : ∀ p ∈ ps, ConOnly p) (hqs : ∀ q ∈ qs, ConOnly q)
    {a b : Subst (sigma ⊕ sigma) nu}
    (hall : List.Forall₂ (Down R)
      (ps.map (Subst.apply a)) (qs.map (Subst.apply b))) :
    (∀ x y z, Down R x y → Down R y z → Down R x z) →
      OmegaUnifiable (Term.app (Sum.inr F) ps) (Term.app (Sum.inr F) qs) :=
  fun htrans =>
    lemma36 (fun _ _ h => Down.symm h) htrans (Down.constructorCompatible hR)
      hps hqs hall

end Lemma36Link

/-! ## Dependencies of the closing claim -/

/-- The dependency nodes for the closing claim. -/
inductive CelebrationNode where
  | downTransitivity
  | crossRuleRefutation
  | sameRuleJoin
  | klopClosed
  deriving DecidableEq, Repr

/-- The dependency rules require transitivity for cross-rule refutation, require both cross-rule refutation and the same-rule join for transitivity, and require transitivity for closure. -/
def celebrationRules (P : Finset CelebrationNode) (q : CelebrationNode) : Prop :=
  (q = .crossRuleRefutation ∧ .downTransitivity ∈ P) ∨
    (q = .downTransitivity ∧ .crossRuleRefutation ∈ P ∧ .sameRuleJoin ∈ P) ∨
    (q = .klopClosed ∧ .downTransitivity ∈ P)

/-- The same-rule join is granted as a fact. -/
def celebrationFacts (q : CelebrationNode) : Prop := q = .sameRuleJoin

/-- With the same-rule join as a fact, Horn derivations do not derive transitivity or the closing theorem. -/
theorem celebration_target_underivable :
    ¬ HornDeriv celebrationFacts celebrationRules .downTransitivity ∧
      ¬ HornDeriv celebrationFacts celebrationRules .klopClosed := by
  have hU := unfounded_component_never_derivable
    (facts := celebrationFacts) (rules := celebrationRules)
    (U := fun q => q = .downTransitivity ∨ q = .crossRuleRefutation ∨
      q = .klopClosed)
    (fun q hq hf => by
      rcases hq with rfl | rfl | rfl <;> simp [celebrationFacts] at hf)
    (fun P q hrule _ => by
      rcases hrule with ⟨rfl, hP⟩ | ⟨rfl, hP, -⟩ | ⟨rfl, hP⟩
      · exact ⟨.downTransitivity, hP, Or.inl rfl⟩
      · exact ⟨.crossRuleRefutation, hP, Or.inr (Or.inl rfl)⟩
      · exact ⟨.downTransitivity, hP, Or.inl rfl⟩)
  exact ⟨fun h => hU _ h (Or.inl rfl), fun h => hU _ h (Or.inr (Or.inr rfl))⟩

/-- Adding transitivity as a fact allows the rules to derive the closing theorem. The underivability result follows from the missing derivation of transitivity. -/
theorem celebration_closes_given_transitivity :
    HornDeriv (fun q => q = .downTransitivity ∨ q = .sameRuleJoin)
      celebrationRules .klopClosed :=
  HornDeriv.rule (P := {.downTransitivity})
    (Or.inr (Or.inr ⟨rfl, Finset.mem_singleton_self _⟩))
    (fun p hp => by
      rw [Finset.mem_singleton] at hp
      subst hp
      exact HornDeriv.fact (Or.inl rfl))

end OperatorKO7.Meta.ProofSearchBoundary.KlopTrace
