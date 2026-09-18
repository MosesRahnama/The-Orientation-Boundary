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
# The Report-9 Klop episode as a first-class failure object

Source: `KO7-LLM-Benchmark\Unsupported-Promotion\notes\Brains-09-11-2026-2300.md`,
Report 9 (lines 1769-1916) and its self-correction (lines 1918-2051).  The
annotation follows `HIGHER-BOUNDRY.md` lines 3585-3619, 3685 and 3710-3712.

* `s0` (open): the two-level representation shift is proposed.
* `s1` (open): the architecture routes cross-rule peaks through
  `distinct_rules_no_down_peak`, whose proof applies `lemma36` at `S := Down R`;
  the transitivity premise of `lemma36` is then the Section-7 target.
* `s2` (certified): Report 9 announces "the final, unconditional
  machine-checked proof of Klop's 1980 conjecture" on that architecture.
* `s2withdraw` (withdrawn): the self-correction withdraws the claim ("I cannot
  call `lemma36` on `Down R` without assuming `Down` is transitive").
* `s3` (open): the self-correction recommends the universal rational-tree
  interpretation as the next construction.

The `Handles` table is an answer key, audited by two theorems:
`lemma36_at_down_needs_only_transitivity` (every premise of `lemma36` at
`S := Down R` except transitivity is discharged by the library) and
`celebration_target_underivable` (the target is underivable from the
celebration's own support, even with the same-rule join granted).

Two boundaries are computed on one trace.  The manuscript's boundary, for
`Licensed`, is the certification edge `s1 → s2` (`firstPromotion`).  The
working-note boundary, for `Consumes`, is the edge `s0 → s1`
(`consumptionFailure`), whose failing state is open and licensed.

Trust: kernel only, Mathlib baseline.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.ProofSearchBoundary.KlopTrace

open OperatorKO7.Meta.DistinctionBoundary.PersistentLicense
open OperatorKO7.Meta.LicensedBoundaryCalculus
open OperatorKO7.Meta.ProofSearchBoundary
open OperatorKO7.Meta.ProofSearchBoundary.GroundedSupport

/-- The target of the episode: transitivity of the Section-7 invariant. -/
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

/-- The proposals of Report 9 and its self-correction. -/
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

/-- The open obligations carried by the episode. -/
def obligations : List Obligation :=
  [.proveDownTransitivity, .constructUniformSeparatingModel]

/-- Report 9, Parts I-II: the two-level shift is proposed. -/
def s0 : State where
  target := .section7DownTransitivity
  known := blockers
  openObligations := obligations
  proposal := .proposeTwoLevelShift
  status := .«open»

/-- Report 9, Part III items 1-3: the architecture, still open. -/
def s1 : State where
  target := .section7DownTransitivity
  known := blockers
  openObligations := obligations
  proposal := .buildCrossRuleRefutation
  status := .«open»

/-- Report 9, Part III item 4: the closing claim, certified. -/
def s2 : State where
  target := .section7DownTransitivity
  known := blockers
  openObligations := obligations
  proposal := .celebrateKlopClosed
  status := .certified

/-- The self-correction: the same proposal, withdrawn. -/
def s2withdraw : State := { s2 with status := .withdrawn }

/-- The self-correction's recommendation, open. -/
def s3 : State where
  target := .section7DownTransitivity
  known := blockers
  openObligations := obligations
  proposal := .recommendRationalTree
  status := .«open»

/-- The path to the celebration. -/
inductive NextProposal : State → State → Prop
  | first : NextProposal s0 s1
  | second : NextProposal s1 s2

/-- The whole recorded episode. -/
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

/-- The open architecture already carries the unhandled transitivity
obligation: a self-application gap without a promotion. -/
theorem s1_selfApplicationGap : SelfApplicationGap Applicable AuditRejects s1 :=
  ⟨.htransObligation, by simp [s1, blockers], trivial, trivial⟩

theorem s2_selfApplicationGap : SelfApplicationGap Applicable AuditRejects s2 :=
  ⟨.htransObligation, by simp [s2, blockers], trivial, trivial⟩

/-- The celebration certifies without consuming: an unsupported promotion. -/
theorem s2_unsupportedPromotion :
    UnsupportedPromotion Applicable Handles s2 :=
  ⟨rfl, s2_not_consumes⟩

/-- The path from the proposal to the celebration. -/
def trace : FinitePath NextProposal s0 s2 :=
  .cons NextProposal.first
    (.cons NextProposal.second (.refl s2))

/-- Generic consumption-crossing extraction from the trace. -/
theorem extracted_failure :
    Nonempty
      (FailureObject NextProposal (Consumes Applicable Handles) s0 s2 trace) :=
  FailureObject.of_explicit_path trace s0_consumes s2_not_consumes

/-- The working-note boundary: the consumption crossing is the first edge,
into the open architecture. -/
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

/-- The manuscript's boundary: the first unsupported promotion is the
certification edge `s1 → s2`. -/
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

/-- The recorded episode, from the proposal to the recommendation. -/
def history : FinitePath EpisodeStep s0 s3 :=
  .cons EpisodeStep.first (.cons EpisodeStep.second
    (.cons EpisodeStep.retract (.cons EpisodeStep.recommend (.refl s3))))

/-- The withdrawal restores the present license without erasing the earlier
promotion. -/
theorem correction_restores_license_not_history :
    Licensed Applicable Handles s2withdraw ∧ Licensed Applicable Handles s3 ∧
      ¬ PersistentLicensed Applicable Handles EpisodeStep s0 :=
  ⟨s2withdraw_licensed, s3_licensed,
    reachable_unsupportedPromotion_not_persistentLicensed _ _ _
      (Relation.ReflTransGen.head EpisodeStep.first
        (Relation.ReflTransGen.single EpisodeStep.second))
      s2_unsupportedPromotion⟩

/-- The recommendation is open research: it leaves the construction
unhandled, is licensed, and is not a promotion. -/
theorem recommendation_open_research :
    ¬ Consumes Applicable Handles s3 ∧ Licensed Applicable Handles s3 ∧
      ¬ UnsupportedPromotion Applicable Handles s3 :=
  ⟨s3_not_consumes, s3_licensed,
    not_unsupportedPromotion_of_not_commits _ _ (by simp [Commits, s3])⟩

/-! ## Audit of the answer key: the `lemma36` premise -/

section Lemma36Link

open OperatorKO7.Meta.Rewriting
open OperatorKO7.Meta.UniqueNormalization

universe u v

/-- `lemma36` at `S := Down R`: the library discharges symmetry
(`Down.symm`) and constructor compatibility (`Down.constructorCompatible`), so
the only premise left is transitivity of `Down R`, the Section-7 target.  The
celebration used that premise without proof. -/
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

/-! ## Audit of the answer key: the celebration's support -/

/-- The dependency nodes of the celebration. -/
inductive CelebrationNode where
  | downTransitivity
  | crossRuleRefutation
  | sameRuleJoin
  | klopClosed
  deriving DecidableEq, Repr

/-- The celebration's inferences: the cross-rule refutation applies `lemma36`
at `S := Down R` and cites transitivity; transitivity is claimed from the
cross-rule refutation and the same-rule join; the closing theorem cites
transitivity. -/
def celebrationRules (P : Finset CelebrationNode) (q : CelebrationNode) : Prop :=
  (q = .crossRuleRefutation ∧ .downTransitivity ∈ P) ∨
    (q = .downTransitivity ∧ .crossRuleRefutation ∈ P ∧ .sameRuleJoin ∈ P) ∨
    (q = .klopClosed ∧ .downTransitivity ∈ P)

/-- The same-rule join is granted as a fact. -/
def celebrationFacts (q : CelebrationNode) : Prop := q = .sameRuleJoin

/-- With the same-rule join granted, the celebration derives neither
transitivity nor the closing theorem: its support is a cycle. -/
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

/-- Positive control: the same rules derive the closing theorem once
transitivity is supplied independently, so the underivability comes from the
missing grounding. -/
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
