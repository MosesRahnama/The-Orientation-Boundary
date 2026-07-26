import OperatorKO7.Meta.ConfessionMethod
import OperatorKO7.Meta.ConfessionMethod_RouteEvidence
import OperatorKO7.Meta.OperationalIncompleteness
import OperatorKO7.Meta.DependencyPairs_Works
import OperatorKO7.Meta.PolyInterpretation_FullStep
import OperatorKO7.Meta.ContextClosed_SN_Full

/-!
# The Confession-Method Family: Collected Results

This module collects four `ConfessionMethod` values on the KO7
step-duplicating schema. It proves finite-list facts about their shared rank,
distinct license tags, duplicating-step orientation, wrapper-sensitivity
violations, and conversion to `CertifiedForgettingWitness`.

The capstone `confession_is_a_class` states three facts: the list has
four members, every member has the DP rank function, and the four enum-valued
license fields are pairwise distinct. These field equalities and inequalities
remain separate from external soundness and methodological-equivalence results.

The four methods are:
1. Dependency pairs + subterm criterion (Arts-Giesl 2000)
2. Direct counter-projection via the subterm criterion
3. Size-Change Termination (Lee-Jones-Ben-Amram 2001)
4. Argument filtering within the DP framework
-/

namespace OperatorKO7.ConfessionMethodFamily

open OperatorKO7
open OperatorKO7.Trace
open OperatorKO7.StepDuplicating
open OperatorKO7.StepDuplicating.StepDuplicatingSchema
open OperatorKO7.CompositionalImpossibility
open OperatorKO7.MetaOperationalIncompleteness

/-- All four confession methods enumerated. -/
def allConfessionMethods : List (ConfessionMethod ko7Schema) :=
  [dpConfession, counterProjectionConfession, sctConfession, argumentFilteringConfession]

/-- The family list has length four. -/
theorem family_size : allConfessionMethods.length = 4 := by rfl

/-- Every listed confession method has the same rank function as
`dpConfession`. The other three cases use their route-specific equality
theorems. -/
theorem family_rank_agreement :
    ∀ C ∈ allConfessionMethods,
      C.rank = dpConfession.rank := by
  intro C hC
  simp [allConfessionMethods] at hC
  rcases hC with rfl | rfl | rfl | rfl
  · rfl
  · exact counterProjection_eq_dp_rank
  · exact sct_eq_dp_rank
  · exact argumentFiltering_eq_dp_rank

/-- Every confession method in the family orients the KO7 duplicating
    step. -/
theorem family_orients_dup_step :
    ∀ C ∈ allConfessionMethods,
      ∀ b s n : Trace,
        C.rank (app s (recΔ b s n)) < C.rank (recΔ b s (delta n)) := by
  intro C hC b s n
  exact confession_orients C b s n

/-- Every listed rank has witnesses showing failure of strict wrapper
sensitivity in each payload position. -/
theorem family_violates_sensitivity :
    ∀ C ∈ allConfessionMethods,
      (∃ x y : Trace, ¬ (C.rank (app x y) > C.rank x))
      ∧ (∃ x y : Trace, ¬ (C.rank (app x y) > C.rank y)) := by
  intro C hC
  exact ⟨confession_violates_wrap1 C, confession_violates_wrap2 C⟩

/-- Every listed method converts to a `CertifiedForgettingWitness`, whose fields
are duplicating-step orientation and two wrapper-sensitivity violations. -/
theorem family_certified_forgetting :
    ∀ C ∈ allConfessionMethods,
      ∃ fw : CertifiedForgettingWitness,
        fw.rank = C.rank := by
  intro C hC
  exact ⟨CertifiedForgettingWitness.ofConfessionMethod C, rfl⟩

/-- Construct certified-forgetting records through the four route-evidence
adapters. The conclusion compares their retained rank fields; route-specific
evidence fields remain in the source records. -/
theorem family_certified_forgetting_via_route_evidence :
    ∀ C ∈ allConfessionMethods,
      ∃ fw : CertifiedForgettingWitness,
        fw.rank = C.rank := by
  intro C hC
  simp [allConfessionMethods] at hC
  rcases hC with rfl | rfl | rfl | rfl
  · exact ⟨dpRouteEvidenceCertifiedForgettingWitness, rfl⟩
  · exact ⟨directCounterProjectionRouteEvidenceCertifiedForgettingWitness, rfl⟩
  · exact ⟨sctRouteEvidenceCertifiedForgettingWitness, rfl⟩
  · exact ⟨argumentFilteringRouteEvidenceCertifiedForgettingWitness, rfl⟩

/-- The four enum-valued license fields are pairwise distinct. The proposition
is a finite tag inequality; external soundness requires separate theorem
adapters. -/
theorem family_distinct_licenses :
    (allConfessionMethods.map (·.license)).Nodup := by
  decide

/-- The three alternatively tagged instances have the same rank function as
the DP instance. -/
theorem family_single_core :
    counterProjectionConfession.rank = dpConfession.rank
    ∧ sctConfession.rank = dpConfession.rank
    ∧ argumentFilteringConfession.rank = dpConfession.rank := by
  exact ⟨counterProjection_eq_dp_rank, sct_eq_dp_rank, argumentFiltering_eq_dp_rank⟩

/-- Bundle pairwise distinct license tags with equality of the other three rank
functions to the DP rank. This proposition concerns enum tags and rank
functions. -/
theorem family_distinct_license_tags_and_single_core :
    (allConfessionMethods.map (·.license)).Nodup
    ∧ counterProjectionConfession.rank = dpConfession.rank
    ∧ sctConfession.rank = dpConfession.rank
    ∧ argumentFilteringConfession.rank = dpConfession.rank := by
  rcases confession_routes_converge with
    ⟨_, _, _, _, hCounter, hSCT, hFilter⟩
  exact ⟨family_distinct_licenses, hCounter, hSCT, hFilter⟩

/-- Capstone for the finite family: list length four, rank-function agreement,
and pairwise distinct license tags. Certified-forgetting conversion is proved
separately by `family_certified_forgetting`. -/
theorem confession_is_a_class :
    allConfessionMethods.length = 4
    ∧ (∀ C ∈ allConfessionMethods, C.rank = dpConfession.rank)
    ∧ (allConfessionMethods.map (·.license)).Nodup := by
  exact ⟨family_size, family_rank_agreement, family_distinct_licenses⟩

/-- Every listed method supplies a `CertifiedForgettingWitness` with the same
rank. External licenses and source-system termination require their respective
adapters. -/
theorem confession_family_supplies_certified_forgetting_witnesses :
    ∀ C ∈ allConfessionMethods,
      ∃ fw : CertifiedForgettingWitness, fw.rank = C.rank :=
  family_certified_forgetting

/-! ## Extracted-pair and polynomial termination facts

For every listed method, rank agreement transfers `dpPair_decreases` to that
method's rank on the fixed KO7 dependency-pair relation. The reverse relation is
well founded by `wf_DPPairRev`. Source-system termination requires an external
transport theorem.

The root-step and context-closed termination theorems below restate polynomial
proofs imported from their respective modules. Their proof terms use those
imports directly.
-/

/-- For every listed method, its rank decreases on every pair in the fixed KO7
dependency-pair relation, whose reverse relation is well founded. -/
theorem family_terminates_pair_problem :
    ∀ C ∈ allConfessionMethods,
      (∀ {a b : Trace},
        OperatorKO7.MetaDependencyPairs.DPPair a b → C.rank b < C.rank a)
      ∧ WellFounded (fun a b : Trace =>
          OperatorKO7.MetaDependencyPairs.DPPair b a) := by
  intro C hC
  constructor
  · intro a b hPair
    rw [family_rank_agreement C hC]
    exact OperatorKO7.MetaDependencyPairs.dpPair_decreases hPair
  · exact OperatorKO7.MetaDependencyPairs.wf_DPPairRev

/-- Restatement of the imported polynomial proof that the reverse KO7 root-step
relation is well founded. -/
theorem ko7_full_system_terminates :
    WellFounded (fun a b : Trace => Step b a) :=
  OperatorKO7.PolyInterpretation.wf_StepRev_poly

/-- Restatement of the imported polynomial proof that the full context-closed
reverse relation is well founded. -/
theorem ko7_full_context_closed_terminates :
    WellFounded MetaSN_KO7.StepCtxFullRev :=
  MetaSN_KO7.wf_StepCtxFullRev_poly

end OperatorKO7.ConfessionMethodFamily
