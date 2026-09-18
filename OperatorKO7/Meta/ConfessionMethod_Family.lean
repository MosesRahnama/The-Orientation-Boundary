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

set_option autoImplicit false

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

/-! ## Resolution of payload-level operational incompleteness

The two theorems below are the family-level resolution statements. They record
both halves of the claim in one type: the gap, namely that the direct
whole-term witness universe has no witness and that the benchmark contract
admits none at or below the imported-whole level, and the licensed route that
closes that gap, namely a contract-admissible witness at the transformed-call
layer realized for every family member as the certified-forgetting field of a
`PayloadOperationalIncompleteness` package carrying that member's own rank.

Supplying a `CertifiedForgettingWitness` is strictly weaker than this and is
recorded separately by `confession_family_supplies_certified_forgetting_witnesses`,
which says nothing about the direct-language gap or the contract thresholds.
-/

section ResolvesOperationalIncompleteness

open OperatorKO7.WitnessOrder

/--
Proves: the KO7 payload coordinate is operationally incomplete for the direct
whole-term witness language under the benchmark contract, and every member of
the confession family supplies the licensed transformed-call route that closes
it, carrying that member's own rank.
Does not prove: that every admissible witness must forget; nor source-system
termination from any individual member's soundness license.
Relation: witness-language tower `ko7Tower` and its contract restriction.
Closure: not applicable, this is a witness-level statement.
Strategy: not applicable.
Trust: kernel-only.
Scope: the duplicated payload coordinate of `ko7Schema` under `benchmarkContract`.
Non-vacuity witness: `family_size` for the quantified list, and
`confession_family_resolution_witness_dp` at the exact quantified domain.
-/
theorem confession_family_resolves_operational_incompleteness :
    (¬ HasWitness ko7Tower WLevel.directWhole)
    ∧ kappaGt (contractTower ko7Tower benchmarkContract) WLevel.importedWhole
    ∧ kappaLe (contractTower ko7Tower benchmarkContract) WLevel.transformedCall
    ∧ ∀ C ∈ allConfessionMethods,
        ∃ P : PayloadOperationalIncompleteness,
          P.certifiedForgetting.rank = C.rank := by
  refine ⟨ko7_no_directWhole_witness, ko7_kappaContract_gt_importedWhole,
    ko7_kappaContract_le_transformedCall, ?_⟩
  intro C _
  exact ⟨{ ko7PayloadOperationalIncompleteness with
    certifiedForgetting := CertifiedForgettingWitness.ofConfessionMethod C }, rfl⟩

/-- Non-vacuity at the exact quantified domain of
`confession_family_resolves_operational_incompleteness`: the dependency-pair
method is a member of the quantified list, and its resolution package is
exhibited explicitly. -/
theorem confession_family_resolution_witness_dp :
    dpConfession ∈ allConfessionMethods
    ∧ ∃ P : PayloadOperationalIncompleteness,
        P.certifiedForgetting.rank = dpConfession.rank := by
  refine ⟨by simp [allConfessionMethods], ?_⟩
  exact ⟨{ ko7PayloadOperationalIncompleteness with
    certifiedForgetting :=
      CertifiedForgettingWitness.ofConfessionMethod dpConfession }, rfl⟩

end ResolvesOperationalIncompleteness

end OperatorKO7.ConfessionMethodFamily
