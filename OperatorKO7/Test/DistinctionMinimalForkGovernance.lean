import OperatorKO7.Meta.DistinctionBoundary.MinimalFork.API

/-!
# Minimal equality-witness universality governance

This module closes the roadmap's release-governance obligations without treating
string metadata as mathematical evidence. The string list below is coverage
bookkeeping only. Every listed declaration is separately elaborated by the reach,
anchor, claim-liveness, and axiom-audit gates.
-/

set_option autoImplicit false

namespace OperatorKO7.Test.DistinctionMinimalForkGovernance

open OperatorKO7.Meta.DistinctionBoundary.MinimalFork
open OperatorKO7.Meta.DistinctionBoundary.MinimalFork.API
open OperatorKO7.Meta.DistinctionBoundary.Quantitative

/-- Exact paper-facing anchor names for the schema-first crown.

This is metadata for coverage counting; the imported declarations and the
law-bearing theorems below provide the semantic evidence. -/
def minimalForkPublicAnchorNames : List String :=
  [ "distinction_minimal_cardinality"
  , "distinction_fork3_card_eq_three"
  , "distinction_fork3_initial"
  , "distinction_exact_schema_contains_fork3"
  , "distinction_minimal_eqW_terminates_not_confluent"
  , "distinction_deep_eqW_terminates_but_not_localConfluent"
  , "distinction_guarded_root_vs_context_scope"
  , "distinction_three_context_stable_repairs"
  , "distinction_ko7_localCone_is_fork3"
  , "distinction_one_bit_terminal_collapse"
  , "distinction_semanticFork_iff_unguardedTotalizedRewrite"
  , "minimal_distinction_boundary_crown"
  ]

/-- The public anchor inventory contains no duplicate name. -/
theorem minimalForkPublicAnchorNames_nodup :
    minimalForkPublicAnchorNames.Nodup := by
  decide

/-- The schema-first public anchor inventory has exactly twelve entries. -/
theorem full_anchor_gate_count_exact :
    minimalForkPublicAnchorNames.length = 12 := by
  rfl

/-- Law-bearing conjunction exercised independently by all seven reach gates.

The build logs establish module reachability; this theorem records the exact
mathematical crown those gates jointly replay. -/
theorem all_minimalFork_reach_gates : MinimalForkCrown.{0} :=
  minimal_distinction_boundary_crown

/-- The manuscript's schema-first headline is bound to the live crown, not to a
string, Boolean flag, or catalog row. -/
theorem manuscript_schema_first_crown : MinimalForkCrown.{0} :=
  minimal_distinction_boundary_crown

/-- A small law-bearing record for the manuscript's headline claims. -/
structure MinimalForkManuscriptClaimLiveness : Prop where
  crown : MinimalForkCrown.{0}
  fork3_cardinality : Fintype.card Fork3 = 3
  ko7_local_cone :
    Nonempty
      (OperatorKO7.Meta.DistinctionBoundary.MinimalFork.RelIso Fork3Step
        OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7LocalCone.LocalRaw)
  support_collapse :
    terminalMultiplicity Fork3Step .source = 2 ∧
      terminalMultiplicity Fork3LicensedStep .source = 1 ∧
      terminalHartleyEntropy Fork3Step .source = 1 ∧
      terminalHartleyEntropy Fork3LicensedStep .source = 0 ∧
      structuralHartleyCollapse Fork3Step Fork3LicensedStep .source = 1

/-- Every schema-first manuscript headline resolves to a live theorem object.

Source-line ranges and the final source hash are recorded in the external claim
crosswalk; this declaration supplies the semantic side of that binding. -/
theorem manuscript_claim_liveness : MinimalForkManuscriptClaimLiveness where
  crown := minimal_distinction_boundary_crown
  fork3_cardinality := distinction_fork3_card_eq_three
  ko7_local_cone := distinction_ko7_localCone_is_fork3
  support_collapse := distinction_one_bit_terminal_collapse

/-- No binary relation on a two-element carrier has a nonjoinable one-step peak. -/
theorem no_nonjoinable_peak_on_fin_two :
    ¬ ∃ (R : Fin 2 → Fin 2 → Prop) (s l r : Fin 2),
        R s l ∧ R s r ∧ ¬ Joinable R l r := by
  rintro ⟨R, s, l, r, hsl, hsr, hnj⟩
  have hcard : 3 ≤ Fintype.card (Fin 2) :=
    distinction_minimal_cardinality hsl hsr hnj
  simp at hcard

/-- Formal companion to the independently archived finite enumeration.

Lean proves the two-state exclusion universally and the canonical three-state
attainment. The external enumerator separately exhausts every relation on
carriers of sizes zero, one, and two and checks the canonical three-state fork. -/
theorem independent_three_state_validation :
    (¬ ∃ (R : Fin 2 → Fin 2 → Prop) (s l r : Fin 2),
        R s l ∧ R s r ∧ ¬ Joinable R l r) ∧
      Fintype.card Fork3 = 3 :=
  ⟨no_nonjoinable_peak_on_fin_two, distinction_fork3_card_eq_three⟩

#check @all_minimalFork_reach_gates
#check @full_anchor_gate_count_exact
#check @manuscript_claim_liveness
#check @manuscript_schema_first_crown
#check @independent_three_state_validation

#print axioms all_minimalFork_reach_gates
#print axioms full_anchor_gate_count_exact
#print axioms manuscript_claim_liveness
#print axioms manuscript_schema_first_crown
#print axioms independent_three_state_validation

end OperatorKO7.Test.DistinctionMinimalForkGovernance
