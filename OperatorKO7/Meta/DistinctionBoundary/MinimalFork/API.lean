import OperatorKO7.Meta.DistinctionBoundary.MinimalFork.Crown

/-!
# Stable schema-first Distinction Boundary API

The aliases below expose exact theorem types and keep all scope hypotheses
visible. They do not weaken statements, hide relation choices, or promote root
results to contextual results.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.DistinctionBoundary.MinimalFork.API

open OperatorKO7.Meta.DistinctionBoundary.MinimalFork
open OperatorKO7.Meta.DistinctionBoundary.Quantitative

universe u

/-- Absolute finite-carrier lower bound for a nonjoinable one-step peak. -/
theorem distinction_nonjoinable_peak_card_ge_three
    {T : Type u} [Fintype T] [DecidableEq T]
    {R : T → T → Prop} {s l r : T}
    (hsl : R s l) (hsr : R s r) (hnj : ¬ Joinable R l r) :
    3 ≤ Fintype.card T :=
  nonjoinable_peak_card_ge_three hsl hsr hnj

/-- Roadmap-stable public cardinality-minimality theorem. -/
theorem distinction_minimal_cardinality
    {T : Type u} [Fintype T] [DecidableEq T]
    {R : T → T → Prop} {s l r : T}
    (hsl : R s l) (hsr : R s r) (hnj : ¬ Joinable R l r) :
    3 ≤ Fintype.card T :=
  distinction_nonjoinable_peak_card_ge_three hsl hsr hnj

/-- Canonical three-state attainment theorem. -/
theorem distinction_fork3_card_eq_three : Fintype.card Fork3 = 3 :=
  fork3_card_eq_three

/-- Genuine categorical universal property. -/
def distinction_fork3_initial :
    CategoryTheory.Limits.IsInitial (fork3Pointed : PointedFork.{0}) :=
  fork3_isInitial

/-- Exact terminal diagonal contains the canonical fork. -/
theorem distinction_exact_terminal_diagonal_contains_fork3
    {T : Type u} (S : ExactDiagonalForkSchema T) (a : T)
    (hterm : TerminalDiagonal S a) :
    Function.Injective (fork3Embedding S a hterm).toFun :=
  fork3Embedding_injective S a hterm
/-- Public universal embedding theorem. Under terminal and determined-diagonal
hypotheses, the canonical map is injective and preserves *and reflects* the
one-step relation on its three marked states. -/
theorem distinction_exact_schema_contains_fork3
    {T : Type u} (S : ExactDiagonalForkSchema T) (a : T)
    (hterm : TerminalDiagonal S a) (hdet : DiagonalDetermined S a) :
    Function.Injective
        (fork3_embedding_of_terminalDiagonal S a hterm).toFun ∧
      ∀ {x y : Fork3},
        Fork3Step x y ↔
          S.R ((fork3_embedding_of_terminalDiagonal S a hterm).toFun x)
            ((fork3_embedding_of_terminalDiagonal S a hterm).toFun y) := by
  refine ⟨fork3_embedding_injective S a hterm, ?_⟩
  intro x y
  constructor
  · exact fork3_embedding_preserves_edges S a hterm
  · exact fork3_embedding_reflects_edges_of_determined S a hterm hdet

/-- Determined terminal diagonal is exactly the canonical marked local cone. -/
noncomputable def distinction_determined_terminal_diagonal_localCone_iso_fork3 :=
  @determined_terminal_diagonal_localCone_equiv_fork3

/-- Minimal equality-witness system terminates at root and under unrestricted
context closure, but its closed raw diagonal is nonconfluent. -/
theorem distinction_minimal_eqW_terminates_but_root_nonconfluent :
    WellFounded (flip MiniEqWRootStep) ∧
      WellFounded (flip MiniEqWCtxStep) ∧
      ¬ ConfluentAt MiniEqWRootStep miniEqWClosedDiagonal :=
  ⟨minimalEqW_root_SN,
    minimalEqW_context_SN,
    minimalEqW_closed_diagonal_not_confluent⟩

/-- Roadmap-stable public termination/nonconfluence package. The root and
context relations remain separately named in the type. -/
theorem distinction_minimal_eqW_terminates_not_confluent :
    WellFounded (flip MiniEqWRootStep) ∧
      WellFounded (flip MiniEqWCtxStep) ∧
      ¬ ConfluentAt MiniEqWRootStep miniEqWClosedDiagonal :=
  distinction_minimal_eqW_terminates_but_root_nonconfluent

/-- Generic deep first-order reification is terminating but not locally confluent. -/
theorem distinction_deep_eqW_terminates_but_not_localConfluent :
    WellFounded
      (flip (OperatorKO7.Meta.Rewriting.Step
        OperatorKO7.Meta.DistinctionBoundary.MinimalFork.DeepEqW.minimalTRS)) ∧
    ¬ OperatorKO7.Meta.Rewriting.localConfluent
      (OperatorKO7.Meta.Rewriting.renameTRS
        OperatorKO7.Meta.DistinctionBoundary.MinimalFork.DeepEqW.minimalTRS) :=
  ⟨OperatorKO7.Meta.DistinctionBoundary.MinimalFork.DeepEqW.deep_minimalTRS_SN,
    OperatorKO7.Meta.DistinctionBoundary.MinimalFork.DeepEqW.deep_generic_not_localConfluent⟩

/-- Declared minimality notions kept separate. -/
theorem distinction_declared_minimality_bundle :
    Fintype.card ComparatorRole3 = 3 ∧
      Fintype.card ComparatorRole5 = 5 ∧
      Fintype.card TwoRuleId = 2 :=
  declared_minimality_bundle

/-- Root repair plus explicit unrestricted-context scope wall. -/
theorem distinction_guarded_root_confluent_but_full_context_counterexample :
    (∀ source, ConfluentAt MiniEqWGuardedRootStep source) ∧
      ¬ ConfluentAt MiniEqWGuardedCtxStep contextualCounterexample :=
  ⟨guarded_root_confluent, guarded_full_context_not_confluent⟩

/-- Roadmap-stable public scope-wall theorem. -/
theorem distinction_guarded_root_vs_context_scope :
    (∀ source, ConfluentAt MiniEqWGuardedRootStep source) ∧
      ¬ ConfluentAt MiniEqWGuardedCtxStep contextualCounterexample :=
  distinction_guarded_root_confluent_but_full_context_counterexample

/-- Three fully proved context-stable repair routes. -/
theorem distinction_three_context_stable_repairs :
    (∀ source, ConfluentAt FrozenCtxStep source) ∧
    (∀ source, ConfluentAt NormalizedComparisonStep source) ∧
    (∀ source, ConfluentAt MiniEqWPersistentCtxStep source) :=
  ⟨frozen_comparison_context_confluent,
    normalizedComparison_confluent,
    persistentGuard_context_confluent⟩

/-- KO7's restricted raw local cone is exactly relation-isomorphic to Fork3. -/
theorem distinction_ko7_localCone_is_fork3 :
    Nonempty
      (RelIso Fork3Step
        OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7LocalCone.LocalRaw) :=
  OperatorKO7.Meta.DistinctionBoundary.MinimalFork.KO7LocalConeBridge.ko7_raw_local_cone_is_Fork3

/-- Every KO7 root equality diagonal has the exact schema-level confluence break. -/
theorem distinction_ko7_every_eqW_diagonal_not_localJoin
    (a : OperatorKO7.Trace) :
    ¬ LocalJoinAt
        OperatorKO7.Meta.DistinctionBoundary.MinimalFork.KO7SchemaInstance.ko7ExactDiagonalFork
        (OperatorKO7.Trace.eqW a a) :=
  OperatorKO7.Meta.DistinctionBoundary.MinimalFork.KO7SchemaInstance.ko7_every_diagonal_not_localJoin a

/-- Independent comparator instances realize relation-isomorphic local cones. -/
noncomputable def distinction_independent_comparators_localCone_iso :=
  OperatorKO7.Meta.DistinctionBoundary.MinimalFork.CrossInstanceIsomorphism.classicLocalConeIsoReflectionLocalCone

/-- Structural terminal support collapse only; no physical heat conclusion. -/
theorem distinction_terminal_support_collapse_one_bit :
    terminalMultiplicity Fork3Step .source = 2 ∧
      terminalMultiplicity Fork3LicensedStep .source = 1 ∧
      structuralHartleyCollapse Fork3Step Fork3LicensedStep .source = 1 :=
  ⟨fork3_raw_terminalMultiplicity_eq_two,
    fork3_licensed_terminalMultiplicity_eq_one,
    fork3_structuralHartleyCollapse_eq_one⟩

/-- Exact one-bit terminal-support collapse with both multiplicity and Hartley
coordinates displayed. This theorem is structural and dimensionless. -/
theorem distinction_one_bit_terminal_collapse :
    terminalMultiplicity Fork3Step .source = 2 ∧
      terminalMultiplicity Fork3LicensedStep .source = 1 ∧
      terminalHartleyEntropy Fork3Step .source = 1 ∧
      terminalHartleyEntropy Fork3LicensedStep .source = 0 ∧
      structuralHartleyCollapse Fork3Step Fork3LicensedStep .source = 1 :=
  ⟨fork3_raw_terminalMultiplicity_eq_two,
    fork3_licensed_terminalMultiplicity_eq_one,
    fork3_raw_hartley_eq_one,
    fork3_licensed_hartley_eq_zero,
    fork3_structuralCollapse_eq_one⟩

/-- Semantic mode theorem based on actual fork embeddings. -/
theorem distinction_semanticFork_iff_unguardedTotalizedRewrite
    (m : OperatorKO7.Meta.DistinctionBoundary.EqualityMode) :
    ContainsCanonicalFork m ↔
      m = OperatorKO7.Meta.DistinctionBoundary.EqualityMode.unguardedTotalizedRewrite :=
  containsCanonicalFork_iff_raw m

/-- Full production crown. -/
theorem distinction_minimalFork_crown : MinimalForkCrown.{u} :=
  minimal_distinction_boundary_crown

end OperatorKO7.Meta.DistinctionBoundary.MinimalFork.API
