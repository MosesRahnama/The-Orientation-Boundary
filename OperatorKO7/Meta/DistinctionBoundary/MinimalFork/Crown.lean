import OperatorKO7.Meta.DistinctionBoundary.MinimalFork.Category
import OperatorKO7.Meta.DistinctionBoundary.MinimalFork.UniversalEmbedding
import OperatorKO7.Meta.DistinctionBoundary.MinimalFork.LegacySchemaBridge
import OperatorKO7.Meta.DistinctionBoundary.MinimalFork.EqW.Confluence
import OperatorKO7.Meta.DistinctionBoundary.MinimalFork.EqW.GuardedRoot
import OperatorKO7.Meta.DistinctionBoundary.MinimalFork.EqW.ContextualScope
import OperatorKO7.Meta.DistinctionBoundary.MinimalFork.EqW.FrozenContext
import OperatorKO7.Meta.DistinctionBoundary.MinimalFork.EqW.NormalizedComparison
import OperatorKO7.Meta.DistinctionBoundary.MinimalFork.EqW.PersistentGuard
import OperatorKO7.Meta.DistinctionBoundary.MinimalFork.EqW.SignatureMinimality
import OperatorKO7.Meta.DistinctionBoundary.MinimalFork.EqW.CriticalPairs
import OperatorKO7.Meta.DistinctionBoundary.MinimalFork.CrossInstanceIsomorphism
import OperatorKO7.Meta.DistinctionBoundary.MinimalFork.KO7SchemaInstance
import OperatorKO7.Meta.DistinctionBoundary.MinimalForkQuantitativeKO7Transport
import OperatorKO7.Meta.DistinctionBoundary.MinimalForkHartleyExact
import OperatorKO7.Meta.DistinctionBoundary.MinimalFork.SemanticModeClassification
import OperatorKO7.Meta.DistinctionBoundary.MinimalFork.DefectProfile

/-!
# Schema-first Distinction Boundary crown

Every field below is proof-bearing. No Boolean or metadata field substitutes for
a mathematical theorem. Scope is explicit per field; in particular the root
repair is not advertised as unrestricted contextual confluence, and the one-bit
collapse is structural Hartley support rather than physical heat.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.DistinctionBoundary.MinimalFork

open CategoryTheory
open OperatorKO7.Meta.DistinctionBoundary.Quantitative
open OperatorKO7.Meta.DistinctionBoundary

universe u

/-- Complete schema-first theorem bundle for the minimal Distinction obstruction. -/
structure MinimalForkCrown : Prop where
  /-- Absolute finite-carrier lower bound for a nonjoinable one-step peak. -/
  cardinality_minimal :
    ∀ {T : Type u} [Fintype T] [DecidableEq T]
      {R : T → T → Prop} {s l r : T},
      R s l → R s r → ¬ Joinable R l r → 3 ≤ Fintype.card T
  /-- The canonical carrier attains that lower bound. -/
  cardinality_attained : Fintype.card Fork3 = 3
  /-- Genuine Mathlib categorical initiality in the declared marked-fork category. -/
  initial : Nonempty (CategoryTheory.Limits.IsInitial (fork3Pointed : PointedFork.{0}))
  /-- Three role-collapsed symbols are sharp. -/
  collapsed_signature_minimal :
    Fintype.card ComparatorRole3 = 3
  /-- Five role-separated symbols are sharp. -/
  separated_signature_minimal :
    Fintype.card ComparatorRole5 = 5
  /-- The declared two-verdict root architecture has two distinct rule identities. -/
  two_rule_surface : Fintype.card TwoRuleId = 2
  /-- Minimal raw root relation terminates. -/
  minimal_eqW_root_SN : WellFounded (flip MiniEqWRootStep)
  /-- Minimal unrestricted context relation terminates. -/
  minimal_eqW_context_SN : WellFounded (flip MiniEqWCtxStep)
  /-- Termination does not imply confluence: the closed diagonal fails. -/
  minimal_eqW_diagonal_nonconfluent :
    ¬ ConfluentAt MiniEqWRootStep miniEqWClosedDiagonal
  /-- Generic deep first-order artifact also terminates contextually. -/
  deep_eqW_context_SN : WellFounded (flip (OperatorKO7.Meta.Rewriting.Step DeepEqW.minimalTRS))
  /-- The deep first-order artifact contains exactly the intended two rules. -/
  deep_eqW_rule_count_two : minimalEqWTRS.length = 2
  /-- The transparent contextual relation and deep generic contextual relation
  are the same relation on encoded terms. -/
  deep_eqW_context_correspondence :
    ∀ {s t : MiniEqWTerm},
      MiniEqWCtxStep s t ↔
        OperatorKO7.Meta.Rewriting.Step minimalEqWTRS
          (DeepEqW.encode s) (DeepEqW.encode t)
  /-- The generic critical-pair engine finds the same nonconfluence defect. -/
  deep_eqW_not_localConfluent :
    ¬ OperatorKO7.Meta.Rewriting.localConfluent (OperatorKO7.Meta.Rewriting.renameTRS DeepEqW.minimalTRS)
  /-- Every exact terminal diagonal contains an injective canonical fork. -/
  exact_terminal_contains_fork :
    ∀ {T : Type u} (S : ExactDiagonalForkSchema T) (a : T)
      (hterm : TerminalDiagonal S a),
      Function.Injective (fork3Embedding S a hterm).toFun
  /-- A determined terminal diagonal has exactly the marked local cone. -/
  determined_terminal_localCone :
    ∀ {T : Type u} (S : ExactDiagonalForkSchema T) (a : T)
      (hterm : TerminalDiagonal S a) (_hdet : DiagonalDetermined S a),
      Nonempty (RelIso Fork3Step (LocalConeStep S a hterm))
  /-- The independent role-separated comparator realizes the same fork. -/
  classic_instance :
    Function.Injective OperatorKO7.Meta.DistinctionBoundary.MinimalFork.IndependentClassicInstance.classicFork3Embedding.toFun
  /-- The equality-reflection comparator realizes the same fork. -/
  reflection_instance :
    Function.Injective OperatorKO7.Meta.DistinctionBoundary.MinimalFork.ReflectionInstanceBridge.reflectionFork3Embedding.toFun
  /-- KO7's three-node raw local cone is exactly relation-isomorphic to Fork3. -/
  ko7_localCone : Nonempty (RelIso Fork3Step
    OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7LocalCone.LocalRaw)
  /-- In fact every KO7 root diagonal is an exact terminal fork. -/
  ko7_all_diagonals :
    ∀ a : OperatorKO7.Trace,
      ¬ LocalJoinAt OperatorKO7.Meta.DistinctionBoundary.MinimalFork.KO7SchemaInstance.ko7ExactDiagonalFork (OperatorKO7.Trace.eqW a a)
  /-- The guarded raw root repair is confluent. -/
  guarded_root_confluent :
    ∀ source, ConfluentAt MiniEqWGuardedRootStep source
  /-- The canonical guarded root relation is greatest under the independent
  diagonal-safe subrelation policy. -/
  guarded_root_maximal :
    DiagonalSafeRootSubrel MiniEqWGuardedRootStep ∧
      ∀ {R : MiniEqWTerm → MiniEqWTerm → Prop},
        DiagonalSafeRootSubrel R →
          ∀ {s t}, R s t → MiniEqWGuardedRootStep s t
  /-- The same syntactic guard fails under unrestricted context rewriting. -/
  guarded_context_scope_wall :
    ¬ ConfluentAt MiniEqWGuardedCtxStep contextualCounterexample
  /-- Frozen comparison is a fully proved context-stable repair strategy. -/
  frozen_context_confluent : ∀ source, ConfluentAt FrozenCtxStep source
  /-- Normalize-before-compare is a fully proved context-stable repair strategy. -/
  normalized_comparison_confluent :
    ∀ source, ConfluentAt NormalizedComparisonStep source
  /-- Persistent distinction licensing is a fully proved full-context repair. -/
  persistent_context_confluent :
    ∀ source, ConfluentAt MiniEqWPersistentCtxStep source
  /-- Raw and licensed terminal multiplicities are exactly two and one. -/
  raw_multiplicity_two : terminalMultiplicity Fork3Step .source = 2
  licensed_multiplicity_one : terminalMultiplicity Fork3LicensedStep .source = 1
  /-- The structural Hartley support collapse is exactly one bit. -/
  structural_collapse_one_bit :
    structuralHartleyCollapse Fork3Step Fork3LicensedStep .source = 1
  /-- The live KO7 quantitative profiles transport exactly to the canonical
  minimal raw/licensed profiles. -/
  quantitative_profile_transport :
    ko7_raw_profile = minimal_raw_profile ∧
      ko7_licensed_profile = minimal_licensed_profile
  /-- Real semantic mode classification via fork embeddings. -/
  mode_classification :
    ∀ m : EqualityMode,
      ContainsCanonicalFork m ↔ m = EqualityMode.unguardedTotalizedRewrite

/-- The production crown constructor. -/
theorem minimal_distinction_boundary_crown : MinimalForkCrown.{u} := by
  refine {
    cardinality_minimal := fun hsl hsr hnj =>
      nonjoinable_peak_card_ge_three hsl hsr hnj,
    cardinality_attained := fork3_card_eq_three,
    initial := ⟨fork3_isInitial⟩,
    collapsed_signature_minimal := comparatorRole3_card_eq_three,
    separated_signature_minimal := comparatorRole5_card_eq_five,
    two_rule_surface := twoRuleId_card_eq_two,
    minimal_eqW_root_SN := minimalEqW_root_SN,
    minimal_eqW_context_SN := minimalEqW_context_SN,
    minimal_eqW_diagonal_nonconfluent := minimalEqW_closed_diagonal_not_confluent,
    deep_eqW_context_SN := OperatorKO7.Meta.DistinctionBoundary.MinimalFork.DeepEqW.deep_minimalTRS_SN,
    deep_eqW_rule_count_two := minimalEqW_rule_count_eq_two,
    deep_eqW_context_correspondence := @minimalEqW_custom_ctx_iff_generic_step,
    deep_eqW_not_localConfluent := OperatorKO7.Meta.DistinctionBoundary.MinimalFork.DeepEqW.deep_generic_not_localConfluent,
    exact_terminal_contains_fork := fun S a hterm =>
      fork3Embedding_injective S a hterm,
    determined_terminal_localCone := fun S a hterm hdet =>
      ⟨determined_terminal_diagonal_localCone_equiv_fork3 S a hterm hdet⟩,
    classic_instance := OperatorKO7.Meta.DistinctionBoundary.MinimalFork.IndependentClassicInstance.classicFork3Embedding_injective,
    reflection_instance := OperatorKO7.Meta.DistinctionBoundary.MinimalFork.ReflectionInstanceBridge.reflectionFork3Embedding_injective,
    ko7_localCone := OperatorKO7.Meta.DistinctionBoundary.MinimalFork.KO7LocalConeBridge.ko7_raw_local_cone_is_Fork3,
    ko7_all_diagonals := OperatorKO7.Meta.DistinctionBoundary.MinimalFork.KO7SchemaInstance.ko7_every_diagonal_not_localJoin,
    guarded_root_confluent := guarded_root_confluent,
    guarded_root_maximal := guardedRoot_greatest_diagonalSafe_restriction,
    guarded_context_scope_wall := guarded_full_context_not_confluent,
    frozen_context_confluent := frozen_comparison_context_confluent,
    normalized_comparison_confluent := normalizedComparison_confluent,
    persistent_context_confluent := persistentGuard_context_confluent,
    raw_multiplicity_two := fork3_raw_terminalMultiplicity_eq_two,
    licensed_multiplicity_one := fork3_licensed_terminalMultiplicity_eq_one,
    structural_collapse_one_bit := fork3_structuralHartleyCollapse_eq_one,
    quantitative_profile_transport := ko7_profile_eq_minimal_profile,
    mode_classification := containsCanonicalFork_iff_raw
  }


/-- Nonvacuity of the crown itself. -/
theorem minimalForkCrown_nonempty : Nonempty (MinimalForkCrown.{0}) :=
  ⟨minimal_distinction_boundary_crown⟩

end OperatorKO7.Meta.DistinctionBoundary.MinimalFork





