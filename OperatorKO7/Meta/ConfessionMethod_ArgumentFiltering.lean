import OperatorKO7.Meta.ConfessionMethod
import OperatorKO7.Meta.ConfessionMethod_DP

/-!
# Argument-filtering projection witness

This module defines a rank projection and a constructorwise filter into unary counter syntax.
It proves that the rank equals the registered dependency-pair projection, computes the filtered
shape of the duplicating rule, and packages the resulting projection-rank profile.

`SoundnessLicense.argumentFilteringSoundness` is a route-classification tag. It does not by
itself prove that termination of the filtered relation transfers to the source system. This
module therefore establishes the projection and its local filtered-step facts, not a global
termination theorem for the source rewrite system.
-/

namespace OperatorKO7.ConfessionMethodFamily

open OperatorKO7.Trace
open OperatorKO7.StepDuplicating
open OperatorKO7.StepDuplicating.StepDuplicatingSchema
open OperatorKO7.CompositionalImpossibility

/-- A witness selecting the third, zero-based counter coordinate of `recΔ`. -/
structure ArgumentFilteringWitness where
  keepRecurCoordinate : Fin 3
  keepRecurCoordinate_is_counter : keepRecurCoordinate = ⟨2, by decide⟩

/-- The concrete witness selecting coordinate `2` of the three `recΔ` arguments. -/
def schemaArgumentFilteringWitness : ArgumentFilteringWitness where
  keepRecurCoordinate := ⟨2, by decide⟩
  keepRecurCoordinate_is_counter := rfl

/-- Counter depth retained by the route: `delta` increments, `recΔ` follows its counter,
and all other constructors contribute zero. -/
@[simp] def argumentFilteringRankFn : Trace → Nat
  | void        => 0
  | delta t     => argumentFilteringRankFn t + 1
  | integrate _ => 0
  | merge _ _   => 0
  | app _ _     => 0
  | recΔ _ _ n  => argumentFilteringRankFn n
  | eqW _ _     => 0

/-- The argument-filtering rank is extensionally equal to the registered DP projection. -/
theorem argumentFilteringRankFn_eq_dpProjection :
    argumentFilteringRankFn = dpProjection := by
  funext t
  induction t <;> simp [argumentFilteringRankFn, dpProjection, *]

/-- Package the fixed argument-filtering rank and its four defining equations as a
`ConfessionCoreWitness`. -/
def ArgumentFilteringWitness.toConfessionCoreWitness
    (_W : ArgumentFilteringWitness) : ConfessionCoreWitness ko7Schema where
  rank := argumentFilteringRankFn
  rank_base := by rfl
  rank_succ := by intro t; rfl
  rank_wrap := by intro x y; rfl
  rank_recur := by intro b s n; rfl

/-- The projection-rank object induced by `argumentFilteringRankFn`. -/
def argumentFilteringDerivedRank : ProjectionRank ko7Schema where
  rank := argumentFilteringRankFn
  rank_base := by rfl
  rank_succ := by intro t; rfl
  rank_wrap := by intro x y; rfl
  rank_recur := by intro b s n; rfl

/-- The derived rank function agrees with the canonical DP projection rank function. -/
theorem argumentFilteringDerivedRank_eq_dp_core :
    argumentFilteringDerivedRank.rank = dpProjectionRank.rank := by
  simpa [argumentFilteringDerivedRank, dpProjectionRank] using
    argumentFilteringRankFn_eq_dpProjection

/-- The derived projection-rank object is extensionally equal to `dpProjectionRank`. -/
theorem argumentFilteringDerivedRank_eq_dpProjectionRank :
    argumentFilteringDerivedRank = dpProjectionRank := by
  ext t
  simpa [argumentFilteringDerivedRank, dpProjectionRank] using
    congrFun argumentFilteringRankFn_eq_dpProjection t

/-- The packaged rank assigns zero to every `app` term, so wrapper payload is erased. -/
theorem argumentFilteringWitness_forgets_wrapper_payload :
    ∀ x y : Trace,
      schemaArgumentFilteringWitness.toConfessionCoreWitness.rank (app x y) = 0 := by
  intro x y
  rfl

/-- The witness induces the canonical DP projection-rank object. -/
theorem argumentFilteringWitness_toConfessionCoreWitness_eq_core :
    schemaArgumentFilteringWitness.toConfessionCoreWitness.toProjectionRank =
      dpProjectionRank := by
  ext t
  simpa [ArgumentFilteringWitness.toConfessionCoreWitness, dpProjectionRank] using
    congrFun argumentFilteringRankFn_eq_dpProjection t

/-- Package the derived rank with the argument-filtering route tag. The tag is metadata and
does not supply a source-termination transfer theorem. -/
def argumentFilteringConfession : ConfessionMethod ko7Schema where
  toProjectionRank := argumentFilteringDerivedRank
  license := SoundnessLicense.argumentFilteringSoundness

/-- The exported confession method contains the derived argument-filtering rank. -/
theorem argumentFilteringConfession_is_derived :
    argumentFilteringConfession.toProjectionRank = argumentFilteringDerivedRank := rfl

/-- The argument-filtering and dependency-pair packages expose the same rank function. -/
theorem argumentFiltering_eq_dp_rank :
    argumentFilteringConfession.rank = dpConfession.rank := by
  simpa [argumentFilteringConfession, dpConfession, argumentFilteringDerivedRank,
    dpProjectionRank] using argumentFilteringRankFn_eq_dpProjection

/-- Unary counter syntax retained after filtering. -/
inductive FilteredCounterTerm
  | zero : FilteredCounterTerm
  | succ : FilteredCounterTerm → FilteredCounterTerm
  deriving DecidableEq, Repr

/-- The one-step predecessor relation on filtered unary counters. -/
inductive FilteredCounterStep : FilteredCounterTerm → FilteredCounterTerm → Prop
  | succ_step (n : FilteredCounterTerm) : FilteredCounterStep (.succ n) n

/-- Constructor handlers specifying a partial interpretation of `Trace` in filtered counters. -/
structure ConstructorwiseArgumentFilter where
  onBase : Option FilteredCounterTerm
  onSucc : Option FilteredCounterTerm → Option FilteredCounterTerm
  onIntegrate : Option FilteredCounterTerm → Option FilteredCounterTerm
  onMerge : Option FilteredCounterTerm → Option FilteredCounterTerm → Option FilteredCounterTerm
  onWrap : Option FilteredCounterTerm → Option FilteredCounterTerm → Option FilteredCounterTerm
  onRecur :
    Option FilteredCounterTerm → Option FilteredCounterTerm → Option FilteredCounterTerm →
      Option FilteredCounterTerm
  onEqW : Option FilteredCounterTerm → Option FilteredCounterTerm → Option FilteredCounterTerm

/-- Recursive evaluator induced by a constructorwise filter policy. -/
def applyConstructorwiseFilter (F : ConstructorwiseArgumentFilter) : Trace → Option FilteredCounterTerm
  | void => F.onBase
  | delta t => F.onSucc (applyConstructorwiseFilter F t)
  | integrate t => F.onIntegrate (applyConstructorwiseFilter F t)
  | merge x y => F.onMerge (applyConstructorwiseFilter F x) (applyConstructorwiseFilter F y)
  | app x y => F.onWrap (applyConstructorwiseFilter F x) (applyConstructorwiseFilter F y)
  | recΔ b s n =>
      F.onRecur
        (applyConstructorwiseFilter F b)
        (applyConstructorwiseFilter F s)
        (applyConstructorwiseFilter F n)
  | eqW x y => F.onEqW (applyConstructorwiseFilter F x) (applyConstructorwiseFilter F y)

/-- Keep `void` and `delta`, project `app` to its right argument and `recΔ` to its counter,
and reject the remaining constructors. -/
def counterOnlyConstructorFilter : ConstructorwiseArgumentFilter where
  onBase := some FilteredCounterTerm.zero
  onSucc := Option.map FilteredCounterTerm.succ
  onIntegrate := fun _ => none
  onMerge := fun _ _ => none
  onWrap := fun _ y => y
  onRecur := fun _ _ n => n
  onEqW := fun _ _ => none

/-- Direct recursive presentation of the concrete counter-only constructor filter. -/
@[simp] def argumentFilterTrace : Trace → Option FilteredCounterTerm
  | void => some FilteredCounterTerm.zero
  | delta t => Option.map FilteredCounterTerm.succ (argumentFilterTrace t)
  | integrate _ => none
  | merge _ _ => none
  | app _ y => argumentFilterTrace y
  | recΔ _ _ n => argumentFilterTrace n
  | eqW _ _ => none

/-- The direct recursive filter equals evaluation of `counterOnlyConstructorFilter`. -/
theorem argumentFilterTrace_eq_applyConstructorwiseFilter :
    argumentFilterTrace = applyConstructorwiseFilter counterOnlyConstructorFilter := by
  funext t
  induction t <;> simp [argumentFilterTrace, applyConstructorwiseFilter, counterOnlyConstructorFilter, *]

/-- Route-local evidence that the concrete filter erases wrapper payload and maps the
duplicating rule to a single filtered `succ` step. -/
structure ArgumentFilteringRouteEvidence where
  witness : ArgumentFilteringWitness
  constructorFilter : ConstructorwiseArgumentFilter
  realizesConstructorFilter :
    argumentFilterTrace = applyConstructorwiseFilter constructorFilter
  filteredDupLhs :
    ∀ b s n,
      argumentFilterTrace (recΔ b s (delta n)) =
        Option.map FilteredCounterTerm.succ (argumentFilterTrace n)
  filteredDupRhs :
    ∀ b s n,
      argumentFilterTrace (app s (recΔ b s n)) = argumentFilterTrace n
  payloadErased :
    ∀ s n,
      argumentFilterTrace (app s n) = argumentFilterTrace n
  filteredStepShape :
    ∀ b s n m,
      argumentFilterTrace n = some m →
      argumentFilterTrace (recΔ b s (delta n)) = some (FilteredCounterTerm.succ m)
      ∧ argumentFilterTrace (app s (recΔ b s n)) = some m
      ∧ FilteredCounterStep (FilteredCounterTerm.succ m) m

/-- The concrete route evidence obtained from the counter-only filter. -/
def schemaArgumentFilteringRouteEvidence : ArgumentFilteringRouteEvidence where
  witness := schemaArgumentFilteringWitness
  constructorFilter := counterOnlyConstructorFilter
  realizesConstructorFilter := argumentFilterTrace_eq_applyConstructorwiseFilter
  filteredDupLhs := by
    intro b s n
    rfl
  filteredDupRhs := by
    intro b s n
    rfl
  payloadErased := by
    intro s n
    rfl
  filteredStepShape := by
    intro b s n m hm
    refine ⟨?_, ?_, FilteredCounterStep.succ_step m⟩
    · simp [argumentFilterTrace, hm]
    · simpa [argumentFilterTrace] using hm

/-- Forget filter-specific fields while retaining the generic projection-rank equations. -/
def ArgumentFilteringRouteEvidence.toRouteEvidence
    (E : ArgumentFilteringRouteEvidence) : RouteEvidence ko7Schema where
  rank := E.witness.toConfessionCoreWitness.rank
  rank_base := E.witness.toConfessionCoreWitness.rank_base
  rank_succ := E.witness.toConfessionCoreWitness.rank_succ
  rank_wrap := E.witness.toConfessionCoreWitness.rank_wrap
  rank_recur := E.witness.toConfessionCoreWitness.rank_recur

/-- The concrete argument-filtering evidence viewed through the generic route interface. -/
abbrev schemaArgumentFilteringGenericRouteEvidence : RouteEvidence ko7Schema :=
  schemaArgumentFilteringRouteEvidence.toRouteEvidence

/-- The rank carried by the concrete route evidence satisfies the four generic projection
profile predicates. This is a rank-profile result, not a source-termination theorem. -/
theorem argumentFilteringRouteEvidence_implies_semantic_profile :
    NormalizedAtBase ko7Schema
      schemaArgumentFilteringRouteEvidence.witness.toConfessionCoreWitness.rank
    ∧ TracksSuccessorDepth ko7Schema
      schemaArgumentFilteringRouteEvidence.witness.toConfessionCoreWitness.rank
    ∧ ForgetsWrapperPayload ko7Schema
      schemaArgumentFilteringRouteEvidence.witness.toConfessionCoreWitness.rank
    ∧ FollowsRecursiveCounter ko7Schema
      schemaArgumentFilteringRouteEvidence.witness.toConfessionCoreWitness.rank := by
  have h :=
    ConfessionCoreWitness.satisfies_semantic_profile
      schemaArgumentFilteringRouteEvidence.witness.toConfessionCoreWitness
  simpa [schemaArgumentFilteringRouteEvidence] using h

/-- The concrete witness's rank satisfies the four generic projection profile predicates. -/
theorem argumentFilteringWitness_has_semantic_profile :
    NormalizedAtBase ko7Schema schemaArgumentFilteringWitness.toConfessionCoreWitness.rank
    ∧ TracksSuccessorDepth ko7Schema schemaArgumentFilteringWitness.toConfessionCoreWitness.rank
    ∧ ForgetsWrapperPayload ko7Schema schemaArgumentFilteringWitness.toConfessionCoreWitness.rank
    ∧ FollowsRecursiveCounter ko7Schema schemaArgumentFilteringWitness.toConfessionCoreWitness.rank := by
  exact schemaArgumentFilteringWitness.toConfessionCoreWitness.satisfies_semantic_profile

end OperatorKO7.ConfessionMethodFamily
