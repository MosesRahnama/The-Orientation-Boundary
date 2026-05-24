import OperatorKO7.Meta.ConstructionMethodClassification
import OperatorKO7.Meta.BenchmarkedPrimitiveRecursionFamily
import OperatorKO7.Meta.RecCore

/-!
# Transformed-Call Classification

This module continues the M1 classification layer with an explicit W2 surface.
It stays narrow: the carrier is built around theorem-backed transformed-call
witnesses already present in the artifact, not around a generic dependency-pair
library.

The canonical W2 routes formalized here are:

- the KO7 DP-projection route for the duplicating benchmark-family member;
- the benchmark-family transformed-call route for the linear member.
-/

namespace OperatorKO7.TransformedCallClassification

open OperatorKO7
open OperatorKO7.ConstructionMethodClassification
open OperatorKO7.BenchmarkedPRCFamily
open OperatorKO7.RecCore

/-- Permitted transformed-call routes for the narrow W2 layer. -/
inductive W2TransformClass where
  | ko7DPProjection
  | benchmarkFamilyTransformedCall
deriving DecidableEq, Repr

/-- The KO7 projection route is the existing transformed-call projection witness on the
RecCore duplicating step. -/
theorem ko7_dp_projection_route_orients_rec_succ :
    ∀ b s n : RecCoreTerm,
      dpProjection (RecCoreTerm.app s (RecCoreTerm.recΔ b s n)) <
        dpProjection (RecCoreTerm.recΔ b s (RecCoreTerm.delta n)) := by
  intro b s n
  exact dp_projection_orients_rec_succ b s n

/-- The theorem-bearing evidence attached to a permitted W2 transform class. -/
inductive W2TransformEvidence : W2TransformClass → PRCConfig → Type where
  | ko7DPProjectionImport :
      (projectionRoute : ∀ b s n : RecCoreTerm,
        dpProjection (RecCoreTerm.app s (RecCoreTerm.recΔ b s n)) <
          dpProjection (RecCoreTerm.recΔ b s (RecCoreTerm.delta n))) →
      (witness : HasTransformedCallWitness fullDuplicating) →
      W2TransformEvidence .ko7DPProjection fullDuplicating
  | benchmarkFamilyTransformedCallImport {cfg : PRCConfig} :
      (witness : HasTransformedCallWitness cfg) →
      W2TransformEvidence .benchmarkFamilyTransformedCall cfg

/-- A first-class W2 construction success carries theorem-level transformed-call evidence. -/
structure W2ConstructionSuccess where
  route : ConstructionRoute
  route_is_w2 : route = .W2
  target : PRCConfig
  transformClass : W2TransformClass
  evidence : W2TransformEvidence transformClass target

/-- The permitted W2 transforms restated as a proposition carrying the theorem payload. -/
inductive PermittedW2Transform : W2TransformClass → PRCConfig → Prop where
  | ko7DPProjection :
      (projectionRoute : ∀ b s n : RecCoreTerm,
        dpProjection (RecCoreTerm.app s (RecCoreTerm.recΔ b s n)) <
          dpProjection (RecCoreTerm.recΔ b s (RecCoreTerm.delta n))) →
      (witness : HasTransformedCallWitness fullDuplicating) →
      PermittedW2Transform .ko7DPProjection fullDuplicating
  | benchmarkFamilyTransformedCall {cfg : PRCConfig} :
      (witness : HasTransformedCallWitness cfg) →
      PermittedW2Transform .benchmarkFamilyTransformedCall cfg

/-- Any theorem-backed W2 success must realize one of the permitted transformed-call routes. -/
theorem w2_success_requires_permitted_transform (S : W2ConstructionSuccess) :
    PermittedW2Transform S.transformClass S.target := by
  rcases S with ⟨_, _, _, _, evidence⟩
  cases evidence with
  | ko7DPProjectionImport projectionRoute witness =>
      exact PermittedW2Transform.ko7DPProjection projectionRoute witness
  | benchmarkFamilyTransformedCallImport witness =>
      exact PermittedW2Transform.benchmarkFamilyTransformedCall witness

/-- Every theorem-backed W2 success packages an underlying transformed-call witness. -/
theorem w2_success_requires_transformed_call_witness (S : W2ConstructionSuccess) :
    HasTransformedCallWitness S.target := by
  rcases S with ⟨_, _, _, _, evidence⟩
  cases evidence with
  | ko7DPProjectionImport _ witness =>
      exact witness
  | benchmarkFamilyTransformedCallImport witness =>
      exact witness

/-- Canonical W2 success witness using the KO7 DP-projection route on the duplicating member. -/
def fullDuplicating_w2_success : W2ConstructionSuccess where
  route := .W2
  route_is_w2 := rfl
  target := fullDuplicating
  transformClass := .ko7DPProjection
  evidence := .ko7DPProjectionImport
    ko7_dp_projection_route_orients_rec_succ
    fullDuplicating_has_transformed_call_witness

/-- Canonical W2 success witness using the benchmark-family transformed-call route. -/
def fullLinear_w2_success : W2ConstructionSuccess where
  route := .W2
  route_is_w2 := rfl
  target := fullLinear
  transformClass := .benchmarkFamilyTransformedCall
  evidence := .benchmarkFamilyTransformedCallImport
    fullLinear_has_transformed_call_witness

/-- The duplicating W2 success extracts the KO7 DP-projection transform. -/
theorem fullDuplicating_w2_success_requires_ko7_dp_projection :
    PermittedW2Transform .ko7DPProjection fullDuplicating := by
  simpa [fullDuplicating_w2_success] using
    w2_success_requires_permitted_transform fullDuplicating_w2_success

/-- The linear W2 success extracts the benchmark-family transformed-call route. -/
theorem fullLinear_w2_success_requires_benchmark_family_transform :
    PermittedW2Transform .benchmarkFamilyTransformedCall fullLinear := by
  simpa [fullLinear_w2_success] using
    w2_success_requires_permitted_transform fullLinear_w2_success

/-- The duplicating W2 success extracts the underlying transformed-call witness. -/
theorem fullDuplicating_w2_success_requires_transformed_call_witness :
    HasTransformedCallWitness fullDuplicating := by
  simpa [fullDuplicating_w2_success] using
    w2_success_requires_transformed_call_witness fullDuplicating_w2_success

/-- The linear W2 success extracts the underlying transformed-call witness. -/
theorem fullLinear_w2_success_requires_transformed_call_witness :
    HasTransformedCallWitness fullLinear := by
  simpa [fullLinear_w2_success] using
    w2_success_requires_transformed_call_witness fullLinear_w2_success

/-- The duplicating W2 route remains separated from direct whole-term search. -/
theorem fullDuplicating_w2_separates_from_direct_search :
    fullDuplicating_w2_success.route ≠ .W0 ∧
      HasTransformedCallWitness fullDuplicating ∧
      ¬ HasDirectWitness fullDuplicating := by
  refine ⟨?_, fullDuplicating_has_transformed_call_witness,
    fullDuplicating_has_no_direct_witness⟩
  simp [fullDuplicating_w2_success]

/-- The duplicating transformed-call route is the same KO7 DP route carried by
the confession-method convergence package. -/
theorem fullDuplicating_w2_success_projects_confession_route_evidence :
    fullDuplicating_w2_success.transformClass = .ko7DPProjection
    ∧ PermittedW2Transform .ko7DPProjection fullDuplicating
    ∧ OperatorKO7.ConfessionMethodFamily.confessionRouteConvergencePackage.dpRouteEvidence
        = OperatorKO7.ConfessionMethodFamily.confessionRouteConvergencePackage.commonRouteEvidence
    ∧ HasTransformedCallWitness fullDuplicating := by
  exact ⟨rfl,
    fullDuplicating_w2_success_requires_ko7_dp_projection,
    OperatorKO7.ConfessionMethodFamily.confessionRouteConvergencePackage_projects_route_agreement.1,
    fullDuplicating_w2_success_requires_transformed_call_witness⟩

/-- Combined catalog for the canonical theorem-backed W2 witnesses formalized here. -/
theorem canonical_w2_witness_catalog :
    (fullDuplicating_w2_success.target = fullDuplicating ∧
      fullDuplicating_w2_success.transformClass = .ko7DPProjection ∧
      PermittedW2Transform .ko7DPProjection fullDuplicating ∧
      HasTransformedCallWitness fullDuplicating) ∧
      (fullLinear_w2_success.target = fullLinear ∧
        fullLinear_w2_success.transformClass = .benchmarkFamilyTransformedCall ∧
        PermittedW2Transform .benchmarkFamilyTransformedCall fullLinear ∧
        HasTransformedCallWitness fullLinear) := by
  refine ⟨?_, ?_⟩
  · exact ⟨rfl, rfl, fullDuplicating_w2_success_requires_ko7_dp_projection,
      fullDuplicating_w2_success_requires_transformed_call_witness⟩
  · exact ⟨rfl, rfl, fullLinear_w2_success_requires_benchmark_family_transform,
      fullLinear_w2_success_requires_transformed_call_witness⟩

end OperatorKO7.TransformedCallClassification
