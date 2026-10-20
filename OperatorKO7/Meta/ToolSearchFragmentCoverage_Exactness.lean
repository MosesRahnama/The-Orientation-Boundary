import OperatorKO7.Meta.ToolSearchFragmentCoverage_ListAudit

/-!
# Tool Search Fragment Coverage Exactness

This module closes the finite-inventory bookkeeping for the M4 tool-search
coverage stack. It records exact membership, exact list size, NoDup, and exact
group counts for the theorem-backed and residual family lists.
-/

namespace OperatorKO7.ToolSearchFragmentCoverageExactness

open OperatorKO7.ToolSearchFragmentCoverage
open OperatorKO7.ToolSearchFragmentCoverageStatus
open OperatorKO7.ToolSearchFragmentCoveragePerFamily
open OperatorKO7.ToolSearchFragmentCoverageListAudit

/-- The theorem-backed family list has no duplicates. -/
theorem theoremBackedToolSearchFamilies_nodup :
    theoremBackedToolSearchFamilies.Nodup := by
  simp [theoremBackedToolSearchFamilies]

/-- The theorem-backed family list has exact length `14`. -/
theorem theoremBackedToolSearchFamilies_length :
    theoremBackedToolSearchFamilies.length = 14 := by
  rfl

/-- The residual family list has no duplicates. -/
theorem residualToolSearchFamilies_nodup :
    residualToolSearchFamilies.Nodup := by
  simp [residualToolSearchFamilies]

/-- The residual family list has exact length `2`. -/
theorem residualToolSearchFamilies_length :
    residualToolSearchFamilies.length = 2 := by
  rfl

/-- Filtering the theorem-backed list by the direct-scalar group keeps exactly
the direct-scalar families. -/
theorem theoremBackedToolSearchFamilies_directScalar_filter :
    theoremBackedToolSearchFamilies.filter (fun family =>
      decide (toolSearchFragmentGroup family = ToolSearchFragmentGroup.directScalar)) =
      [ .directAdditive
      , .directAffine
      , .directQuadratic
      , .directMultilinear
      , .directPolynomial
      ] := by
  rfl

/-- Filtering the theorem-backed list by the extended-direct group keeps exactly
the extended-direct families. -/
theorem theoremBackedToolSearchFamilies_extendedDirect_filter :
    theoremBackedToolSearchFamilies.filter (fun family =>
      decide (toolSearchFragmentGroup family = ToolSearchFragmentGroup.extendedDirect)) =
      [ .extendedCrossQuadratic
      , .extendedMaxPlus
      , .extendedWPOPolynomial
      ] := by
  rfl

/-- Filtering the theorem-backed list by the matrix-projection group keeps exactly
the matrix-projection families. -/
theorem theoremBackedToolSearchFamilies_matrixProjection_filter :
    theoremBackedToolSearchFamilies.filter (fun family =>
      decide (toolSearchFragmentGroup family = ToolSearchFragmentGroup.matrixProjection)) =
      [ .matrixFixedRow
      , .matrixRowSum
      , .matrixArcticFixedRow
      , .matrixArcticRowSum
      , .matrixTropicalFixedRow
      , .matrixTropicalRowSum
      ] := by
  rfl

/-- Exact iff-level membership catalog for the theorem-backed family list. -/
theorem theoremBackedToolSearchFamilies_complete_exact
    (family : ToolSearchFragmentFamily) :
    family ∈ theoremBackedToolSearchFamilies ↔
      family = .directAdditive
      ∨ family = .directAffine
      ∨ family = .directQuadratic
      ∨ family = .directMultilinear
      ∨ family = .directPolynomial
      ∨ family = .extendedCrossQuadratic
      ∨ family = .extendedMaxPlus
      ∨ family = .extendedWPOPolynomial
      ∨ family = .matrixFixedRow
      ∨ family = .matrixRowSum
      ∨ family = .matrixArcticFixedRow
      ∨ family = .matrixArcticRowSum
      ∨ family = .matrixTropicalFixedRow
      ∨ family = .matrixTropicalRowSum := by
  cases family <;> simp [theoremBackedToolSearchFamilies]

/-- Exact iff-level membership catalog for the residual family list. -/
theorem residualToolSearchFamilies_complete_exact
    (family : ResidualFragmentFamily) :
    family ∈ residualToolSearchFamilies ↔
      family = .unrestrictedNonlinearDirect
      ∨ family = .unrestrictedMatrixClasses := by
  cases family <;> simp [residualToolSearchFamilies]

/-- Exact direct-scalar group catalog inside the theorem-backed list. -/
theorem direct_scalar_family_group_catalog
    (family : ToolSearchFragmentFamily) :
    (family ∈ theoremBackedToolSearchFamilies
      ∧ toolSearchFragmentGroup family = ToolSearchFragmentGroup.directScalar) ↔
      family = .directAdditive
      ∨ family = .directAffine
      ∨ family = .directQuadratic
      ∨ family = .directMultilinear
      ∨ family = .directPolynomial := by
  cases family <;> simp [theoremBackedToolSearchFamilies, toolSearchFragmentGroup]

/-- Exact extended-direct group catalog inside the theorem-backed list. -/
theorem extended_direct_family_group_catalog
    (family : ToolSearchFragmentFamily) :
    (family ∈ theoremBackedToolSearchFamilies
      ∧ toolSearchFragmentGroup family = ToolSearchFragmentGroup.extendedDirect) ↔
      family = .extendedCrossQuadratic
      ∨ family = .extendedMaxPlus
      ∨ family = .extendedWPOPolynomial := by
  cases family <;> simp [theoremBackedToolSearchFamilies, toolSearchFragmentGroup]

/-- Exact matrix-projection group catalog inside the theorem-backed list. -/
theorem matrix_projection_family_group_catalog
    (family : ToolSearchFragmentFamily) :
    (family ∈ theoremBackedToolSearchFamilies
      ∧ toolSearchFragmentGroup family = ToolSearchFragmentGroup.matrixProjection) ↔
      family = .matrixFixedRow
      ∨ family = .matrixRowSum
      ∨ family = .matrixArcticFixedRow
      ∨ family = .matrixArcticRowSum
      ∨ family = .matrixTropicalFixedRow
      ∨ family = .matrixTropicalRowSum := by
  cases family <;> simp [theoremBackedToolSearchFamilies, toolSearchFragmentGroup]

/-- Exact group-count partition of the theorem-backed family list. -/
theorem tool_search_group_partition_catalog :
    ((theoremBackedToolSearchFamilies.filter fun family =>
        decide (toolSearchFragmentGroup family = ToolSearchFragmentGroup.directScalar)).length = 5)
    ∧ ((theoremBackedToolSearchFamilies.filter fun family =>
        decide (toolSearchFragmentGroup family = ToolSearchFragmentGroup.extendedDirect)).length = 3)
    ∧ ((theoremBackedToolSearchFamilies.filter fun family =>
        decide (toolSearchFragmentGroup family = ToolSearchFragmentGroup.matrixProjection)).length = 6) := by
  constructor
  · rw [theoremBackedToolSearchFamilies_directScalar_filter]
    rfl
  constructor
  · rw [theoremBackedToolSearchFamilies_extendedDirect_filter]
    rfl
  · rw [theoremBackedToolSearchFamilies_matrixProjection_filter]
    rfl

/-- Paper-facing proposition packaging exact finite inventory bookkeeping for
the M4 tool-search coverage stack. -/
abbrev ToolSearchFragmentExactInventory : Prop :=
  theoremBackedToolSearchFamilies.Nodup
  ∧ theoremBackedToolSearchFamilies.length = 14
  ∧ residualToolSearchFamilies.Nodup
  ∧ residualToolSearchFamilies.length = 2
  ∧ ((theoremBackedToolSearchFamilies.filter fun family =>
        decide (toolSearchFragmentGroup family = ToolSearchFragmentGroup.directScalar)).length = 5)
  ∧ ((theoremBackedToolSearchFamilies.filter fun family =>
        decide (toolSearchFragmentGroup family = ToolSearchFragmentGroup.extendedDirect)).length = 3)
  ∧ ((theoremBackedToolSearchFamilies.filter fun family =>
        decide (toolSearchFragmentGroup family = ToolSearchFragmentGroup.matrixProjection)).length = 6)

/-- Exact finite inventory for the theorem-backed and residual tool-search
family lists. -/
theorem tool_search_fragment_exact_inventory : ToolSearchFragmentExactInventory := by
  refine ⟨theoremBackedToolSearchFamilies_nodup,
    theoremBackedToolSearchFamilies_length,
    residualToolSearchFamilies_nodup,
    residualToolSearchFamilies_length,
    ?_, ?_, ?_⟩
  exact tool_search_group_partition_catalog.1
  exact tool_search_group_partition_catalog.2.1
  exact tool_search_group_partition_catalog.2.2

end OperatorKO7.ToolSearchFragmentCoverageExactness
