import OperatorKO7.Meta.BoundaryQuantitative.Transaction
import OperatorKO7.Meta.DistinctionBoundary.Quantitative.RepairCover
import OperatorKO7.Meta.DistinctionBoundary.Quantitative.WitnessRank
import OperatorKO7.Meta.DistinctionBoundary.Quantitative.FiniteDistinctionSurface

/-!
# Distinction quantitative instance

Relation: diagonal/off-diagonal defects, repair covers, and witness ranks are
separate product-profile coordinates.
Closure: finite set-cover and finite-surface laws.
Trust: PROVEN-IN-LEAN, reusing the Distinction quantitative package.
Scope: this file does not identify defect count, terminal multiplicity, and
repair cover. It exposes the permitted inequalities and fixtures only.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.BoundaryQuantitative

open OperatorKO7.Meta.DistinctionBoundary.Quantitative

universe u v

/-- Raw bad-pair profile: defect count is represented as carrier burden,
branch excess, and naive repair burden before a cover is supplied. -/
def distinctionRawBadProfile (badCount witnessRank : Nat) : ObstructionProfile where
  carrierBurden := badCount
  branchExcess := badCount
  repairCover := badCount
  witnessRank := witnessRank

/-- Licensed repair-cover profile: branch excess is closed, while repair-cover
cost is the actual minimum cover number, not the raw defect count. -/
def distinctionLicensedRepairProfile (badCount repairCount witnessRank : Nat) :
    ObstructionProfile where
  carrierBurden := badCount
  branchExcess := 0
  repairCover := repairCount
  witnessRank := witnessRank

theorem distinction_repair_profile_reduces
    {badCount repairCount witnessRank : Nat} (hrepair : repairCount <= badCount) :
    CoordinateLe
      (distinctionLicensedRepairProfile badCount repairCount witnessRank)
      (distinctionRawBadProfile badCount witnessRank) := by
  exact ⟨le_rfl, Nat.zero_le _, hrepair, le_rfl⟩

/-- Finite surface profile: the branch coordinate is the sum of diagonal
false positives and off-diagonal false negatives. -/
def finiteSurfaceProfile {A : Type u} {V : Type v}
    [Fintype A] [DecidableEq A] [Fintype V] [DecidableEq V]
    (S : FiniteDistinctionSurface A V) : ObstructionProfile where
  carrierBurden := Fintype.card A
  branchExcess := S.diagonalFalsePositive + S.offDiagonalFalseNegative
  repairCover := 0
  witnessRank := 0

theorem exactEqualitySurface_profile_branch_zero
    {A : Type u} [Fintype A] [DecidableEq A] :
    (finiteSurfaceProfile (FiniteDistinctionSurface.exactEqualitySurface (A := A))).branchExcess = 0 := by
  rcases FiniteDistinctionSurface.exactEqualitySurface_counts (A := A) with ⟨hdiag, hoff⟩
  simp [finiteSurfaceProfile, hdiag, hoff]

theorem sharedGuard_distinction_repair_reduces :
    CoordinateLe
      (distinctionLicensedRepairProfile
        sharedBadPairs.card
        (repairCoverNumber sharedBadPairs sharedGuardCoverage sharedGuard_coverable)
        1)
      (distinctionRawBadProfile sharedBadPairs.card 1) := by
  apply distinction_repair_profile_reduces
  rw [sharedGuard_repairCoverNumber_eq_one]
  norm_num [sharedBadPairs]

theorem licensedAdequacy_profile_witness_rank_one :
    (distinctionRawBadProfile 2 (witnessRank licensedAdequacy)).witnessRank = 1 := by
  rw [licensedAdequacy_rank_one]
  rfl

#print axioms distinction_repair_profile_reduces
#print axioms exactEqualitySurface_profile_branch_zero
#print axioms sharedGuard_distinction_repair_reduces
#print axioms licensedAdequacy_profile_witness_rank_one

end OperatorKO7.Meta.BoundaryQuantitative
