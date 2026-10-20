import OperatorKO7.Meta.BoundaryQuantitative.Transaction

/-!
# QEC obstruction profiles

The two finite obstruction profiles of the QEC row of the quantitative atlas, as coordinate
records: the correctable profile closes the branch excess, the uncorrectable profile keeps one unit
of branch excess and one unit of refusal rank. The boundary-instance anchors for these profiles are
in `Meta/BoundaryQuantitative/QECInstance.lean`.

Relation: obstruction profiles compared coordinatewise.
Closure: the four profile coordinates.
External trust: none.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.BoundaryQuantitative

/-- Correctable QEC profile: recovery is licensed and the branch excess is
closed at the boundary carrier. -/
def qecCorrectableProfile : ObstructionProfile where
  carrierBurden := 1
  branchExcess := 0
  repairCover := 1
  witnessRank := 0

/-- Uncorrectable QEC profile: the finite carrier routes to typed refusal. -/
def qecUncorrectableProfile : ObstructionProfile where
  carrierBurden := 1
  branchExcess := 1
  repairCover := 1
  witnessRank := 1

theorem qec_correctable_profile_reduces_uncorrectable :
    StrictlyReduces qecCorrectableProfile qecUncorrectableProfile := by
  unfold StrictlyReduces CoordinateLe qecCorrectableProfile qecUncorrectableProfile
  exact ⟨⟨by norm_num, by norm_num, by norm_num, by norm_num⟩, Or.inr (Or.inl (by norm_num))⟩

end OperatorKO7.Meta.BoundaryQuantitative
