import OperatorKO7.Meta.BoundaryQuantitative.Transaction
import OperatorKO7.Meta.Recursor.TraceAction
import OperatorKO7.Meta.Recursor.GaugeCost

/-!
# Orientation quantitative instance

Relation: live trace action and sufficient projection width are packaged as
separate boundary-profile coordinates.
Closure: finite natural-number recursor laws.
Trust: PROVEN-IN-LEAN, reusing the Recursor quantitative laws.
Scope: Orientation/Operational instance only. `projBits` is used through the
clarified sufficient-width alias.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.BoundaryQuantitative

open OperatorKO7.Meta.Recursor.TraceAction
open OperatorKO7.Meta.Recursor.GaugeCost

/-- Raw orientation profile: the live trace carries the carrier burden, while
the sufficient projection width is the witness-rank coordinate. -/
def orientationRawProfile (k w cstar : Nat) : ObstructionProfile where
  carrierBurden := liveTraceAction k w cstar
  branchExcess := conMassCell k w
  repairCover := 0
  witnessRank := sufficientProjectionBits k

/-- Licensed orientation profile: the progress counter is retained with a
sufficient fixed-width projection. -/
def orientationLicensedProfile (k : Nat) : ObstructionProfile where
  carrierBurden := sufficientProjectionBits k
  branchExcess := 0
  repairCover := 0
  witnessRank := sufficientProjectionBits k

/-- Orientation transaction cost: projection bits plus the manuscript confession
mass are kept as transaction-side data, not obstruction coordinates. -/
def orientationTransactionCost (k beta : Nat) : TransactionCost where
  certificateBits := sufficientProjectionBits k
  ledgerBits := conMassPayManuscript k beta
  externalAssumptions := 1

theorem orientation_liveTrace_alias (k w cstar : Nat) :
    liveTraceAction k w cstar = traceAction k w cstar :=
  liveTraceAction_eq_traceAction k w cstar

theorem orientation_projection_fits (k : Nat) :
    k < 2 ^ sufficientProjectionBits k :=
  (L8_sufficientProjection_comparison k).1

/-- Conditional coordinate reduction. The carrier inequality is explicit
because sufficiency of the projection width does not imply it is always below
every degenerate live-action value. -/
theorem orientation_profile_coordinate_reduction
    (k w cstar : Nat)
    (hcarrier : sufficientProjectionBits k <= liveTraceAction k w cstar) :
    CoordinateLe (orientationLicensedProfile k) (orientationRawProfile k w cstar) := by
  exact ⟨hcarrier, Nat.zero_le _, le_rfl, le_rfl⟩

/-- Non-vacuity fixture for the concrete parameters used in the recursor sample. -/
theorem orientation_sample_strict_reduction :
    StrictlyReduces (orientationLicensedProfile 3) (orientationRawProfile 3 3 6) := by
  constructor
  · exact orientation_profile_coordinate_reduction 3 3 6
      (by norm_num [sufficientProjectionBits, projBits, liveTraceAction, traceAction, tri])
  · left
    norm_num [orientationLicensedProfile, orientationRawProfile, sufficientProjectionBits,
      projBits, liveTraceAction, traceAction, tri]

theorem orientation_sample_transaction_cost :
    (orientationTransactionCost 3 2).total = 23 := by
  norm_num [orientationTransactionCost, TransactionCost.total, sufficientProjectionBits,
    projBits, conMassPayManuscript, tri]

#print axioms orientation_liveTrace_alias
#print axioms orientation_projection_fits
#print axioms orientation_profile_coordinate_reduction
#print axioms orientation_sample_strict_reduction
#print axioms orientation_sample_transaction_cost

end OperatorKO7.Meta.BoundaryQuantitative
