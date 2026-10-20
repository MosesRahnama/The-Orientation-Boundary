import OperatorKO7.Meta.BoundaryOperator.TypedRefusalCompleteness
import OperatorKO7.QEC.Codes.BranchLicense

set_option autoImplicit false

open scoped BigOperators

/-!
# UUET observation interface: licensed Y/N/U/H emission (U-04)

A UUET observation emits one of four typed outcomes Y/N/U/H, and the decision is
admitted only with its branch license. This module imports the boundary-operator
typed-refusal carrier and the QEC branch-license anchor, identifies the two as the
same four-way licensed interface, and re-exports the QEC admission bound under a
UUET-facing name.

Load-bearing content:

* `uuet_observation_exhaustive`: every observation outcome is one of Y/N/U/H.
* `refusal_branch_agree`: the boundary-operator refusal carrier and the QEC decoder
 branch are the same four-way interface (a genuine carrier identification).
* `uuet_qec_observation_licensed`: the in-code posterior emits a licensed identity (N)
 branch, the outside-code posterior a licensed halt (H) branch.
* `uuet_licensed_observation_error_bound`: over any finite cohort of accepted
 (licensed Y/N) observations with nonnegative weights, the weighted-mean error is at
 most `1 - tauY`, the branch-license complement (the QEC `thm:abstention-rate` bound).

This file contains no `sorry`, no `admit`, no new `axiom`, no `native_decide`, no
`bv_decide`, no `@[csimp]`, no `unsafe`, no `partial`, and no `opaque`. Headline
declarations are `#print axioms`-checked at the bottom against the baseline whitelist.

Claim type: PROVEN-IN-LEAN (carrier identification + the real admission inequality).
The reading of Y/N/U/H as physical measurement outcomes is ANALOGY (docstring only).
-/

namespace OperatorKO7.Meta.UUET

open OperatorKO7.Meta.BoundaryOperator
open QEC.Codes
open QEC.Codes.Abstention
open QEC.Codes.BranchLicense

/-- The four-way licensed observation interface, as the boundary-operator refusal
carrier mapped to the QEC decoder branch. -/
def refusalToQECBranch : RefusalType → QECBranch
  | .Y => .correction
  | .N => .identity
  | .U => .undecidable
  | .H => .halt

/-- A QEC decoder decision read as a boundary-operator refusal type. -/
def refusalOfDecision : AbstentionDecision → RefusalType
  | .Y => .Y
  | .N => .N
  | .U => .U
  | .H => .H

/-- **Carrier identification.** The boundary-operator refusal carrier (Y/N/U/H) and the
QEC decoder branch carrier (correction/identity/undecidable/halt) are the same four-way
licensed interface: reading a decision as a refusal type and then mapping to a QEC
branch agrees with the decoder's own `branchOfDecision`. -/
theorem refusal_branch_agree (d : AbstentionDecision) :
    refusalToQECBranch (refusalOfDecision d) = branchOfDecision d := by
  cases d <;> rfl

/-- **Observation exhaustiveness.** Every UUET observation outcome is one of the four
typed refusal outcomes Y/N/U/H; there is no fifth outcome. -/
theorem uuet_observation_exhaustive (r : RefusalType) :
    r = RefusalType.Y ∨ r = RefusalType.N ∨ r = RefusalType.U ∨ r = RefusalType.H :=
  refusalType_exhaustive r

/-- **Licensed QEC observation (non-vacuity).** The in-code posterior emits a licensed
identity (N) branch and the outside-code posterior emits a licensed halt (H) branch:
both branch-license arms used by the QEC paper are inhabited, so the licensed
observation interface is not vacuous. -/
theorem uuet_qec_observation_licensed (decoder : AbstentionDecoder) :
    DecisionLicensed identityEvidence (Abstention.decide decoder inCodePosterior)
      ∧ DecisionLicensed haltEvidence (Abstention.decide decoder outOfCodePosterior) :=
  qec_branch_license_nonvacuous decoder

/-- **Licensed-observation error bound (UUET reading of `thm:abstention-rate`).** Over
any finite cohort whose observations are all accepted (licensed Y or N) branches, with
nonnegative weights summing to a positive total, the weighted-mean error is at most
`1 - tauY`: accepting a branch only under the `tauY` license bounds its error by the
license complement. -/
theorem uuet_licensed_observation_error_bound {Ω : Type*}
    (decoder : AbstentionDecoder) (cohort : Finset Ω)
    (p : Ω → CalibratedPosterior) (weight : Ω → ℝ)
    (hw : ∀ ω ∈ cohort, 0 ≤ weight ω)
    (hpos : 0 < ∑ ω ∈ cohort, weight ω)
    (haccept : ∀ ω ∈ cohort,
      Abstention.decide decoder (p ω) = .Y ∨ Abstention.decide decoder (p ω) = .N) :
    (∑ ω ∈ cohort, weight ω *
        (1 - acceptedConfidence (p ω) (Abstention.decide decoder (p ω))))
      / (∑ ω ∈ cohort, weight ω) ≤ 1 - decoder.tauY :=
  accepted_cohort_mean_error_le decoder cohort p weight hw hpos haccept

#print axioms refusal_branch_agree
#print axioms uuet_observation_exhaustive
#print axioms uuet_qec_observation_licensed
#print axioms uuet_licensed_observation_error_bound

end OperatorKO7.Meta.UUET
