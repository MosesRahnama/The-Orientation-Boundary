import OperatorKO7.Kernel
import OperatorKO7.Meta.BoundaryGeneral.PayloadStress
import OperatorKO7.Meta.SchemaConfessionDominance
import OperatorKO7.Meta.SafeStep.RefusalLoad
import OperatorKO7.Meta.DistinctionBoundary.RepairRoutes
import OperatorKO7.Meta.InformationalIncompleteness.AxisGrowthSeparation
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Verdict-retaining cost dual for the orientation and distinction axes

This module packages the cost-side dual named in the Distinction Boundary paper.
The shared object is finite additive charge accounting on verdict-retaining
licensed routes.

* orientation axis: the dependency-pair confession keeps the termination verdict
  and carries the triangular carrier burden already formalized as
  `PayloadStress.cumulativeCarrier`;
* distinction axis: guarded rewriting keeps off-diagonal distinction verdicts and
  carries the refusal load already formalized in `SafeStep.RefusalLoad`;
* verdict-nulling routes, such as the inert-witness repair, carry no
  retained-verdict charge.

The orientation side is tied back to the Operational Inexpressibility burden
surface by the doubled identity with
`StepDuplicatingSchema.BaseDuplicatingSystem.confessedBurdenDoubled`.
-/

set_option autoImplicit false

open OperatorKO7 Trace
open scoped BigOperators

namespace OperatorKO7.Meta.DistinctionBoundary.CostDual

/-! ## Generic additive charge ledger -/

/-- A finite boundary-charge law over event tokens. -/
structure BoundaryChargeLaw (Event : Type) where
  /-- Charge assigned to one event. -/
  charge : Event -> Nat

/-- Total charge over a finite event list. -/
def totalCharge {Event : Type} (L : BoundaryChargeLaw Event)
    (events : List Event) : Nat :=
  (events.map L.charge).sum

/-- Additivity over concatenated event ledgers. -/
theorem totalCharge_append {Event : Type} (L : BoundaryChargeLaw Event)
    (xs ys : List Event) :
    totalCharge L (xs ++ ys) = totalCharge L xs + totalCharge L ys := by
  simp [totalCharge, List.map_append, List.sum_append]

/-- Closed form for a repeated event with constant charge `c`. -/
theorem totalCharge_replicate_const {Event : Type} (L : BoundaryChargeLaw Event)
    (e : Event) (N c : Nat) (h : L.charge e = c) :
    totalCharge L (List.replicate N e) = N * c := by
  induction N with
  | zero =>
      simp [totalCharge]
  | succ N ih =>
      simp [totalCharge, h, Nat.succ_mul]

private theorem list_sum_range_eq_finset_sum (f : Nat -> Nat) (n : Nat) :
    (List.map f (List.range n)).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [List.sum_range_succ, Finset.sum_range_succ, ih]

/-! ## Orientation instance: confessed carrier burden -/

/-- Orientation-axis per-depth charge: event `i` carries `(i+1)` payload copies. -/
def orientationChargeLaw (L : Nat) : BoundaryChargeLaw Nat where
  charge := fun i => (i + 1) * L

/-- The depth events for stages `0, ..., K`. -/
def orientationEvents (K : Nat) : List Nat := List.range (K + 1)

/-- The finite charge ledger equals the existing triangular carrier-burden
function. -/
theorem orientation_totalCharge_eq_cumulativeCarrier (K L : Nat) :
    totalCharge (orientationChargeLaw L) (orientationEvents K)
      =
        _root_.OperatorKO7.Meta.BoundaryGeneral.PayloadStress.cumulativeCarrier K L := by
  unfold totalCharge orientationChargeLaw orientationEvents
    _root_.OperatorKO7.Meta.BoundaryGeneral.PayloadStress.cumulativeCarrier
  exact list_sum_range_eq_finset_sum (fun i => (i + 1) * L) (K + 1)

/-- Division-free triangular law for the orientation charge. -/
theorem orientation_two_mul_totalCharge (K L : Nat) :
    2 * totalCharge (orientationChargeLaw L) (orientationEvents K)
      = (K + 1) * (K + 2) * L := by
  rw [orientation_totalCharge_eq_cumulativeCarrier]
  exact _root_.OperatorKO7.Meta.BoundaryGeneral.PayloadStress.two_mul_cumulativeCarrier K L

/-- The orientation charge is the Operational Inexpressibility confessed-burden
quantity, stated in the doubled division-free form used by that paper's Lean
surface. -/
theorem orientation_totalCharge_doubled_eq_confessedBurdenDoubled
    (K L : Nat) :
    2 * totalCharge (orientationChargeLaw L) (orientationEvents K)
      =
        _root_.OperatorKO7.StepDuplicating.StepDuplicatingSchema.BaseDuplicatingSystem.confessedBurdenDoubled K L := by
  rw [orientation_two_mul_totalCharge]
  rfl

/-- Equivalent bridge from `PayloadStress.cumulativeCarrier` to the Operational
Inexpressibility confessed-burden surface. -/
theorem cumulativeCarrier_doubled_eq_confessedBurdenDoubled
    (K L : Nat) :
    2 * _root_.OperatorKO7.Meta.BoundaryGeneral.PayloadStress.cumulativeCarrier K L
      =
        _root_.OperatorKO7.StepDuplicating.StepDuplicatingSchema.BaseDuplicatingSystem.confessedBurdenDoubled K L := by
  rw [_root_.OperatorKO7.Meta.BoundaryGeneral.PayloadStress.two_mul_cumulativeCarrier]
  rfl

/-- The retained orientation-route charge is unbounded at any positive payload
length. -/
theorem orientation_totalCharge_unbounded (L : Nat) (hL : 1 <= L) (N : Nat) :
    exists K, N <= totalCharge (orientationChargeLaw L) (orientationEvents K) := by
  rcases _root_.OperatorKO7.Meta.BoundaryGeneral.PayloadStress.cumulativeCarrier_unbounded
      L hL N with ⟨K, hK⟩
  exact ⟨K, by simpa [orientation_totalCharge_eq_cumulativeCarrier] using hK⟩

/-! ## Distinction instance: refusal load -/

/-- Distinction-axis retained-route charge: one unit per refused diagonal branch. -/
def distinctionChargeLaw : BoundaryChargeLaw Unit where
  charge := fun _ => 1

/-- `N` retained-route diagonal refusals carry charge `N`. -/
theorem distinction_totalCharge_eq_N (N : Nat) :
    totalCharge distinctionChargeLaw (List.replicate N ()) = N := by
  simpa using
    (totalCharge_replicate_const distinctionChargeLaw () N 1 rfl)

/-- The abstract unit-charge ledger is tied to the genuine KO7 forbidden-branch
singleton from `RefusalLoad`. -/
theorem distinction_matches_refLoad_batch (N : Nat) :
    totalCharge distinctionChargeLaw (List.replicate N ())
      =
        _root_.OperatorKO7.Meta.SafeStep.RefusalLoad.refLoad
          _root_.OperatorKO7.Meta.SafeStep.RefusalLoad.diagonalForbidden * N := by
  rw [distinction_totalCharge_eq_N,
    _root_.OperatorKO7.Meta.SafeStep.RefusalLoad.refLoad_diagonal_eq_one]
  simp

/-- Same batch law in the exact form already exposed by `RefusalLoad`. -/
theorem distinction_matches_refLoad_batch_sum (N : Nat) :
    totalCharge distinctionChargeLaw (List.replicate N ())
      =
      ((List.replicate N (eqW void void)).map
        (fun a =>
          _root_.OperatorKO7.Meta.SafeStep.RefusalLoad.refLoad
            (_root_.OperatorKO7.Meta.SafeStep.RefusalLoad.batchForbidden a))).sum := by
  rw [distinction_totalCharge_eq_N,
    _root_.OperatorKO7.Meta.SafeStep.RefusalLoad.refLoad_batch_replicate_eq_N]

/-! ## Separation and null route -/

/-- Cost-side magnitude separation: the orientation retained-route charge is
unbounded at fixed positive payload, while the distinction retained-route charge
is exactly linear in the number of diagonal refusals. -/
theorem retained_route_magnitudes_separate (L : Nat) (hL : 1 <= L) :
    (forall M, exists K,
        M <= totalCharge (orientationChargeLaw L) (orientationEvents K))
      /\ (forall N,
        totalCharge distinctionChargeLaw (List.replicate N ()) = N) :=
  ⟨orientation_totalCharge_unbounded L hL, distinction_totalCharge_eq_N⟩

/-- The already-proven marginal-growth separation remains available as the
axis-level comparison behind the cost-dual reading. -/
theorem reused_axis_growth_separation (L : Nat) (hL : 1 <= L) :
    (forall N,
        _root_.OperatorKO7.Meta.InformationalIncompleteness.AxisGrowthSeparation.batchBranchEntropy
            (N + 1)
          - _root_.OperatorKO7.Meta.InformationalIncompleteness.AxisGrowthSeparation.batchBranchEntropy
            N = 1)
      /\ (forall M, exists K,
        M <
          _root_.OperatorKO7.Meta.InformationalIncompleteness.CarrierBurden.carrierRaw
              L (K + 1)
            - _root_.OperatorKO7.Meta.InformationalIncompleteness.CarrierBurden.carrierRaw
              L K) :=
  _root_.OperatorKO7.Meta.InformationalIncompleteness.AxisGrowthSeparation.axis_growth_separation
    L hL

/-- Verdict-nulling via the inert witness carries an empty retained-route charge
ledger. The left conjunct is the genuine inert-witness anchor: `eqW void void`
has no reduct under `InertStep`. -/
theorem inert_route_zero_retained_charge :
    (Not (exists u,
        _root_.OperatorKO7.Meta.DistinctionBoundary.RepairRoutes.InertStep
          (eqW void void) u))
      /\ totalCharge distinctionChargeLaw ([] : List Unit) = 0 := by
  exact
    ⟨_root_.OperatorKO7.Meta.DistinctionBoundary.RepairRoutes.inertStep_eqW_diagonal_normalForm
      void, rfl⟩

/-- Non-vacuity for the cost dual: both retained-route sides have concrete
positive-charge witnesses. -/
theorem verdict_retaining_cost_dual_nonvacuous :
    (exists K L, 1 <= L /\
        0 < totalCharge (orientationChargeLaw L) (orientationEvents K))
      /\
      (exists N,
        0 < totalCharge distinctionChargeLaw (List.replicate (N + 1) ())) := by
  constructor
  · refine ⟨0, 1, by norm_num, ?_⟩
    norm_num [totalCharge, orientationChargeLaw, orientationEvents]
  · refine ⟨0, ?_⟩
    norm_num [totalCharge, distinctionChargeLaw]

#print axioms totalCharge_append
#print axioms totalCharge_replicate_const
#print axioms orientation_totalCharge_eq_cumulativeCarrier
#print axioms orientation_totalCharge_doubled_eq_confessedBurdenDoubled
#print axioms cumulativeCarrier_doubled_eq_confessedBurdenDoubled
#print axioms distinction_totalCharge_eq_N
#print axioms distinction_matches_refLoad_batch
#print axioms distinction_matches_refLoad_batch_sum
#print axioms retained_route_magnitudes_separate
#print axioms reused_axis_growth_separation
#print axioms inert_route_zero_retained_charge
#print axioms verdict_retaining_cost_dual_nonvacuous

end OperatorKO7.Meta.DistinctionBoundary.CostDual
