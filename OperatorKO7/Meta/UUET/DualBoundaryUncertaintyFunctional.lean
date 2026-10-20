import OperatorKO7.Meta.UUET.DualBoundaryUncertainty
import OperatorKO7.Meta.UUET.OperationalCompleteness

set_option autoImplicit false

/-!
# UUET dual-boundary uncertainty functional (U-50)

This module unifies the two earlier core carriers into the UUET headline thesis:
*uncertainty is unresolved licensed descent plus unresolved licensed distinction.*

It builds the scalar functional `uuetUncertainty` on top of the two-coordinate
object of U-03 (`DualBoundaryUncertainty`: `descentDeficit`, `distinctionDeficit`,
each strictly positive before its external license) and connects it to the
two-key terminal-record admission gate of U-27 (`OperationalCompleteness`).

Headline content (all non-vacuous, both deficits are concrete and strictly
positive from `uuet_uncertainty_two_positive`):

* `uuet_uncertainty_zero_iff_both_licensed`: the scalar uncertainty is zero iff
  *both* the orientation (descent/projection) and distinction (branch) licenses
  are in force. One license alone never zeroes it.
* `uuet_descent_only_uncertainty_eq_distinction` / `..._pos` and the distinction
  mirror: a single resolved axis leaves exactly the other coordinate's deficit,
  still strictly positive. These are the scalar-uncertainty analogue of U-27's
  projection-only / branch-only admission rejections.
* `uuet_uncertainty_zero_iff_terminal_record_licensed`: the scalar uncertainty
  is zero iff the U-27 admission gate licenses the terminal record. This is the
  explicit bridge between the uncertainty functional and the two-key event.

This file contains no `sorry`, no `admit`, no new `axiom`, no `native_decide`,
no `bv_decide`, no `@[csimp]`, no `unsafe`, no `partial`, and no `opaque`.
Headline declarations are `#print axioms`-checked at the bottom against the
baseline whitelist `{propext, Classical.choice, Quot.sound}`.

Claim type: PROVEN-IN-LEAN (finite Boolean license flags over the real-valued
collapse deficits of the U-03 anchor). The identification of the two flags with
physical projection/branch licenses is ANALOGY (docstring only); the formal
content is the scalar zero-iff-both-resolved structure.
-/

namespace OperatorKO7.Meta.UUET

noncomputable section

/-- Residual descent (orientation-axis) uncertainty: zero once the projection
license is in force, otherwise the pre-license descent deficit of U-03. -/
def residualDescent (descentLicensed : Bool) : ℝ :=
  if descentLicensed then 0 else descentDeficit

/-- Residual distinction (confluence-axis) uncertainty: zero once the branch
license is in force, otherwise the pre-license distinction deficit of U-03. -/
def residualDistinction (distinctionLicensed : Bool) : ℝ :=
  if distinctionLicensed then 0 else distinctionDeficit

/-- The dual-boundary uncertainty functional: unresolved licensed descent plus
unresolved licensed distinction. -/
def uuetUncertainty (descentLicensed distinctionLicensed : Bool) : ℝ :=
  residualDescent descentLicensed + residualDistinction distinctionLicensed

@[simp] theorem residualDescent_true : residualDescent true = 0 := rfl
@[simp] theorem residualDescent_false : residualDescent false = descentDeficit := rfl
@[simp] theorem residualDistinction_true : residualDistinction true = 0 := rfl
@[simp] theorem residualDistinction_false :
    residualDistinction false = distinctionDeficit := rfl

theorem residualDescent_nonneg (d : Bool) : 0 ≤ residualDescent d := by
  unfold residualDescent
  split
  · exact le_refl 0
  · exact uuet_uncertainty_two_positive.1.le

theorem residualDistinction_nonneg (b : Bool) : 0 ≤ residualDistinction b := by
  unfold residualDistinction
  split
  · exact le_refl 0
  · exact uuet_uncertainty_two_positive.2.le

theorem residualDescent_eq_zero_iff (d : Bool) :
    residualDescent d = 0 ↔ d = true := by
  unfold residualDescent
  split
  · next h => simp [h]
  · next h => exact iff_of_false uuet_uncertainty_two_positive.1.ne' h

theorem residualDistinction_eq_zero_iff (b : Bool) :
    residualDistinction b = 0 ↔ b = true := by
  unfold residualDistinction
  split
  · next h => simp [h]
  · next h => exact iff_of_false uuet_uncertainty_two_positive.2.ne' h

/-- **The scalar uncertainty is zero iff both boundary licenses are in force.**
This is the UUET dual-boundary thesis at the functional level: a committed
boundary event has zero residual uncertainty exactly when both the orientation
(descent/projection) and distinction (branch) licenses resolve their axis. -/
theorem uuet_uncertainty_zero_iff_both_licensed (d b : Bool) :
    uuetUncertainty d b = 0 ↔ d = true ∧ b = true := by
  unfold uuetUncertainty
  rw [add_eq_zero_iff_of_nonneg (residualDescent_nonneg d) (residualDistinction_nonneg b),
    residualDescent_eq_zero_iff, residualDistinction_eq_zero_iff]

/-- The fully unlicensed state carries strictly positive uncertainty: it is the
sum of both pre-license deficits. -/
theorem uuet_unlicensed_uncertainty_pos :
    0 < uuetUncertainty false false := by
  unfold uuetUncertainty
  simp only [residualDescent_false, residualDistinction_false]
  exact add_pos uuet_uncertainty_two_positive.1 uuet_uncertainty_two_positive.2

/-- Descent resolved, distinction unresolved: the residual uncertainty is exactly
the distinction coordinate (the one-bit confluence deficit of U-03). -/
theorem uuet_descent_only_uncertainty_eq_distinction :
    uuetUncertainty true false = distinctionDeficit := by
  unfold uuetUncertainty
  simp

/-- A single resolved axis (descent only) does not zero the uncertainty. The
scalar analogue of U-27's projection-only admission rejection. -/
theorem uuet_descent_only_uncertainty_pos :
    0 < uuetUncertainty true false := by
  rw [uuet_descent_only_uncertainty_eq_distinction]
  exact uuet_uncertainty_two_positive.2

/-- Distinction resolved, descent unresolved: the residual uncertainty is exactly
the descent coordinate. -/
theorem uuet_distinction_only_uncertainty_eq_descent :
    uuetUncertainty false true = descentDeficit := by
  unfold uuetUncertainty
  simp

/-- A single resolved axis (distinction only) does not zero the uncertainty. The
scalar analogue of U-27's branch-only admission rejection. -/
theorem uuet_distinction_only_uncertainty_pos :
    0 < uuetUncertainty false true := by
  rw [uuet_distinction_only_uncertainty_eq_descent]
  exact uuet_uncertainty_two_positive.1

/-- The orientation-axis license status of an operational-completeness state:
the projection transaction is licensed or typed-deferred. -/
def descentLicensedOf (s : OperationalCompletenessState) : Bool :=
  s.projectionLicensed || s.projectionDeferred

/-- The confluence-axis license status of an operational-completeness state:
the branch transaction is licensed or typed-refused. -/
def distinctionLicensedOf (s : OperationalCompletenessState) : Bool :=
  s.branchLicensed || s.branchRefused

theorem descentLicensedOf_iff (s : OperationalCompletenessState) :
    descentLicensedOf s = true ↔ projectionResolved s := by
  unfold descentLicensedOf projectionResolved
  rw [Bool.or_eq_true]

theorem distinctionLicensedOf_iff (s : OperationalCompletenessState) :
    distinctionLicensedOf s = true ↔ branchResolved s := by
  unfold distinctionLicensedOf branchResolved
  rw [Bool.or_eq_true]

/-- **Bridge to the two-key admission gate.** The scalar dual-boundary
uncertainty of a state is zero iff that state's terminal record is licensed
(U-27): zero residual uncertainty and an admissible boundary event are the same
condition, namely both transactions resolved. -/
theorem uuet_uncertainty_zero_iff_terminal_record_licensed
    (s : OperationalCompletenessState) :
    uuetUncertainty (descentLicensedOf s) (distinctionLicensedOf s) = 0
      ↔ terminalRecordLicensed s := by
  rw [uuet_uncertainty_zero_iff_both_licensed, descentLicensedOf_iff,
    distinctionLicensedOf_iff]
  rfl

/-- Non-vacuity: the canonical fully-licensed state has zero uncertainty, each of
the three under-licensed states has strictly positive uncertainty, and the
canonical U-27 complete state lands at zero through the admission bridge. -/
theorem dualBoundaryUncertaintyFunctional_nonvacuous :
    uuetUncertainty true true = 0
      ∧ 0 < uuetUncertainty false false
      ∧ 0 < uuetUncertainty true false
      ∧ 0 < uuetUncertainty false true
      ∧ uuetUncertainty (descentLicensedOf canonicalOperationallyComplete)
          (distinctionLicensedOf canonicalOperationallyComplete) = 0 := by
  refine ⟨?_, uuet_unlicensed_uncertainty_pos, uuet_descent_only_uncertainty_pos,
    uuet_distinction_only_uncertainty_pos, ?_⟩
  · unfold uuetUncertainty; simp
  · rw [uuet_uncertainty_zero_iff_terminal_record_licensed]
    exact operationallyComplete_terminal_record_licensed
      canonicalOperationallyComplete_complete

/-! ## Monotonicity and strict drop under licensing -/

/-- Licensing the descent axis strictly drops uncertainty: the descent deficit is
strictly positive, so resolving it lowers the total for every distinction state. -/
theorem uuet_uncertainty_descent_strict_drop (b : Bool) :
    uuetUncertainty true b < uuetUncertainty false b := by
  unfold uuetUncertainty
  have h : residualDescent true < residualDescent false := by
    simp only [residualDescent_true, residualDescent_false]
    exact uuet_uncertainty_two_positive.1
  exact add_lt_add_right h _

/-- Licensing the distinction axis strictly drops uncertainty. -/
theorem uuet_uncertainty_distinction_strict_drop (d : Bool) :
    uuetUncertainty d true < uuetUncertainty d false := by
  unfold uuetUncertainty
  have h : residualDistinction true < residualDistinction false := by
    simp only [residualDistinction_true, residualDistinction_false]
    exact uuet_uncertainty_two_positive.2
  exact add_lt_add_left h _

/-- Licensing the descent axis weakly decreases uncertainty (monotone form). -/
theorem uuet_uncertainty_descent_monotone (b : Bool) :
    uuetUncertainty true b ≤ uuetUncertainty false b :=
  (uuet_uncertainty_descent_strict_drop b).le

/-- Licensing the distinction axis weakly decreases uncertainty (monotone form). -/
theorem uuet_uncertainty_distinction_monotone (d : Bool) :
    uuetUncertainty d true ≤ uuetUncertainty d false :=
  (uuet_uncertainty_distinction_strict_drop d).le

/-- Licensing both axes from the fully unlicensed state strictly drops to zero. -/
theorem uuet_uncertainty_full_license_strict_drop :
    uuetUncertainty true true < uuetUncertainty false false := by
  have h0 : uuetUncertainty true true = 0 := by unfold uuetUncertainty; simp
  rw [h0]
  exact uuet_unlicensed_uncertainty_pos

/-! ## Dual-boundary uncertainty product floor (quantitative) -/

/-- The dual-boundary uncertainty *product*: the orientation residual times the
distinction residual, the product analogue of `uuetUncertainty`. -/
def uuetUncertaintyProduct (d b : Bool) : ℝ :=
  residualDescent d * residualDistinction b

/-- The fully unlicensed uncertainty product equals the product of the two
pre-license deficits. -/
theorem uuet_unlicensed_uncertainty_product_eq :
    uuetUncertaintyProduct false false = descentDeficit * distinctionDeficit := by
  unfold uuetUncertaintyProduct
  simp

/-- The fully unlicensed uncertainty product is a strictly positive floor. -/
theorem uuet_unlicensed_uncertainty_product_pos :
    0 < uuetUncertaintyProduct false false := by
  rw [uuet_unlicensed_uncertainty_product_eq]
  exact mul_pos uuet_uncertainty_two_positive.1 uuet_uncertainty_two_positive.2

/-- The uncertainty product is zero iff at least one axis is licensed. -/
theorem uuet_uncertainty_product_zero_iff_some_licensed (d b : Bool) :
    uuetUncertaintyProduct d b = 0 ↔ d = true ∨ b = true := by
  unfold uuetUncertaintyProduct
  rw [mul_eq_zero, residualDescent_eq_zero_iff, residualDistinction_eq_zero_iff]

#print axioms uuet_uncertainty_zero_iff_both_licensed
#print axioms uuet_unlicensed_uncertainty_pos
#print axioms uuet_descent_only_uncertainty_pos
#print axioms uuet_distinction_only_uncertainty_pos
#print axioms uuet_uncertainty_zero_iff_terminal_record_licensed
#print axioms dualBoundaryUncertaintyFunctional_nonvacuous
#print axioms uuet_uncertainty_descent_strict_drop
#print axioms uuet_uncertainty_distinction_strict_drop
#print axioms uuet_uncertainty_descent_monotone
#print axioms uuet_uncertainty_distinction_monotone
#print axioms uuet_uncertainty_full_license_strict_drop
#print axioms uuet_unlicensed_uncertainty_product_pos
#print axioms uuet_uncertainty_product_zero_iff_some_licensed

end

end OperatorKO7.Meta.UUET
