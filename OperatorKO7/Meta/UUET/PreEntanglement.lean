import Mathlib

set_option autoImplicit false

/-!
# UUET pre-entanglement carrier (U-PRE)

This module mechanizes the UUET reading of entanglement as a shared boundary
record committed before separation: two subsystems that both read one
committed bit are perfectly correlated, yet neither party's local marginal
carries any dependence on the other party's measurement setting. Correlation
without signaling is a theorem of the ledger picture, not an axiom.

The finite carrier: a joint rational distribution on outcome pairs
`Bool × Bool` produced by a shared hidden record `r : Bool` drawn with weight
`w`/(1-w), each side reporting `r` XOR a setting-dependent flip. For the
identity readout on both sides:

* `sharedRecord_perfect_correlation`: the joint weight of unequal outcomes is
 zero and equal outcomes carry full weight, perfect correlation;
* `marginal_setting_independent`: the left marginal is the same rational
 function of `w` for every right-hand setting, the no-signaling equation,
 proved for all four setting pairs at once;
* `nonseparable_before_commit`: the correlated joint is not a product of its
 marginals unless the record weight is degenerate (`w = 0` or `w = 1`):
 query dependence forces non-separability exactly when the shared record is
 genuinely uncertain;
* `one_commit_separates`: conditioning on the committed record value (one
 boundary commit) factorizes the joint exactly, the "one commit separates"
 half of the UUET claim.

Claim type: PROVEN-IN-LEAN for the rational correlation algebra. This carrier
is local-hidden-record by construction; it models the pre-entanglement
(common-cause) sector only and makes no Bell-violation claim. The Tsirelson
side lives in `QMLaw_TsirelsonLiebRobinson`.
-/

namespace OperatorKO7.Meta.UUET.PreEntanglement

/-- Joint weight that both parties report outcomes `(a, b)` when the shared
record is `true` with weight `w` and both apply the identity readout. -/
def sharedJoint (w : ℚ) (a b : Bool) : ℚ :=
  (if a then w else 0) * (if b then 1 else 0)
    + (if a then 0 else (1 - w)) * (if b then 0 else 1)

/-- Left marginal of the shared joint. -/
def leftMarginal (w : ℚ) (a : Bool) : ℚ :=
  sharedJoint w a true + sharedJoint w a false

/-- Right marginal of the shared joint. -/
def rightMarginal (w : ℚ) (b : Bool) : ℚ :=
  sharedJoint w true b + sharedJoint w false b

/-- The shared joint is normalized. -/
theorem sharedJoint_normalized (w : ℚ) :
    sharedJoint w true true + sharedJoint w true false
      + sharedJoint w false true + sharedJoint w false false = 1 := by
  unfold sharedJoint
  simp

/-- Perfect correlation: unequal outcome pairs carry zero weight. -/
theorem sharedRecord_perfect_correlation (w : ℚ) :
    sharedJoint w true false = 0 ∧ sharedJoint w false true = 0
      ∧ sharedJoint w true true = w ∧ sharedJoint w false false = 1 - w := by
  unfold sharedJoint
  simp

/-- The setting-dependent joint: the right party may flip its readout
according to a setting `s : Bool` (flip when `s = true`). -/
def settingJoint (w : ℚ) (s : Bool) (a b : Bool) : ℚ :=
  sharedJoint w a (if s then !b else b)

/-- No signaling: the left marginal is independent of the right setting.
Both settings give the same left marginal, for both left outcomes. -/
theorem marginal_setting_independent (w : ℚ) (a : Bool) :
    settingJoint w true a true + settingJoint w true a false
      = settingJoint w false a true + settingJoint w false a false := by
  unfold settingJoint sharedJoint
  cases a <;> simp

/-- The left marginal equals the record weight profile regardless of setting. -/
theorem leftMarginal_value (w : ℚ) :
    leftMarginal w true = w ∧ leftMarginal w false = 1 - w := by
  unfold leftMarginal sharedJoint
  simp

/-- Non-separability before the commit: the joint equals the product of its
marginals only at degenerate record weight. For `0 < w < 1` the correlated
joint is strictly non-product on the `(true, true)` cell. -/
theorem nonseparable_before_commit (w : ℚ) (h0 : 0 < w) (h1 : w < 1) :
    sharedJoint w true true ≠ leftMarginal w true * rightMarginal w true := by
  have hcell : sharedJoint w true true = w :=
    (sharedRecord_perfect_correlation w).2.2.1
  have hl : leftMarginal w true = w := (leftMarginal_value w).1
  have hr : rightMarginal w true = w := by
    unfold rightMarginal sharedJoint
    simp
  rw [hcell, hl, hr]
  intro hEq
  have hfac : w * (1 - w) = 0 := by
    calc w * (1 - w) = w - w * w := by ring
      _ = w - w := by rw [← hEq]
      _ = 0 := by ring
  rcases mul_eq_zero.1 hfac with h | h
  · exact absurd h (ne_of_gt h0)
  · have hw1 : w = 1 := by linarith
    exact absurd hw1 (ne_of_lt h1)

/-- Conditioning on the committed record value `r`: the post-commit joint is
deterministic on the diagonal cell selected by `r`. -/
def postCommitJoint (r : Bool) (a b : Bool) : ℚ :=
  (if a = r then 1 else 0) * (if b = r then 1 else 0)

/-- One commit separates: the post-commit joint is exactly a product of its
own marginals, for every record value and every outcome pair. -/
theorem one_commit_separates (r a b : Bool) :
    postCommitJoint r a b
      = (postCommitJoint r a true + postCommitJoint r a false)
        * (postCommitJoint r true b + postCommitJoint r false b) := by
  unfold postCommitJoint
  cases r <;> cases a <;> cases b <;> simp

/-- The commit is consistent with the pre-commit joint: mixing the two
post-commit products with weights `w`/(1-w) recovers the shared joint. -/
theorem commit_mixture_recovers (w : ℚ) (a b : Bool) :
    w * postCommitJoint true a b + (1 - w) * postCommitJoint false a b
      = sharedJoint w a b := by
  unfold postCommitJoint sharedJoint
  cases a <;> cases b <;> simp

/-- Non-vacuity at `w = 1/2`: perfect correlation, no signaling, strict
non-separability, and one-commit separation all hold simultaneously. -/
theorem preEntanglement_nonvacuous :
    sharedJoint (1/2) true false = 0
      ∧ (settingJoint (1/2) true true true + settingJoint (1/2) true true false
          = settingJoint (1/2) false true true + settingJoint (1/2) false true false)
      ∧ sharedJoint (1/2) true true ≠ leftMarginal (1/2) true * rightMarginal (1/2) true
      ∧ ∀ r a b : Bool,
          postCommitJoint r a b
            = (postCommitJoint r a true + postCommitJoint r a false)
              * (postCommitJoint r true b + postCommitJoint r false b) := by
  refine ⟨(sharedRecord_perfect_correlation (1/2)).1,
    marginal_setting_independent (1/2) true,
    nonseparable_before_commit (1/2) (by norm_num) (by norm_num),
    one_commit_separates⟩

#print axioms sharedJoint_normalized
#print axioms sharedRecord_perfect_correlation
#print axioms marginal_setting_independent
#print axioms leftMarginal_value
#print axioms nonseparable_before_commit
#print axioms one_commit_separates
#print axioms commit_mixture_recovers
#print axioms preEntanglement_nonvacuous

end OperatorKO7.Meta.UUET.PreEntanglement
