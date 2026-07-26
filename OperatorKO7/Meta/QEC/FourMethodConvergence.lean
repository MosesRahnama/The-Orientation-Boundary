import OperatorKO7.Meta.QEC.MethodOneObligationType
import OperatorKO7.Meta.QEC.MethodTwoSPRTBound
import OperatorKO7.Meta.QEC.MethodThreeObligationType
import OperatorKO7.Meta.QEC.MethodFourSymNGaugedCode

/-!
# QEC four-method metadata projections

This module defines a common two-field codomain containing a natural number and
an enum tag. Four projection functions copy one numeric field from their input
and assign either `abstention` or `leakage` by definition. The aggregate
theorem proves the corresponding equations by case analysis on the method tag.

The formal surface is a definitional metadata comparison. Typed QEC guarantees,
gauge invariance, semantic equality among methods, and a universal
factorization property require separate structures and adapters.
-/

namespace OperatorKO7.Meta.QEC.FourMethodConvergence

open OperatorKO7.Meta.QEC.MethodOneObligationType
open OperatorKO7.Meta.QEC.MethodTwoSPRTBound
open OperatorKO7.Meta.QEC.MethodThreeObligationType
open OperatorKO7.Meta.QEC.MethodFourSymNGaugedCode

/-- Finite enumeration of the four QEC method identities. -/
inductive QECMethodTag
  | methodOne
  | methodTwo
  | methodThree
  | methodFour
  deriving DecidableEq, Repr

/-- Two enum tags assigned by the four projection definitions. -/
inductive ConfessionLicenseTag
  | abstention
  | leakage
  deriving DecidableEq, Repr

/-- Common metadata codomain for the four projection functions.

Two fields capture the structural content the four QEC methods share:

* `projectedAwaySyndromeDimension : Nat` stores the copied input field.
* `licenseTag : ConfessionLicenseTag` stores the assigned enum tag.

The structure itself carries no QEC semantics or license-validity predicate. -/
structure ConfessionCoreProjection where
  projectedAwaySyndromeDimension : Nat
  licenseTag : ConfessionLicenseTag
  deriving Repr

/-! ## Per-method projections

Each function below reads one numeric field from a method-specific carrier and
assigns a fixed enum tag. -/

/-- Method 1 metadata projection: copy
`syndromeRound.syndromeBitCount` and assign `abstention`. -/
def methodOneConfessionCoreProjection
    (obligation : QECMethodOneObligation) : ConfessionCoreProjection where
  projectedAwaySyndromeDimension := obligation.syndromeRound.syndromeBitCount
  licenseTag := ConfessionLicenseTag.abstention

/-- Method 2 metadata projection: copy `syndromeBitCount` and assign
`abstention`. -/
def methodTwoConfessionCoreProjection
    (obligation : WaldSPRTObligation) : ConfessionCoreProjection where
  projectedAwaySyndromeDimension := obligation.syndromeBitCount
  licenseTag := ConfessionLicenseTag.abstention

/-- Method 3 metadata projection: copy the reference syndrome bit count and
assign `leakage`. -/
def methodThreeConfessionCoreProjection
    (obligation : QECMethodThreeObligation) : ConfessionCoreProjection where
  projectedAwaySyndromeDimension :=
    (obligation.syndrome SyndromeRound.reference).syndromeBitCount
  licenseTag := ConfessionLicenseTag.leakage

/-- Method 4 metadata projection: copy `distance` and assign `leakage`. -/
def methodFourConfessionCoreProjection
    (code : SymNGaugedCode) : ConfessionCoreProjection where
  projectedAwaySyndromeDimension := code.distance
  licenseTag := ConfessionLicenseTag.leakage

/-- Select one of the four metadata projections by method tag. -/
def projectionOfTag
    (tag : QECMethodTag)
    (m1 : QECMethodOneObligation)
    (m2 : WaldSPRTObligation)
    (m3 : QECMethodThreeObligation)
    (m4 : SymNGaugedCode) : ConfessionCoreProjection :=
  match tag with
  | .methodOne   => methodOneConfessionCoreProjection m1
  | .methodTwo   => methodTwoConfessionCoreProjection m2
  | .methodThree => methodThreeConfessionCoreProjection m3
  | .methodFour  => methodFourConfessionCoreProjection m4

/-! ## Projection equations

For each method tag, the selected projection lands in the common record type,
its numeric field equals the copied input field, and its tag equals one of the
two constructors. Each conjunct follows by unfolding the definitions. -/

/-- Casewise equations for the four metadata projections. The conclusion is a
record-membership fact, an inclusive tag disjunction, and the numeric-field
equation selected by the method tag. -/
theorem all_four_methods_share_confession_core
    (m1 : QECMethodOneObligation)
    (m2 : WaldSPRTObligation)
    (m3 : QECMethodThreeObligation)
    (m4 : SymNGaugedCode) :
    (∀ tag : QECMethodTag,
        (projectionOfTag tag m1 m2 m3 m4).licenseTag
            = ConfessionLicenseTag.abstention
          ∨ (projectionOfTag tag m1 m2 m3 m4).licenseTag
              = ConfessionLicenseTag.leakage)
    ∧ (methodOneConfessionCoreProjection m1).projectedAwaySyndromeDimension
        = m1.syndromeRound.syndromeBitCount
    ∧ (methodTwoConfessionCoreProjection m2).projectedAwaySyndromeDimension
        = m2.syndromeBitCount
    ∧ (methodThreeConfessionCoreProjection m3).projectedAwaySyndromeDimension
        = (m3.syndrome SyndromeRound.reference).syndromeBitCount
    ∧ (methodFourConfessionCoreProjection m4).projectedAwaySyndromeDimension
        = m4.distance := by
  refine ⟨?_, rfl, rfl, rfl, rfl⟩
  intro tag
  cases tag
  · -- Method 1: abstention tag
    left
    rfl
  · -- Method 2: abstention tag
    left
    rfl
  · -- Method 3: leakage tag
    right
    rfl
  · -- Method 4: leakage tag
    right
    rfl

/-! ## Per-tag equations

The four lemmas below unfold the assigned tags: Method 1 and Method 2 yield
`abstention`; Method 3 and Method 4 yield `leakage`. -/

theorem methodOne_license_abstention (m : QECMethodOneObligation) :
    (methodOneConfessionCoreProjection m).licenseTag
      = ConfessionLicenseTag.abstention := rfl

theorem methodTwo_license_abstention (m : WaldSPRTObligation) :
    (methodTwoConfessionCoreProjection m).licenseTag
      = ConfessionLicenseTag.abstention := rfl

theorem methodThree_license_leakage (m : QECMethodThreeObligation) :
    (methodThreeConfessionCoreProjection m).licenseTag
      = ConfessionLicenseTag.leakage := rfl

theorem methodFour_license_leakage (m : SymNGaugedCode) :
    (methodFourConfessionCoreProjection m).licenseTag
      = ConfessionLicenseTag.leakage := rfl

/-! ## Name references

Both strings contain fully qualified Lean names for the projection-equation
theorem and common metadata carrier. -/

/-- Fully qualified name of the four-method projection-equation theorem. -/
def qec_four_method_convergence_anchor : String :=
  "OperatorKO7.Meta.QEC.FourMethodConvergence" ++
    ".all_four_methods_share_confession_core"

/-- Fully qualified name of the common metadata carrier. -/
def qec_confession_core_projection_anchor : String :=
  "OperatorKO7.Meta.QEC.FourMethodConvergence.ConfessionCoreProjection"

end OperatorKO7.Meta.QEC.FourMethodConvergence
