import OperatorKO7.Meta.UniversalFirstOrderInterpretationMethod
import OperatorKO7.Meta.UniversalFirstOrderDichotomy

/-!
# Verdict-projection corollaries

This module derives consequences of the finite classifier imported from
`UniversalFirstOrderInterpretationMethod` and
`UniversalFirstOrderDichotomy`. On that carrier,
`admitsStepsUnconditionally m` is defined as
`universalMethodVerdict m != .w0_blocked`, while
`isLicensedViaW1W2OrExternal m` is the disjunction of the other three verdict
constructors. The results below restate the imported case split and
equivalence. They do not quantify over arbitrary external termination methods
or independently establish step orientation.
-/

namespace OperatorKO7.W1W2UniversalNecessity

open OperatorKO7.UniversalFirstOrderInterpretationMethod
open OperatorKO7.UniversalFirstOrderDichotomy

/-- For the imported finite carrier, a non-`w0_blocked` verdict lies in one of
the three remaining verdict classes. -/
theorem w1_w2_universal_necessity_unconditional
    (m : UniversalFirstOrderInterpretationMethod)
    (hAdmits : admitsStepsUnconditionally m) :
    isLicensedViaW1W2OrExternal m := by
  rcases universal_first_order_dichotomy_unconditional m with hNotAdmits | hLic
  · exact absurd hAdmits hNotAdmits
  · exact hLic

/-- Contrapositive of `w1_w2_universal_necessity_unconditional` on the same
classifier. -/
theorem not_licensed_implies_not_admits_steps
    (m : UniversalFirstOrderInterpretationMethod)
    (hNotLic : ¬ isLicensedViaW1W2OrExternal m) :
    ¬ admitsStepsUnconditionally m := by
  intro hAdmits
  exact hNotLic (w1_w2_universal_necessity_unconditional m hAdmits)

/-- Expands the licensed predicate as its three verdict equalities. -/
theorem admits_steps_implies_verdict_licensed
    (m : UniversalFirstOrderInterpretationMethod)
    (hAdmits : admitsStepsUnconditionally m) :
    universalMethodVerdict m = .w1_licensed ∨
    universalMethodVerdict m = .w2_licensed ∨
    universalMethodVerdict m = .externally_certified :=
  w1_w2_universal_necessity_unconditional m hAdmits

/-- Re-exports the imported equivalence between a non-`w0_blocked` verdict and
the disjunction of the other three verdicts. -/
theorem admits_steps_iff_licensed_via_w1_w2_or_external
    (m : UniversalFirstOrderInterpretationMethod) :
    admitsStepsUnconditionally m ↔ isLicensedViaW1W2OrExternal m :=
  admitsStepsUnconditionally_iff_licensed m

/-- String identifier for the headline theorem in this namespace. -/
def w1_w2_universal_necessity_unconditional_anchor : String :=
  "OperatorKO7.W1W2UniversalNecessity." ++
    "w1_w2_universal_necessity_unconditional"

end OperatorKO7.W1W2UniversalNecessity
