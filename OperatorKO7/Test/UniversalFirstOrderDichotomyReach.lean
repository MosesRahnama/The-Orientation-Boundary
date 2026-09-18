import OperatorKO7.Meta.UniversalFirstOrderInterpretationMethod
import OperatorKO7.Meta.UniversalFirstOrderEmbeddings
import OperatorKO7.Meta.UniversalFirstOrderDichotomy
import OperatorKO7.Meta.W1W2UniversalNecessity

/-!
# Reach test for the Lane L trilogy capstone

Per `.agent-control/COMPLETION_PROTOCOL.md` the reach test is the
live-demo gate for theorem-side lanes. Asserts L.5, L.6, L.8 by name
(per dispatch §6 gate 4).
-/

namespace UniversalFirstOrderDichotomyReach

open OperatorKO7.UniversalFirstOrderInterpretationMethod
open OperatorKO7.UniversalFirstOrderEmbeddings
open OperatorKO7.UniversalFirstOrderDichotomy
open OperatorKO7.W1W2UniversalNecessity

#check @UniversalFirstOrderInterpretationMethod
#check @UniversalMethodVerdict
#check @universalMethodVerdict
#check @universal_first_order_method_classification
#check @isW0Blocked
#check @isLicensedViaW1W2OrExternal
#check @admitsStepsUnconditionally
#check @universal_method_verdict_dichotomy
#check @admitsStepsUnconditionally_iff_licensed
#check @isW0Blocked_iff_not_licensed

#check @embedDirectSchemaBarrier
#check @embedTransparentNonlinear
#check @embedUnconstrainedNonlinear
#check @embedFBIGeneric
#check @embedMatrixUnrestricted
#check @embedGenericDP
#check @embedSemantic
#check @embedW1Licensed
#check @embedW2Licensed
#check @embedKO7CertifiedExternal
#check @universal_first_order_method_embedding_coverage

#check @universal_first_order_dichotomy_W0_or_licensed
#check @universal_first_order_dichotomy_no_undefined_method
#check @UniversalFirstOrderDichotomy
#check @universal_first_order_dichotomy_unconditional
#check @universal_first_order_dichotomy_at_verdict_layer
#check @tool_search_residual_universal_coverage_corollary
#check @capstone_subsumes_residual_method_finite_ledger
#check universal_first_order_dichotomy_anchor
#check universal_first_order_dichotomy_no_undefined_method_anchor
#check tool_search_residual_universal_coverage_corollary_anchor

#check @w1_w2_universal_necessity_unconditional
#check @not_licensed_implies_not_admits_steps
#check @admits_steps_implies_verdict_licensed
#check @admits_steps_iff_licensed_via_w1_w2_or_external
#check w1_w2_universal_necessity_unconditional_anchor

/-! ### L.5 / L.6 sample instantiations -/

example : UniversalFirstOrderDichotomy :=
  universal_first_order_dichotomy_unconditional

example (m : UniversalFirstOrderInterpretationMethod) :
    ¬ admitsStepsUnconditionally m ∨ isLicensedViaW1W2OrExternal m :=
  universal_first_order_dichotomy_unconditional m

example (idx : Nat) :
    isW0Blocked (embedDirectSchemaBarrier idx) :=
  embedDirectSchemaBarrier_isW0Blocked idx

example (idx : Nat) :
    isW0Blocked (embedMatrixUnrestricted idx) :=
  embedMatrixUnrestricted_isW0Blocked idx

example (idx : Nat) :
    isW0Blocked (embedFBIGeneric idx) :=
  embedFBIGeneric_isW0Blocked idx

example (idx : Nat) :
    isW0Blocked (embedTransparentNonlinear idx) :=
  embedTransparentNonlinear_isW0Blocked idx

example (idx : Nat) :
    universalMethodVerdict (embedKO7CertifiedExternal idx)
      = UniversalMethodVerdict.externally_certified :=
  embedKO7CertifiedExternal_verdict_externally_certified idx

/-! ### L.8 sample instantiation -/

example
    (m : UniversalFirstOrderInterpretationMethod)
    (hAdmits : admitsStepsUnconditionally m) :
    isLicensedViaW1W2OrExternal m :=
  w1_w2_universal_necessity_unconditional m hAdmits

/-! ### L.9 sample instantiation -/

example (m : UniversalFirstOrderInterpretationMethod) :
    universalMethodVerdict m = .w0_blocked ∨
    universalMethodVerdict m = .w1_licensed ∨
    universalMethodVerdict m = .w2_licensed ∨
    universalMethodVerdict m = .externally_certified :=
  tool_search_residual_universal_coverage_corollary m

/-! ### Anchor string equality checks -/

example : universal_first_order_dichotomy_anchor =
    "OperatorKO7.UniversalFirstOrderDichotomy." ++
      "universal_first_order_dichotomy_unconditional" :=
  rfl

example : w1_w2_universal_necessity_unconditional_anchor =
    "OperatorKO7.W1W2UniversalNecessity." ++
      "w1_w2_universal_necessity_unconditional" :=
  rfl

end UniversalFirstOrderDichotomyReach
