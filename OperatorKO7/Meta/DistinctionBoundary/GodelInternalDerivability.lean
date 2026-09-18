import OperatorKO7.Meta.DistinctionBoundary.GodelFixedPointSemantics
import OperatorKO7.Meta.DistinctionBoundary.GodelSecondIncompleteness

set_option autoImplicit false

/-!
# Internal-derivability frontier after semantic checker representation

The fixed-point semantics module proves the exact standard-model graph of
`bewOf`.  This file promotes that result to the existing `RepresentsChecker`
interface and records the unconditional semantic consequences for `ConQ`.
It deliberately does not manufacture the missing Hilbert proof of
`ConQ → arithGodelSentence` or internal D3.
-/

namespace OperatorKO7.Meta.DistinctionBoundary.GodelArith

/-- The live arithmetized provability predicate exactly represents the compiled
checker in the standard model. -/
theorem bewOf_representsChecker : RepresentsChecker bewOf := by
  intro φ
  exact eval_bewOf_iff_provable φ

/-- The compiled consistency sentence is unconditionally true in the standard
model, because `bewOf` now has an exact representation theorem. -/
theorem conQ_true_unconditional : evalForm env0 ConQ :=
  con_true_of_representsChecker bewOf_representsChecker

/-- The negation of the compiled consistency sentence is unprovable in the
current Hilbert checker. -/
theorem not_provable_not_conQ_unconditional : ¬ Provable (Formula.not ConQ) :=
  not_provable_not_ConQ bewOf_representsChecker

/-- The semantic implication `ConQ → G` is unconditional now that the concrete
fixed-point semantics is inhabited.  This remains a standard-model statement,
not a Hilbert derivation. -/
theorem conQ_imp_godel_true_unconditional :
    evalForm env0 (Formula.imp ConQ arithGodelSentence) :=
  con_imp_godel_true_on_nat arithGodelFixedPointSemantics_holds

/-- The remaining Gödel-II theorem is isolated at one exact proof object. -/
theorem godel_second_incompleteness_from_internal_imp
    (hImp : Provable (Formula.imp ConQ arithGodelSentence)) :
    ¬ Provable ConQ :=
  godel_second_incompleteness arithGodelFixedPointSemantics_holds hImp

end OperatorKO7.Meta.DistinctionBoundary.GodelArith
