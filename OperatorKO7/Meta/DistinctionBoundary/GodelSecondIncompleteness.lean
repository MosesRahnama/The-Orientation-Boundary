import OperatorKO7.Meta.DistinctionBoundary.GodelFirstIncompleteness

set_option autoImplicit false

/-!
# Conditional Gödel-II boundary for the arithmetized checker

`ConQ` is the consistency sentence already defined in `GodelArithmetization` as
`¬ bewOf falsum`.  The current live evaluator has not yet proved that `bewOf`
represents the proof checker, nor has it proved the internal Hilbert--Bernays D3
implication needed to derive `ConQ → arithGodelSentence` inside Q.

This module therefore exposes only the strongest compiled statements justified
by the current stack:

* `con_true_of_representsChecker`: standard-model truth of `ConQ` from an exact
  representation theorem for `bewOf`;
* `godel_second_incompleteness`: the final G2 modus-ponens step from the explicit
  fixed-point semantics and an internal proof of `ConQ → G`;
* `con_imp_godel_true_on_nat`: standard-model truth of that implication from the
  same fixed-point semantics.

No theorem here claims that the current arithmetic layer has discharged the
missing representability/D3 premises.
-/

namespace OperatorKO7.Meta.DistinctionBoundary.GodelArith

/-- If the object-language `bewOf` exactly represents the live proof checker,
then the encoded consistency sentence is true in the standard model. -/
theorem con_true_of_representsChecker
    (hRep : RepresentsChecker bewOf) : evalForm env0 ConQ := by
  intro hBew
  exact q_consistent ((hRep falsum).1 hBew)

/-- Under exact checker representation, the negation of `ConQ` is not provable. -/
theorem not_provable_not_ConQ
    (hRep : RepresentsChecker bewOf) : ¬ Provable (Formula.not ConQ) := by
  intro h
  have ht := provable_sound h env0
  exact ht (con_true_of_representsChecker hRep)

/--
Conditional final Gödel-II step.  `hFixed` supplies Gödel I for the actual
arithmetized sentence; `hImp` is the internal Hilbert--Bernays consequence that
must ultimately be derived from the real D1--D3 machinery.
-/
theorem godel_second_incompleteness
    (hFixed : ArithGodelFixedPointSemantics)
    (hImp : Provable (Formula.imp ConQ arithGodelSentence)) :
    ¬ Provable ConQ :=
  internal_D3_implies_G2 (fun φ => bewOf φ) arithGodelSentence
    (fun a b hab ha => derivability_D2_provable hab ha)
    hImp (godel_first_incompleteness_Q hFixed).1

/-- The consistency-to-Gödel implication is true on Nat once the exact fixed
point semantics is supplied.  Semantic truth is not confused with Q-provability. -/
theorem con_imp_godel_true_on_nat
    (hFixed : ArithGodelFixedPointSemantics) :
    evalForm env0 (Formula.imp ConQ arithGodelSentence) := by
  intro _hC
  have hNP : ¬ Provable arithGodelSentence :=
    (godel_first_incompleteness_Q hFixed).1
  exact hFixed.2 hNP

/-- Decidability of the primitive recursive Q-axiom checker on a numeral
reflexivity formula.  This is bookkeeping, not an incompleteness result. -/
theorem numeral_axiom_decidable (n : Nat) :
    isQAxiom (Formula.eq (numeral n) (numeral n)) = false ∨
      isQAxiom (Formula.eq (numeral n) (numeral n)) = true := by
  cases h : isQAxiom (Formula.eq (numeral n) (numeral n)) with
  | true => exact Or.inr rfl
  | false => exact Or.inl rfl

#check @con_true_of_representsChecker
#check @not_provable_not_ConQ
#check @godel_second_incompleteness
#check @con_imp_godel_true_on_nat
#print axioms con_true_of_representsChecker
#print axioms not_provable_not_ConQ
#print axioms godel_second_incompleteness
#print axioms con_imp_godel_true_on_nat

end OperatorKO7.Meta.DistinctionBoundary.GodelArith
