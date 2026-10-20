import OperatorKO7.Meta.ReverseMath.RCA0
import OperatorKO7.Meta.ReverseMath.ArtsGieslPi02
import Mathlib.ModelTheory.Satisfiability

/-!
# Semantic entailment for the predecessor-descent sentence

This module proves that every model of the five-sentence theory `finitePredecessorArithmeticAxioms`
satisfies `numberPredecessorDescentSentence`. The proof uses `axZeroOrSucc`: a number is zero or has
a predecessor strictly below it. The result is semantic entailment of that elementary sentence. It
is not a formalization of Arts-Giesl dependency-pair soundness or size-change termination soundness.
The historical names `rca0_models_imp_sct` and `rca0_modelsBoundedFormula_sct` are compatibility
aliases of the two theorems below.
-/

set_option autoImplicit false

namespace OperatorKO7.ReverseMath

open FirstOrder Language

/-- Every model `M` of `finitePredecessorArithmeticAxioms` satisfies the predecessor-descent
sentence. For each element `a`, a set element makes the relativizing antecedent false. A number is
either zero, and then `a` itself satisfies the matrix, or it has a predecessor `z < a`, and then `z`
satisfies the matrix. -/
theorem finitePredecessorArithmetic_models_numberPredecessorDescent
    {M : Type*} [L2.Structure M] [Nonempty M]
    (hM : M ⊨ finitePredecessorArithmeticAxioms) :
    M ⊨ numberPredecessorDescentSentence := by
  haveI := hM
  have hZOS : M ⊨ axZeroOrSucc :=
    Theory.realize_sentence_of_mem finitePredecessorArithmeticAxioms
      (show axZeroOrSucc ∈ finitePredecessorArithmeticAxioms by
        simp [finitePredecessorArithmeticAxioms, rca0BasicAxioms])
  simp only [axZeroOrSucc, numberPredecessorDescentSentence, numberPredecessorDescentMatrix,
    isSetBd, ltBd, succTerm, zeroTerm, Sentence.Realize, Formula.Realize,
    BoundedFormula.realize_all, BoundedFormula.realize_ex, BoundedFormula.realize_imp,
    BoundedFormula.realize_inf, BoundedFormula.realize_sup, BoundedFormula.realize_not,
    BoundedFormula.realize_bdEqual, BoundedFormula.realize_rel₁, BoundedFormula.realize_rel₂,
    Term.realize_constants, Term.realize_functions_apply₁] at hZOS ⊢
  intro a
  by_cases hset : Structure.RelMap (L := L2) Rel.isSet ![a]
  · exact ⟨Classical.arbitrary M, fun h => absurd hset h⟩
  · rcases hZOS a hset with h0 | ⟨z, hz1, _, hz3⟩
    · exact ⟨a, fun _ => ⟨hset, Or.inr h0⟩⟩
    · exact ⟨z, fun _ => ⟨hz1, Or.inl hz3⟩⟩

/-- The model theorem above as first-order semantic entailment from
`finitePredecessorArithmeticAxioms`. -/
theorem finitePredecessorArithmetic_entails_numberPredecessorDescent :
    finitePredecessorArithmeticAxioms ⊨ᵇ numberPredecessorDescentSentence :=
  Theory.models_sentence_iff.mpr
    (fun M => finitePredecessorArithmetic_models_numberPredecessorDescent M.is_model)

/-- Historical name of `finitePredecessorArithmetic_models_numberPredecessorDescent`. It formalizes
predecessor descent; it does not formalize size-change or dependency-pair soundness. -/
theorem rca0_models_imp_sct {M : Type*} [L2.Structure M] [Nonempty M]
    (hM : M ⊨ rca0BasicAxioms) : M ⊨ ArtsGieslSctSoundnessFormula :=
  finitePredecessorArithmetic_models_numberPredecessorDescent hM

/-- Historical name of `finitePredecessorArithmetic_entails_numberPredecessorDescent`. It formalizes
predecessor descent; it does not formalize size-change or dependency-pair soundness. -/
theorem rca0_modelsBoundedFormula_sct :
    rca0BasicAxioms ⊨ᵇ ArtsGieslSctSoundnessFormula :=
  finitePredecessorArithmetic_entails_numberPredecessorDescent

end OperatorKO7.ReverseMath
