import OperatorKO7.Meta.ReverseMath.RCA0
import OperatorKO7.Meta.ReverseMath.ArtsGieslPi02
import Mathlib.ModelTheory.Satisfiability

/-!
# Semantic entailment for the predecessor-descent sentence

This module proves that every model of `rca0BasicAxioms` satisfies the sentence historically named
`ArtsGieslSctSoundnessFormula`. The proof uses `axZeroOrSucc`: a number is zero or has a predecessor
strictly below it. The result is semantic entailment of that elementary sentence. It is not a
formalization of Arts-Giesl dependency-pair soundness or size-change termination soundness.
-/

set_option autoImplicit false

namespace OperatorKO7.ReverseMath

open FirstOrder Language

/-- Every model `M` of `rca0BasicAxioms` satisfies the predecessor-descent sentence. For each `a`, a
set element makes the relativizing antecedent false. A number is either zero, witnessed by itself,
or has a predecessor `z < a`, witnessed by `z`. -/
theorem rca0_models_imp_sct {M : Type*} [L2.Structure M] [Nonempty M]
    (hM : M ⊨ rca0BasicAxioms) : M ⊨ ArtsGieslSctSoundnessFormula := by
  haveI := hM
  have hZOS : M ⊨ axZeroOrSucc := Theory.realize_sentence_of_mem rca0BasicAxioms
    (show axZeroOrSucc ∈ rca0BasicAxioms by simp [rca0BasicAxioms])
  simp only [axZeroOrSucc, ArtsGieslSctSoundnessFormula, sctMatrix, isSetBd, ltBd,
    succTerm, zeroTerm, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_ex, BoundedFormula.realize_imp, BoundedFormula.realize_inf,
    BoundedFormula.realize_sup, BoundedFormula.realize_not, BoundedFormula.realize_bdEqual,
    BoundedFormula.realize_rel₁, BoundedFormula.realize_rel₂, Term.realize_constants,
    Term.realize_functions_apply₁] at hZOS ⊢
  intro a
  by_cases hset : Structure.RelMap (L := L2) Rel.isSet ![a]
  · exact ⟨Classical.arbitrary M, fun h => absurd hset h⟩
  · rcases hZOS a hset with h0 | ⟨z, hz1, _, hz3⟩
    · exact ⟨a, fun _ => ⟨hset, Or.inr h0⟩⟩
    · exact ⟨z, fun _ => ⟨hz1, Or.inl hz3⟩⟩

/-- The preceding model argument packaged as first-order semantic entailment from
`rca0BasicAxioms`. -/
theorem rca0_modelsBoundedFormula_sct :
    rca0BasicAxioms ⊨ᵇ ArtsGieslSctSoundnessFormula :=
  Theory.models_sentence_iff.mpr (fun M => rca0_models_imp_sct M.is_model)

end OperatorKO7.ReverseMath
