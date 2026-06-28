import OperatorKO7.Meta.ReverseMath.RCA0
import OperatorKO7.Meta.ReverseMath.ArtsGieslPi02
import Mathlib.ModelTheory.Satisfiability

/-!
# Semantic upper bound: `RCA₀` proves the SCT/AG soundness sentence (over all models)

The dominant-cost upper-derivation phase (roadmap R1) has two routes. Route (b) — the standard
reverse-math style — first proves the **semantic** upper bound `RCA₀ ⊨ᵇ φ` (every model of `RCA₀`
satisfies `φ`), then lifts it to syntactic derivability `RCA₀ ⊢ φ` by first-order completeness. This
module delivers the substantive first half: a kernel-checked proof that **every** model of the `RCA₀`
basic axioms satisfies the SCT/AG soundness sentence, reasoning in an arbitrary model.

The sentence `∀x∃y, ¬IsSet x → (¬IsSet y ∧ (y<x ∨ x=0))` follows from just two `RCA₀` axioms:
`axZeroOrSucc` (every number is `0` or a successor) and `axLtSucc` (`z < S z`). The argument is the
genuine mathematical content (a per-element case split), not a metadata tag.

`rca0_modelsBoundedFormula_sct` packages this as Mathlib's semantic entailment `⊨ᵇ`. The classical
first-order completeness theorem identifies semantic entailment `⊨ᵇ` with syntactic provability `⊢`,
so the semantic bound proved here *corresponds* to `RCA₀ ⊢ φ` — but that completeness theorem is **not
mechanized in this development**, and this module proves only the semantic form. The literal syntactic
`Derivable RCA0 φ` remains a scheduled build (object derivation, or an internal Henkin completeness
lift, since Mathlib `ModelTheory` has no completeness theorem). This is the genuine reverse-math upper
bound; the syntactic packaging is open, not an "honest gap".

No `sorry`, `axiom`, or `native_decide`.
-/

set_option autoImplicit false

namespace OperatorKO7.ReverseMath

open FirstOrder Language

/-- **Semantic upper bound (all models).** Every model `M` of the `RCA₀` basic axioms satisfies the
SCT/AG soundness sentence. The genuine mathematical argument: for each `a`, either `a` is a set
(antecedent false, vacuous), or `a` is a number and `axZeroOrSucc` makes it `0` (witness `a` itself,
`x=0` disjunct) or a successor `S z` with `z < a` (witness `z`, with `z < a` directly from the
`axZeroOrSucc` existential). -/
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

/-- The semantic upper bound as Mathlib's first-order semantic entailment: every model of the `RCA₀`
basic axioms satisfies the sentence (`rca0BasicAxioms ⊨ᵇ φ`; and `rca0BasicAxioms ⊆ RCA₀`, so full
`RCA₀` does too). The classical completeness theorem identifies `⊨ᵇ` with syntactic `⊢`, but that
theorem is NOT mechanized here — this proves only the semantic form. -/
theorem rca0_modelsBoundedFormula_sct :
    rca0BasicAxioms ⊨ᵇ ArtsGieslSctSoundnessFormula :=
  Theory.models_sentence_iff.mpr (fun M => rca0_models_imp_sct M.is_model)

end OperatorKO7.ReverseMath
