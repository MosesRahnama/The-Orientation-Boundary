import OperatorKO7.Meta.ReverseMath.NewmanComplexity
import OperatorKO7.Meta.ReverseMath.RCA0
import Mathlib.ModelTheory.Satisfiability

/-!
# Upper bound: the bare-Newman well-founded-induction sentence holds in the standard model

The bare-Newman sentence (`NewmanComplexity.lean`) is the well-founded-induction principle "every
`<`-inductive set of numbers is the whole number domain". Its genuine mathematical content is **strong
induction over the number order**: the principle holds exactly because the `<`-relation on numbers is
well-founded. This module delivers the substantive upper-bound facts:

* `stdModel_newmanSentence`: the standard model `StdCarrier = ℕ ⊕ Set ℕ` satisfies the bare-Newman
  sentence. The proof is `Nat.strong_induction_on`, the well-foundedness of `<` on `ℕ`. This is the
  faithful Lean realization of the principle, and it is the Gate R5 non-vacuity witness for the
  upper-bound target (the standard model is also a model of `rca0BasicAxioms`).

* `rca0Basic_consistent_with_newman`: combining `stdModel_models_rca0BasicAxioms` with the above, the
  RCA₀ basic fragment together with the bare-Newman sentence is satisfiable (the standard model is a
  common model). The bare-Newman principle is consistent over the basic arithmetic fragment.

The constructive `Acc`-recursion of `MetaSN_KO7.newman_safe` is the informal witness that this
argument lives at the low (RCA₀-adjacent, well-founded-induction) level: the same strong-induction
shape drives both the abstract principle here and the KO7 confluence ascent.

The scope boundary, mirrored from `ArtsGieslUpperSemantic`: the genuine reverse-math content is the
well-founded-induction principle realized over the number order. The standard model carries that order
(`<` on `ℕ`), so the principle holds there by strong induction. Lifting to *every* model of the basic
axioms would need a well-foundedness or induction schema beyond the elementary basic axioms, exactly
the strength climb the calibration records; that lift is the scheduled syntactic build, not asserted
here.

No `sorry`, `admit`, `axiom`, `constant`, `opaque`, `unsafe`, `partial`, `native_decide`, `bv_decide`,
or `@[csimp]`.
-/

set_option autoImplicit false

namespace OperatorKO7.ReverseMath

open FirstOrder Language

/-! ### Standard-model realization (strong induction on `ℕ`) -/

/-- **Upper bound (standard model).** The standard model `StdCarrier` satisfies the bare-Newman
well-founded-induction sentence. The genuine argument: a witness `X` with `IsSet X` is `X = Sum.inr S`
for some `S : Set ℕ`; the inductive-step hypothesis says every number all of whose `<`-predecessors lie
in `S` lies in `S`; strong induction on `ℕ` (well-foundedness of `<`) then puts every number in `S`,
which is the conclusion. -/
theorem stdModel_newmanSentence : StdCarrier ⊨ newmanSentence := by
  simp only [newmanSentence, newmanBody, newmanInductiveStep, newmanConclusion, isSetBd, memBd,
    ltBd, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all, BoundedFormula.realize_imp,
    BoundedFormula.realize_not, BoundedFormula.realize_rel₁, BoundedFormula.realize_rel₂]
  intro X hXset hStep n hnNum
  -- `X` is a set object: `X = Sum.inr S`.
  cases X with
  | inr S =>
      -- `n` is a number object: `n = Sum.inl k`.
      cases n with
      | inr T =>
          -- a set object cannot satisfy `¬IsSet`; contradiction discharges this branch.
          exact absurd (trivial : stdStructure.RelMap Rel.isSet ![Sum.inr T]) hnNum
      | inl k =>
          -- The goal is `RelMap Rel.mem ![Sum.inl k, Sum.inr S]`. Strong induction on `k : ℕ`,
          -- using `hStep` specialized at the number object `Sum.inl k` as the induction step.
          have key : ∀ k : ℕ, stdStructure.RelMap Rel.mem ![Sum.inl k, Sum.inr S] := by
            intro k
            induction k using Nat.strong_induction_on with
            | _ k ih =>
                -- Apply `hStep` at the number object `Sum.inl k`.
                have hk := hStep (Sum.inl k)
                -- Discharge `¬IsSet (Sum.inl k)`.
                have hkNum : ¬ stdStructure.RelMap Rel.isSet ![Sum.inl k] := id
                refine hk hkNum ?_
                -- Provide the predecessor hypothesis `∀ m, ¬IsSet m → (m < k → m ∈ S)`.
                intro m hmNum hmlt
                cases m with
                | inr U =>
                    exact absurd (trivial : stdStructure.RelMap Rel.isSet ![Sum.inr U]) hmNum
                | inl j =>
                    -- `Sum.inl j < Sum.inl k` reduces to `j < k` on `ℕ`.
                    have hjk : j < k := hmlt
                    exact ih j hjk
          exact key k
  | inl m =>
      -- `X = Sum.inl m` is a number, not a set: the guard `IsSet X` is false.
      exact absurd hXset (id : ¬ stdStructure.RelMap Rel.isSet ![Sum.inl m])

/-! ### Consistency of the bare-Newman principle over the basic fragment -/

/-- The standard model satisfies both the `RCA₀` basic axioms and the bare-Newman sentence. -/
theorem stdModel_models_rca0BasicAxioms_and_newman :
    StdCarrier ⊨ rca0BasicAxioms ∧ StdCarrier ⊨ newmanSentence :=
  ⟨stdModel_models_rca0BasicAxioms, stdModel_newmanSentence⟩

/-- **Upper-bound consistency (Gate R5).** The `RCA₀` basic fragment together with the bare-Newman
well-founded-induction sentence is satisfiable: the standard model is a common model. The bare-Newman
principle is consistent over the basic arithmetic fragment, so its placement at this level is not
vacuous. -/
theorem rca0Basic_consistent_with_newman :
    (insert newmanSentence rca0BasicAxioms).IsSatisfiable := by
  haveI : StdCarrier ⊨ (insert newmanSentence rca0BasicAxioms) :=
    Theory.model_insert_iff.mpr ⟨stdModel_newmanSentence, stdModel_models_rca0BasicAxioms⟩
  exact Theory.Model.isSatisfiable StdCarrier

#print axioms stdModel_newmanSentence
#print axioms stdModel_models_rca0BasicAxioms_and_newman
#print axioms rca0Basic_consistent_with_newman

end OperatorKO7.ReverseMath
