import OperatorKO7.Meta.ReverseMath.NewmanComplexity
import OperatorKO7.Meta.ReverseMath.RCA0
import OperatorKO7.Meta.ReverseMath.RCA0Derivations
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

* `stdModel_models_rca0SimpsonBasic` and `rca0SimpsonBasic_consistent_with_newman`: the standard
 model satisfies the eight number-relativized basic axioms of Simpson (`rca0SimpsonBasic`, the theory
 `B` of the calibration theorem), and `B` together with the bare-Newman sentence is satisfiable, the
 standard model being a common model.

* `rca0Basic_consistent_with_newman`: the same satisfiability for the five-sentence finite
 predecessor-arithmetic fragment `rca0BasicAxioms` of `RCA0.lean`. That fragment is a different
 theory from `B`: it contains the zero-or-successor sentence and the irreflexivity sentence, which `B`
 does not derive.

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

/-! ### Consistency of the bare-Newman principle over the five-sentence fragment -/

/-- Proves: the standard model satisfies the five-sentence fragment `rca0BasicAxioms` and the
bare-Newman sentence.
Does not prove: satisfaction of the eight basic axioms of Simpson; that is
`stdModel_models_rca0SimpsonBasic_and_newman`.
Relation: model-theoretic satisfaction `StdCarrier ⊨ _` in the language `L2`.
Closure: not applicable. Strategy: not applicable.
Trust: kernel only; axioms within `propext`, `Classical.choice`, `Quot.sound`.
Scope: the finite predecessor-arithmetic fragment of `RCA0.lean`, which contains the zero-or-successor
and irreflexivity sentences. -/
theorem stdModel_models_rca0BasicAxioms_and_newman :
    StdCarrier ⊨ rca0BasicAxioms ∧ StdCarrier ⊨ newmanSentence :=
  ⟨stdModel_models_rca0BasicAxioms, stdModel_newmanSentence⟩

/-- Proves: `insert newmanSentence rca0BasicAxioms` is satisfiable, with the standard model as a
common model.
Does not prove: satisfiability of the eight-axiom theory `B` of the calibration theorem together with
the bare-Newman sentence; that is `rca0SimpsonBasic_consistent_with_newman`.
Relation: `Theory.IsSatisfiable` of an `L2` theory.
Closure: not applicable. Strategy: not applicable.
Trust: kernel only; axioms within `propext`, `Classical.choice`, `Quot.sound`.
Scope: the five-sentence fragment `rca0BasicAxioms` (`axZeroOrSucc`, `axLtSucc`, `axSuccNeZero`,
`axAddZero`, `axLtIrrefl`); two of its sentences are sentences the calibration theorem proves `B` does
not derive. -/
theorem rca0Basic_consistent_with_newman :
    (insert newmanSentence rca0BasicAxioms).IsSatisfiable := by
  haveI : StdCarrier ⊨ (insert newmanSentence rca0BasicAxioms) :=
    Theory.model_insert_iff.mpr ⟨stdModel_newmanSentence, stdModel_models_rca0BasicAxioms⟩
  exact Theory.Model.isSatisfiable StdCarrier

/-! ### The eight basic axioms of Simpson in the standard model

The theory `B` of the calibration theorem is `rca0SimpsonBasic` (`RCA0Derivations.lean`): the eight
number-relativized basic axioms of Simpson for `0`, `S`, `+`, `·` and `<`. Each axiom is checked in the
standard model by cases on the number-or-set shape of its variables; a set object fails the number
guard `¬IsSet`, and on numbers each axiom is an identity or an order fact of `ℕ`. -/

private theorem simpson_axSuccNeZero : StdCarrier ⊨ axSuccNeZero := by
  simp only [axSuccNeZero, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_imp, BoundedFormula.realize_not, BoundedFormula.realize_bdEqual,
    BoundedFormula.realize_rel₁, isSetBd]
  intro a
  rcases a with m | S
  · intro _ h
    change (Sum.inl (m + 1) : StdCarrier) = Sum.inl 0 at h
    exact Nat.succ_ne_zero m (Sum.inl_injective h)
  · intro h
    exact (h trivial).elim

private theorem simpson_axSuccInj : StdCarrier ⊨ axSuccInj := by
  simp only [axSuccInj, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_imp, BoundedFormula.realize_not, BoundedFormula.realize_bdEqual,
    BoundedFormula.realize_rel₁, isSetBd]
  intro a b
  rcases a with m | S <;> rcases b with k | T
  · intro _ _ h
    change (Sum.inl (k + 1) : StdCarrier) = Sum.inl (m + 1) at h
    change (Sum.inl k : StdCarrier) = Sum.inl m
    exact congrArg Sum.inl (Nat.succ.inj (Sum.inl_injective h))
  · intro h
    exact (h trivial).elim
  · intro _ h
    exact (h trivial).elim
  · intro h
    exact (h trivial).elim

private theorem simpson_axAddZero : StdCarrier ⊨ axAddZero := by
  simp only [axAddZero, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_imp, BoundedFormula.realize_not, BoundedFormula.realize_bdEqual,
    BoundedFormula.realize_rel₁, isSetBd]
  intro a
  rcases a with m | S
  · intro _
    change (Sum.inl (m + 0) : StdCarrier) = Sum.inl m
    rfl
  · intro h
    exact (h trivial).elim

private theorem simpson_axAddSucc : StdCarrier ⊨ axAddSucc := by
  simp only [axAddSucc, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_imp, BoundedFormula.realize_not, BoundedFormula.realize_bdEqual,
    BoundedFormula.realize_rel₁, isSetBd]
  intro a b
  rcases a with m | S <;> rcases b with k | T
  · intro _ _
    change (Sum.inl (k + (m + 1)) : StdCarrier) = Sum.inl (k + m + 1)
    exact congrArg Sum.inl (Nat.add_assoc k m 1).symm
  · intro h
    exact (h trivial).elim
  · intro _ h
    exact (h trivial).elim
  · intro h
    exact (h trivial).elim

private theorem simpson_axMulZero : StdCarrier ⊨ axMulZero := by
  simp only [axMulZero, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_imp, BoundedFormula.realize_not, BoundedFormula.realize_bdEqual,
    BoundedFormula.realize_rel₁, isSetBd]
  intro a
  rcases a with m | S
  · intro _
    change (Sum.inl (m * 0) : StdCarrier) = Sum.inl 0
    exact congrArg Sum.inl (Nat.mul_zero m)
  · intro h
    exact (h trivial).elim

private theorem simpson_axMulSucc : StdCarrier ⊨ axMulSucc := by
  simp only [axMulSucc, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_imp, BoundedFormula.realize_not, BoundedFormula.realize_bdEqual,
    BoundedFormula.realize_rel₁, isSetBd]
  intro a b
  rcases a with m | S <;> rcases b with k | T
  · intro _ _
    change (Sum.inl (k * (m + 1)) : StdCarrier) = Sum.inl (k * m + k)
    exact congrArg Sum.inl (Nat.mul_succ k m)
  · intro h
    exact (h trivial).elim
  · intro _ h
    exact (h trivial).elim
  · intro h
    exact (h trivial).elim

private theorem simpson_axNotLtZero : StdCarrier ⊨ axNotLtZero := by
  simp only [axNotLtZero, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_imp, BoundedFormula.realize_not, BoundedFormula.realize_rel₁,
    BoundedFormula.realize_rel₂, isSetBd, ltBd]
  intro a
  rcases a with m | S
  · intro _
    change ¬ (m < 0)
    exact Nat.not_lt_zero m
  · intro h
    exact (h trivial).elim

private theorem simpson_axLtSuccIff : StdCarrier ⊨ axLtSuccIff := by
  simp only [axLtSuccIff, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_imp, BoundedFormula.realize_not, BoundedFormula.realize_inf,
    BoundedFormula.realize_sup, BoundedFormula.realize_bdEqual, BoundedFormula.realize_rel₁,
    BoundedFormula.realize_rel₂, isSetBd, ltBd]
  intro a b
  rcases a with m | S <;> rcases b with k | T
  · intro _ _
    change (k < m + 1 → k < m ∨ (Sum.inl k : StdCarrier) = Sum.inl m) ∧
      (k < m ∨ (Sum.inl k : StdCarrier) = Sum.inl m → k < m + 1)
    simp only [Sum.inl.injEq]
    constructor
    · intro h
      -- `k < m + 1` on `ℕ` splits into `k < m` or `k = m`.
      omega
    · intro h
      -- each disjunct gives `k < m + 1` on `ℕ`.
      omega
  · intro h
    exact (h trivial).elim
  · intro _ h
    exact (h trivial).elim
  · intro h
    exact (h trivial).elim

/-- Proves: the standard model `StdCarrier = ℕ ⊕ Set ℕ` satisfies every sentence of
`rca0SimpsonBasic`, the eight number-relativized basic axioms of Simpson (`axSuccNeZero`, `axSuccInj`,
`axAddZero`, `axAddSucc`, `axMulZero`, `axMulSucc`, `axNotLtZero`, `axLtSuccIff`).
Does not prove: any induction instance, any comprehension instance, or a syntactic consistency
statement.
Relation: model-theoretic satisfaction `StdCarrier ⊨ _` in the language `L2`.
Closure: not applicable. Strategy: not applicable.
Trust: kernel only; axioms within `propext`, `Classical.choice`, `Quot.sound`.
Scope: the theory `B` of the calibration theorem, in the single-sorted encoding with the `IsSet`
guard. -/
theorem stdModel_models_rca0SimpsonBasic : StdCarrier ⊨ rca0SimpsonBasic :=
  ⟨fun φ hφ => by
    simp only [rca0SimpsonBasic, Set.mem_insert_iff, Set.mem_singleton_iff] at hφ
    rcases hφ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact simpson_axSuccNeZero
    · exact simpson_axSuccInj
    · exact simpson_axAddZero
    · exact simpson_axAddSucc
    · exact simpson_axMulZero
    · exact simpson_axMulSucc
    · exact simpson_axNotLtZero
    · exact simpson_axLtSuccIff⟩

/-- Proves: the standard model satisfies the eight basic axioms of Simpson and the bare-Newman
well-founded-induction sentence.
Does not prove: that every model of the eight axioms satisfies the bare-Newman sentence.
Relation: model-theoretic satisfaction `StdCarrier ⊨ _` in the language `L2`.
Closure: not applicable. Strategy: not applicable.
Trust: kernel only; axioms within `propext`, `Classical.choice`, `Quot.sound`.
Scope: the standard model only. -/
theorem stdModel_models_rca0SimpsonBasic_and_newman :
    StdCarrier ⊨ rca0SimpsonBasic ∧ StdCarrier ⊨ newmanSentence :=
  ⟨stdModel_models_rca0SimpsonBasic, stdModel_newmanSentence⟩

/-- Proves: `insert newmanSentence rca0SimpsonBasic` is satisfiable, so `B + WFI` of the calibration
theorem, clause (b), has a model; the standard model is a common model.
Does not prove: that `B` derives the bare-Newman sentence, or syntactic consistency of `B + WFI`
beyond the existence of the model.
Relation: `Theory.IsSatisfiable` of an `L2` theory.
Closure: not applicable. Strategy: not applicable.
Trust: kernel only; axioms within `propext`, `Classical.choice`, `Quot.sound`.
Scope: the eight-axiom theory `rca0SimpsonBasic` of `RCA0Derivations.lean` with `newmanSentence` of
`NewmanComplexity.lean`. -/
theorem rca0SimpsonBasic_consistent_with_newman :
    (insert newmanSentence rca0SimpsonBasic).IsSatisfiable := by
  haveI : StdCarrier ⊨ (insert newmanSentence rca0SimpsonBasic) :=
    Theory.model_insert_iff.mpr ⟨stdModel_newmanSentence, stdModel_models_rca0SimpsonBasic⟩
  exact Theory.Model.isSatisfiable StdCarrier

end OperatorKO7.ReverseMath
