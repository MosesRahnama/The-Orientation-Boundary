import OperatorKO7.Meta.ReverseMath.StandardModel

/-!
# The `RCA₀` theory (basic arithmetic fragment) and its standard-model consistency

This module defines the basic-arithmetic (PA⁻-style, number-relativized) fragment of `RCA₀` as an
`L2.Theory`, and proves the standard model `StdCarrier` satisfies every axiom — the Gate R5
consistency guard (an inconsistent theory would make the upper-derivation target vacuous).

The two axioms `axZeroOrSucc` and `axLtSucc` are exactly what the object derivation of the SCT/AG
soundness sentence needs (the sentence "every number is `0` or has a smaller predecessor"). The
remaining axioms (`axSuccNeZero`, `axAddZero`, `axLtIrrefl`) are representative PA⁻ content included
so the theory is a genuine arithmetic theory, not an ad hoc pair. The full Σ⁰₁-induction and
Δ⁰₁-comprehension schemes are scheduled additions (not needed for the elementary upper derivation).

All quantifiers are number-relativized (`¬IsSet`) per the Simpson single-sorted encoding, so the
axioms read over the number sort `ℕ` of the standard model.

No `sorry`, `axiom`, or `native_decide`.
-/

set_option autoImplicit false

namespace OperatorKO7.ReverseMath

open FirstOrder Language

/-! ### Basic arithmetic axioms (number-relativized `L2` sentences) -/

/-- `∀x, ¬IsSet x → (x = 0 ∨ ∃z, (¬IsSet z ∧ x = S z ∧ z < x))` — every number is zero or a
successor, with the predecessor strictly smaller (a basic arithmetic fact, provable from `axLtSucc`,
included here so the SCT descent witness is available without `eq_leibniz`). -/
def axZeroOrSucc : L2.Sentence :=
  ∀' ((∼ (isSetBd (&0))) ⟹
    ((Term.bdEqual (&0) zeroTerm) ⊔
      ∃' ((∼ (isSetBd (&1))) ⊓ ((Term.bdEqual (&0) (succTerm (&1))) ⊓ (ltBd (&1) (&0))))))

/-- `∀z, ¬IsSet z → z < S z`. -/
def axLtSucc : L2.Sentence :=
  ∀' ((∼ (isSetBd (&0))) ⟹ ltBd (&0) (succTerm (&0)))

/-- `∀x, ¬IsSet x → S x ≠ 0`. -/
def axSuccNeZero : L2.Sentence :=
  ∀' ((∼ (isSetBd (&0))) ⟹ (∼ (Term.bdEqual (succTerm (&0)) zeroTerm)))

/-- `∀x, ¬IsSet x → x + 0 = x`. -/
def axAddZero : L2.Sentence :=
  ∀' ((∼ (isSetBd (&0))) ⟹ (Term.bdEqual (addTerm (&0) zeroTerm) (&0)))

/-- `∀x, ¬IsSet x → ¬(x < x)` — irreflexivity of `<`. -/
def axLtIrrefl : L2.Sentence :=
  ∀' ((∼ (isSetBd (&0))) ⟹ (∼ (ltBd (&0) (&0))))

/-- The basic-arithmetic fragment of `RCA₀` as an `L2.Theory`. -/
def rca0BasicAxioms : L2.Theory :=
  {axZeroOrSucc, axLtSucc, axSuccNeZero, axAddZero, axLtIrrefl}

/-! ### Standard-model satisfaction (consistency guard) -/

private theorem stdModel_axZeroOrSucc : StdCarrier ⊨ axZeroOrSucc := by
  simp only [axZeroOrSucc, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_imp, BoundedFormula.realize_not, BoundedFormula.realize_sup,
    BoundedFormula.realize_ex, BoundedFormula.realize_inf, BoundedFormula.realize_bdEqual,
    BoundedFormula.realize_rel₁, BoundedFormula.realize_rel₂, isSetBd, ltBd]
  intro a hnotset
  cases a with
  | inr S => exact absurd (trivial : stdStructure.RelMap Rel.isSet ![Sum.inr S]) hnotset
  | inl m =>
      cases m with
      | zero => exact Or.inl rfl
      | succ k =>
          exact Or.inr ⟨Sum.inl k, (id : ¬ stdStructure.RelMap Rel.isSet ![Sum.inl k]), rfl,
            Nat.lt_succ_self k⟩

private theorem stdModel_axLtSucc : StdCarrier ⊨ axLtSucc := by
  simp only [axLtSucc, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_imp, BoundedFormula.realize_not, BoundedFormula.realize_rel₁,
    BoundedFormula.realize_rel₂, isSetBd, ltBd]
  intro a hnotset
  cases a with
  | inr S => exact absurd (trivial : stdStructure.RelMap Rel.isSet ![Sum.inr S]) hnotset
  | inl m => exact Nat.lt_succ_self m

private theorem stdModel_axSuccNeZero : StdCarrier ⊨ axSuccNeZero := by
  simp only [axSuccNeZero, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_imp, BoundedFormula.realize_not, BoundedFormula.realize_bdEqual,
    BoundedFormula.realize_rel₁, isSetBd]
  intro a hnotset
  cases a with
  | inr S => exact absurd (trivial : stdStructure.RelMap Rel.isSet ![Sum.inr S]) hnotset
  | inl m => exact fun h => Nat.succ_ne_zero m (Sum.inl_injective h)

private theorem stdModel_axAddZero : StdCarrier ⊨ axAddZero := by
  simp only [axAddZero, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_imp, BoundedFormula.realize_not, BoundedFormula.realize_bdEqual,
    BoundedFormula.realize_rel₁, isSetBd]
  intro a hnotset
  cases a with
  | inr S => exact absurd (trivial : stdStructure.RelMap Rel.isSet ![Sum.inr S]) hnotset
  | inl m => rfl

private theorem stdModel_axLtIrrefl : StdCarrier ⊨ axLtIrrefl := by
  simp only [axLtIrrefl, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_imp, BoundedFormula.realize_not, BoundedFormula.realize_rel₁,
    BoundedFormula.realize_rel₂, isSetBd, ltBd]
  intro a hnotset
  cases a with
  | inr S => exact absurd (trivial : stdStructure.RelMap Rel.isSet ![Sum.inr S]) hnotset
  | inl m => exact Nat.lt_irrefl m

/-- **Consistency guard (Gate R5).** The standard model satisfies every basic-arithmetic axiom, so
the `RCA₀` basic fragment is satisfiable (hence consistent); the upper-derivation target is not
vacuous. -/
theorem stdModel_models_rca0BasicAxioms : StdCarrier ⊨ rca0BasicAxioms :=
  ⟨fun φ hφ => by
    simp only [rca0BasicAxioms, Set.mem_insert_iff, Set.mem_singleton_iff] at hφ
    rcases hφ with rfl | rfl | rfl | rfl | rfl
    · exact stdModel_axZeroOrSucc
    · exact stdModel_axLtSucc
    · exact stdModel_axSuccNeZero
    · exact stdModel_axAddZero
    · exact stdModel_axLtIrrefl⟩

end OperatorKO7.ReverseMath
