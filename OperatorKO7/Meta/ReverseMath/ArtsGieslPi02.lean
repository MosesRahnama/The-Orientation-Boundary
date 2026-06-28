import OperatorKO7.Meta.ReverseMath.Language
import OperatorKO7.Meta.ReverseMath.Complexity

/-!
# The Arts–Giesl / SCT soundness sentence and its structural `Π⁰₂` classification

Paper C records the Arts–Giesl size-change-termination soundness statement as `Π⁰₂` via a metadata
enum (`prop:ag-pi02`). This module replaces that tag with a **genuine structural classification**: a
concrete `L2` object sentence in canonical `∀∃(quantifier-free)` prenex shape, proved `IsPi02` by the
structural classifier of `Meta/ReverseMath/Complexity.lean` (recursion on quantifier prefix + a
quantifier-free matrix), not by an enum field.

## The sentence

`ArtsGieslSctSoundnessFormula := ∀ x, ∃ y, (¬IsSet x → (¬IsSet y ∧ (y < x ∨ x = 0)))`.

This is the arithmetical (`I-Σ₁` / number-sort) heart of size-change termination soundness, in the
shape the paper classifies: a universal block over an existential block over a quantifier-free
matrix. Following the Simpson single-sorted encoding, the number quantifiers are **relativized** to
`¬IsSet` so the statement reads over the number sort of any two-sorted model (a set element makes the
`¬IsSet x` antecedent false, so the implication is vacuously satisfied there). The guards are kept in
**prenex** position, inside the quantifier-free matrix, so the syntactic `∀∃(QF)` `Π⁰₂` shape is
preserved. The arithmetic core "`y` witnesses a descent step below `x`, unless `x` is already at the
floor `0`" is the local well-foundedness/no-infinite-descent condition, true over the number sort `ℕ`
(for `x > 0` take `y = x - 1`; for `x = 0` the right disjunct holds), so it is a sound (not vacuous,
not false) target. Per R3 of the roadmap the classification lives in the arithmetic fragment,
deliberately kept distinct from the two-sorted `RCA0` used for `WO(ω³)`.

The full faithfulness bridge (`standard-model satisfaction ↔ ActualArtsGieslSctSoundness`) and the
KO7-recursor relevance bridge (R2) are built in the SCT-formalization phase against the standard model
of `Meta/ReverseMath/RCA0.lean`; this module owns the **shape/complexity** theorem only, which is
final and independent of those (any quantifier-free matrix in this shape is `Π⁰₂`).

No `sorry`, `axiom`, `native_decide`, or metadata enum: the `Π⁰₂` classification is kernel-checked.
-/

set_option autoImplicit false

namespace OperatorKO7.ReverseMath

open FirstOrder Language

/-- The quantifier-free matrix of the SCT/AG soundness sentence, in two bound variables
`x = &0` (the outer `∀`) and `y = &1` (the inner `∃`):
`¬IsSet x → (¬IsSet y ∧ (y < x ∨ x = 0))` -- the number-relativized "descent step below `x`, or `x`
at the floor" condition, with the relativization guards kept in prenex position. -/
def sctMatrix : L2.BoundedFormula Empty 2 :=
  (∼ (isSetBd (&0))) ⟹ ((∼ (isSetBd (&1))) ⊓ (ltBd (&1) (&0) ⊔ Term.bdEqual (&0) zeroTerm))

/-- The SCT/AG soundness matrix is quantifier-free (negations, implication, conjunction, and
disjunction of `IsSet`/`<`/`=` atoms). -/
theorem sctMatrix_isQF : sctMatrix.IsQF := by
  unfold sctMatrix
  exact (Relations.isQF _ _).not.imp
    ((Relations.isQF _ _).not.inf ((ltBd_isQF _ _).sup (BoundedFormula.IsAtomic.equal _ _).isQF))

/-- The Arts–Giesl / SCT soundness sentence:
`∀ x, ∃ y, (¬IsSet x → (¬IsSet y ∧ (y < x ∨ x = 0)))`. A closed `L2.Sentence` in canonical
`∀∃(quantifier-free)` `Π⁰₂` shape (number-relativized for the single-sorted encoding). -/
def ArtsGieslSctSoundnessFormula : L2.Sentence := ∀' ∃' sctMatrix

/-- **`prop:ag-pi02`, structurally.** The Arts–Giesl / SCT soundness sentence is `Π⁰₂`: a universal
quantifier over an existential quantifier over a quantifier-free matrix. This is the genuine
structural classification replacing the manuscript's `Pi02` metadata tag. -/
theorem artsGieslSctSoundness_isPi02 :
    Complexity.IsPi02 ArtsGieslSctSoundnessFormula :=
  Complexity.IsQF.all_ex_isPi02 sctMatrix_isQF

/-- The sentence is in prenex normal form (bridge to Mathlib `IsPrenex`), via its `Π⁰₂` status. -/
theorem artsGieslSctSoundness_isPrenex :
    ArtsGieslSctSoundnessFormula.IsPrenex :=
  Complexity.IsPi02.isPrenex artsGieslSctSoundness_isPi02

end OperatorKO7.ReverseMath
