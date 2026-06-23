import Mathlib.ModelTheory.Semantics
import OperatorKO7.Meta.ReverseMath.Language

/-!
# The standard model of the single-sorted `L2`

The standard `L2`-structure for the OperatorKO7 reverse-math program: the carrier is `ℕ ⊕ Set ℕ`,
with a number `n` encoded as `Sum.inl n` and a set `S ⊆ ℕ` as `Sum.inr S`. Numbers and sets share one
sort (Simpson single-sorted encoding); the unary predicate `IsSet` recovers the set part and the
binary `∈` recovers membership, so the two-sorted second-order reading is faithfully present.

This structure is the shared base for:
* `RCA0` consistency (standard-model satisfaction of every `RCA₀` axiom — the Gate R5 guard);
* the faithfulness bridges of `WOOmega3Sentence` and `ArtsGieslSctSoundnessSentence` (their
  standard-model realizations are the genuine Lean facts they encode).

Arithmetic acts on the number part; on set arguments the functions return the junk value `0`
(Lean structures are total, and the number-relativized axioms never constrain function values at set
arguments). No `sorry`, `axiom`, or `native_decide`.
-/

set_option autoImplicit false

namespace OperatorKO7.ReverseMath

open FirstOrder Language

/-- Carrier of the standard model: a number `n` is `Sum.inl n`, a set `S ⊆ ℕ` is `Sum.inr S`. -/
abbrev StdCarrier : Type := ℕ ⊕ Set ℕ

namespace StdModel

/-- Interpretation of the `L2` function symbols on `StdCarrier`. -/
def funMap : {n : ℕ} → Func n → (Fin n → StdCarrier) → StdCarrier
  | _, Func.zero, _ => Sum.inl 0
  | _, Func.succ, v =>
      match v 0 with
      | Sum.inl k => Sum.inl (k + 1)
      | Sum.inr _ => Sum.inl 0
  | _, Func.add, v =>
      match v 0, v 1 with
      | Sum.inl a, Sum.inl b => Sum.inl (a + b)
      | _, _ => Sum.inl 0
  | _, Func.mul, v =>
      match v 0, v 1 with
      | Sum.inl a, Sum.inl b => Sum.inl (a * b)
      | _, _ => Sum.inl 0

/-- Interpretation of the `L2` relation symbols on `StdCarrier`: `<` is order on numbers, `∈` is
membership of a number in a set, `IsSet` picks out the set (`Sum.inr`) elements. -/
def relMap : {n : ℕ} → Rel n → (Fin n → StdCarrier) → Prop
  | _, Rel.lt, v =>
      match v 0, v 1 with
      | Sum.inl a, Sum.inl b => a < b
      | _, _ => False
  | _, Rel.mem, v =>
      match v 0, v 1 with
      | Sum.inl a, Sum.inr S => a ∈ S
      | _, _ => False
  | _, Rel.isSet, v =>
      match v 0 with
      | Sum.inr _ => True
      | Sum.inl _ => False

end StdModel

/-- The standard `L2`-structure on `StdCarrier`. -/
instance stdStructure : L2.Structure StdCarrier where
  funMap := StdModel.funMap
  RelMap := StdModel.relMap

instance : Inhabited StdCarrier := ⟨Sum.inl 0⟩

instance : Nonempty StdCarrier := ⟨Sum.inl 0⟩

/-! ### Smoke confirmations that the interpretations compute -/

example : (stdStructure.funMap Func.zero ![] : StdCarrier) = Sum.inl 0 := rfl
example : stdStructure.funMap Func.succ ![Sum.inl 4] = Sum.inl 5 := rfl
example : stdStructure.funMap Func.add ![Sum.inl 2, Sum.inl 3] = Sum.inl 5 := rfl
example : stdStructure.RelMap Rel.lt ![Sum.inl 2, Sum.inl 5] := by
  show (2 : ℕ) < 5
  decide
example : stdStructure.RelMap Rel.isSet ![Sum.inr {0, 1}] := trivial
example : ¬ stdStructure.RelMap Rel.isSet ![Sum.inl 7] := id

end OperatorKO7.ReverseMath
