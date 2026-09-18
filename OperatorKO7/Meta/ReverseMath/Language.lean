import Mathlib.ModelTheory.Syntax
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Complexity

/-!
# The single-sorted language `L2` for RCA₀-style second-order arithmetic

This module promotes the infrastructure spike (`Meta/ReverseMath/InfrastructureSpike.lean`) into the
canonical, reusable `FirstOrder.Language` for the OperatorKO7 reverse-math program. Every downstream
module (the RCA₀ theory, the SCT/AG soundness sentence, the `Π⁰₂` classification, the upper
derivation) builds on the `L2` language, term builders, and atomic-formula builders defined here.

## Encoding

`RCA₀` is two-sorted (numbers and sets). Following Simpson (*Subsystems of Second Order Arithmetic*),
we encode it single-sorted: one domain carrying both numbers and sets, a unary predicate `IsSet`
separating the set objects, and a binary membership relation `∈`. The arithmetic vocabulary is the
standard `0, S, +, ·, <`.

| Symbol | Arity | Constructor | Role |
|---|---|---|---|
| `0` | 0 | `Func.zero` | zero |
| `S` | 1 | `Func.succ` | successor |
| `+` | 2 | `Func.add` | addition |
| `·` | 2 | `Func.mul` | multiplication |
| `<` | 2 | `Rel.lt` | order |
| `∈` | 2 | `Rel.mem` | set membership |
| `IsSet` | 1 | `Rel.isSet` | "is a set" predicate |

## Substrate confirmations (genuine theorems, not tags)

The atomic-formula builders are proved quantifier-free (`Relations.isQF`), and a sample quantified
sentence is proved to be in prenex normal form (`IsPrenex`). These are the hooks the structural
`Π⁰₂` classifier (`Meta/ReverseMath/Complexity.lean`) recurses through. No `sorry`, `axiom`,
`native_decide`, or metadata enum: the language and its complexity facts are kernel-checked.
-/

set_option autoImplicit false

namespace OperatorKO7.ReverseMath

open FirstOrder Language

/-- Function symbols of `L2`: `0` (nullary), `S` (unary), `+`, `·` (binary). -/
inductive Func : Nat → Type
  | zero : Func 0
  | succ : Func 1
  | add : Func 2
  | mul : Func 2

/-- Relation symbols of `L2`: `<`, `∈` (binary), and the unary set predicate `IsSet`. -/
inductive Rel : Nat → Type
  | lt : Rel 2
  | mem : Rel 2
  | isSet : Rel 1

/-- The single-sorted language `L2` for `RCA₀`-style second-order arithmetic (Simpson encoding). -/
def L2 : FirstOrder.Language := ⟨Func, Rel⟩

/-! ### Named symbol accessors (typed at the `L2` function/relation slots) -/

/-- The constant `0` as an `L2` constant symbol. -/
abbrev zeroSym : L2.Constants := Func.zero
/-- The successor function symbol `S`. -/
abbrev succSym : L2.Functions 1 := Func.succ
/-- The addition function symbol `+`. -/
abbrev addSym : L2.Functions 2 := Func.add
/-- The multiplication function symbol `·`. -/
abbrev mulSym : L2.Functions 2 := Func.mul
/-- The order relation symbol `<`. -/
abbrev ltSym : L2.Relations 2 := Rel.lt
/-- The membership relation symbol `∈`. -/
abbrev memSym : L2.Relations 2 := Rel.mem
/-- The unary set predicate `IsSet`. -/
abbrev isSetSym : L2.Relations 1 := Rel.isSet

/-! ### Term builders (generic over the variable type `α`) -/

/-- The closed term `0`. -/
def zeroTerm {α : Type*} : L2.Term α := Constants.term zeroSym
/-- The term `S t`. -/
def succTerm {α : Type*} (t : L2.Term α) : L2.Term α := Functions.apply₁ succSym t
/-- The term `s + t`. -/
def addTerm {α : Type*} (s t : L2.Term α) : L2.Term α := Functions.apply₂ addSym s t
/-- The term `s · t`. -/
def mulTerm {α : Type*} (s t : L2.Term α) : L2.Term α := Functions.apply₂ mulSym s t

/-- The closed term `Sⁿ 0` representing the numeral `n`. -/
def numeral {α : Type*} : Nat → L2.Term α
  | 0 => zeroTerm
  | (n + 1) => succTerm (numeral n)

/-! ### Atomic formula builders (free-variable `Formula` form) -/

/-- The atomic formula `s < t`. -/
def ltF {α : Type*} (s t : L2.Term α) : L2.Formula α := Relations.formula₂ ltSym s t
/-- The atomic formula `s ∈ t`. -/
def memF {α : Type*} (s t : L2.Term α) : L2.Formula α := Relations.formula₂ memSym s t
/-- The atomic formula `IsSet t`. -/
def isSetF {α : Type*} (t : L2.Term α) : L2.Formula α := Relations.formula₁ isSetSym t

/-! ### Atomic bounded-formula builders (for use under quantifiers) -/

/-- The bounded atomic formula `s < t` (terms over `α ⊕ Fin n`). -/
def ltBd {α : Type*} {n : Nat} (s t : L2.Term (α ⊕ Fin n)) : L2.BoundedFormula α n :=
  Relations.boundedFormula₂ ltSym s t
/-- The bounded atomic formula `s ∈ t`. -/
def memBd {α : Type*} {n : Nat} (s t : L2.Term (α ⊕ Fin n)) : L2.BoundedFormula α n :=
  Relations.boundedFormula₂ memSym s t
/-- The bounded atomic formula `IsSet t`. -/
def isSetBd {α : Type*} {n : Nat} (t : L2.Term (α ⊕ Fin n)) : L2.BoundedFormula α n :=
  Relations.boundedFormula₁ isSetSym t

/-! ### Substrate confirmations -/

/-- The order atom `s < t` is quantifier-free. -/
theorem ltF_isQF {α : Type*} (s t : L2.Term α) : (ltF s t).IsQF := Relations.isQF _ _
/-- The membership atom `s ∈ t` is quantifier-free. -/
theorem memF_isQF {α : Type*} (s t : L2.Term α) : (memF s t).IsQF := Relations.isQF _ _
/-- The set-predicate atom `IsSet t` is quantifier-free. -/
theorem isSetF_isQF {α : Type*} (t : L2.Term α) : (isSetF t).IsQF := Relations.isQF _ _

/-- The bounded order atom `s < t` is quantifier-free. -/
theorem ltBd_isQF {α : Type*} {n : Nat} (s t : L2.Term (α ⊕ Fin n)) :
    (ltBd s t).IsQF := Relations.isQF _ _

/-- A sample closed `L2` sentence: `∀ x, S x ≠ 0` (the second Peano axiom). Confirms that the
quantifier + negation + equality builders combine into a genuine `L2.Sentence`. -/
def succNeZero : L2.Sentence := ∀' ∼ (succTerm (&0) =' zeroTerm)

/-- The sample sentence `∀ x, S x ≠ 0` is in prenex normal form (`∀` over a quantifier-free matrix):
the bridge a `Σ⁰ₙ`/`Π⁰ₙ` classifier recurses through on concrete `L2` sentences. -/
theorem succNeZero_isPrenex : succNeZero.IsPrenex :=
  (((BoundedFormula.IsAtomic.equal _ _).isQF).not.isPrenex).all

/-- A sample `∀∃` sentence: `∀ x, ∃ y, x < y` (no greatest element). Confirms the `∀∃(QF)` shape that
the `Π⁰₂` classifier certifies. -/
def noGreatest : L2.Sentence := ∀' ∃' (ltBd (&0) (&1))

end OperatorKO7.ReverseMath
