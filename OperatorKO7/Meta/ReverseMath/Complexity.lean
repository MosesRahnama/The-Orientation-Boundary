import Mathlib.ModelTheory.Syntax
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Complexity

/-!
# Cumulative prenex-prefix classifier on `BoundedFormula`

This module defines a proof-carrying syntactic classifier using quantifier-free formulas, level
cumulativity, polarity changes, and leading `.all` or `.ex` constructors. In Mathlib,
`BoundedFormula` refers to a bound on available de Bruijn variables; it does not mean that arithmetic
quantifiers range below numeric bounds. The classifier therefore records prenex-prefix shape only. It
does not by itself supply an arithmetical language, number-sort relativization, or semantic
arithmetical-hierarchy theorem.

## Design

The base level uses Mathlib's `BoundedFormula.IsQF`. Higher levels are cumulative: `bump` may raise a
classification without changing the formula, and `dual` may change polarity while raising the level.
Consequently, proof-tree steps are not in bijection with the formula's quantifiers.

The two predicates are defined together as a single strictly-positive inductive family
`IsArith (b : Bool) (n : ℕ)`, where `b = false` reads "`Σ⁰ₙ`" and `b = true` reads "`Π⁰ₙ`". The
`ex` and `all` extend a same-polarity classified body by a leading quantifier. `IsSigma0Of` and
`IsPi0Of` are wrappers around this inductive relation.

`IsPi02 φ := IsPi0Of 2 φ` is the historical name for the Pi-labelled level-two predicate. Because
the classifier is cumulative, membership does not imply an exact universal-existential prefix.

The final lemmas show that every classified formula is prenex and provide constructors for the
specific universal-existential prefix used downstream.
-/

set_option autoImplicit false

universe u v u'

namespace OperatorKO7.ReverseMath.Complexity

open FirstOrder Language BoundedFormula

variable {L : FirstOrder.Language.{u, v}} {α : Type u'}

/-! ### The cumulative prefix classifier as one strictly-positive inductive family

`IsArith false n φ` and `IsArith true n φ` are historically named Sigma and Pi levels. The
constructors are:

* `qf` places a quantifier-free formula at level `0` in either polarity.
* `bump` raises a classification level without changing the formula.
* `ex` prefixes an existential quantifier at a positive Sigma-labelled level.
* `all` prefixes a universal quantifier at a positive Pi-labelled level.
* `dual` changes the polarity label while raising the level, without changing the formula.

Because `bump` and `dual` do not add formula quantifiers, inhabitants need not correspond bijectively
to the formula's leading quantifiers. -/
inductive IsArith : Bool → ℕ → ∀ {n : ℕ}, L.BoundedFormula α n → Prop
  | qf {b : Bool} {n : ℕ} {φ : L.BoundedFormula α n} (h : φ.IsQF) : IsArith b 0 φ
  | bump {b : Bool} {k n : ℕ} {φ : L.BoundedFormula α n} (h : IsArith b k φ) :
      IsArith b (k + 1) φ
  | ex {k n : ℕ} {φ : L.BoundedFormula α (n + 1)} (h : IsArith false (k + 1) φ) :
      IsArith false (k + 1) φ.ex
  | all {k n : ℕ} {φ : L.BoundedFormula α (n + 1)} (h : IsArith true (k + 1) φ) :
      IsArith true (k + 1) φ.all
  | dual {b : Bool} {k n : ℕ} {φ : L.BoundedFormula α n} (h : IsArith (!b) k φ) :
      IsArith b (k + 1) φ

/-- Wrapper for the false-polarity branch of `IsArith` at level `n`. -/
def IsSigma0Of (n : ℕ) {m : ℕ} (φ : L.BoundedFormula α m) : Prop := IsArith false n φ

/-- Wrapper for the true-polarity branch of `IsArith` at level `n`. -/
def IsPi0Of (n : ℕ) {m : ℕ} (φ : L.BoundedFormula α m) : Prop := IsArith true n φ

/-- Historical `Π⁰₂` name for level two of the cumulative universal-prefix classifier. -/
def IsPi02 {m : ℕ} (φ : L.BoundedFormula α m) : Prop := IsPi0Of 2 φ

/-! ### Base-case bridges -/

/-- A quantifier-free formula enters the Sigma-labelled branch at level zero. -/
theorem IsQF.isSigma0Of_zero {n : ℕ} {φ : L.BoundedFormula α n} (h : φ.IsQF) :
    IsSigma0Of 0 φ := IsArith.qf h

/-- A quantifier-free formula enters the Pi-labelled branch at level zero. -/
theorem IsQF.isPi0Of_zero {n : ℕ} {φ : L.BoundedFormula α n} (h : φ.IsQF) :
    IsPi0Of 0 φ := IsArith.qf h

/-- Raise a Sigma-labelled classification by one level without changing the formula. -/
theorem IsSigma0Of.cumulative {k n : ℕ} {φ : L.BoundedFormula α n} (h : IsSigma0Of k φ) :
    IsSigma0Of (k + 1) φ := IsArith.bump h

/-- Raise a Pi-labelled classification by one level without changing the formula. -/
theorem IsPi0Of.cumulative {k n : ℕ} {φ : L.BoundedFormula α n} (h : IsPi0Of k φ) :
    IsPi0Of (k + 1) φ := IsArith.bump h

/-- Place a quantifier-free formula in the Sigma-labelled branch at any level by repeated `bump`. -/
theorem IsQF.isSigma0Of {n : ℕ} {φ : L.BoundedFormula α n} (h : φ.IsQF) :
    ∀ k, IsSigma0Of k φ
  | 0 => IsArith.qf h
  | k + 1 => (IsQF.isSigma0Of h k).cumulative

/-- Place a quantifier-free formula in the Pi-labelled branch at any level by repeated `bump`. -/
theorem IsQF.isPi0Of {n : ℕ} {φ : L.BoundedFormula α n} (h : φ.IsQF) :
    ∀ k, IsPi0Of k φ
  | 0 => IsArith.qf h
  | k + 1 => (IsQF.isPi0Of h k).cumulative

/-- Change a Pi-labelled level-`n` proof to a Sigma-labelled level-`n+1` proof. -/
theorem IsPi0Of.isSigma0Of_succ {k n : ℕ} {φ : L.BoundedFormula α n} (h : IsPi0Of k φ) :
    IsSigma0Of (k + 1) φ := IsArith.dual (b := false) (by simpa using h)

/-- Change a Sigma-labelled level-`n` proof to a Pi-labelled level-`n+1` proof. -/
theorem IsSigma0Of.isPi0Of_succ {k n : ℕ} {φ : L.BoundedFormula α n} (h : IsSigma0Of k φ) :
    IsPi0Of (k + 1) φ := IsArith.dual (b := true) (by simpa using h)

/-! ### Quantifier introduction (`∃`/`∀` blocks) -/

/-- Prefix an existential quantifier while retaining a positive Sigma-labelled level. -/
theorem IsSigma0Of.ex {k n : ℕ} {φ : L.BoundedFormula α (n + 1)} (h : IsSigma0Of (k + 1) φ) :
    IsSigma0Of (k + 1) φ.ex := IsArith.ex h

/-- Prefix a universal quantifier while retaining a positive Pi-labelled level. -/
theorem IsPi0Of.all {k n : ℕ} {φ : L.BoundedFormula α (n + 1)} (h : IsPi0Of (k + 1) φ) :
    IsPi0Of (k + 1) φ.all := IsArith.all h

/-- Change polarity by `dual`, then prefix an existential quantifier at the raised level. -/
theorem IsPi0Of.ex_isSigma0Of_succ {k n : ℕ} {φ : L.BoundedFormula α (n + 1)} (h : IsPi0Of k φ) :
    IsSigma0Of (k + 1) φ.ex := h.isSigma0Of_succ.ex

/-- Change polarity by `dual`, then prefix a universal quantifier at the raised level. -/
theorem IsSigma0Of.all_isPi0Of_succ {k n : ℕ} {φ : L.BoundedFormula α (n + 1)} (h : IsSigma0Of k φ) :
    IsPi0Of (k + 1) φ.all := h.isPi0Of_succ.all

/-! ### Bridge to Mathlib prenex normal form

Every accepted classifier proof yields Mathlib's `IsPrenex`, by induction on the proof tree. -/

/-- Every formula accepted by the classifier is in prenex normal form. -/
theorem IsArith.isPrenex {b : Bool} {k n : ℕ} {φ : L.BoundedFormula α n}
    (h : IsArith b k φ) : φ.IsPrenex := by
  induction h with
  | qf hq => exact hq.isPrenex
  | bump _ ih => exact ih
  | ex _ ih => exact ih.ex
  | all _ ih => exact ih.all
  | dual _ ih => exact ih

/-- Every Sigma-labelled classified formula is in prenex normal form. -/
theorem IsSigma0Of.isPrenex {k n : ℕ} {φ : L.BoundedFormula α n} (h : IsSigma0Of k φ) :
    φ.IsPrenex := IsArith.isPrenex h

/-- Every Pi-labelled classified formula is in prenex normal form. -/
theorem IsPi0Of.isPrenex {k n : ℕ} {φ : L.BoundedFormula α n} (h : IsPi0Of k φ) :
    φ.IsPrenex := IsArith.isPrenex h

/-- Every formula accepted by the historical `IsPi02` predicate is prenex. -/
theorem IsPi02.isPrenex {n : ℕ} {φ : L.BoundedFormula α n} (h : IsPi02 φ) : φ.IsPrenex :=
  IsPi0Of.isPrenex h

/-! ### Constructors for `IsPi02`

These lemmas build level-two Pi-labelled proofs. They provide sufficient constructions, not a
characterization of every inhabitant's quantifier prefix. -/

/-- Change a Sigma-labelled level-one proof to a Pi-labelled level-two proof by `dual`. -/
theorem IsSigma0Of.isPi02 {n : ℕ} {φ : L.BoundedFormula α n} (h : IsSigma0Of 1 φ) :
    IsPi02 φ := h.isPi0Of_succ

/-- Prefix a universal quantifier while retaining Pi-labelled level two. -/
theorem IsPi02.all {n : ℕ} {φ : L.BoundedFormula α (n + 1)} (h : IsPi02 φ) :
    IsPi02 φ.all := IsPi0Of.all h

/-- A quantifier-free body wrapped in one existential receives a Sigma-labelled level-one proof. -/
theorem IsQF.ex_isSigma0Of_one {n : ℕ} {φ : L.BoundedFormula α (n + 1)} (h : φ.IsQF) :
    IsSigma0Of 1 φ.ex := (IsQF.isPi0Of_zero h).ex_isSigma0Of_succ

/-- A single universal over a level-one existential classification is accepted at universal level
two. -/
theorem IsSigma0Of.all_isPi02 {n : ℕ} {φ : L.BoundedFormula α (n + 1)} (h : IsSigma0Of 1 φ) :
    IsPi02 φ.all := h.all_isPi0Of_succ

/-- The classifier accepts a universal quantifier over an existential quantifier over a
quantifier-free matrix at universal level two. -/
theorem IsQF.all_ex_isPi02 {n : ℕ} {φ : L.BoundedFormula α (n + 1 + 1)} (h : φ.IsQF) :
    IsPi02 φ.ex.all := (IsQF.ex_isSigma0Of_one h).all_isPi02

end OperatorKO7.ReverseMath.Complexity
