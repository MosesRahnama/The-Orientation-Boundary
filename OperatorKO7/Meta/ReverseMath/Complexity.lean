import Mathlib.ModelTheory.Syntax
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Complexity

/-!
# Structural arithmetical hierarchy on `BoundedFormula`

This module builds a genuine **syntactic** arithmetical-hierarchy classifier on Mathlib's
`FirstOrder.Language.BoundedFormula`. It is the substrate for Paper C's `prop:ag-pi02`: the
manuscript currently records `Pi02` as a metadata enum; here it is replaced by a real structural
predicate defined by recursion on formula *structure* (`.all` / `.ex`) and on the hierarchy *level*.

## Design

The base level `Δ⁰₀ = Σ⁰₀ = Π⁰₀` is Mathlib's `BoundedFormula.IsQF` (quantifier-free). A level-`(n+1)`
`Σ` formula is a block of existential quantifiers applied to a level-`n` `Π` formula; dually for `Π`.

The two predicates are defined together as a single strictly-positive inductive family
`IsArith (b : Bool) (n : ℕ)`, where `b = false` reads "`Σ⁰ₙ`" and `b = true` reads "`Π⁰ₙ`". The
constructors recurse through the `.ex` / `.all` constructors of `BoundedFormula` (genuine structural
recursion on the formula) and drop the level when crossing from a quantifier block to its dual matrix.
`IsSigma0Of`/`IsPi0Of` are thin wrappers. None of these is `:= True`, a standalone `Bool`, or an enum
tag on the formula: the `Bool` here only names which *quantifier* a constructor introduces, and every
inhabitant is an actual proof tree mirroring the formula's quantifier prefix.

Because Mathlib bounds the quantified variable to the model's domain (`BoundedFormula` quantifiers
range `∀ a : M, …` / `∃ a : M, …`), these are *bounded / number* quantifiers in the model-theoretic
sense, exactly the arithmetical-hierarchy reading intended by the paper.

`IsPi02 φ := IsPi0Of 2 φ`: a `∀`-block over a `Σ⁰₁` matrix, i.e. `∀…∀ ∃…∃ φ` with `φ` quantifier-free.

## Trust surface

No `sorry`, `admit`, `axiom`, `constant`, `opaque`, `unsafe`, `partial`, `native_decide`, or `@[csimp]`.
Everything is a kernel-checked structural recursion or induction. Closure/bridge lemmas connect the
predicates back to Mathlib's `IsQF` / `IsPrenex`.
-/

set_option autoImplicit false

universe u v u'

namespace OperatorKO7.ReverseMath.Complexity

open FirstOrder Language BoundedFormula

variable {L : FirstOrder.Language.{u, v}} {α : Type u'}

/-! ### The arithmetical hierarchy as one strictly-positive inductive family

`IsArith false n φ` means `φ` is `Σ⁰ₙ`; `IsArith true n φ` means `φ` is `Π⁰ₙ`. The constructors:

* `qf` — a quantifier-free formula is at level `0` (both directions).
* `bump` — anything at level `n` is at level `n+1` (cumulativity of the hierarchy).
* `ex` — a `Σ⁰ₙ₊₁` formula may gain a leading `∃`, provided the body is `Σ⁰ₙ₊₁`; combined with `bump`
  from the dual `Π⁰ₙ`, this realises "`∃`-block over `Π⁰ₙ`".
* `all` — dually, a `Π⁰ₙ₊₁` formula may gain a leading `∀`.
* `dual` — a `Π⁰ₙ` matrix sits inside `Σ⁰ₙ₊₁` (and `Σ⁰ₙ` inside `Π⁰ₙ₊₁`); this is what lets the
  `∃`-block bottom out on a `Π⁰ₙ` formula and vice versa.

Every inhabitant is a finite proof tree whose `ex`/`all` steps are in bijection with the formula's
actual leading quantifiers, so this is a faithful structural classifier, not a tag. -/
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

/-- `IsSigma0Of n φ`: `φ` is `Σ⁰ₙ` (existential prefix over a `Π⁰ₙ₋₁` matrix; level `0` = `IsQF`). -/
def IsSigma0Of (n : ℕ) {m : ℕ} (φ : L.BoundedFormula α m) : Prop := IsArith false n φ

/-- `IsPi0Of n φ`: `φ` is `Π⁰ₙ` (universal prefix over a `Σ⁰ₙ₋₁` matrix; level `0` = `IsQF`). -/
def IsPi0Of (n : ℕ) {m : ℕ} (φ : L.BoundedFormula α m) : Prop := IsArith true n φ

/-- Paper C's `Π⁰₂` predicate: a `∀`-block over a `Σ⁰₁` matrix, i.e. `∀…∀ ∃…∃ φ` with `φ`
quantifier-free. This is the genuine syntactic predicate replacing the manuscript's metadata enum. -/
def IsPi02 {m : ℕ} (φ : L.BoundedFormula α m) : Prop := IsPi0Of 2 φ

/-! ### Base-case bridges (`IsQF` enters the hierarchy) -/

/-- Every quantifier-free formula is `Σ⁰₀`. -/
theorem IsQF.isSigma0Of_zero {n : ℕ} {φ : L.BoundedFormula α n} (h : φ.IsQF) :
    IsSigma0Of 0 φ := IsArith.qf h

/-- Every quantifier-free formula is `Π⁰₀`. -/
theorem IsQF.isPi0Of_zero {n : ℕ} {φ : L.BoundedFormula α n} (h : φ.IsQF) :
    IsPi0Of 0 φ := IsArith.qf h

/-- A `Σ⁰ₙ` formula is `Σ⁰ₙ₊₁` (cumulativity). -/
theorem IsSigma0Of.cumulative {k n : ℕ} {φ : L.BoundedFormula α n} (h : IsSigma0Of k φ) :
    IsSigma0Of (k + 1) φ := IsArith.bump h

/-- A `Π⁰ₙ` formula is `Π⁰ₙ₊₁` (cumulativity). -/
theorem IsPi0Of.cumulative {k n : ℕ} {φ : L.BoundedFormula α n} (h : IsPi0Of k φ) :
    IsPi0Of (k + 1) φ := IsArith.bump h

/-- `IsQF → Σ⁰ₙ` for every level `n`: the quantifier-free formulas sit at the bottom of every level. -/
theorem IsQF.isSigma0Of {n : ℕ} {φ : L.BoundedFormula α n} (h : φ.IsQF) :
    ∀ k, IsSigma0Of k φ
  | 0 => IsArith.qf h
  | k + 1 => (IsQF.isSigma0Of h k).cumulative

/-- `IsQF → Π⁰ₙ` for every level `n`. -/
theorem IsQF.isPi0Of {n : ℕ} {φ : L.BoundedFormula α n} (h : φ.IsQF) :
    ∀ k, IsPi0Of k φ
  | 0 => IsArith.qf h
  | k + 1 => (IsQF.isPi0Of h k).cumulative

/-- A `Π⁰ₙ` matrix is `Σ⁰ₙ₊₁` (dual inclusion): the body of an existential block. -/
theorem IsPi0Of.isSigma0Of_succ {k n : ℕ} {φ : L.BoundedFormula α n} (h : IsPi0Of k φ) :
    IsSigma0Of (k + 1) φ := IsArith.dual (b := false) (by simpa using h)

/-- A `Σ⁰ₙ` matrix is `Π⁰ₙ₊₁` (dual inclusion): the body of a universal block. -/
theorem IsSigma0Of.isPi0Of_succ {k n : ℕ} {φ : L.BoundedFormula α n} (h : IsSigma0Of k φ) :
    IsPi0Of (k + 1) φ := IsArith.dual (b := true) (by simpa using h)

/-! ### Quantifier introduction (`∃`/`∀` blocks) -/

/-- Prefix one existential quantifier to a `Σ⁰ₙ₊₁` formula. -/
theorem IsSigma0Of.ex {k n : ℕ} {φ : L.BoundedFormula α (n + 1)} (h : IsSigma0Of (k + 1) φ) :
    IsSigma0Of (k + 1) φ.ex := IsArith.ex h

/-- Prefix one universal quantifier to a `Π⁰ₙ₊₁` formula. -/
theorem IsPi0Of.all {k n : ℕ} {φ : L.BoundedFormula α (n + 1)} (h : IsPi0Of (k + 1) φ) :
    IsPi0Of (k + 1) φ.all := IsArith.all h

/-- A single existential over a `Π⁰ₙ` formula is `Σ⁰ₙ₊₁`. -/
theorem IsPi0Of.ex_isSigma0Of_succ {k n : ℕ} {φ : L.BoundedFormula α (n + 1)} (h : IsPi0Of k φ) :
    IsSigma0Of (k + 1) φ.ex := h.isSigma0Of_succ.ex

/-- A single universal over a `Σ⁰ₙ` formula is `Π⁰ₙ₊₁`. -/
theorem IsSigma0Of.all_isPi0Of_succ {k n : ℕ} {φ : L.BoundedFormula α (n + 1)} (h : IsSigma0Of k φ) :
    IsPi0Of (k + 1) φ.all := h.isPi0Of_succ.all

/-! ### Bridge to Mathlib prenex normal form

Every level of the hierarchy lands inside Mathlib's `IsPrenex`, by induction on the proof tree. This
is the structural link enabling reuse of Mathlib's prenex API. -/

/-- Every arithmetical-hierarchy formula (any direction, any level) is in prenex normal form. -/
theorem IsArith.isPrenex {b : Bool} {k n : ℕ} {φ : L.BoundedFormula α n}
    (h : IsArith b k φ) : φ.IsPrenex := by
  induction h with
  | qf hq => exact hq.isPrenex
  | bump _ ih => exact ih
  | ex _ ih => exact ih.ex
  | all _ ih => exact ih.all
  | dual _ ih => exact ih

/-- Every `Σ⁰ₙ` formula is in prenex normal form (bridge to Mathlib `IsPrenex`). -/
theorem IsSigma0Of.isPrenex {k n : ℕ} {φ : L.BoundedFormula α n} (h : IsSigma0Of k φ) :
    φ.IsPrenex := IsArith.isPrenex h

/-- Every `Π⁰ₙ` formula is in prenex normal form (bridge to Mathlib `IsPrenex`). -/
theorem IsPi0Of.isPrenex {k n : ℕ} {φ : L.BoundedFormula α n} (h : IsPi0Of k φ) :
    φ.IsPrenex := IsArith.isPrenex h

/-- `Π⁰₂` formulas are prenex. -/
theorem IsPi02.isPrenex {n : ℕ} {φ : L.BoundedFormula α n} (h : IsPi02 φ) : φ.IsPrenex :=
  IsPi0Of.isPrenex h

/-! ### Constructors for `IsPi02`

The target builder lemmas: a `∀`-block over a `Σ⁰₁` matrix is `Π⁰₂`. A later module proving a concrete
sentence `IsPi02` uses these to assemble the witness. -/

/-- A `Σ⁰₁` matrix is already `Π⁰₂` (empty universal prefix). -/
theorem IsSigma0Of.isPi02 {n : ℕ} {φ : L.BoundedFormula α n} (h : IsSigma0Of 1 φ) :
    IsPi02 φ := h.isPi0Of_succ

/-- Prefixing one universal quantifier to a `Π⁰₂` formula keeps it `Π⁰₂`. -/
theorem IsPi02.all {n : ℕ} {φ : L.BoundedFormula α (n + 1)} (h : IsPi02 φ) :
    IsPi02 φ.all := IsPi0Of.all h

/-- A `Σ⁰₀` (quantifier-free) matrix wrapped in one existential is `Σ⁰₁`. -/
theorem IsQF.ex_isSigma0Of_one {n : ℕ} {φ : L.BoundedFormula α (n + 1)} (h : φ.IsQF) :
    IsSigma0Of 1 φ.ex := (IsQF.isPi0Of_zero h).ex_isSigma0Of_succ

/-- A single universal over a `Σ⁰₁` formula is `Π⁰₂` (smallest genuinely level-2 `Π` witness). -/
theorem IsSigma0Of.all_isPi02 {n : ℕ} {φ : L.BoundedFormula α (n + 1)} (h : IsSigma0Of 1 φ) :
    IsPi02 φ.all := h.all_isPi0Of_succ

/-- **Target builder.** A universal quantifier over an existential over a quantifier-free matrix is
`Π⁰₂`: `∀ ∃ (quantifier-free) ⟹ Π⁰₂`. This is the canonical shape a concrete-sentence module invokes
to certify `IsPi02`. -/
theorem IsQF.all_ex_isPi02 {n : ℕ} {φ : L.BoundedFormula α (n + 1 + 1)} (h : φ.IsQF) :
    IsPi02 φ.ex.all := (IsQF.ex_isSigma0Of_one h).all_isPi02

end OperatorKO7.ReverseMath.Complexity
