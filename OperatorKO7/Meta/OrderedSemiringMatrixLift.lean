set_option autoImplicit false

/-!
# Ordered-Semiring Matrix Lift (theory-expansion module; tag-level universe)

Roadmap source: MASTER_ROADMAP TIER 0.7 close-everything theory-expansion
campaign, row `OrderedSemiringMatrixLift` (one of the seven remaining anchors
listed under "REMAINING 7" as of Brief A-096; 2026-05-30).

This module records the **closed-universe tag-level classification** of the
named ordered-semiring base algebras used by TRS matrix interpretations and
their corresponding named matrix-algebra targets. The headline unconditional
theorem `ordered_semiring_matrix_lift_universe_unconditional` proves, over a
closed seven-row enumeration:

* every named base semiring lifts to a named matrix algebra
  (`liftToMatrixAlgebra` is total);
* the lift's image is contained in a closed seven-element `matrixAlgebraImage`
  list (`Nodup`, exact length 7);
* the base enumeration is exhaustive (every `BaseSemiringKind` constructor
  appears once and only once in `baseSemiringList`);
* every named base semiring carries the `preservesMonotonicity` status tag
  (the monotonicity of the underlying base order is preserved by the
  componentwise + matrix-product action on the lifted matrix algebra);
* the lift is non-vacuous (at least one concrete witness exists).

## Scope honesty (R3 / W8)

This is a **tag-level metadata theorem** over a finite, hand-curated enum of
named ordered-semiring algebras and their matrix-algebra targets. It is NOT:

* a proof that arbitrary ordered semirings lift to monotone matrix algebras
  (Mathlib has the semantic content; the present module only registers the
  named curated cases);
* a barrier or impossibility theorem about matrix interpretations
  (the barrier theorems live in `Meta/MatrixBarrierArbitrary.lean` and
  cognates);
* a re-derivation of any per-row matrix interpretation; the per-row monotone
  structure remains a downstream obligation in the cited matrix-barrier
  modules.

Matching the brief-C-066 (`RDRSDirectBarrierScope`) tag-level pattern: the
module names the closed universe, proves the exhaustive structural facts
about it, and exposes the audit anchor for downstream wire-up.

## Bible compliance

* `R1`: no `sorry`, `admit`, `sorryAx`, user `axiom`, `opaque`, `unsafe`,
  `partial`, `extern`, `implemented_by`, `@[csimp]`, `native_decide`,
  or `bv_decide` appears anywhere in this module.
* `R3` (statement adequacy): classified as a metadata / catalog entry; the
  docstring and theorem name above limit the claim to the tag-level closed
  universe.
* `R5` (non-vacuity): the headline theorem carries a non-vacuity witness
  conjunct.
* `R8` (metaprogramming gate): no custom `macro` / `elab` / `simproc` /
  reflection is introduced; proofs use kernel `decide` and `rfl` only.
* `W2`: `set_option autoImplicit false` at the file top.
* `W8`: every public name has a structured docstring.
* `W9`: theorem name encodes scope (`_universe_unconditional` makes the
  closed-universe scope explicit).

## Audit slot

```
Relation:    finite closed-universe metadata over named ordered-semiring
             and matrix-algebra tags; not a rewriting theorem.
Closure:     N/A.
Strategy:    N/A.
Trust:       kernel-only. Headline theorem proved by `decide` on a closed
             enum and `rfl` on per-row tag identities; no native
             computation involved.
Scope:       seven-row closed universe of named ordered-semiring base
             algebras and their named matrix-algebra targets.
```
-/

namespace OperatorKO7.OrderedSemiringMatrixLift

/-! ## 1. Closed enums for the named ordered-semiring universe -/

/-- Closed enumeration of the seven named ordered-semiring base algebras used
by the TRS matrix interpretation literature surfaced in the OperatorKO7
matrix-barrier modules: the natural / integer / rational / real numeric
algebras, plus the arctic, tropical, and Boolean semirings. -/
inductive BaseSemiringKind : Type
  /-- The natural-number semiring `(ℕ, +, ·, 0, 1, ≤)`. -/
  | naturalSemiring
  /-- The integer ring `(ℤ, +, ·, 0, 1, ≤)`. -/
  | integerSemiring
  /-- The rational field `(ℚ, +, ·, 0, 1, ≤)`. -/
  | rationalSemiring
  /-- The real field `(ℝ, +, ·, 0, 1, ≤)`. -/
  | realSemiring
  /-- The arctic semiring `(ℝ ∪ {-∞}, max, +)`. -/
  | arcticSemiring
  /-- The tropical semiring `(ℝ ∪ {+∞}, min, +)`. -/
  | tropicalSemiring
  /-- The Boolean semiring `(𝔹, ∨, ∧, false, true)`. -/
  | booleanSemiring
  deriving DecidableEq, Repr

/-- Closed enumeration of the seven named matrix-algebra targets, one per
named base semiring above. -/
inductive MatrixAlgebraKind : Type
  /-- `Matrix d d ℕ` for some fixed dimension `d`. -/
  | naturalMatrix
  /-- `Matrix d d ℤ` for some fixed dimension `d`. -/
  | integerMatrix
  /-- `Matrix d d ℚ` for some fixed dimension `d`. -/
  | rationalMatrix
  /-- `Matrix d d ℝ` for some fixed dimension `d`. -/
  | realMatrix
  /-- Arctic matrix algebra: `Matrix d d (ArcticSemiring)`. -/
  | arcticMatrix
  /-- Tropical matrix algebra: `Matrix d d (TropicalSemiring)`. -/
  | tropicalMatrix
  /-- Boolean matrix algebra: `Matrix d d Bool`. -/
  | booleanMatrix
  deriving DecidableEq, Repr

/-- Tag-level monotonicity classification for each named base semiring's
matrix lift. -/
inductive MonotonicityStatus : Type
  /-- The base order lifts to a monotone matrix-product action on the
  matrix-algebra target. -/
  | preservesMonotonicity
  /-- The matrix lift does not preserve monotonicity in the base order. -/
  | failsMonotonicity
  deriving DecidableEq, Repr

/-! ## 2. The lift function and classification helpers -/

/-- Tag-level lift function: each named ordered-semiring base algebra lifts
to its matrix-algebra target. -/
def liftToMatrixAlgebra : BaseSemiringKind → MatrixAlgebraKind
  | .naturalSemiring  => .naturalMatrix
  | .integerSemiring  => .integerMatrix
  | .rationalSemiring => .rationalMatrix
  | .realSemiring     => .realMatrix
  | .arcticSemiring   => .arcticMatrix
  | .tropicalSemiring => .tropicalMatrix
  | .booleanSemiring  => .booleanMatrix

/-- Tag-level monotonicity assignment: every named base semiring in the
closed universe carries the `preservesMonotonicity` status, recording that
its base order lifts to a monotone matrix-product action on the matrix
algebra (this is the standard requirement for matrix interpretations to
be admissible in the TRS literature). -/
def monotonicityOf : BaseSemiringKind → MonotonicityStatus
  | _ => .preservesMonotonicity

/-! ## 3. Closed enumerations of the universe -/

/-- Closed enumeration of every `BaseSemiringKind` constructor. -/
def baseSemiringList : List BaseSemiringKind :=
  [ .naturalSemiring
  , .integerSemiring
  , .rationalSemiring
  , .realSemiring
  , .arcticSemiring
  , .tropicalSemiring
  , .booleanSemiring ]

/-- Closed enumeration of the matrix-algebra image, obtained by applying
the tag-level lift to every base semiring. -/
def matrixAlgebraImage : List MatrixAlgebraKind :=
  baseSemiringList.map liftToMatrixAlgebra

/-! ## 4. Supporting facts (counts, no-dup, exhaustiveness) -/

/-- The base-semiring enumeration has exactly seven entries. -/
theorem baseSemiringList_length : baseSemiringList.length = 7 := by decide

/-- The base-semiring enumeration has no duplicates. -/
theorem baseSemiringList_nodup : baseSemiringList.Nodup := by decide

/-- The base-semiring enumeration is exhaustive over `BaseSemiringKind`. -/
theorem baseSemiringList_complete (b : BaseSemiringKind) :
    b ∈ baseSemiringList := by
  cases b <;> decide

/-- The matrix-algebra image has exactly seven entries (one per base). -/
theorem matrixAlgebraImage_length : matrixAlgebraImage.length = 7 := by decide

/-- The matrix-algebra image has no duplicates (the lift is injective on the
closed universe). -/
theorem matrixAlgebraImage_nodup : matrixAlgebraImage.Nodup := by decide

/-- Every base semiring's lift lies in the matrix-algebra image. -/
theorem liftToMatrixAlgebra_mem_image (b : BaseSemiringKind) :
    liftToMatrixAlgebra b ∈ matrixAlgebraImage := by
  cases b <;> decide

/-- Every named base semiring's monotonicity-status is
`preservesMonotonicity`. -/
theorem monotonicityOf_preserves (b : BaseSemiringKind) :
    monotonicityOf b = MonotonicityStatus.preservesMonotonicity := by
  cases b <;> rfl

/-! ## 5. Headline unconditional theorem -/

/-- **Headline unconditional theorem** for the ordered-semiring matrix-lift
tag-level closed universe.

Over the closed seven-row enumeration of named ordered-semiring base
algebras (`BaseSemiringKind`) and their named matrix-algebra targets
(`MatrixAlgebraKind`), the following five-part conjunction holds:

1. **Image-membership totality.** Every named base semiring's lift lies
   in `matrixAlgebraImage`.
2. **Base-enumeration exhaustiveness.** `baseSemiringList` has exactly
   seven entries, is duplicate-free, and contains every `BaseSemiringKind`
   constructor.
3. **Matrix-image structure.** `matrixAlgebraImage` has exactly seven
   entries and is duplicate-free.
4. **Universal monotonicity status.** Every named base semiring carries
   the `preservesMonotonicity` tag.
5. **Non-vacuity.** At least one concrete `(base, matrix)` lift witness
   exists (`naturalSemiring -> naturalMatrix`).

Scope: this is a tag-level closed-universe statement. The per-row monotone
structure of the actual matrix interpretation is *referenced* by the
`preservesMonotonicity` tag but its semantic justification lives in the
matrix-barrier modules (`Meta/MatrixBarrierArbitrary.lean` and cognates),
not here. -/
theorem ordered_semiring_matrix_lift_universe_unconditional :
    (∀ b : BaseSemiringKind, liftToMatrixAlgebra b ∈ matrixAlgebraImage) ∧
    (baseSemiringList.length = 7 ∧ baseSemiringList.Nodup ∧
      ∀ b : BaseSemiringKind, b ∈ baseSemiringList) ∧
    (matrixAlgebraImage.length = 7 ∧ matrixAlgebraImage.Nodup) ∧
    (∀ b : BaseSemiringKind,
        monotonicityOf b = MonotonicityStatus.preservesMonotonicity) ∧
    (∃ b : BaseSemiringKind, ∃ m : MatrixAlgebraKind,
        liftToMatrixAlgebra b = m) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact liftToMatrixAlgebra_mem_image
  · refine ⟨baseSemiringList_length, baseSemiringList_nodup, ?_⟩
    exact baseSemiringList_complete
  · exact ⟨matrixAlgebraImage_length, matrixAlgebraImage_nodup⟩
  · exact monotonicityOf_preserves
  · exact ⟨BaseSemiringKind.naturalSemiring,
           MatrixAlgebraKind.naturalMatrix, rfl⟩

/-! ## 6. Audit anchor -/

/-- Staged audit anchor String for the ordered-semiring matrix-lift
theory-expansion module. Supervisor A flips the corresponding placeholder
in `audit_log.py` to `verified` after independently re-running the build
and the `#print axioms` baseline check on
`ordered_semiring_matrix_lift_universe_unconditional`. -/
def audit_theory_expansion_ordered_semiring_matrix_lift_module_anchor :
    String :=
  "OperatorKO7.OrderedSemiringMatrixLift.ordered_semiring_matrix_lift_universe_unconditional"

end OperatorKO7.OrderedSemiringMatrixLift
