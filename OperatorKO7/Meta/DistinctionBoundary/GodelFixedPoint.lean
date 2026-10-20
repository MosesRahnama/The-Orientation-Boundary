/-
Copyright (c) 2026 Moses Rahnama. All rights reserved.
Source-available; see the file LICENSE. Free for individual research;
departmental academic use and commercial use require a paid license.
Authors: Moses Rahnama
-/
import OperatorKO7.Meta.DistinctionBoundary.DiagonalLevels

/-!
# Fixed points from represented diagonals (paper engine, no carrier lock)

Paper: `Rahnama_The_Godel_Object.tex`, theorems on an arbitrary
`SelfEvaluationDiagonal`. This is the Lawvere engine without cartesian
closure. It does not re-derive incompleteness. NameGate: no
`goedel_first`, no `incompleteness`, no `feferman_completeness`.

The four theorems are unconditional on the frozen A5 structure. They do
not inhabit a non-degenerate evaluator and do not fill Lawvere slots on
the DP object.

Relation: representation of a composite against the self-application
`S_D = diag ∘ quote`. Closure: propositional. Trust: kernel only.
-/

set_option autoImplicit false

open OperatorKO7
open OperatorKO7.Trace
open OperatorKO7.Meta.DistinctionBoundary.DiagonalLevels

namespace OperatorKO7.Meta.DistinctionBoundary.GodelFixedPoint

/-- Self-application of a self-evaluation diagonal: `S_D = diag ∘ quote`. -/
def selfApplication {C : Type*} (D : SelfEvaluationDiagonal C) : C → C :=
  D.diag ∘ D.quote

/-- Paper Definition 3: `D` represents `f` when some quotation evaluates as `f`. -/
def Represents {C : Type*} (D : SelfEvaluationDiagonal C) (f : C → C) : Prop :=
  ∃ x : C, ∀ y : C, D.eval (D.quote x) y = f y

/-- P-G-0. If `D` represents `g ∘ S_D` at witness `x`, then `S_D x` is a
fixed point of `g`. Instantiate representation at `y = x` and apply
`diag_law`. -/
theorem represented_composite_has_fixed_point {C : Type*}
    (D : SelfEvaluationDiagonal C) (g : C → C) {x : C}
    (h : ∀ y : C, D.eval (D.quote x) y = g (selfApplication D y)) :
    selfApplication D x = g (selfApplication D x) := by
  have hx := h x
  have hdiag := D.diag_law x
  calc
    selfApplication D x = D.diag (D.quote x) := rfl
    _ = D.eval (D.quote x) x := hdiag
    _ = g (selfApplication D x) := hx

/-- P-G-1. Contrapositive: a fixed-point-free endomap cannot have its
composite with `S_D` represented. -/
theorem not_represents_composite_of_fixed_point_free {C : Type*}
    (D : SelfEvaluationDiagonal C) {g : C → C}
    (hg : ∀ c : C, g c ≠ c) :
    ¬ Represents D (g ∘ selfApplication D) := by
  intro ⟨x, hx⟩
  exact hg (selfApplication D x)
    (represented_composite_has_fixed_point D g hx).symm

/-- P-G-2. Successor obstruction on Trace: `delta` is fixed-point-free, so
no self-evaluation diagonal on Trace represents `delta ∘ S_D`. -/
theorem not_represents_delta_composite (D : SelfEvaluationDiagonal Trace) :
    ¬ Represents D (Trace.delta ∘ selfApplication D) :=
  not_represents_composite_of_fixed_point_free D delta_ne_self

/-- A class of unary maps closed under left composition with `delta`. -/
def ClosedUnderLeftDelta (R : (Trace → Trace) → Prop) : Prop :=
  ∀ f : Trace → Trace, R f → R (Trace.delta ∘ f)

/-- P-G-3. Self-exclusion: a class that contains `S_D` and is closed under
left `delta` cannot be fully represented. The obstruction is closure under
one height-increasing constructor, not signature definability. -/
theorem self_exclusion_of_class (D : SelfEvaluationDiagonal Trace)
    (R : (Trace → Trace) → Prop)
    (hS : R (selfApplication D))
    (hcl : ClosedUnderLeftDelta R)
    (hrep : ∀ f : Trace → Trace, R f → Represents D f) :
    False :=
  not_represents_delta_composite D (hrep _ (hcl _ hS))

/-- R5 for the degenerate A5 instance: it does not represent `delta ∘ S_D`.
This is P-G-2 at `trivialSelfEvaluationDiagonal`. -/
theorem trivial_not_represents_delta_composite :
    ¬ Represents trivialSelfEvaluationDiagonal
        (Trace.delta ∘ selfApplication trivialSelfEvaluationDiagonal) :=
  not_represents_delta_composite trivialSelfEvaluationDiagonal

/-- The degenerate evaluator is the second projection, so it represents a
map if and only if that map is the identity. Kill for a G4 that stayed
degenerate. -/
theorem represents_trivial_iff {f : Trace → Trace} :
    Represents trivialSelfEvaluationDiagonal f ↔ f = id := by
  constructor
  · intro ⟨_x, hx⟩
    funext y
    simpa using (hx y).symm
  · intro hf
    refine ⟨Trace.void, ?_⟩
    intro y
    simp [trivialSelfEvaluationDiagonal, hf]

/-- R5 pair: the degenerate instance represents the identity and does not
represent `delta`. -/
theorem trivial_represents_id_not_delta :
    Represents trivialSelfEvaluationDiagonal id ∧
      ¬ Represents trivialSelfEvaluationDiagonal Trace.delta := by
  constructor
  · exact (represents_trivial_iff (f := id)).mpr rfl
  · intro h
    have hf := (represents_trivial_iff (f := Trace.delta)).mp h
    exact delta_ne_self Trace.void (congrFun hf Trace.void)

end OperatorKO7.Meta.DistinctionBoundary.GodelFixedPoint
