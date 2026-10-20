import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian

set_option autoImplicit false

/-!
# QEC Operator Substrate (finite-dimensional complex operators)

This module provides the finite-dimensional operator-algebra primitives
that the downstream files (TensorPower, Projector)
and the manuscript labels `cor:heisenberg-minimum`,
`thm:kl-license`, `cor:kl-wf-overlap`, and `prop:abstention-as-overlap`
require.

The substrate is built on Mathlib's existing inner-product-space layer:
operators are `LinearMap`s on a finite-dimensional complex inner-product
space `V`, with `LinearMap.adjoint` supplying the adjoint and
`Mathlib.Analysis.InnerProductSpace.Projection` supplying orthogonal
projectors. No fake Hilbert spaces are introduced; no operator carrier
is `Prop := True`.

## Public surfaces

* `Op V` -- the operator algebra `V →ₗ[ℂ] V` on a finite-dimensional
  complex inner-product space `V`.
* `Op.id`, `Op.comp` -- identity and composition.
* `Op.adjoint` -- adjoint via `LinearMap.adjoint` (available on
  finite-dim inner-product spaces).
* `Op.commutator` -- `[A, B] := A·B − B·A`.
* `Op.expectation` -- `⟨ψ, A ψ⟩`.
* `Op.variance` -- `‖(A − ⟨A⟩·I) ψ‖²`.
* `Op.IsHermitian` -- `A = adjoint A`.
* `Op.IsProjector` -- `A·A = A ∧ adjoint A = A`.
-/

namespace QEC.Operators

open scoped ComplexConjugate

variable {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

/-! ## 1. Operator algebra -/

/-- Operator algebra on a finite-dimensional complex inner-product
space: the type of `ℂ`-linear maps `V → V`. -/
abbrev Op (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] : Type _ := V →ₗ[ℂ] V

namespace Op

/-- The identity operator. -/
def id : Op V := LinearMap.id

@[simp] theorem id_apply (ψ : V) : (id : Op V) ψ = ψ := rfl

/-- Operator composition `A · B` (left-then-right action: `(A · B) ψ = A (B ψ)`). -/
def comp (A B : Op V) : Op V := LinearMap.comp A B

@[simp] theorem comp_apply (A B : Op V) (ψ : V) : comp A B ψ = A (B ψ) :=
  LinearMap.comp_apply A B ψ

/-- The adjoint operator `A†`. Defined via Mathlib's
`LinearMap.adjoint` (which exists on finite-dim inner-product spaces). -/
noncomputable def adjoint (A : Op V) : Op V := LinearMap.adjoint A

/-- Defining property of the adjoint: `⟨A† x, y⟩ = ⟨x, A y⟩`. -/
theorem adjoint_inner_left (A : Op V) (x y : V) :
    inner ℂ (adjoint A x) y = inner ℂ x (A y) := by
  -- Mathlib: `LinearMap.adjoint_inner_left A x y : ⟪adjoint A y, x⟫ = ⟪y, A x⟫`.
  -- Swap our `x, y` to feed Mathlib's lemma.
  show inner ℂ (LinearMap.adjoint A x) y = inner ℂ x (A y)
  exact LinearMap.adjoint_inner_left (E := V) (F := V) A y x

/-- Symmetric form of the adjoint defining property:
`⟨x, A† y⟩ = ⟨A x, y⟩`. -/
theorem adjoint_inner_right (A : Op V) (x y : V) :
    inner ℂ x (adjoint A y) = inner ℂ (A x) y := by
  show inner ℂ x (LinearMap.adjoint A y) = inner ℂ (A x) y
  exact LinearMap.adjoint_inner_right (E := V) (F := V) A x y

/-- Commutator `[A, B] := A · B − B · A`. -/
def commutator (A B : Op V) : Op V := comp A B - comp B A

@[simp] theorem commutator_apply (A B : Op V) (ψ : V) :
    commutator A B ψ = A (B ψ) - B (A ψ) := by
  simp [commutator, comp]

/-- Antisymmetry of the commutator: `[A, B] = − [B, A]`. -/
theorem commutator_antisymm (A B : Op V) :
    commutator A B = - commutator B A := by
  unfold commutator
  rw [neg_sub]

/-- Commutator with the identity vanishes on the left. -/
@[simp] theorem commutator_id_left (A : Op V) :
    commutator (Op.id : Op V) A = 0 := by
  ext ψ
  simp [commutator, Op.id]

/-- Commutator with the identity vanishes on the right. -/
@[simp] theorem commutator_id_right (A : Op V) :
    commutator A (Op.id : Op V) = 0 := by
  ext ψ
  simp [commutator, Op.id]

/-! ## 2. Expectation, variance, and Hermitian operators -/

/-- Expectation `⟨ψ | A ψ⟩` of an operator `A` in the state `ψ`. -/
noncomputable def expectation (A : Op V) (ψ : V) : ℂ := inner ℂ ψ (A ψ)

/-- Variance `Var(A, ψ) := ‖(A − ⟨A⟩·I) ψ‖²`. This is the squared
norm of the centred-action `(A − ⟨A⟩) ψ`. For Hermitian `A` with
normalized `ψ`, this coincides with `⟨ψ, A² ψ⟩ − ⟨ψ, A ψ⟩²`. -/
noncomputable def variance (A : Op V) (ψ : V) : ℝ :=
  ‖A ψ - expectation A ψ • ψ‖ ^ 2

/-- The variance is nonnegative (it is a squared norm). -/
theorem variance_nonneg (A : Op V) (ψ : V) : 0 ≤ variance A ψ := by
  unfold variance
  exact sq_nonneg _

/-- The variance of the zero operator vanishes. -/
@[simp] theorem variance_zero (ψ : V) : variance (0 : Op V) ψ = 0 := by
  unfold variance expectation
  simp

/-- Hermitian (self-adjoint) operator: `A = A†`. -/
def IsHermitian (A : Op V) : Prop := adjoint A = A

/-- The zero operator is Hermitian. -/
theorem IsHermitian.zero : IsHermitian (0 : Op V) := by
  unfold IsHermitian adjoint; simp

/-- The identity operator is Hermitian. -/
theorem IsHermitian.id : IsHermitian (Op.id : Op V) := by
  show adjoint (Op.id : Op V) = (Op.id : Op V)
  show LinearMap.adjoint (LinearMap.id : V →ₗ[ℂ] V) = LinearMap.id
  exact LinearMap.adjoint_id

/-- Sum of Hermitian operators is Hermitian. -/
theorem IsHermitian.add {A B : Op V}
    (hA : IsHermitian A) (hB : IsHermitian B) :
    IsHermitian (A + B) := by
  unfold IsHermitian adjoint at *
  rw [map_add, hA, hB]

/-! ## 3. Hermitian expectation is real -/

/-- For a Hermitian operator, the expectation `⟨ψ, A ψ⟩` is real,
i.e. equals its complex conjugate. -/
theorem expectation_isReal_of_hermitian
    {A : Op V} (hA : IsHermitian A) (ψ : V) :
    conj (expectation A ψ) = expectation A ψ := by
  unfold expectation
  rw [inner_conj_symm]
  -- After conjugation symmetry: conj ⟨ψ, Aψ⟩ = ⟨Aψ, ψ⟩
  -- Use the adjoint defining property + Hermitian to swap
  -- ⟨Aψ, ψ⟩ = ⟨ψ, A† ψ⟩ = ⟨ψ, A ψ⟩ since A = A†.
  rw [← adjoint_inner_left, hA]

/-! ## 4. Projector predicate -/

/-- An orthogonal projector: idempotent and self-adjoint. -/
def IsProjector (P : Op V) : Prop :=
  comp P P = P ∧ IsHermitian P

/-- The zero operator is a (trivial) projector. -/
theorem IsProjector.zero : IsProjector (0 : Op V) := by
  refine ⟨?_, IsHermitian.zero⟩
  ext ψ
  simp

/-- The identity operator is a projector. -/
theorem IsProjector.id : IsProjector (Op.id : Op V) := by
  refine ⟨?_, IsHermitian.id⟩
  ext ψ
  simp [Op.id]

/-- A projector `P` is Hermitian. -/
theorem IsProjector.hermitian {P : Op V} (hP : IsProjector P) :
    IsHermitian P := hP.2

/-- A projector `P` is idempotent: `P · P = P`. -/
theorem IsProjector.idempotent {P : Op V} (hP : IsProjector P) :
    comp P P = P := hP.1

/-- The pointwise idempotence equation: `P (P ψ) = P ψ`. -/
theorem IsProjector.apply_apply {P : Op V} (hP : IsProjector P) (ψ : V) :
    P (P ψ) = P ψ := by
  have h := hP.idempotent
  have := congrArg (fun (L : Op V) => L ψ) h
  simpa [comp] using this

/-! ## 5. Identity-minus-projector is also a projector -/

/-- If `P` is an orthogonal projector, so is `id − P`. -/
theorem IsProjector.complement {P : Op V} (hP : IsProjector P) :
    IsProjector ((Op.id : Op V) - P) := by
  refine ⟨?_, ?_⟩
  · -- (id − P) · (id − P) = id − P  (because P · P = P).
    ext ψ
    have hPP : P (P ψ) = P ψ := hP.apply_apply ψ
    simp [Op.id, LinearMap.sub_apply, hPP]
  · -- id − P is Hermitian since both id and P are.
    have hnegP : IsHermitian (-P) := by
      show adjoint (-P) = -P
      have := hP.hermitian
      show LinearMap.adjoint (-P) = -P
      rw [show ((-P : Op V) : V →ₗ[ℂ] V) = -(P : V →ₗ[ℂ] V) from rfl, map_neg]
      show -(LinearMap.adjoint P) = -P
      rw [show LinearMap.adjoint P = adjoint P from rfl, this]
    have hsub : ((Op.id : Op V) - P) = (Op.id : Op V) + (-P) :=
      sub_eq_add_neg _ _
    rw [hsub]
    exact IsHermitian.add IsHermitian.id hnegP

end Op

end QEC.Operators
