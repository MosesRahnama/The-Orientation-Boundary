import Mathlib
import OperatorKO7.Meta.UUET.Units.Quantity

set_option autoImplicit false

/-!
# Finite Hilbert-space carriers

Relation: equality of finite complex vectors and operators.
Closure: finite matrix composition, adjoint, and rank-one outer products.
Trust: kernel-checked Mathlib finite linear algebra.
Scope: finite-dimensional complex carriers only; no physical-substrate promotion.
-/

namespace OperatorKO7.Meta.UUET.Quantum

open Matrix

/-- A finite complex ket indexed by `ι`. -/
abbrev Ket (ι : Type) := ι -> ℂ

/-- A finite complex operator indexed by `ι`. -/
abbrev Operator (ι : Type) := Matrix ι ι ℂ

/-- A finite bipartite operator with explicit product indices. -/
abbrev BipartiteOperator (ι κ : Type) := Matrix (ι × κ) (ι × κ) ℂ

/-- A ket written as a one-column matrix. -/
def ketColumn {ι : Type} (ψ : Ket ι) : Matrix ι (Fin 1) ℂ :=
  Matrix.of fun i _ => ψ i

/-- Rank-one outer product `|ψ><ψ|`. -/
noncomputable def outer {ι : Type} (ψ : Ket ι) : Operator ι :=
  ketColumn ψ * (ketColumn ψ)ᴴ

@[simp] theorem ketColumn_apply {ι : Type} (ψ : Ket ι) (i : ι) (j : Fin 1) :
    ketColumn ψ i j = ψ i := rfl

@[simp] theorem outer_apply {ι : Type} (ψ : Ket ι) (i j : ι) :
    outer ψ i j = ψ i * star (ψ j) := by
  simp [outer, Matrix.mul_apply]

/-- Positive fixture: the first qubit basis ket has unit first coordinate. -/
def basisKetZero : Ket (Fin 2) := ![1, 0]

theorem basisKetZero_fixture :
    basisKetZero 0 = 1 /\ basisKetZero 1 = 0 := by
  norm_num [basisKetZero]

/-! Imported NameGate and TypeGate. -/
#check @Matrix.mul_apply
#check @Matrix.conjTranspose_apply
#check @ketColumn
#check @outer

#check @ketColumn_apply
#print axioms ketColumn_apply
#check @outer_apply
#print axioms outer_apply
#check @basisKetZero_fixture
#print axioms basisKetZero_fixture

end OperatorKO7.Meta.UUET.Quantum
