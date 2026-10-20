import OperatorKO7.Meta.QuantumBoundary.DensityMatrixPOVM
import OperatorKO7.Meta.UUET.Quantum.PositiveSemidefinite

set_option autoImplicit false

/-!
# Canonical finite density matrices

Relation: equality of finite complex density operators.
Closure: positive semidefiniteness and unit trace are bundled and inseparable.
Trust: kernel-checked Mathlib positivity and trace algebra.
Scope: finite density operators; pure and mixed states remain distinct carriers.
-/

namespace OperatorKO7.Meta.UUET.Quantum

open Matrix
open scoped ComplexOrder

/-- A density matrix on an arbitrary finite index type. -/
structure DensityMatrix (ι : Type) [Fintype ι] where
  matrix : Operator ι
  positive : PositiveSemidefinite matrix
  trace_one : matrix.trace = 1

/-- Projection to the pre-existing `Fin n` density predicate. -/
theorem DensityMatrix.toIsDensityMatrix {n : Nat} (ρ : DensityMatrix (Fin n)) :
    OperatorKO7.Meta.QuantumBoundary.DensityMatrixPOVM.IsDensityMatrix ρ.matrix :=
  ⟨ρ.positive, ρ.trace_one⟩

/-- Canonical maximally mixed qubit. -/
noncomputable def maximallyMixedQubit : DensityMatrix (Fin 2) where
  matrix := OperatorKO7.Meta.QuantumBoundary.DensityMatrixPOVM.rhoMix
  positive := OperatorKO7.Meta.QuantumBoundary.DensityMatrixPOVM.isDensityMatrix_rhoMix.1
  trace_one := OperatorKO7.Meta.QuantumBoundary.DensityMatrixPOVM.isDensityMatrix_rhoMix.2

/-- Pure computational-basis qubit `|0><0|`. -/
noncomputable def pureZeroQubit : DensityMatrix (Fin 2) where
  matrix := Matrix.diagonal ![1, 0]
  positive := by
    change (Matrix.diagonal ![(1 : ℂ), (0 : ℂ)]).PosSemidef
    rw [Matrix.posSemidef_diagonal_iff]
    intro i
    fin_cases i <;> exact Complex.zero_le_real.mpr (by norm_num)
  trace_one := by
    rw [Matrix.trace_diagonal, Fin.sum_univ_two]
    norm_num

/-- Pure computational-basis qubit `|1><1|`. -/
noncomputable def pureOneQubit : DensityMatrix (Fin 2) where
  matrix := Matrix.diagonal ![0, 1]
  positive := by
    change (Matrix.diagonal ![(0 : ℂ), (1 : ℂ)]).PosSemidef
    rw [Matrix.posSemidef_diagonal_iff]
    intro i
    fin_cases i <;> exact Complex.zero_le_real.mpr (by norm_num)
  trace_one := by
    rw [Matrix.trace_diagonal, Fin.sum_univ_two]
    norm_num

/-- Every canonical finite density matrix has trace one. -/
theorem density_trace_one {ι : Type} [Fintype ι] (ρ : DensityMatrix ι) :
    ρ.matrix.trace = 1 :=
  ρ.trace_one

/-- Negative fixture: a pure state is not the maximally mixed state. -/
theorem pureZero_ne_maximallyMixed :
    pureZeroQubit.matrix ≠ maximallyMixedQubit.matrix := by
  intro h
  have h00 := congrArg (fun A : Operator (Fin 2) => A 0 0) h
  norm_num [pureZeroQubit, maximallyMixedQubit,
    OperatorKO7.Meta.QuantumBoundary.DensityMatrixPOVM.rhoMix] at h00

/-! Imported NameGate and TypeGate. -/
#check @Matrix.posSemidef_diagonal_iff
#check @Matrix.trace_diagonal
#check @OperatorKO7.Meta.QuantumBoundary.DensityMatrixPOVM.isDensityMatrix_rhoMix
#check @DensityMatrix.toIsDensityMatrix

#check @DensityMatrix.toIsDensityMatrix
#print axioms DensityMatrix.toIsDensityMatrix
#check @density_trace_one
#print axioms density_trace_one
#check @pureZero_ne_maximallyMixed
#print axioms pureZero_ne_maximallyMixed

end OperatorKO7.Meta.UUET.Quantum
