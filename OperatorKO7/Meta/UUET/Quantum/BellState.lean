import OperatorKO7.Meta.UUET.Quantum.PartialTrace
import OperatorKO7.Meta.UUET.Quantum.TwoQubitEntanglement

set_option autoImplicit false

/-!
# Bell-state fixtures

Relation: equality of a projective Bell amplitude and its normalized density operator.
Closure: determinant nonseparability and explicit reduced-state computation.
Trust: kernel-checked finite matrix and sum arithmetic.
Scope: one two-qubit Bell fixture; no Bell-inequality theorem is inferred.
-/

namespace OperatorKO7.Meta.UUET.Quantum

/-- Projective amplitude representative of `|00> + |11>`. -/
def bellAmplitude : TwoQubitAmplitude :=
  fun i j => if i = j then 1 else 0

theorem bellAmplitude_det : amplitudeDet bellAmplitude = 1 := by
  norm_num [amplitudeDet, bellAmplitude]

/-- Positive fixture: the Bell amplitude is nonseparable. -/
theorem bell_state_nonseparable : QuantumEntangled bellAmplitude := by
  rw [quantumEntangled_iff_det_ne_zero, bellAmplitude_det]
  norm_num

/-- Unnormalized Bell ket used to build a normalized density operator. -/
def bellKet (p : Fin 2 × Fin 2) : ℂ :=
  if p.1 = p.2 then 1 else 0

/-- Normalized Bell density `(1/2) |Bell><Bell|`. -/
noncomputable def bellDensityMatrix : BipartiteOperator (Fin 2) (Fin 2) :=
  ((1 / 2 : ℝ) : ℂ) • outer bellKet

theorem bellDensityMatrix_positive :
    PositiveSemidefinite bellDensityMatrix := by
  exact real_smul_positiveSemidefinite (outer_positiveSemidefinite bellKet) (by norm_num)

theorem bellDensityMatrix_trace : bellDensityMatrix.trace = 1 := by
  norm_num [bellDensityMatrix, Matrix.trace, Fintype.sum_prod_type,
    Matrix.diag_apply, outer_apply, bellKet, Fin.sum_univ_two]

/-- Bundled normalized Bell density operator. -/
noncomputable def bellDensity : DensityMatrix (Fin 2 × Fin 2) where
  matrix := bellDensityMatrix
  positive := bellDensityMatrix_positive
  trace_one := bellDensityMatrix_trace

/-- Each Bell subsystem is maximally mixed. -/
theorem bell_partialTraceRight :
    partialTraceRight bellDensity.matrix = maximallyMixedQubit.matrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [partialTraceRight, bellDensity, bellDensityMatrix, bellKet,
      outer_apply, maximallyMixedQubit,
      OperatorKO7.Meta.QuantumBoundary.DensityMatrixPOVM.rhoMix,
      Matrix.diagonal_apply]

/-! Imported NameGate and TypeGate. -/
#check @real_smul_positiveSemidefinite
#check @partialTraceRight
#check @quantumEntangled_iff_det_ne_zero
#check @bellDensity

#check @bellAmplitude_det
#print axioms bellAmplitude_det
#check @bell_state_nonseparable
#print axioms bell_state_nonseparable
#check @bellDensityMatrix_positive
#print axioms bellDensityMatrix_positive
#check @bellDensityMatrix_trace
#print axioms bellDensityMatrix_trace
#check @bell_partialTraceRight
#print axioms bell_partialTraceRight

end OperatorKO7.Meta.UUET.Quantum
