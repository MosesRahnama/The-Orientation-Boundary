import OperatorKO7.Meta.UUET.Quantum.BellState

set_option autoImplicit false

/-!
# Explicit two-qubit entangling channel

Relation: equality under the controlled-NOT basis permutation.
Closure: one invertible finite amplitude channel and a scoped entanglement-grade witness.
Trust: kernel-checked finite case analysis.
Scope: one explicit input/channel theorem; no universal recursion-entanglement law.
-/

namespace OperatorKO7.Meta.UUET.Quantum

/-- Flip a qubit basis index. -/
def flipQubit : Fin 2 -> Fin 2 := ![1, 0]

/-- Controlled-NOT action on a two-qubit amplitude table. -/
def cnotAmplitude (A : TwoQubitAmplitude) : TwoQubitAmplitude :=
  fun control target =>
    if control = 0 then A control target else A control (flipQubit target)

/-- Unnormalized `|+> tensor |0>` product input. -/
def plusZeroAmplitude : TwoQubitAmplitude :=
  fun _ target => if target = 0 then 1 else 0

theorem plusZeroAmplitude_product : ProductAmplitude plusZeroAmplitude := by
  refine ⟨![1, 1], ![1, 0], ?_⟩
  have h :
      plusZeroAmplitude =
        fun i j => (![1, 1] : Fin 2 → ℂ) i * (![1, 0] : Fin 2 → ℂ) j := by
    funext i j
    fin_cases i <;> fin_cases j <;> simp [plusZeroAmplitude]
  intro i j
  exact congrFun (congrFun h i) j

/-- Controlled-NOT is involutive on amplitudes. -/
theorem cnotAmplitude_involutive (A : TwoQubitAmplitude) :
    cnotAmplitude (cnotAmplitude A) = A := by
  funext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem cnot_plusZero_det :
    amplitudeDet (cnotAmplitude plusZeroAmplitude) = 1 := by
  norm_num [amplitudeDet, cnotAmplitude, plusZeroAmplitude, flipQubit]

/-- Separability anchor: the explicit premeasurement permutation entangles a nontrivial product input. -/
theorem premeasurement_unitary_entangles_nontrivial_input :
    QuantumEntangled (cnotAmplitude plusZeroAmplitude) := by
  rw [quantumEntangled_iff_det_ne_zero, cnot_plusZero_det]
  norm_num

/-- Binary entanglement grade for the pure two-qubit determinant criterion. -/
noncomputable def entanglementGrade (A : TwoQubitAmplitude) : Nat :=
  if amplitudeDet A = 0 then 0 else 1

theorem cnot_grade_increases_on_plusZero :
    entanglementGrade plusZeroAmplitude <
      entanglementGrade (cnotAmplitude plusZeroAmplitude) := by
  norm_num [entanglementGrade, amplitudeDet, plusZeroAmplitude,
    cnotAmplitude, flipQubit]

/-- Negative fixture: identity recursion never strictly increases the grade. -/
theorem identity_channel_not_strictly_entangling (A : TwoQubitAmplitude) :
    Not (entanglementGrade A < entanglementGrade A) :=
  Nat.lt_irrefl _

/-! Imported NameGate and TypeGate. -/
#check @Nat.lt_irrefl
#check @quantumEntangled_iff_det_ne_zero
#check @cnotAmplitude
#check @entanglementGrade

#check @plusZeroAmplitude_product
#print axioms plusZeroAmplitude_product
#check @cnotAmplitude_involutive
#print axioms cnotAmplitude_involutive
#check @cnot_plusZero_det
#print axioms cnot_plusZero_det
#check @premeasurement_unitary_entangles_nontrivial_input
#print axioms premeasurement_unitary_entangles_nontrivial_input
#check @cnot_grade_increases_on_plusZero
#print axioms cnot_grade_increases_on_plusZero
#check @identity_channel_not_strictly_entangling
#print axioms identity_channel_not_strictly_entangling

end OperatorKO7.Meta.UUET.Quantum
