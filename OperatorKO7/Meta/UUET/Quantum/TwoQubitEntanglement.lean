import OperatorKO7.Meta.UUET.Quantum.PureBipartite

set_option autoImplicit false

/-!
# Pure two-qubit entanglement

Relation: negation of amplitude product factorization.
Closure: determinant nonvanishing exactly characterizes this finite pure-state notion.
Trust: kernel-checked consequence of the factorization theorem.
Scope: pure two-qubit entanglement; Bell nonlocality is a separate predicate.
-/

namespace OperatorKO7.Meta.UUET.Quantum

/-- Quantum entanglement for a pure two-qubit amplitude table. -/
def QuantumEntangled (A : TwoQubitAmplitude) : Prop :=
  Not (ProductAmplitude A)

/-- Exact determinant characterization of pure two-qubit entanglement. -/
theorem quantumEntangled_iff_det_ne_zero (A : TwoQubitAmplitude) :
    QuantumEntangled A <-> amplitudeDet A ≠ 0 := by
  rw [QuantumEntangled, productAmplitude_iff_det_zero]

/-- Separability anchor with the proposed exact separability spelling. -/
theorem pure_two_qubit_separable_iff_amplitude_determinant_zero
    (A : TwoQubitAmplitude) :
    ProductAmplitude A <-> amplitudeDet A = 0 :=
  productAmplitude_iff_det_zero A

/-- Negative fixture: the product `|00>` amplitude is not entangled. -/
theorem productZeroZero_not_entangled :
    Not (QuantumEntangled productZeroZero) := by
  intro h
  exact h productZeroZero_is_product

/-! Imported NameGate and TypeGate. -/
#check @not_congr
#check @productAmplitude_iff_det_zero
#check @QuantumEntangled
#check @amplitudeDet

#check @quantumEntangled_iff_det_ne_zero
#print axioms quantumEntangled_iff_det_ne_zero
#check @pure_two_qubit_separable_iff_amplitude_determinant_zero
#print axioms pure_two_qubit_separable_iff_amplitude_determinant_zero
#check @productZeroZero_not_entangled
#print axioms productZeroZero_not_entangled

end OperatorKO7.Meta.UUET.Quantum
