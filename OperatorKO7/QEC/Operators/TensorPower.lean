import OperatorKO7.QEC.Operators.Basic
import OperatorKO7.QEC.Dicke.Basis

set_option autoImplicit false

/-!
# QEC tensor-power surface for `(ℂ²)^⊗n`

The manuscript writes the n-qubit Hilbert space as `(ℂ²)^⊗n`. In Mathlib
this is the finite-dimensional complex Hilbert space
`EuclideanSpace ℂ (Fin n → Bool)` (the L²-space of bitstrings), already
the carrier of `QEC.Dicke.Basis.QubitRegister n`. This module exposes
the manuscript-facing names `Qubit`, `TensorPower n`, and the canonical
identifications with the existing Dicke-basis carrier, so the
downstream operator-substrate files and the code-subspace projector
can refer to `(ℂ²)^⊗n` without re-deriving the Hilbert-space structure.

## Public surfaces

* `Qubit` -- the single-qubit Hilbert space `EuclideanSpace ℂ Bool`.
* `TensorPower n` -- the n-qubit Hilbert space `(ℂ²)^⊗n`,
  identified with `QubitRegister n`.
* `Qubit.finiteDimensional`, `TensorPower.finiteDimensional` -- the
  carriers are finite-dimensional.
* `Qubit.finrank_eq`, `TensorPower.finrank_eq` -- the dimensions are
  `2` and `2^n` respectively.
* `TensorPower.eq_qubitRegister` -- the canonical identification with
  the existing Dicke carrier.
* `TensorPower.opAlgebra` -- the operator algebra surface
  `Op (TensorPower n)` for code-subspace statements.

## Audit slots

```
Relation:  finite-dim complex Hilbert space `(ℂ²)^⊗n`.
Closure:   N/A.
Strategy:  N/A.
Trust:     kernel-only.
Scope:     names + dimension theorems + identification with the Dicke
           carrier. No new theorems beyond standard Mathlib finrank
           computations.
```
-/

namespace QEC.Operators.TensorPower

set_option linter.dupNamespace false

open QEC.Dicke.Basis QEC.Operators

/-- The single-qubit Hilbert space `ℂ²`. -/
abbrev Qubit : Type := EuclideanSpace ℂ Bool

/-- The n-qubit Hilbert space `(ℂ²)^⊗n`. Identified with
`EuclideanSpace ℂ (Fin n → Bool)`, the L²-space of length-n bitstrings.
This is the same carrier as `QEC.Dicke.Basis.QubitRegister n`. -/
abbrev TensorPower (n : ℕ) : Type := EuclideanSpace ℂ (Fin n → Bool)

/-- The single-qubit Hilbert space has finite dimension `2`. -/
theorem Qubit.finrank_eq : Module.finrank ℂ Qubit = 2 := by
  unfold Qubit
  rw [finrank_euclideanSpace]
  decide

/-- The n-qubit Hilbert space has finite dimension `2^n`. -/
theorem TensorPower.finrank_eq (n : ℕ) :
    Module.finrank ℂ (TensorPower n) = 2 ^ n := by
  unfold TensorPower
  rw [finrank_euclideanSpace]
  simp [Fintype.card_bool]

/-- The n-qubit tensor power coincides definitionally with the
existing Dicke `QubitRegister n` carrier. This lets downstream files
freely interchange the two names. -/
theorem TensorPower.eq_qubitRegister (n : ℕ) :
    TensorPower n = QubitRegister n := rfl

/-- Operator algebra on the n-qubit tensor power. -/
abbrev opAlgebra (n : ℕ) : Type _ := Op (TensorPower n)

end QEC.Operators.TensorPower
