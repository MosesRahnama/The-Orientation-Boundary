import Mathlib

/-!
# Operator-law corrections: the trace shift is not a bosonic ladder

The CORRECTED mechanization of the blueprint's section 10 operator corrections.
The early-draft action-quantum claim
treated the trace-position shift `D` as a bosonic annihilation operator with `[D, D†] = I`. That is
false: `D` is a (finite) one-sided shift, an isometry-like operator, and its commutator is a rank-≤2
edge operator, not the identity. This module proves the corrected fact concretely on the 2-dimensional
trace space: `[D, D†] = diag(1, -1) ≠ I`.

The exact `|0⟩⟨0|` commutator of the blueprint's prose is the infinite-dimensional (ℓ²) limit; on the
finite trace space there is a second edge term at the top. Either way `D` is NOT bosonic, so it cannot
support Glauber coherent states, and the harmonic-oscillator structure must come from a SEPARATE
square-root-weighted ladder. The corrected dimensionless-quadrature spectrum `Eₙ = |b|(n + 1/2)` is
also recorded (its spacing is exactly `|b|` and its zero-point is `|b|/2`).

## Module contract
- Relation: not a rewriting relation; concrete finite operator algebra.
- Closure: `propext`, `Classical.choice`, `Quot.sound`.
- Trust: no `sorry`/`axiom`/`native_decide`; the commutator is a concrete 2×2 integer matrix identity.
- Scope: the finite (2-dim) commutator and the oscillator spectrum spacing/zero-point only.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.QuantumBoundary.OperatorLawCorrections

open Matrix

/-- The finite 2-dimensional lowering shift: `D|1⟩ = |0⟩`, `D|0⟩ = 0`. -/
def D : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 0, 0]

/-- Its adjoint, the raising shift: `D†|0⟩ = |1⟩`, `D†|1⟩ = 0`. -/
def Ddag : Matrix (Fin 2) (Fin 2) ℤ := !![0, 0; 1, 0]

/-- **The finite shift commutator is the edge operator `diag(1, -1)`**, not the bosonic identity.
On the finite trace space the one-sided shift has edges at both ends; the exact `|0⟩⟨0|` of the
blueprint's prose is the infinite-dimensional (ℓ²) limit. -/
theorem shift_commutator : D * Ddag - Ddag * D = !![1, 0; 0, -1] := by
  decide

/-- **The trace-shift operator is not bosonic:** `[D, D†] ≠ I`. This corrects the early-draft claim
`[D, D†] = I` (and the separately-flagged wrong form `I - |0⟩⟨0|`). -/
theorem shift_not_bosonic : D * Ddag - Ddag * D ≠ (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
  decide

/-! ## Corrected dimensionless-quadrature oscillator spectrum -/

/-- The corrected oscillator energy `Eₙ = |b| (n + 1/2)` (dimensionless quadratures, pure energy
multiplier `|b|`). -/
noncomputable def oscEnergy (b : ℝ) (n : ℕ) : ℝ := |b| * (n + 1 / 2)

/-- The level spacing is exactly `|b|`, independent of `n`. -/
theorem osc_spacing (b : ℝ) (n : ℕ) : oscEnergy b (n + 1) - oscEnergy b n = |b| := by
  unfold oscEnergy
  push_cast
  ring

/-- The zero-point energy is exactly `|b| / 2`. -/
theorem osc_zeroPoint (b : ℝ) : oscEnergy b 0 = |b| / 2 := by
  unfold oscEnergy
  push_cast
  ring

#check @shift_commutator
#print axioms shift_commutator
#check @shift_not_bosonic
#print axioms shift_not_bosonic
#check @osc_spacing
#print axioms osc_spacing
#check @osc_zeroPoint
#print axioms osc_zeroPoint


/-! ## Universal finite-dimensional scalar-commutator obstruction -/

/-- Every finite matrix commutator has zero trace. -/
theorem trace_commutator {n R : Type*} [Fintype n] [CommRing R]
    (a b : Matrix n n R) : (a * b - b * a).trace = 0 := by
  rw [Matrix.trace_sub, Matrix.trace_mul_comm a b, sub_self]

/-- Over a characteristic-zero domain, a scalar commutator in nonzero finite dimension
must be zero; the two matrices then commute. -/
theorem commutator_eq_scalar_iff {n R : Type*} [Fintype n] [DecidableEq n]
    [Nonempty n] [CommRing R] [IsDomain R] [CharZero R]
    (a b : Matrix n n R) (c : R) :
    a * b - b * a = c • (1 : Matrix n n R) ↔ c = 0 ∧ a * b = b * a := by
  constructor
  · intro h
    have ht := congrArg Matrix.trace h
    rw [trace_commutator, Matrix.trace_smul, Matrix.trace_one, smul_eq_mul] at ht
    have hn : (Fintype.card n : R) ≠ 0 :=
      Nat.cast_ne_zero.mpr (ne_of_gt Fintype.card_pos)
    have hc : c = 0 := (mul_eq_zero.mp ht.symm).resolve_right hn
    refine ⟨hc, ?_⟩
    rw [hc, zero_smul, sub_eq_zero] at h
    exact h
  · rintro ⟨rfl, h⟩
    rw [h, sub_self, zero_smul]

/-- No finite matrix pair in characteristic zero realizes a nonzero scalar canonical commutator. -/
theorem finite_commutator_ne_scalar {n R : Type*} [Fintype n] [DecidableEq n]
    [Nonempty n] [CommRing R] [IsDomain R] [CharZero R]
    (a b : Matrix n n R) (c : R) (hc : c ≠ 0) :
    a * b - b * a ≠ c • (1 : Matrix n n R) := by
  intro h
  exact hc ((commutator_eq_scalar_iff a b c).mp h).1

theorem finite_commutator_ne_one {n R : Type*} [Fintype n] [DecidableEq n]
    [Nonempty n] [CommRing R] [IsDomain R] [CharZero R]
    (a b : Matrix n n R) : a * b - b * a ≠ (1 : Matrix n n R) := by
  simpa only [one_smul] using finite_commutator_ne_scalar a b (1 : R) one_ne_zero

#check @trace_commutator
#print axioms trace_commutator
#check @commutator_eq_scalar_iff
#print axioms commutator_eq_scalar_iff
#check @finite_commutator_ne_scalar
#print axioms finite_commutator_ne_scalar
#check @finite_commutator_ne_one
#print axioms finite_commutator_ne_one

end OperatorKO7.Meta.QuantumBoundary.OperatorLawCorrections

