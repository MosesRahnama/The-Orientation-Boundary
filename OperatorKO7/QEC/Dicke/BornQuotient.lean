import Mathlib.Data.Complex.Trigonometric

/-!
# Born quotient removes the Dicke wrapper gauge

This module formalizes the carrier-level content of manuscript corollary
`cor:born-elim-gauge`: multiplying a complex amplitude by a unit-modulus
phase leaves its Born weight unchanged.
-/

namespace QEC.Dicke.BornQuotient

/-- Manuscript label `cor:born-elim-gauge`.

The Born quotient removes the wrapper-gauge phase from a complex amplitude:
for any `c : ℂ` and `φ : ℝ`, the squared norm of
`c * exp (I * φ)` is exactly the squared norm of `c`. -/
theorem kills_gauge (c : ℂ) (φ : ℝ) :
    ‖c * Complex.exp (Complex.I * φ)‖ ^ 2 = ‖c‖ ^ 2 := by
  rw [Complex.norm_mul]
  have hphase : ‖Complex.exp (Complex.I * φ)‖ = 1 := by
    simpa [mul_comm] using Complex.norm_exp_ofReal_mul_I φ
  rw [hphase, mul_one]

end QEC.Dicke.BornQuotient
