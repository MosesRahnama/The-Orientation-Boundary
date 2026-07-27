import Mathlib

/-!
# Theory XIV: Moment-controlled wavepacket bridge (rigorous core)

Boundary-general cross-paper packet, Theory XIV. This module mechanizes the *honest, load-bearing*
core of the wavepacket bridge and nothing more. The superposition-forcing theorem of the Boundary
Operator Framework delivers a boundary-enforced **mixture** over trace terminals. Turning a mixture
into a **coherent amplitude** requires a phase law that the mixture does not contain.

We model a coherent amplitude as `amplitude r u = √r · u` from a nonnegative Born weight `r` and a
unit-modulus phase `u` (`normSq u = 1`).

* `born_density` (Theorem 14.7): the Born density of `amplitude r u` is exactly `r`, for any phase.
* `mixture_not_amplitude` (Theorem 14.6): two distinct phases give the *same* Born density but a
  *different* amplitude, so the Born density (the mixture) does not determine the amplitude. The
  phase is genuinely extra data, not recoverable from the diagonal weights.

The maximum-entropy Gaussian step (Theorem 14.4) and the no-maximizer-under-mean-alone fact
(Lemma 14.3) are real-analysis statements over function spaces and are intentionally left to a
dedicated analysis pass; the algebraic amplitude/phase separation proved here is the part the rest of
the framework actually relies on, and it is exact.

No `sorry`, `axiom`, or `native_decide`.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.BoundaryGeneral.Wavepacket

/-- A coherent amplitude from a nonnegative Born weight `r` and a unit-modulus phase `u`. -/
noncomputable def amplitude (r : ℝ) (u : ℂ) : ℂ := (Real.sqrt r : ℂ) * u

/-- **Amplitude bridge (Theorem 14.7).** The Born density of `amplitude r u` is exactly the weight
`r`, for any unit-modulus phase `u`. -/
theorem born_density (r : ℝ) (u : ℂ) (hr : 0 ≤ r) (hu : Complex.normSq u = 1) :
    Complex.normSq (amplitude r u) = r := by
  unfold amplitude
  rw [Complex.normSq_mul, Complex.normSq_ofReal, hu, mul_one, Real.mul_self_sqrt hr]

/-- **Mixture does not determine the amplitude (Theorem 14.6).** For any positive weight there are
two unit-modulus phases giving the same Born density but different amplitudes: the diagonal weights
(the boundary-enforced mixture) do not fix the phase, hence do not fix the coherent amplitude. -/
theorem mixture_not_amplitude (r : ℝ) (hr : 0 < r) :
    ∃ u₁ u₂ : ℂ,
      Complex.normSq u₁ = 1 ∧ Complex.normSq u₂ = 1 ∧
      Complex.normSq (amplitude r u₁) = Complex.normSq (amplitude r u₂) ∧
      amplitude r u₁ ≠ amplitude r u₂ := by
  refine ⟨1, -1, by simp, by simp, ?_, ?_⟩
  · rw [born_density r 1 hr.le (by simp), born_density r (-1) hr.le (by simp)]
  · have hpos : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr
    rw [show amplitude r 1 = (↑(Real.sqrt r) : ℂ) from by simp [amplitude],
        show amplitude r (-1) = (↑(-Real.sqrt r) : ℂ) from by simp [amplitude]]
    intro h
    have : Real.sqrt r = -Real.sqrt r := Complex.ofReal_inj.mp h
    linarith

#print axioms born_density
#print axioms mixture_not_amplitude

end OperatorKO7.Meta.BoundaryGeneral.Wavepacket
