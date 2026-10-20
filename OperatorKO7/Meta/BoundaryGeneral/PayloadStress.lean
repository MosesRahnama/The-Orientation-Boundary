import Mathlib

/-!
# Payload-size and action-parameter stress family

For payload length `L` and depth `K`, cumulative carrier burden is `Σᵢ₌₀ᴷ (i+1)·L`. The identity `2·cumulativeCarrier K L = (K+1)(K+2)·L` shows linear growth in `L` and quadratic growth in `K`. For every positive `L` and bound `N`, some depth has burden at least `N`. For every positive `L`, `H0`, and multiplier `N`, some depth has burden at least `N·H0`.
-/

set_option autoImplicit false

open Finset

namespace OperatorKO7.Meta.BoundaryGeneral.PayloadStress

/-- Depth-`K` cumulative carrier burden for a payload of length `L`: stage `i` carries `i+1` copies. -/
def cumulativeCarrier (K L : Nat) : Nat := ∑ i ∈ range (K + 1), (i + 1) * L

/-- Cumulative carrier burden is additive in payload length. -/
theorem cumulativeCarrier_add_payload (K L₁ L₂ : Nat) :
    cumulativeCarrier K (L₁ + L₂) = cumulativeCarrier K L₁ + cumulativeCarrier K L₂ := by
  simp only [cumulativeCarrier, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The doubled triangular identity (division-free). -/
private theorem two_mul_triangle (K : Nat) :
    ∑ i ∈ range (K + 1), 2 * (i + 1) = (K + 1) * (K + 2) := by
  induction K with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; ring

/-- The doubled closed form is `2·cumulativeCarrier K L = (K+1)(K+2)·L`. -/
theorem two_mul_cumulativeCarrier (K L : Nat) :
    2 * cumulativeCarrier K L = (K + 1) * (K + 2) * L := by
  have h1 : cumulativeCarrier K L = (∑ i ∈ range (K + 1), (i + 1)) * L := by
    simp only [cumulativeCarrier, Finset.sum_mul]
  have h2 : 2 * (∑ i ∈ range (K + 1), (i + 1)) = (K + 1) * (K + 2) := by
    rw [Finset.mul_sum]; exact two_mul_triangle K
  rw [h1, ← Nat.mul_assoc, h2]

/-- The burden is at least `K+1` for any positive payload. -/
theorem cumulativeCarrier_ge (K L : Nat) (hL : 1 ≤ L) : K + 1 ≤ cumulativeCarrier K L := by
  have h : ∑ _i ∈ range (K + 1), 1 ≤ ∑ i ∈ range (K + 1), (i + 1) * L := by
    apply Finset.sum_le_sum
    intro i _
    have : 1 * 1 ≤ (i + 1) * L := Nat.mul_le_mul (by omega) hL
    simpa using this
  simpa [cumulativeCarrier, Finset.sum_const, Finset.card_range] using h

/-- For every positive payload length and bound `N`, some depth `K` has cumulative burden at least `N`. -/
theorem cumulativeCarrier_unbounded (L : Nat) (hL : 1 ≤ L) (N : Nat) :
    ∃ K, N ≤ cumulativeCarrier K L :=
  ⟨N, le_trans (Nat.le_succ N) (cumulativeCarrier_ge N L hL)⟩

/-- For every payload length `L`, `H0`, and multiplier `N`, some depth `K` satisfies `N · H0 ≤ cumulativeCarrier K L`. -/
theorem stress_ratio_unbounded (L H0 : Nat) (hL : 1 ≤ L) (N : Nat) :
    ∃ K, N * H0 ≤ cumulativeCarrier K L :=
  ⟨N * H0, le_trans (Nat.le_succ _) (cumulativeCarrier_ge (N * H0) L hL)⟩

#print axioms two_mul_cumulativeCarrier
#print axioms cumulativeCarrier_unbounded

end OperatorKO7.Meta.BoundaryGeneral.PayloadStress
