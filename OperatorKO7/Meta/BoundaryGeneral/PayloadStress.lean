import Mathlib

/-!
# Theory VI: Payload-size / action-parameter stress family

Boundary-general cross-paper packet, Theory VI. The depth-`K` cumulative carrier burden for a
payload of length `L` (stage `i` carries `i+1` explicit copies of the payload):
`cumulativeCarrier K L = ∑_{i=0}^{K} (i+1)·L`. It is linear in the payload length `L`, equals the
triangular number times `L` (`2·cumulativeCarrier K L = (K+1)(K+2)·L`, so it is quadratic in `K`),
and diverges with depth: at any fixed positive payload it exceeds every bound, and the *normalized*
stress ratio (carrier burden per unit Shannon information) exceeds every multiple of any fixed
entropy budget. This is the formal content of the PRT report obligation: accuracy on payload entropy
alone is insufficient, because carrier burden can diverge while entropy stays fixed.
-/

set_option autoImplicit false

open Finset

namespace OperatorKO7.Meta.BoundaryGeneral.PayloadStress

/-- Depth-`K` cumulative carrier burden for a payload of length `L`: stage `i` carries `i+1` copies. -/
def cumulativeCarrier (K L : Nat) : Nat := ∑ i ∈ range (K + 1), (i + 1) * L

/-- **Linearity in the payload length (part of Lemma 6.2).** -/
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

/-- **Closed form, doubled (Lemma 6.2, quadratic in `K`, division-free).**
`2·cumulativeCarrier K L = (K+1)(K+2)·L`. -/
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

/-- **Unbounded burden at fixed information (Theorem 6.4).** For any positive payload, the carrier
burden exceeds every bound as depth grows. -/
theorem cumulativeCarrier_unbounded (L : Nat) (hL : 1 ≤ L) (N : Nat) :
    ∃ K, N ≤ cumulativeCarrier K L :=
  ⟨N, le_trans (Nat.le_succ N) (cumulativeCarrier_ge N L hL)⟩

/-- **Normalized stress ratio diverges (Theorem 6.4, division-free).** For any fixed entropy budget
`H0` and any multiple `N`, some depth makes the carrier burden exceed `N · H0`: carrier burden per
unit Shannon information is unbounded. -/
theorem stress_ratio_unbounded (L H0 : Nat) (hL : 1 ≤ L) (N : Nat) :
    ∃ K, N * H0 ≤ cumulativeCarrier K L :=
  ⟨N * H0, le_trans (Nat.le_succ _) (cumulativeCarrier_ge (N * H0) L hL)⟩

#print axioms two_mul_cumulativeCarrier
#print axioms cumulativeCarrier_unbounded

end OperatorKO7.Meta.BoundaryGeneral.PayloadStress
