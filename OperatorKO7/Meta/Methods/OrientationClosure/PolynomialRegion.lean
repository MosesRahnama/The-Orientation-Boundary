import Mathlib.Tactic

/-!
# Coupled polynomial orientation region

A positive construction for the two-rule free recursor, stated only in terms of
its natural-valued constructor interpretations.
-/

set_option autoImplicit false

namespace OperatorKO7.Methods.OrientationClosure.PolynomialRegion

/-- Successor interpretation. -/
def successorEval (n : Nat) : Nat := n + 1

/-- Wrapper interpretation with one copy of the step argument. -/
def wrapperEval (s y : Nat) : Nat := s + y + 1

/-- Coupled recursor interpretation. -/
def recursorEval (α β b s n : Nat) : Nat :=
  (n + 1) * (α * s + b + β)

/-- Uniform orientation of the successor recursor rule. -/
def OrientsSuccessor (α β : Nat) : Prop :=
  ∀ b s n,
    wrapperEval s (recursorEval α β b s n) <
      recursorEval α β b s (successorEval n)

/-- Uniform orientation of the zero recursor rule. -/
def OrientsZero (α β : Nat) : Prop :=
  ∀ b s, b < recursorEval α β b s 0

/-- Both free recursor rules are oriented. -/
def OrientsBoth (α β : Nat) : Prop := OrientsZero α β ∧ OrientsSuccessor α β

/-- The successor-step difference under the sufficient parameter region. -/
theorem successor_margin
    {α β : Nat} (hα : 1 ≤ α) (hβ : 2 ≤ β) (b s n : Nat) :
    ∃ q : Nat,
      1 ≤ q ∧
      recursorEval α β b s (successorEval n) =
        wrapperEval s (recursorEval α β b s n) + q := by
  obtain ⟨a, ha⟩ := Nat.exists_eq_add_of_le hα
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hβ
  subst α
  subst β
  refine ⟨a * s + b + d + 1, by omega, ?_⟩
  simp [recursorEval, successorEval, wrapperEval]
  ring

/-- The coupled polynomial orients the successor rule when `α ≥ 1` and
`β ≥ 2`. -/
theorem orientsSuccessor_of_region
    {α β : Nat} (hα : 1 ≤ α) (hβ : 2 ≤ β) :
    OrientsSuccessor α β := by
  intro b s n
  obtain ⟨q, hq, heq⟩ := successor_margin hα hβ b s n
  rw [heq]
  omega

/-- The same parameter region orients the zero rule. -/
theorem orientsZero_of_region
    {α β : Nat} (_hα : 1 ≤ α) (hβ : 2 ≤ β) :
    OrientsZero α β := by
  intro b s
  simp [recursorEval]
  have hle : b + 2 ≤ α * s + b + β := by omega
  omega

/-- Both free rules are oriented throughout the parameter region. -/
theorem orientsBoth_of_region
    {α β : Nat} (hα : 1 ≤ α) (hβ : 2 ≤ β) :
    OrientsBoth α β :=
  ⟨orientsZero_of_region hα hβ, orientsSuccessor_of_region hα hβ⟩

/-- Uniform successor orientation forces a positive step coefficient. -/
theorem orientsSuccessor_implies_alpha
    {α β : Nat} (h : OrientsSuccessor α β) : 1 ≤ α := by
  by_contra hα
  have hα0 : α = 0 := by omega
  have hs := h 0 β 0
  simp [recursorEval, successorEval, wrapperEval, hα0] at hs
  omega

/-- Uniform successor orientation forces recursor bias at least two. -/
theorem orientsSuccessor_implies_beta
    {α β : Nat} (h : OrientsSuccessor α β) : 2 ≤ β := by
  have hs := h 0 0 0
  simp [recursorEval, successorEval, wrapperEval] at hs
  omega

/-- The coupled polynomial parameter region is necessary and sufficient for
uniform successor orientation. -/
theorem orientsSuccessor_iff_region (α β : Nat) :
    OrientsSuccessor α β ↔ 1 ≤ α ∧ 2 ≤ β := by
  constructor
  · intro h
    exact ⟨orientsSuccessor_implies_alpha h, orientsSuccessor_implies_beta h⟩
  · rintro ⟨hα, hβ⟩
    exact orientsSuccessor_of_region hα hβ

/-- The same region is necessary and sufficient for orienting both free rules. -/
theorem orientsBoth_iff_region (α β : Nat) :
    OrientsBoth α β ↔ 1 ≤ α ∧ 2 ≤ β := by
  constructor
  · intro h
    exact (orientsSuccessor_iff_region α β).1 h.2
  · rintro ⟨hα, hβ⟩
    exact orientsBoth_of_region hα hβ

/-- The recursor interpretation is strictly increasing in its base argument. -/
theorem recursor_strict_base (α β b s n : Nat) :
    recursorEval α β b s n < recursorEval α β (b + 1) s n := by
  simp [recursorEval]

/-- A positive step coefficient makes the recursor interpretation strictly
increasing in the step argument. -/
theorem recursor_strict_step
    {α : Nat} (hα : 1 ≤ α) (β b s n : Nat) :
    recursorEval α β b s n < recursorEval α β b (s + 1) n := by
  have hpos : 0 < (n + 1) * α := Nat.mul_pos (by omega) (by omega)
  have heq :
      recursorEval α β b (s + 1) n =
        recursorEval α β b s n + (n + 1) * α := by
    simp [recursorEval]
    ring
  rw [heq]
  omega

/-- Positive recursor bias makes the interpretation strictly increasing in the
counter argument. -/
theorem recursor_strict_counter
    {β : Nat} (hβ : 1 ≤ β) (α b s n : Nat) :
    recursorEval α β b s n < recursorEval α β b s (n + 1) := by
  have hinner : 0 < α * s + b + β := by omega
  have heq :
      recursorEval α β b s (n + 1) =
        recursorEval α β b s n + (α * s + b + β) := by
    simp [recursorEval]
    ring
  rw [heq]
  omega

/-- The wrapper is strictly increasing in its left argument. -/
theorem wrapper_strict_left (s y : Nat) :
    wrapperEval s y < wrapperEval (s + 1) y := by
  simp [wrapperEval]

/-- The wrapper is strictly increasing in its right argument. -/
theorem wrapper_strict_right (s y : Nat) :
    wrapperEval s y < wrapperEval s (y + 1) := by
  simp [wrapperEval]

/-- Repeating the same wrapper `r` times adds `r * (s+1)`. -/
def wrapperIterEval : Nat → Nat → Nat → Nat
  | 0, _, y => y
  | r + 1, s, y => wrapperEval s (wrapperIterEval r s y)

/-- Closed form for repeated wrapper cost. -/
theorem wrapperIterEval_eq (r s y : Nat) :
    wrapperIterEval r s y = y + r * (s + 1) := by
  induction r with
  | zero => simp [wrapperIterEval]
  | succ r ih =>
      simp [wrapperIterEval, wrapperEval, ih]
      ring

/-- Parameter conditions for an `r`-wrapper successor target. -/
theorem nested_wrapper_successor_orients
    {α β r : Nat} (hα : r ≤ α) (hβ : r + 1 ≤ β) :
    ∀ b s n,
      wrapperIterEval r s (recursorEval α β b s n) <
        recursorEval α β b s (successorEval n) := by
  intro b s n
  obtain ⟨a, ha⟩ := Nat.exists_eq_add_of_le hα
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hβ
  subst α
  subst β
  rw [wrapperIterEval_eq]
  have heq :
      recursorEval (r + a) (r + 1 + d) b s (successorEval n) =
        recursorEval (r + a) (r + 1 + d) b s n + r * (s + 1) +
          (a * s + b + d + 1) := by
    simp [recursorEval, successorEval]
    ring
  rw [heq]
  omega

/-- The one-wrapper construction used in the main paper is the `r=1` case. -/
theorem main_polynomial_construction : OrientsBoth 1 2 := by
  exact (orientsBoth_iff_region 1 2).2 (by omega)


/-- The `r`-wrapper successor rule is oriented over all natural valuations exactly when
`α ≥ r` and `β ≥ r + 1`. Necessity uses the zero valuation for `β` and the payload
`s = β + 1` for `α`. -/
theorem nested_wrapper_successor_orients_iff (α β r : Nat) :
    (∀ b s n, wrapperIterEval r s (recursorEval α β b s n) <
        recursorEval α β b s (successorEval n)) ↔ r ≤ α ∧ r + 1 ≤ β := by
  constructor
  · intro h
    have h0 := h 0 0 0
    rw [wrapperIterEval_eq] at h0
    have e1 : recursorEval α β 0 0 0 = β := by
      unfold recursorEval
      ring
    have e2 : recursorEval α β 0 0 (successorEval 0) = 2 * β := by
      unfold recursorEval successorEval
      ring
    rw [e1, e2] at h0
    have hβ : r + 1 ≤ β := by omega
    refine ⟨?_, hβ⟩
    by_contra hα
    have hα' : α + 1 ≤ r := by omega
    have hs := h 0 (β + 1) 0
    rw [wrapperIterEval_eq] at hs
    have e3 : recursorEval α β 0 (β + 1) 0 = α * (β + 1) + β := by
      unfold recursorEval
      ring
    have e4 : recursorEval α β 0 (β + 1) (successorEval 0) = 2 * (α * (β + 1) + β) := by
      unfold recursorEval successorEval
      ring
    rw [e3, e4] at hs
    have hr : (α + 1) * (β + 1 + 1) ≤ r * (β + 1 + 1) := Nat.mul_le_mul_right _ hα'
    nlinarith
  · rintro ⟨hα, hβ⟩
    exact nested_wrapper_successor_orients hα hβ

end OperatorKO7.Methods.OrientationClosure.PolynomialRegion
