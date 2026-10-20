import OperatorKO7.Meta.UUET.FiniteAmplitudeEntanglement

set_option autoImplicit false

/-! The product of the two branch weights of a law on a merged pair, its invariance under the
transposition of the branches, the observer-conditioned law of a pair and its residual
entanglement. -/

noncomputable section

namespace OperatorKO7.Meta.UUET.TwoBranchWeight

/-- The transposition exchanges the two branch weights. -/
def swap (w : TwoBranchWeight) : TwoBranchWeight where
  p := w.q
  nonneg := w.q_nonneg
  le_one := w.q_le_one

end OperatorKO7.Meta.UUET.TwoBranchWeight

namespace OperatorKO7.Meta.BoundaryObserver.EntangledMergedPair

open OperatorKO7.Meta.UUET

/-- The product of the weights is fixed by the transposition. -/
theorem amplitudeEntanglement_swap (w : TwoBranchWeight) :
    amplitudeEntanglement w.swap = amplitudeEntanglement w := by
  unfold amplitudeEntanglement TwoBranchWeight.swap TwoBranchWeight.q
  ring

/-- The product is one quarter exactly at the fair law. -/
theorem amplitudeEntanglement_eq_quarter_iff (w : TwoBranchWeight) :
    amplitudeEntanglement w = 1 / 4 ↔ w.p = 1 / 2 := by
  change w.p * (1 - w.p) = 1 / 4 ↔ w.p = 1 / 2
  constructor
  · intro h
    have hs : (w.p - 1 / 2) * (w.p - 1 / 2) = 0 := by nlinarith [h]
    rcases mul_eq_zero.mp hs with hp | hp <;> linarith
  · intro h
    rw [h]
    norm_num

end OperatorKO7.Meta.BoundaryObserver.EntangledMergedPair

namespace OperatorKO7.Meta.BoundaryObserver.EntangledMergedPair

open OperatorKO7.Meta.UUET
open scoped BigOperators Classical

/-- A full probability law supported on the displayed pair. -/
structure PairLaw {X : Type} (p : X → ℝ) (x₀ x₁ : X) : Prop where
  nonneg : ∀ x, 0 ≤ p x
  support : ∀ x, x ≠ x₀ → x ≠ x₁ → p x = 0
  total : p x₀ + p x₁ = 1

def pairSupport {X : Type} (x₀ x₁ : X) : Finset X := by
  classical
  exact {x₀, x₁}

/-- The pushforward mass, computed from the actual supported law. -/
def pairRecordMass {X Y : Type} (q : X → Y) (p : X → ℝ)
    (x₀ x₁ : X) (y : Y) : ℝ := by
  classical
  exact ∑ x ∈ pairSupport x₀ x₁, if q x = y then p x else 0

/-- Division by a zero record mass gives the zero conditional law. -/
def pairConditionalLaw {X Y : Type} (q : X → Y) (p : X → ℝ)
    (x₀ x₁ : X) (y : Y) (x : X) : ℝ := by
  classical
  exact (if q x = y then p x else 0) / pairRecordMass q p x₀ x₁ y

/-- Expected conditional weight product over the distinct attained records. -/
def residualEntanglement {X Y : Type} (q : X → Y) (p : X → ℝ)
    (x₀ x₁ : X) : ℝ := by
  classical
  exact ∑ y ∈ (pairSupport x₀ x₁).image q,
    pairRecordMass q p x₀ x₁ y *
      (pairConditionalLaw q p x₀ x₁ y x₀ * pairConditionalLaw q p x₀ x₁ y x₁)

theorem pairRecordMass_nonneg {X Y : Type} (q : X → Y)
    {p : X → ℝ} {x₀ x₁ : X} (hp : PairLaw p x₀ x₁) (y : Y) :
    0 ≤ pairRecordMass q p x₀ x₁ y := by
  classical
  unfold pairRecordMass
  apply Finset.sum_nonneg
  intro x _
  dsimp
  split_ifs
  · exact hp.nonneg x
  · exact le_rfl

theorem pairConditionalLaw_nonneg {X Y : Type} (q : X → Y)
    {p : X → ℝ} {x₀ x₁ : X} (hp : PairLaw p x₀ x₁) (y : Y) (x : X) :
    0 ≤ pairConditionalLaw q p x₀ x₁ y x := by
  classical
  unfold pairConditionalLaw
  apply div_nonneg _ (pairRecordMass_nonneg q hp y)
  split_ifs
  · exact hp.nonneg x
  · exact le_rfl

theorem pairConditionalLaw_zero_mass {X Y : Type} (q : X → Y)
    (p : X → ℝ) (x₀ x₁ : X) (y : Y)
    (hy : pairRecordMass q p x₀ x₁ y = 0) :
    pairConditionalLaw q p x₀ x₁ y = 0 := by
  classical
  funext x
  simp [pairConditionalLaw, hy]

theorem pairConditionalLaw_supported {X Y : Type} (q : X → Y)
    {p : X → ℝ} {x₀ x₁ : X} (hp : PairLaw p x₀ x₁) (y : Y)
    (x : X) (hx₀ : x ≠ x₀) (hx₁ : x ≠ x₁) :
    pairConditionalLaw q p x₀ x₁ y x = 0 := by
  classical
  simp [pairConditionalLaw, hp.support x hx₀ hx₁]

theorem pairConditionalLaw_normalized {X Y : Type} (q : X → Y)
    (p : X → ℝ) (x₀ x₁ : X) (y : Y)
    (hy : 0 < pairRecordMass q p x₀ x₁ y) :
    (∑ x ∈ pairSupport x₀ x₁, pairConditionalLaw q p x₀ x₁ y x) = 1 := by
  classical
  unfold pairConditionalLaw
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt hy)

theorem pairConditionalLaw_pair_total {X Y : Type} (q : X → Y)
    (p : X → ℝ) {x₀ x₁ : X} (h : x₀ ≠ x₁) (y : Y)
    (hy : 0 < pairRecordMass q p x₀ x₁ y) :
    pairConditionalLaw q p x₀ x₁ y x₀ +
      pairConditionalLaw q p x₀ x₁ y x₁ = 1 := by
  classical
  simpa [pairSupport, h] using pairConditionalLaw_normalized q p x₀ x₁ y hy

/-- The actual positive-mass conditional law as the existing branch-weight type. -/
def conditionalBranchWeight {X Y : Type} (q : X → Y)
    (p : X → ℝ) {x₀ x₁ : X} (h : x₀ ≠ x₁)
    (hp : PairLaw p x₀ x₁) (y : Y)
    (hy : 0 < pairRecordMass q p x₀ x₁ y) : TwoBranchWeight where
  p := pairConditionalLaw q p x₀ x₁ y x₀
  nonneg := pairConditionalLaw_nonneg q hp y x₀
  le_one := by
    have ht := pairConditionalLaw_pair_total q p h y hy
    have hn := pairConditionalLaw_nonneg q hp y x₁
    linarith

theorem conditionalBranchWeight_amplitude {X Y : Type} (q : X → Y)
    (p : X → ℝ) {x₀ x₁ : X} (h : x₀ ≠ x₁)
    (hp : PairLaw p x₀ x₁) (y : Y)
    (hy : 0 < pairRecordMass q p x₀ x₁ y) :
    amplitudeEntanglement (conditionalBranchWeight q p h hp y hy) =
      pairConditionalLaw q p x₀ x₁ y x₀ * pairConditionalLaw q p x₀ x₁ y x₁ := by
  have ht := pairConditionalLaw_pair_total q p h y hy
  change pairConditionalLaw q p x₀ x₁ y x₀ *
    (1 - pairConditionalLaw q p x₀ x₁ y x₀) = _
  congr 1
  linarith

theorem pairRecordMass_total {X Y : Type} (q : X → Y)
    {p : X → ℝ} {x₀ x₁ : X} (h : x₀ ≠ x₁) (hp : PairLaw p x₀ x₁) :
    (∑ y ∈ (pairSupport x₀ x₁).image q, pairRecordMass q p x₀ x₁ y) = 1 := by
  classical
  by_cases hq : q x₀ = q x₁
  · simp [pairRecordMass, pairSupport, h, hq, hp.total]
  · simpa [pairRecordMass, pairSupport, h, hq, Ne.symm hq] using hp.total

/-- The observer link is proved from the conditional-law expectation. -/
theorem residualEntanglement_eq {X Y : Type} (q : X → Y) {x₀ x₁ : X}
    (h : x₀ ≠ x₁) (p : X → ℝ) (hp : PairLaw p x₀ x₁) :
    residualEntanglement q p x₀ x₁ =
      if q x₀ = q x₁ then p x₀ * p x₁ else 0 := by
  classical
  by_cases hq : q x₀ = q x₁
  · simp [residualEntanglement, pairConditionalLaw, pairRecordMass,
      pairSupport, h, hq, hp.total]
  · rw [if_neg hq]
    unfold residualEntanglement
    apply Finset.sum_eq_zero
    intro y _
    by_cases h₀ : q x₀ = y
    · have h₁ : q x₁ ≠ y := fun h₁ => hq (h₀.trans h₁.symm)
      simp [pairConditionalLaw, h₁]
    · simp [pairConditionalLaw, h₀]

theorem entangledUnder_iff {X Y : Type} (q : X → Y) {x₀ x₁ : X}
    (h : x₀ ≠ x₁) (p : X → ℝ) (hp : PairLaw p x₀ x₁) :
    0 < residualEntanglement q p x₀ x₁ ↔
      q x₀ = q x₁ ∧ 0 < p x₀ ∧ 0 < p x₁ := by
  classical
  rw [residualEntanglement_eq q h p hp]
  by_cases hq : q x₀ = q x₁
  · simp only [hq, if_true, true_and]
    constructor
    · intro hm
      rcases mul_pos_iff.mp hm with hpos | hneg
      · exact hpos
      · exact False.elim ((not_lt_of_ge (hp.nonneg x₀)) hneg.1)
    · rintro ⟨h₀, h₁⟩
      exact mul_pos h₀ h₁
  · simp [hq]

/-- A zero branch weight leaves no residual entanglement under any record. -/
theorem residualEntanglement_zero_weight {X Y : Type} (q : X → Y)
    {x₀ x₁ : X} (h : x₀ ≠ x₁) (p : X → ℝ) (hp : PairLaw p x₀ x₁)
    (hz : p x₀ = 0 ∨ p x₁ = 0) :
    residualEntanglement q p x₀ x₁ = 0 := by
  classical
  rcases hz with hz | hz <;> simp [residualEntanglement_eq q h p hp, hz]

def fairBoolPairLaw : PairLaw (fun _ : Bool => (1 : ℝ) / 2) false true where
  nonneg := by intro x; norm_num
  support := by
    intro x h₀ h₁
    cases x
    · exact False.elim (h₀ rfl)
    · exact False.elim (h₁ rfl)
  total := by norm_num

theorem fair_merged_residual :
    residualEntanglement (fun _ : Bool => ()) (fun _ => (1 : ℝ) / 2) false true = 1 / 4 := by
  rw [residualEntanglement_eq _ Bool.false_ne_true _ fairBoolPairLaw]
  norm_num

theorem fair_separated_residual :
    residualEntanglement (fun x : Bool => x) (fun _ => (1 : ℝ) / 2) false true = 0 := by
  rw [residualEntanglement_eq _ Bool.false_ne_true _ fairBoolPairLaw]
  norm_num

end OperatorKO7.Meta.BoundaryObserver.EntangledMergedPair
