import OperatorKO7.Meta.BoundaryObserver.BoundarySingularity
import OperatorKO7.Meta.BoundaryObserver.FourTestTables

set_option autoImplicit false

/-!
# Fair-label information bound

Proof graph: Audit/ledgers/boundary-theorem/BOUNDARY-THEOREM-MATH-COMPLETION-PROOF-GRAPH.md, N4.
The fair binary label has at most half the triangular discrimination in bits.
Distinct deterministic outputs attain equality.
-/

namespace OperatorKO7.Meta.BoundaryObserver.FairReadingBound

open scoped BigOperators

/-- The entropy increase of a fair mixture is at most half its discrimination term. -/
private theorem fair_entropy_gap_point_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ProtocolResolution.entropyTerm ((a + b) / 2) -
        (ProtocolResolution.entropyTerm a + ProtocolResolution.entropyTerm b) / 2 ≤
      ((a - b) ^ 2 / (a + b)) / 2 := by
  rcases (add_nonneg ha hb).eq_or_lt with hs0 | hs
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    simp [ha0, hb0, ProtocolResolution.entropyTerm_zero]
  · have hsne : a + b ≠ 0 := ne_of_gt hs
    have ha_repr : a = (a + b) * (a / (a + b)) := by
      field_simp [hsne]
    have hb_repr : b = (a + b) * (1 - a / (a + b)) := by
      field_simp [hsne]
    have hnegA : Real.negMulLog a =
        (a / (a + b)) * Real.negMulLog (a + b) +
          (a + b) * Real.negMulLog (a / (a + b)) := by
      calc
        Real.negMulLog a = Real.negMulLog ((a + b) * (a / (a + b))) :=
          congrArg _ ha_repr
        _ = _ := Real.negMulLog_mul _ _
    have hnegB : Real.negMulLog b =
        (1 - a / (a + b)) * Real.negMulLog (a + b) +
          (a + b) * Real.negMulLog (1 - a / (a + b)) := by
      calc
        Real.negMulLog b = Real.negMulLog ((a + b) * (1 - a / (a + b))) :=
          congrArg _ hb_repr
        _ = _ := Real.negMulLog_mul _ _
    have hnegM : Real.negMulLog ((a + b) / 2) =
        (1 / 2 : ℝ) * Real.negMulLog (a + b) + (a + b) * (Real.log 2 / 2) := by
      have hm : (a + b) / 2 = (a + b) * (1 / 2 : ℝ) := by ring
      rw [hm, Real.negMulLog_mul, BitDivision.negMulLog_half]
    have hgap :
        ProtocolResolution.entropyTerm ((a + b) / 2) -
            (ProtocolResolution.entropyTerm a + ProtocolResolution.entropyTerm b) / 2 =
          ((a + b) / 2) *
            (1 - Real.binEntropy (a / (a + b)) / Real.log 2) := by
      simp only [ProtocolResolution.entropyTerm]
      rw [hnegM, hnegA, hnegB, Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
      have hlog : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
      field_simp [hlog, hsne]; ring
    have ht : |(a - b) / (a + b)| ≤ (1 : ℝ) := by
      rw [abs_le]
      constructor
      · apply (le_div_iff₀ hs).mpr
        linarith
      · apply (div_le_iff₀ hs).mpr
        linarith
    have hposterior : (1 + (a - b) / (a + b)) / 2 = a / (a + b) := by
      field_simp [hsne]; ring
    have hbnd := FourTestTables.one_sub_binEntropy_le_sq ((a - b) / (a + b)) ht
    rw [hposterior] at hbnd
    calc
      ProtocolResolution.entropyTerm ((a + b) / 2) -
          (ProtocolResolution.entropyTerm a + ProtocolResolution.entropyTerm b) / 2 =
        ((a + b) / 2) *
          (1 - Real.binEntropy (a / (a + b)) / Real.log 2) := hgap
      _ ≤ ((a + b) / 2) * ((a - b) / (a + b)) ^ 2 :=
        mul_le_mul_of_nonneg_left hbnd (by linarith)
      _ = ((a - b) ^ 2 / (a + b)) / 2 := by
        field_simp [hsne]; ring

/-- A normalized fair binary label carries at most half the triangular discrimination in bits. -/
theorem fair_information_le_half_discrimination {Y : Type} [Fintype Y] (K : Bool → Y → ℝ)
    (hK0 : ∀ b y, 0 ≤ K b y) (hK1 : ∀ b, ∑ y, K b y = 1) :
    ProtocolResolution.jointMI
        (fun by_ : Bool × Y => ProtocolResolution.binaryPrior (1 / 2) by_.1 * K by_.1 by_.2) ≤
      BoundarySingularity.discrimination (K true) (K false) / 2 := by
  have hmix : (fun y => ∑ b, ProtocolResolution.binaryPrior (1 / 2) b * K b y) =
      (fun y => (K true y + K false y) / 2) := by
    funext y
    simp [ProtocolResolution.binaryPrior]
    ring
  calc
    ProtocolResolution.jointMI
        (fun by_ : Bool × Y => ProtocolResolution.binaryPrior (1 / 2) by_.1 *
          K by_.1 by_.2) =
      ProtocolResolution.entropy (fun y => (K true y + K false y) / 2) -
        ((1 / 2 : ℝ) * ProtocolResolution.entropy (K true) +
          (1 / 2 : ℝ) * ProtocolResolution.entropy (K false)) := by
            rw [ProtocolResolution.jointMI_kernel
              (ProtocolResolution.binaryPrior (1 / 2)) K hK1, hmix, Fintype.sum_bool]
            dsimp [ProtocolResolution.binaryPrior]
            ring
    _ = ∑ y, (ProtocolResolution.entropyTerm ((K true y + K false y) / 2) -
          (ProtocolResolution.entropyTerm (K true y) +
            ProtocolResolution.entropyTerm (K false y)) / 2) := by
            rw [ProtocolResolution.entropy_eq_sum, ProtocolResolution.entropy_eq_sum,
              ProtocolResolution.entropy_eq_sum, Finset.mul_sum, Finset.mul_sum,
              ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro y _
            ring
    _ ≤ ∑ y, (((K true y - K false y) ^ 2 / (K true y + K false y)) / 2) := by
            apply Finset.sum_le_sum
            intro y _
            exact fair_entropy_gap_point_le _ _ (hK0 true y) (hK0 false y)
    _ = BoundarySingularity.discrimination (K true) (K false) / 2 := by
            simp only [BoundarySingularity.discrimination, Finset.sum_div]

/-- Two distinct point masses attain one bit of information at discrimination two. -/
theorem fair_bound_attained_split {Y : Type} [Fintype Y] [DecidableEq Y] (y₀ y₁ : Y)
    (hne : y₀ ≠ y₁) :
    ProtocolResolution.jointMI (fun by_ : Bool × Y =>
        ProtocolResolution.binaryPrior (1 / 2) by_.1 *
          (if by_.2 = (if by_.1 then y₀ else y₁) then 1 else 0)) = 1 ∧
      BoundarySingularity.discrimination (fun y => if y = y₀ then (1 : ℝ) else 0)
        (fun y => if y = y₁ then (1 : ℝ) else 0) = 2 := by
  let K : Bool → Y → ℝ := fun b y => if y = (if b then y₀ else y₁) then 1 else 0
  have hK1 : ∀ b, ∑ y, K b y = 1 := by
    intro b
    simp [K]
  have hrow : ∀ b, ProtocolResolution.entropy (K b) = 0 := by
    intro b
    rw [ProtocolResolution.entropy_eq_sum]
    apply Finset.sum_eq_zero
    intro y _
    change ProtocolResolution.entropyTerm
      (if y = (if b then y₀ else y₁) then (1 : ℝ) else 0) = 0
    split_ifs <;> simp [ProtocolResolution.entropyTerm]
  have hhalf : ProtocolResolution.entropyTerm (1 / 2 : ℝ) = 1 / 2 := by
    have hlog : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
    change Real.negMulLog (1 / 2 : ℝ) / Real.log 2 = 1 / 2
    rw [BitDivision.negMulLog_half]
    field_simp [hlog]; ring_nf
  have hmix :
      (fun y => ∑ b, ProtocolResolution.binaryPrior (1 / 2) b * K b y) =
        (fun y => (if y = y₀ then (1 / 2 : ℝ) else 0) +
          (if y = y₁ then (1 / 2 : ℝ) else 0)) := by
    funext y
    simp [K, ProtocolResolution.binaryPrior]
    ring_nf
  have hout :
      ProtocolResolution.entropy (fun y : Y =>
        (if y = y₀ then (1 / 2 : ℝ) else 0) +
        (if y = y₁ then (1 / 2 : ℝ) else 0)) = 1 := by
    rw [ProtocolResolution.entropy_eq_sum]
    have hterm (y : Y) :
        ProtocolResolution.entropyTerm
            ((if y = y₀ then (1 / 2 : ℝ) else 0) +
              (if y = y₁ then (1 / 2 : ℝ) else 0)) =
          (if y = y₀ then (1 / 2 : ℝ) else 0) +
          (if y = y₁ then (1 / 2 : ℝ) else 0) := by
      by_cases h0 : y = y₀
      · have h1 : y ≠ y₁ := by
          intro hy1
          exact hne (h0.symm.trans hy1)
        simp only [if_pos h0, if_neg h1, add_zero]
        exact hhalf
      · by_cases h1 : y = y₁
        · simp only [if_neg h0, if_pos h1, zero_add]
          exact hhalf
        · simp only [if_neg h0, if_neg h1, zero_add]
          exact ProtocolResolution.entropyTerm_zero
    simp only [hterm, Finset.sum_add_distrib]
    simp; norm_num
  constructor
  · change ProtocolResolution.jointMI
        (fun by_ : Bool × Y => ProtocolResolution.binaryPrior (1 / 2) by_.1 *
          K by_.1 by_.2) = 1
    rw [ProtocolResolution.jointMI_kernel
      (ProtocolResolution.binaryPrior (1 / 2)) K hK1, hmix, hout]
    simp [hrow]
  · change BoundarySingularity.discrimination (K true) (K false) = 2
    unfold BoundarySingularity.discrimination
    change (∑ y, ((if y = y₀ then (1 : ℝ) else 0) -
      (if y = y₁ then (1 : ℝ) else 0)) ^ 2 /
      ((if y = y₀ then (1 : ℝ) else 0) +
        (if y = y₁ then (1 : ℝ) else 0))) = 2
    have hterm (y : Y) :
        ((if y = y₀ then (1 : ℝ) else 0) -
          (if y = y₁ then (1 : ℝ) else 0)) ^ 2 /
          ((if y = y₀ then (1 : ℝ) else 0) +
            (if y = y₁ then (1 : ℝ) else 0)) =
          (if y = y₀ then (1 : ℝ) else 0) +
            (if y = y₁ then (1 : ℝ) else 0) := by
      by_cases h0 : y = y₀
      · have h1 : y ≠ y₁ := by
          intro hy1
          exact hne (h0.symm.trans hy1)
        simp only [if_pos h0, if_neg h1]
        norm_num
      · by_cases h1 : y = y₁
        · simp only [if_neg h0, if_pos h1]
          norm_num
        · simp only [if_neg h0, if_neg h1]
          norm_num
    simp only [hterm, Finset.sum_add_distrib]
    norm_num

/-! ## The lower bound in Pinsker form

Proof graph: `Audit/ledgers/boundary-theorem/WAVE6-PROOF-GRAPH.md`, node N28. The sentence after
`prop:one-reading` bounds the information of one fair reading from below by Pinsker's inequality.
The binary Pinsker inequality `log 2 - h((1 + t) / 2) ≥ t² / 2` gives the stronger bound
`I(B;Y) ≥ Δ / (4 ln 2)`, which implies the total-variation form and the squared-discrimination form,
so one reading is informative exactly when its discrimination is positive. -/

/-- `log (1 + t) - log (1 - t)` is at least `2 t` on `[0, 1)`: the first term of its series. -/
theorem two_mul_le_log_sub_log (t : ℝ) (h0 : 0 ≤ t) (h1 : t < 1) :
    2 * t ≤ Real.log (1 + t) - Real.log (1 - t) := by
  have habs : |t| < 1 := by
    rw [abs_lt]
    constructor <;> linarith
  have hs := Real.hasSum_log_sub_log_of_abs_lt_one habs
  have hle := sum_le_hasSum (Finset.range 1) (fun i _ => by positivity) hs
  simpa using hle

/-- The gap of the binary Pinsker inequality, written with `negMulLog` so that it is continuous
on the whole line. -/
noncomputable def pinskerGap (t : ℝ) : ℝ :=
  -(Real.negMulLog (1 + t) + Real.negMulLog (1 - t)) / 2 - t ^ 2 / 2

theorem pinskerGap_hasDerivAt (t : ℝ) (h0 : -1 < t) (h1 : t < 1) :
    HasDerivAt pinskerGap ((Real.log (1 + t) - Real.log (1 - t)) / 2 - t) t := by
  have hA : HasDerivAt (fun x => Real.negMulLog (1 + x)) ((-Real.log (1 + t) - 1) * 1) t :=
    (Real.hasDerivAt_negMulLog (ne_of_gt (by linarith : (0 : ℝ) < 1 + t))).comp t
      ((hasDerivAt_id' t).const_add 1)
  have hB : HasDerivAt (fun x => Real.negMulLog (1 - x)) ((-Real.log (1 - t) - 1) * (-1)) t :=
    (Real.hasDerivAt_negMulLog (ne_of_gt (by linarith : (0 : ℝ) < 1 - t))).comp t
      ((hasDerivAt_id' t).const_sub 1)
  have hC : HasDerivAt (fun x : ℝ => x ^ 2 / 2) t t := by
    convert (hasDerivAt_pow 2 t).div_const 2 using 1
    norm_num
  have h := ((hA.add hB).neg.div_const 2).sub hC
  unfold pinskerGap
  convert h using 1
  ring

theorem pinskerGap_continuous : Continuous pinskerGap := by
  have h1 : Continuous fun x : ℝ => Real.negMulLog (1 + x) :=
    Real.continuous_negMulLog.comp (continuous_add_left 1)
  have h2 : Continuous fun x : ℝ => Real.negMulLog (1 - x) :=
    Real.continuous_negMulLog.comp (continuous_sub_left 1)
  exact ((h1.add h2).neg.div_const 2).sub ((continuous_pow 2).div_const 2)

/-- The gap increases on `[0, 1]`, since its derivative is `artanh t - t ≥ 0` inside. -/
theorem pinskerGap_monotoneOn : MonotoneOn pinskerGap (Set.Icc 0 1) := by
  refine monotoneOn_of_deriv_nonneg (convex_Icc 0 1) pinskerGap_continuous.continuousOn ?_ ?_
  · rw [interior_Icc]
    intro t ht
    exact (pinskerGap_hasDerivAt t (by linarith [ht.1]) ht.2).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]
    intro t ht
    rw [(pinskerGap_hasDerivAt t (by linarith [ht.1]) ht.2).deriv]
    have := two_mul_le_log_sub_log t ht.1.le ht.2
    linarith

/-- The binary entropy deficit at `(1 + s) / 2`, in nats, in terms of `negMulLog`. -/
theorem log_two_sub_binEntropy_eq (s : ℝ) :
    Real.log 2 - Real.binEntropy ((1 + s) / 2) =
      -(Real.negMulLog (1 + s) + Real.negMulLog (1 - s)) / 2 := by
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  have e1 : (1 + s) / 2 = (1 + s) * (1 / 2) := by ring
  have e2 : 1 - (1 + s) / 2 = (1 - s) * (1 / 2) := by ring
  rw [e2, e1, Real.negMulLog_mul, Real.negMulLog_mul, BitDivision.negMulLog_half]
  ring

/-- The binary Pinsker inequality: `log 2 - h((1 + t) / 2) ≥ t² / 2` in nats for `|t| ≤ 1`. -/
theorem sq_div_two_le_log_two_sub_binEntropy (t : ℝ) (ht : |t| ≤ 1) :
    t ^ 2 / 2 ≤ Real.log 2 - Real.binEntropy ((1 + t) / 2) := by
  rw [log_two_sub_binEntropy_eq]
  have key : ∀ s ∈ Set.Icc (0 : ℝ) 1, 0 ≤ pinskerGap s := by
    intro s hs
    have h0 : pinskerGap 0 = 0 := by simp [pinskerGap]
    have := pinskerGap_monotoneOn (Set.left_mem_Icc.mpr zero_le_one) hs hs.1
    linarith
  rcases le_total 0 t with h | h
  · have := key t ⟨h, (abs_le.mp ht).2⟩
    unfold pinskerGap at this
    linarith
  · have := key (-t) ⟨by linarith, by linarith [(abs_le.mp ht).1]⟩
    unfold pinskerGap at this
    have e1 : (1 : ℝ) + -t = 1 - t := by ring
    have e2 : (1 : ℝ) - -t = 1 + t := by ring
    rw [e1, e2, neg_sq] at this
    linarith

/-- The entropy increase of a fair mixture at a positive total, as a weighted binary deficit. -/
private theorem fair_entropy_gap_point_eq (a b : ℝ) (hs : 0 < a + b) :
    ProtocolResolution.entropyTerm ((a + b) / 2) -
        (ProtocolResolution.entropyTerm a + ProtocolResolution.entropyTerm b) / 2 =
      ((a + b) / 2) * (1 - Real.binEntropy (a / (a + b)) / Real.log 2) := by
  have hsne : a + b ≠ 0 := ne_of_gt hs
  have ha_repr : a = (a + b) * (a / (a + b)) := by
    field_simp [hsne]
  have hb_repr : b = (a + b) * (1 - a / (a + b)) := by
    field_simp [hsne]
  have hnegA : Real.negMulLog a =
      (a / (a + b)) * Real.negMulLog (a + b) +
        (a + b) * Real.negMulLog (a / (a + b)) := by
    calc
      Real.negMulLog a = Real.negMulLog ((a + b) * (a / (a + b))) :=
        congrArg _ ha_repr
      _ = _ := Real.negMulLog_mul _ _
  have hnegB : Real.negMulLog b =
      (1 - a / (a + b)) * Real.negMulLog (a + b) +
        (a + b) * Real.negMulLog (1 - a / (a + b)) := by
    calc
      Real.negMulLog b = Real.negMulLog ((a + b) * (1 - a / (a + b))) :=
        congrArg _ hb_repr
      _ = _ := Real.negMulLog_mul _ _
  have hnegM : Real.negMulLog ((a + b) / 2) =
      (1 / 2 : ℝ) * Real.negMulLog (a + b) + (a + b) * (Real.log 2 / 2) := by
    have hm : (a + b) / 2 = (a + b) * (1 / 2 : ℝ) := by ring
    rw [hm, Real.negMulLog_mul, BitDivision.negMulLog_half]
  simp only [ProtocolResolution.entropyTerm]
  rw [hnegM, hnegA, hnegB, Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  field_simp [hlog, hsne]; ring

/-- The entropy increase of a fair mixture is at least its discrimination term over `4 ln 2`. -/
private theorem fair_entropy_gap_point_ge (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ((a - b) ^ 2 / (a + b)) / (4 * Real.log 2) ≤
      ProtocolResolution.entropyTerm ((a + b) / 2) -
        (ProtocolResolution.entropyTerm a + ProtocolResolution.entropyTerm b) / 2 := by
  rcases (add_nonneg ha hb).eq_or_lt with hs0 | hs
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    simp [ha0, hb0, ProtocolResolution.entropyTerm_zero]
  · have hsne : a + b ≠ 0 := ne_of_gt hs
    have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
    have ht : |(a - b) / (a + b)| ≤ (1 : ℝ) := by
      rw [abs_le]
      constructor
      · apply (le_div_iff₀ hs).mpr
        linarith
      · apply (div_le_iff₀ hs).mpr
        linarith
    have hposterior : (1 + (a - b) / (a + b)) / 2 = a / (a + b) := by
      field_simp [hsne]; ring
    have hp := sq_div_two_le_log_two_sub_binEntropy ((a - b) / (a + b)) ht
    rw [hposterior] at hp
    rw [fair_entropy_gap_point_eq a b hs]
    have hdef : 1 - Real.binEntropy (a / (a + b)) / Real.log 2 =
        (Real.log 2 - Real.binEntropy (a / (a + b))) / Real.log 2 := by
      field_simp [hlog.ne']
    rw [hdef]
    calc ((a - b) ^ 2 / (a + b)) / (4 * Real.log 2)
        = ((a + b) / 2) * ((((a - b) / (a + b)) ^ 2 / 2) / Real.log 2) := by
          field_simp [hsne, hlog.ne']
          ring
      _ ≤ ((a + b) / 2) * ((Real.log 2 - Real.binEntropy (a / (a + b))) / Real.log 2) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hp hlog.le) (by linarith)

/-- The information of a fair binary label as the sum of the entropy increases of its outputs. -/
private theorem fair_information_eq_sum_gap {Y : Type} [Fintype Y] (K : Bool → Y → ℝ)
    (hK1 : ∀ b, ∑ y, K b y = 1) :
    ProtocolResolution.jointMI
        (fun by_ : Bool × Y => ProtocolResolution.binaryPrior (1 / 2) by_.1 * K by_.1 by_.2) =
      ∑ y, (ProtocolResolution.entropyTerm ((K true y + K false y) / 2) -
        (ProtocolResolution.entropyTerm (K true y) +
          ProtocolResolution.entropyTerm (K false y)) / 2) := by
  have hmix : (fun y => ∑ b, ProtocolResolution.binaryPrior (1 / 2) b * K b y) =
      (fun y => (K true y + K false y) / 2) := by
    funext y
    simp [ProtocolResolution.binaryPrior]
    ring
  calc
    ProtocolResolution.jointMI
        (fun by_ : Bool × Y => ProtocolResolution.binaryPrior (1 / 2) by_.1 *
          K by_.1 by_.2) =
      ProtocolResolution.entropy (fun y => (K true y + K false y) / 2) -
        ((1 / 2 : ℝ) * ProtocolResolution.entropy (K true) +
          (1 / 2 : ℝ) * ProtocolResolution.entropy (K false)) := by
            rw [ProtocolResolution.jointMI_kernel
              (ProtocolResolution.binaryPrior (1 / 2)) K hK1, hmix, Fintype.sum_bool]
            dsimp [ProtocolResolution.binaryPrior]
            ring
    _ = ∑ y, (ProtocolResolution.entropyTerm ((K true y + K false y) / 2) -
          (ProtocolResolution.entropyTerm (K true y) +
            ProtocolResolution.entropyTerm (K false y)) / 2) := by
            rw [ProtocolResolution.entropy_eq_sum, ProtocolResolution.entropy_eq_sum,
              ProtocolResolution.entropy_eq_sum, Finset.mul_sum, Finset.mul_sum,
              ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro y _
            ring

/-- A normalized fair binary label carries at least `Δ / (4 ln 2)` bits. -/
theorem fair_information_ge_quarter_discrimination {Y : Type} [Fintype Y] (K : Bool → Y → ℝ)
    (hK0 : ∀ b y, 0 ≤ K b y) (hK1 : ∀ b, ∑ y, K b y = 1) :
    BoundarySingularity.discrimination (K true) (K false) / (4 * Real.log 2) ≤
      ProtocolResolution.jointMI
        (fun by_ : Bool × Y => ProtocolResolution.binaryPrior (1 / 2) by_.1 * K by_.1 by_.2) := by
  rw [fair_information_eq_sum_gap K hK1]
  calc
    BoundarySingularity.discrimination (K true) (K false) / (4 * Real.log 2) =
        ∑ y, (((K true y - K false y) ^ 2 / (K true y + K false y)) / (4 * Real.log 2)) := by
          simp only [BoundarySingularity.discrimination, Finset.sum_div]
    _ ≤ _ := Finset.sum_le_sum (fun y _ =>
          fair_entropy_gap_point_ge _ _ (hK0 true y) (hK0 false y))

/-- The total variation distance of two weight functions on a finite alphabet. -/
noncomputable def totalVariation {Y : Type} [Fintype Y] (P Q : Y → ℝ) : ℝ :=
  (∑ y, |P y - Q y|) / 2

/-- Half the discrimination is at most the total variation distance. -/
theorem half_discrimination_le_totalVariation {Y : Type} [Fintype Y] (P Q : Y → ℝ)
    (hP0 : ∀ y, 0 ≤ P y) (hQ0 : ∀ y, 0 ≤ Q y) :
    BoundarySingularity.discrimination P Q / 2 ≤ totalVariation P Q := by
  have h := BoundarySingularity.discrimination_le_sum_abs P Q hP0 hQ0
  unfold totalVariation
  linarith

/-- For two laws, the squared total variation distance is at most half the discrimination, by the
Cauchy-Schwarz inequality with the weights `P y + Q y` of total two. -/
theorem totalVariation_sq_le_half_discrimination {Y : Type} [Fintype Y] (P Q : Y → ℝ)
    (hP0 : ∀ y, 0 ≤ P y) (hQ0 : ∀ y, 0 ≤ Q y) (hP1 : ∑ y, P y = 1) (hQ1 : ∑ y, Q y = 1) :
    totalVariation P Q ^ 2 ≤ BoundarySingularity.discrimination P Q / 2 := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun y => |P y - Q y| / Real.sqrt (P y + Q y)) (fun y => Real.sqrt (P y + Q y))
  have hfg : ∀ y, |P y - Q y| / Real.sqrt (P y + Q y) * Real.sqrt (P y + Q y) = |P y - Q y| := by
    intro y
    rcases (add_nonneg (hP0 y) (hQ0 y)).eq_or_lt with h0 | hpos
    · have hp : P y = 0 := by linarith [hP0 y, hQ0 y]
      have hq : Q y = 0 := by linarith [hP0 y, hQ0 y]
      simp [hp, hq]
    · exact div_mul_cancel₀ _ (Real.sqrt_pos.mpr hpos).ne'
  have hf2 : ∀ y, (|P y - Q y| / Real.sqrt (P y + Q y)) ^ 2 = (P y - Q y) ^ 2 / (P y + Q y) := by
    intro y
    rw [div_pow, sq_abs, Real.sq_sqrt (add_nonneg (hP0 y) (hQ0 y))]
  have hg2 : ∀ y, Real.sqrt (P y + Q y) ^ 2 = P y + Q y :=
    fun y => Real.sq_sqrt (add_nonneg (hP0 y) (hQ0 y))
  simp only [hfg, hf2, hg2] at hcs
  have htot : ∑ y, (P y + Q y) = 2 := by
    rw [Finset.sum_add_distrib, hP1, hQ1]
    norm_num
  rw [htot] at hcs
  have hsq : totalVariation P Q ^ 2 = (∑ y, |P y - Q y|) ^ 2 / 4 := by
    unfold totalVariation
    ring
  rw [hsq]
  change (∑ y, |P y - Q y|) ^ 2 / 4 ≤ (∑ y, (P y - Q y) ^ 2 / (P y + Q y)) / 2
  linarith

/-- Pinsker's bound for one reading of a fair label: at least `TV² / (2 ln 2)` bits. -/
theorem fair_information_ge_totalVariation_sq {Y : Type} [Fintype Y] (K : Bool → Y → ℝ)
    (hK0 : ∀ b y, 0 ≤ K b y) (hK1 : ∀ b, ∑ y, K b y = 1) :
    totalVariation (K true) (K false) ^ 2 / (2 * Real.log 2) ≤
      ProtocolResolution.jointMI
        (fun by_ : Bool × Y => ProtocolResolution.binaryPrior (1 / 2) by_.1 * K by_.1 by_.2) := by
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have h1 := fair_information_ge_quarter_discrimination K hK0 hK1
  have h2 := totalVariation_sq_le_half_discrimination (K true) (K false) (hK0 true) (hK0 false)
    (hK1 true) (hK1 false)
  calc
    totalVariation (K true) (K false) ^ 2 / (2 * Real.log 2) ≤
        (BoundarySingularity.discrimination (K true) (K false) / 2) / (2 * Real.log 2) :=
      div_le_div_of_nonneg_right h2 (by positivity)
    _ = BoundarySingularity.discrimination (K true) (K false) / (4 * Real.log 2) := by
      ring
    _ ≤ _ := h1

/-- The squared total variation bound is at least the squared-discrimination bound. -/
theorem discrimination_sq_le_totalVariation_sq {Y : Type} [Fintype Y] (P Q : Y → ℝ)
    (hP0 : ∀ y, 0 ≤ P y) (hQ0 : ∀ y, 0 ≤ Q y) :
    BoundarySingularity.discrimination P Q ^ 2 / (8 * Real.log 2) ≤
      totalVariation P Q ^ 2 / (2 * Real.log 2) := by
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have h := half_discrimination_le_totalVariation P Q hP0 hQ0
  have hd0 := BoundarySingularity.discrimination_nonneg P Q hP0 hQ0
  have hsq : (BoundarySingularity.discrimination P Q / 2) ^ 2 ≤ totalVariation P Q ^ 2 := by
    nlinarith
  calc
    BoundarySingularity.discrimination P Q ^ 2 / (8 * Real.log 2) =
        (BoundarySingularity.discrimination P Q / 2) ^ 2 / (2 * Real.log 2) := by
      ring
    _ ≤ _ := div_le_div_of_nonneg_right hsq (by positivity)

/-- The whole chain of the sentence after `prop:one-reading`, with the proposition's upper bound:
`Δ² / (8 ln 2) ≤ TV² / (2 ln 2) ≤ I(B;Y)`, `Δ / (4 ln 2) ≤ I(B;Y) ≤ Δ / 2`. -/
theorem fair_reading_pinsker {Y : Type} [Fintype Y] (K : Bool → Y → ℝ)
    (hK0 : ∀ b y, 0 ≤ K b y) (hK1 : ∀ b, ∑ y, K b y = 1) :
    BoundarySingularity.discrimination (K true) (K false) ^ 2 / (8 * Real.log 2) ≤
        totalVariation (K true) (K false) ^ 2 / (2 * Real.log 2) ∧
      totalVariation (K true) (K false) ^ 2 / (2 * Real.log 2) ≤
        ProtocolResolution.jointMI
          (fun by_ : Bool × Y => ProtocolResolution.binaryPrior (1 / 2) by_.1 * K by_.1 by_.2) ∧
      BoundarySingularity.discrimination (K true) (K false) / (4 * Real.log 2) ≤
        ProtocolResolution.jointMI
          (fun by_ : Bool × Y => ProtocolResolution.binaryPrior (1 / 2) by_.1 * K by_.1 by_.2) ∧
      ProtocolResolution.jointMI
          (fun by_ : Bool × Y => ProtocolResolution.binaryPrior (1 / 2) by_.1 * K by_.1 by_.2) ≤
        BoundarySingularity.discrimination (K true) (K false) / 2 :=
  ⟨discrimination_sq_le_totalVariation_sq (K true) (K false) (hK0 true) (hK0 false),
    fair_information_ge_totalVariation_sq K hK0 hK1,
    fair_information_ge_quarter_discrimination K hK0 hK1,
    fair_information_le_half_discrimination K hK0 hK1⟩

/-- One reading of a fair label is informative if and only if its discrimination is positive. -/
theorem fair_information_pos_iff {Y : Type} [Fintype Y] (K : Bool → Y → ℝ)
    (hK0 : ∀ b y, 0 ≤ K b y) (hK1 : ∀ b, ∑ y, K b y = 1) :
    0 < ProtocolResolution.jointMI
        (fun by_ : Bool × Y => ProtocolResolution.binaryPrior (1 / 2) by_.1 * K by_.1 by_.2) ↔
      0 < BoundarySingularity.discrimination (K true) (K false) := by
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  constructor
  · intro h
    have := fair_information_le_half_discrimination K hK0 hK1
    linarith
  · intro h
    have h1 := fair_information_ge_quarter_discrimination K hK0 hK1
    have h2 : 0 < BoundarySingularity.discrimination (K true) (K false) / (4 * Real.log 2) := by
      positivity
    linarith

end OperatorKO7.Meta.BoundaryObserver.FairReadingBound

