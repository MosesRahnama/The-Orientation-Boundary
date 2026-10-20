import OperatorKO7.Meta.BoundaryObserver.ResolutionAttainment

set_option autoImplicit false

/-!
# The singularity is sharp for every finite reading

Repeating one reading with rows P and Q of discrimination Δ and decoding by the likelihood ratio
errs with probability at most one half of the Bhattacharyya coefficient Σ √(P Q) to the power N;
the coefficient is at most 1 − Δ/4, so N of order log(1/η)/Δ readings acquire 1 − h₂(η) bits at unit
cost each, while every protocol of readings of discrimination at most Δ pays at least c log 2 over Δ
for c bits. At a split pair of a deterministic observer the coefficient is zero and one reading
resolves the pair; at a merged pair it is one and no protocol acquires anything.
Relation: finite stopped laws of one named protocol. External trust: none.
-/

namespace OperatorKO7.Meta.BoundaryObserver.PairResolution

open scoped BigOperators
open ProtocolResolution BoundarySingularity ResolutionAttainment

variable {Y : Type} [Fintype Y]

/-! ## B1: the repeated reading -/

/-- The two rows of a reading at a pair: P for the label true, Q for the label false. -/
noncomputable def row (P Q : FiniteLaw Y) : Bool → FiniteLaw Y
  | true => P
  | false => Q

/-- N repetitions of one reading with rows P and Q about a fair label, unit cost, stopping at N. -/
noncomputable def repeatProtocol (P Q : FiniteLaw Y) (N : ℕ) : FiniteProtocol Bool Unit Y where
  prior := fairLaw
  policy _ := unitLaw
  observation _ _ z := row P Q z
  stop h := decide (N ≤ h.length)
  cost _ _ := 1
  cost_nonnegative _ _ := zero_le_one

section Repeat
variable (P Q : FiniteLaw Y) (N : ℕ)

/-- The repeated reading is a pair menu of discrimination Δ(P, Q). -/
def repeatProtocol_pairMenu :
    PairMenu (repeatProtocol P Q N) (discrimination P.mass Q.mass) where
  rows _ _ := le_rfl
  reading_cost _ _ := le_rfl

theorem repeatProtocol_stop (h : List (Unit × Y)) :
    (repeatProtocol P Q N).stop h = decide (N ≤ h.length) := rfl

theorem repeatProtocol_stop_false {h : List (Unit × Y)} (hl : h.length < N) :
    (repeatProtocol P Q N).stop h = false := by
  rw [repeatProtocol_stop, decide_eq_false_iff_not]
  exact not_le.mpr hl

/-- The likelihood of the outcomes of a history under the label z. -/
noncomputable def likelihood (z : Bool) (h : List (Unit × Y)) : ℝ :=
  (h.map (fun ay => (row P Q z).mass ay.2)).prod

theorem likelihood_true (h : List (Unit × Y)) :
    likelihood P Q true h = (h.map (fun ay => P.mass ay.2)).prod := rfl

theorem likelihood_false (h : List (Unit × Y)) :
    likelihood P Q false h = (h.map (fun ay => Q.mass ay.2)).prod := rfl

theorem likelihood_nil (z : Bool) : likelihood P Q z [] = 1 := by simp [likelihood]

theorem likelihood_append (z : Bool) (h : List (Unit × Y)) (ay : Unit × Y) :
    likelihood P Q z (h ++ [ay]) = likelihood P Q z h * (row P Q z).mass ay.2 := by
  simp [likelihood, List.map_append, List.prod_append]

theorem likelihood_nonneg (z : Bool) (h : List (Unit × Y)) : 0 ≤ likelihood P Q z h := by
  unfold likelihood
  apply List.prod_nonneg
  intro x hx
  obtain ⟨ay, _, rfl⟩ := List.mem_map.mp hx
  exact (row P Q z).nonnegative ay.2

/-- Before the horizon every prefix carries one half times its likelihood. -/
theorem prefixMass_repeat (z : Bool) (h : List (Unit × Y)) (hl : h.length ≤ N) :
    prefixMass (repeatProtocol P Q N) z h = 1 / 2 * likelihood P Q z h := by
  induction h using List.reverseRecOn with
  | nil => simp [prefixMass_nil, repeatProtocol, fairLaw, likelihood_nil]
  | append_singleton h ay ih =>
    have hlt : h.length < N := by
      simp only [List.length_append, List.length_singleton] at hl
      omega
    rw [prefixMass_append, repeatProtocol_stop_false P Q N hlt]
    simp only [Bool.false_eq_true, if_false]
    rw [ih hlt.le, likelihood_append]
    change 1 / 2 * likelihood P Q z h * 1 * (row P Q z).mass ay.2 = _
    ring

/-- The stopped mass at the horizon lives on the histories of exactly that length. -/
theorem stoppedMass_repeat (z : Bool) (h : List (Unit × Y)) :
    stoppedMass (repeatProtocol P Q N) N z h =
      if h.length = N then 1 / 2 * likelihood P Q z h else 0 := by
  unfold stoppedMass
  by_cases hl : h.length = N
  · rw [if_pos hl, if_pos ⟨hl.le, Or.inr hl⟩, prefixMass_repeat P Q N z h hl.le]
  · rw [if_neg hl, if_neg]
    rintro ⟨hle, hs | he⟩
    · rw [repeatProtocol_stop, decide_eq_true_iff] at hs
      exact hl (le_antisymm hle hs)
    · exact hl he

/-- The repeated reading pays one unit per reading: its cost at horizon N is N. -/
theorem repeat_cost :
    expectedCost (repeatProtocol P Q N) N (historyBank Unit Y N) = N := by
  unfold expectedCost
  rw [(historyBank_complete Unit Y N).sum_eq]
  have hterm : ∀ h : List (Unit × Y),
      (if h.length < N ∧ (repeatProtocol P Q N).stop h = false then
        historyMass (repeatProtocol P Q N) h *
          ∑ a : Unit, ((repeatProtocol P Q N).policy h).mass a * (repeatProtocol P Q N).cost h a
      else 0) = if h.length < N then historyMass (repeatProtocol P Q N) h else 0 := by
    intro h
    by_cases hl : h.length < N
    · rw [if_pos ⟨hl, repeatProtocol_stop_false P Q N hl⟩, if_pos hl]
      change historyMass (repeatProtocol P Q N) h * ∑ _a : Unit, (1 : ℝ) * 1 = _
      simp
    · rw [if_neg (fun hh => hl hh.1), if_neg hl]
  rw [Finset.sum_congr rfl (fun h _ => hterm h), historySet_below_eq_levels N]
  rw [Finset.sum_congr rfl (fun ℓ hℓ => levelMass_eq_one (repeatProtocol P Q N) ℓ
    (fun h hl => repeatProtocol_stop_false P Q N
      (lt_of_lt_of_le hl (Finset.mem_range.mp hℓ).le)))]
  simp

end Repeat

/-! ## B2: the Bhattacharyya coefficient -/

/-- The Bhattacharyya coefficient of two rows. -/
noncomputable def bhattacharyya (P Q : Y → ℝ) : ℝ := ∑ y, Real.sqrt (P y * Q y)

theorem bhattacharyya_nonneg (P Q : Y → ℝ) : 0 ≤ bhattacharyya P Q :=
  Finset.sum_nonneg (fun _ _ => Real.sqrt_nonneg _)

/-- For probability rows, 1 − BC is one half of the squared Hellinger distance. -/
theorem one_sub_bhattacharyya (P Q : Y → ℝ) (hP0 : ∀ y, 0 ≤ P y) (hQ0 : ∀ y, 0 ≤ Q y)
    (hP1 : ∑ y, P y = 1) (hQ1 : ∑ y, Q y = 1) :
    1 - bhattacharyya P Q = 1 / 2 * ∑ y, (Real.sqrt (P y) - Real.sqrt (Q y)) ^ 2 := by
  have hterm : ∀ y, (Real.sqrt (P y) - Real.sqrt (Q y)) ^ 2 =
      P y + Q y - 2 * Real.sqrt (P y * Q y) := by
    intro y
    rw [sub_sq, Real.sq_sqrt (hP0 y), Real.sq_sqrt (hQ0 y), Real.sqrt_mul (hP0 y)]
    ring
  simp only [hterm, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hP1, hQ1,
    bhattacharyya]
  ring

/-- One term of the discrimination is at most twice the squared difference of the roots. -/
theorem discrimination_term_le_two_sq (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a - b) ^ 2 / (a + b) ≤ 2 * (Real.sqrt a - Real.sqrt b) ^ 2 := by
  obtain ⟨s, hs0, rfl⟩ : ∃ s, 0 ≤ s ∧ a = s ^ 2 :=
    ⟨Real.sqrt a, Real.sqrt_nonneg a, (Real.sq_sqrt ha).symm⟩
  obtain ⟨t, ht0, rfl⟩ : ∃ t, 0 ≤ t ∧ b = t ^ 2 :=
    ⟨Real.sqrt b, Real.sqrt_nonneg b, (Real.sq_sqrt hb).symm⟩
  rw [Real.sqrt_sq hs0, Real.sqrt_sq ht0]
  rcases (add_nonneg (sq_nonneg s) (sq_nonneg t)).eq_or_lt with hz | hpos
  · have hs : s = 0 := by nlinarith [sq_nonneg s, sq_nonneg t]
    have ht : t = 0 := by nlinarith [sq_nonneg s, sq_nonneg t]
    simp [hs, ht]
  · rw [div_le_iff₀ hpos]
    have hid : 2 * (s - t) ^ 2 * (s ^ 2 + t ^ 2) - (s ^ 2 - t ^ 2) ^ 2 = ((s - t) ^ 2) ^ 2 := by
      ring
    nlinarith [sq_nonneg ((s - t) ^ 2)]

/-- The discrimination is at most four times one minus the Bhattacharyya coefficient. -/
theorem discrimination_le_four_one_sub_bhattacharyya (P Q : Y → ℝ) (hP0 : ∀ y, 0 ≤ P y)
    (hQ0 : ∀ y, 0 ≤ Q y) (hP1 : ∑ y, P y = 1) (hQ1 : ∑ y, Q y = 1) :
    discrimination P Q ≤ 4 * (1 - bhattacharyya P Q) := by
  rw [one_sub_bhattacharyya P Q hP0 hQ0 hP1 hQ1, discrimination]
  have hrhs : (4 : ℝ) * (1 / 2 * ∑ y, (Real.sqrt (P y) - Real.sqrt (Q y)) ^ 2) =
      ∑ y, 2 * (Real.sqrt (P y) - Real.sqrt (Q y)) ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    ring
  rw [hrhs]
  exact Finset.sum_le_sum (fun y _ => discrimination_term_le_two_sq _ _ (hP0 y) (hQ0 y))

theorem bhattacharyya_le_one_sub_quarter_discrimination (P Q : Y → ℝ) (hP0 : ∀ y, 0 ≤ P y)
    (hQ0 : ∀ y, 0 ≤ Q y) (hP1 : ∑ y, P y = 1) (hQ1 : ∑ y, Q y = 1) :
    bhattacharyya P Q ≤ 1 - discrimination P Q / 4 := by
  have h := discrimination_le_four_one_sub_bhattacharyya P Q hP0 hQ0 hP1 hQ1
  linarith

theorem bhattacharyya_le_one (P Q : Y → ℝ) (hP0 : ∀ y, 0 ≤ P y) (hQ0 : ∀ y, 0 ≤ Q y)
    (hP1 : ∑ y, P y = 1) (hQ1 : ∑ y, Q y = 1) : bhattacharyya P Q ≤ 1 := by
  have h := bhattacharyya_le_one_sub_quarter_discrimination P Q hP0 hQ0 hP1 hQ1
  have hd := discrimination_nonneg P Q hP0 hQ0
  linarith

/-! ## B3: the likelihood-ratio decoder and its error -/

section Decoder
variable (P Q : FiniteLaw Y)

/-- The likelihood-ratio decoder returns true when the true-label likelihood is at least the
false-label likelihood. -/
noncomputable def mapDecoder (h : List (Unit × Y)) : Bool :=
  decide (likelihood P Q false h ≤ likelihood P Q true h)

/-- The rejected label has the smaller likelihood. -/
theorem likelihood_rejected_le_min (h : List (Unit × Y)) :
    likelihood P Q (!mapDecoder P Q h) h ≤
      min (likelihood P Q true h) (likelihood P Q false h) := by
  unfold mapDecoder
  by_cases hle : likelihood P Q false h ≤ likelihood P Q true h
  · rw [decide_eq_true hle, Bool.not_true]
    exact le_min hle le_rfl
  · rw [decide_eq_false hle, Bool.not_false]
    exact le_min le_rfl (not_le.mp hle).le

theorem min_le_sqrt_mul (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    min a b ≤ Real.sqrt (a * b) := by
  rw [Real.le_sqrt (le_min ha hb) (mul_nonneg ha hb)]
  rcases le_total a b with h | h
  · rw [min_eq_left h]
    nlinarith
  · rw [min_eq_right h]
    nlinarith

/-- The geometric mean of the two likelihoods is the product of the root products. -/
theorem sqrt_likelihood_mul (h : List (Unit × Y)) :
    Real.sqrt (likelihood P Q true h * likelihood P Q false h) =
      (h.map (fun ay => Real.sqrt (P.mass ay.2 * Q.mass ay.2))).prod := by
  induction h with
  | nil => simp [likelihood_nil]
  | cons ay h ih =>
    rw [likelihood_true, likelihood_false] at ih ⊢
    simp only [List.map_cons, List.prod_cons]
    rw [show P.mass ay.2 * (h.map (fun ay => P.mass ay.2)).prod *
        (Q.mass ay.2 * (h.map (fun ay => Q.mass ay.2)).prod) =
        (P.mass ay.2 * Q.mass ay.2) *
          ((h.map (fun ay => P.mass ay.2)).prod * (h.map (fun ay => Q.mass ay.2)).prod) by ring,
      Real.sqrt_mul (mul_nonneg (P.nonnegative _) (Q.nonnegative _)), ih]

/-- The sum of the root products over the histories of one depth is the coefficient's power. -/
theorem bhattacharyya_level (N : ℕ) :
    (∑ h ∈ historySet (Unit × Y) N, if h.length = N then
      (h.map (fun ay => Real.sqrt (P.mass ay.2 * Q.mass ay.2))).prod else 0) =
      (bhattacharyya P.mass Q.mass) ^ N := by
  rw [historySet_level_prod]
  congr 1
  rw [Fintype.sum_prod_type]
  simp [bhattacharyya]

/-- The likelihood-ratio decoder errs with probability at most one half of BC to the power N. -/
theorem repeat_error_le (N : ℕ) :
    ∑ h ∈ historySet (Unit × Y) N,
        stoppedMass (repeatProtocol P Q N) N (!mapDecoder P Q h) h ≤
      1 / 2 * (bhattacharyya P.mass Q.mass) ^ N := by
  rw [← bhattacharyya_level P Q N, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro h _
  rw [stoppedMass_repeat]
  by_cases hl : h.length = N
  · rw [if_pos hl, if_pos hl]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    calc likelihood P Q (!mapDecoder P Q h) h
        ≤ min (likelihood P Q true h) (likelihood P Q false h) :=
          likelihood_rejected_le_min P Q h
      _ ≤ Real.sqrt (likelihood P Q true h * likelihood P Q false h) :=
          min_le_sqrt_mul _ _ (likelihood_nonneg P Q true h) (likelihood_nonneg P Q false h)
      _ = _ := sqrt_likelihood_mul P Q h
  · rw [if_neg hl, if_neg hl, mul_zero]

theorem discrimination_le_four : discrimination P.mass Q.mass ≤ 4 := by
  have h := bhattacharyya_le_one_sub_quarter_discrimination P.mass Q.mass P.nonnegative
    Q.nonnegative P.total Q.total
  have h0 := bhattacharyya_nonneg P.mass Q.mass
  linarith

/-- The error in the discrimination: at most one half of (1 − Δ/4) to the power N. -/
theorem repeat_error_le_discrimination (N : ℕ) :
    ∑ h ∈ historySet (Unit × Y) N,
        stoppedMass (repeatProtocol P Q N) N (!mapDecoder P Q h) h ≤
      1 / 2 * (1 - discrimination P.mass Q.mass / 4) ^ N := by
  have h1 := repeat_error_le P Q N
  have hbc := bhattacharyya_le_one_sub_quarter_discrimination P.mass Q.mass P.nonnegative
    Q.nonnegative P.total Q.total
  have hp : (bhattacharyya P.mass Q.mass) ^ N ≤ (1 - discrimination P.mass Q.mass / 4) ^ N :=
    pow_le_pow_left₀ (bhattacharyya_nonneg _ _) hbc N
  linarith

/-- The exponential form: at most one half of exp(−NΔ/4). -/
theorem repeat_error_le_exp (N : ℕ) :
    1 / 2 * (1 - discrimination P.mass Q.mass / 4) ^ N ≤
      1 / 2 * Real.exp (-(N * discrimination P.mass Q.mass / 4)) := by
  have hd0 := discrimination_nonneg P.mass Q.mass P.nonnegative Q.nonnegative
  have hd4 := discrimination_le_four P Q
  have h1 : (1 : ℝ) - discrimination P.mass Q.mass / 4 ≤
      Real.exp (-(discrimination P.mass Q.mass / 4)) := by
    have := Real.add_one_le_exp (-(discrimination P.mass Q.mass / 4))
    linarith
  have h0 : (0 : ℝ) ≤ 1 - discrimination P.mass Q.mass / 4 := by linarith
  have hp := pow_le_pow_left₀ h0 h1 N
  rw [← Real.exp_nat_mul] at hp
  have he : (N : ℝ) * -(discrimination P.mass Q.mass / 4) =
      -(N * discrimination P.mass Q.mass / 4) := by ring
  rw [he] at hp
  linarith

end Decoder

/-! ## B4: the information of the repeated reading -/

section Information
variable (P Q : FiniteLaw Y)

/-- The repeated reading acquires at least one bit minus the binary entropy of one half of BC^N. -/
theorem repeat_information (N : ℕ) :
    1 - Real.binEntropy (1 / 2 * (bhattacharyya P.mass Q.mass) ^ N) / Real.log 2 ≤
      terminalMI (repeatProtocol P Q N) N (historyBank Unit Y N) := by
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  rw [terminalMI_eq_entropy_sub _ _ _ (historyBank_complete Unit Y N)]
  rw [show (repeatProtocol P Q N).prior.mass = fairLaw.mass from rfl, fairLaw_entropy]
  have htot : ∑ h ∈ historySet (Unit × Y) N,
      (stoppedMass (repeatProtocol P Q N) N true h +
        stoppedMass (repeatProtocol P Q N) N false h) = 1 := by
    rw [Finset.sum_add_distrib, historySet_stoppedMass_target_marginal,
      historySet_stoppedMass_target_marginal]
    show fairLaw.mass true + fairLaw.mass false = 1
    norm_num [fairLaw]
  have hfano := sum_massUncertainty_le_binEntropy (historySet (Unit × Y) N)
    (fun h z => stoppedMass (repeatProtocol P Q N) N z h)
    (fun h z => stoppedMass_nonnegative _ _ z h) htot (mapDecoder P Q)
  have herr := repeat_error_le P Q N
  have hbc0 := bhattacharyya_nonneg P.mass Q.mass
  have hbc1 := bhattacharyya_le_one P.mass Q.mass P.nonnegative Q.nonnegative P.total Q.total
  have hb1 : 1 / 2 * (bhattacharyya P.mass Q.mass) ^ N ≤ 2⁻¹ := by
    have hp : (bhattacharyya P.mass Q.mass) ^ N ≤ 1 := pow_le_one₀ hbc0 hbc1
    linarith
  have hb0 : 0 ≤ ∑ h ∈ historySet (Unit × Y) N,
      stoppedMass (repeatProtocol P Q N) N (!mapDecoder P Q h) h :=
    Finset.sum_nonneg (fun h _ => stoppedMass_nonnegative _ _ _ h)
  have hnn : (0 : ℝ) ≤ 1 / 2 * (bhattacharyya P.mass Q.mass) ^ N :=
    mul_nonneg (by norm_num) (pow_nonneg hbc0 N)
  have hmono := Real.binEntropy_strictMonoOn.monotoneOn ⟨hb0, herr.trans hb1⟩ ⟨hnn, hb1⟩ herr
  have hfin := hfano.trans (div_le_div_of_nonneg_right hmono hlog.le)
  linarith

/-- For a target error η in (0, 1/2] and a reading of positive discrimination Δ, the repeated
reading with N = ⌈4 log(1/(2η))/Δ⌉ acquires 1 − h₂(η)/log 2 bits at cost N ≤ 4 log(1/(2η))/Δ + 1. -/
theorem repeat_target (hΔ : 0 < discrimination P.mass Q.mass) (η : ℝ) (hη0 : 0 < η)
    (hη1 : η ≤ 1 / 2) :
    1 - Real.binEntropy η / Real.log 2 ≤
        terminalMI (repeatProtocol P Q ⌈4 * Real.log (1 / (2 * η)) / discrimination P.mass Q.mass⌉₊)
          ⌈4 * Real.log (1 / (2 * η)) / discrimination P.mass Q.mass⌉₊
          (historyBank Unit Y ⌈4 * Real.log (1 / (2 * η)) / discrimination P.mass Q.mass⌉₊) ∧
      expectedCost (repeatProtocol P Q ⌈4 * Real.log (1 / (2 * η)) / discrimination P.mass Q.mass⌉₊)
          ⌈4 * Real.log (1 / (2 * η)) / discrimination P.mass Q.mass⌉₊
          (historyBank Unit Y ⌈4 * Real.log (1 / (2 * η)) / discrimination P.mass Q.mass⌉₊) =
        ((⌈4 * Real.log (1 / (2 * η)) / discrimination P.mass Q.mass⌉₊ : ℕ) : ℝ) ∧
      ((⌈4 * Real.log (1 / (2 * η)) / discrimination P.mass Q.mass⌉₊ : ℕ) : ℝ) ≤
        4 * Real.log (1 / (2 * η)) / discrimination P.mass Q.mass + 1 := by
  set Δ := discrimination P.mass Q.mass with hΔdef
  set N := ⌈4 * Real.log (1 / (2 * η)) / Δ⌉₊ with hN
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hL0 : 0 ≤ Real.log (1 / (2 * η)) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hnle : 4 * Real.log (1 / (2 * η)) / Δ ≤ N := Nat.le_ceil _
  have hnlt : (N : ℝ) < 4 * Real.log (1 / (2 * η)) / Δ + 1 :=
    Nat.ceil_lt_add_one (div_nonneg (by linarith) hΔ.le)
  have herr : 1 / 2 * (bhattacharyya P.mass Q.mass) ^ N ≤ η := by
    have h1 := repeat_error_le_discrimination P Q N
    have h2 := repeat_error_le_exp P Q N
    have hbc := bhattacharyya_le_one_sub_quarter_discrimination P.mass Q.mass P.nonnegative
      Q.nonnegative P.total Q.total
    have hp : (bhattacharyya P.mass Q.mass) ^ N ≤ (1 - Δ / 4) ^ N :=
      pow_le_pow_left₀ (bhattacharyya_nonneg _ _) hbc N
    have hle : Real.log (1 / (2 * η)) ≤ N * Δ / 4 := by
      rw [div_le_iff₀ hΔ] at hnle
      linarith
    have h3 : Real.exp (-(N * Δ / 4)) ≤ 2 * η := by
      calc Real.exp (-(N * Δ / 4)) ≤ Real.exp (-Real.log (1 / (2 * η))) :=
            Real.exp_le_exp.mpr (by linarith)
        _ = 2 * η := by rw [Real.exp_neg, Real.exp_log (by positivity), one_div, inv_inv]
    linarith
  refine ⟨?_, repeat_cost P Q N, ?_⟩
  · have hinfo := repeat_information P Q N
    have hnn : (0 : ℝ) ≤ 1 / 2 * (bhattacharyya P.mass Q.mass) ^ N :=
      mul_nonneg (by norm_num) (pow_nonneg (bhattacharyya_nonneg _ _) N)
    have hη2 : η ≤ 2⁻¹ := by
      rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num]
      exact hη1
    have hmono := Real.binEntropy_strictMonoOn.monotoneOn ⟨hnn, herr.trans hη2⟩ ⟨hη0.le, hη2⟩ herr
    have hfin := div_le_div_of_nonneg_right hmono hlog.le
    linarith
  · exact hnlt.le

end Information

/-! ## B5: the two-sided singularity for every finite reading -/

/-- The singularity is sharp for every finite reading. Every protocol of readings of discrimination
at most Δ pays at least c log 2/Δ for c bits at every horizon; and for every reading with rows P, Q
of discrimination Δ and every target η in (0, 1/2], repeating the reading acquires 1 − h₂(η)/log 2
bits within 4 log(1/(2η))/Δ + 1 readings. Both sides of the resolution cost are of order Δ⁻¹. -/
theorem pair_resolution_two_sided (P Q : FiniteLaw Y) (hΔ : 0 < discrimination P.mass Q.mass) :
    (∀ {A : Type} [Fintype A] (p : FiniteProtocol Bool A Y) (c : ℝ),
      PairMenu p (discrimination P.mass Q.mass) →
      ∀ (n : ℕ) (bank : List (List (A × Y))), HistoryBank n bank →
        c ≤ terminalMI p n bank →
          c * Real.log 2 / discrimination P.mass Q.mass ≤ expectedCost p n bank) ∧
    (∀ η : ℝ, 0 < η → η ≤ 1 / 2 → ∃ N : ℕ,
      1 - Real.binEntropy η / Real.log 2 ≤
          terminalMI (repeatProtocol P Q N) N (historyBank Unit Y N) ∧
        expectedCost (repeatProtocol P Q N) N (historyBank Unit Y N) = N ∧
        (N : ℝ) ≤ 4 * Real.log (1 / (2 * η)) / discrimination P.mass Q.mass + 1) := by
  refine ⟨fun p c menu n bank hb hc =>
    pairMenu_cost_lower_bound p _ c menu hΔ n bank hb hc, ?_⟩
  intro η hη0 hη1
  obtain ⟨h1, h2, h3⟩ := repeat_target P Q hΔ η hη0 hη1
  exact ⟨_, h1, h2, h3⟩

/-! ## B6: the two ends of the coordinate on a deterministic observer -/

section Deterministic
variable {X : Type} [DecidableEq Y]

/-- The row of the deterministic observer q at the state x, as a finite law. -/
noncomputable def deterministicRow (q : X → Y) (x : X) : FiniteLaw Y where
  mass := (StochasticGraph.deterministic q).prob x
  nonnegative := (StochasticGraph.deterministic q).nonneg x
  total := (StochasticGraph.deterministic q).row_sum x

theorem deterministicRow_mass (q : X → Y) (x : X) (y : Y) :
    (deterministicRow q x).mass y = if q x = y then 1 else 0 := by
  simp [deterministicRow, StochasticGraph.deterministic]

/-- At a split pair the Bhattacharyya coefficient of the two rows is zero. -/
theorem bhattacharyya_deterministic_split (q : X → Y) (x x' : X) (hq : q x ≠ q x') :
    bhattacharyya (deterministicRow q x).mass (deterministicRow q x').mass = 0 := by
  unfold bhattacharyya
  apply Finset.sum_eq_zero
  intro y _
  rw [deterministicRow_mass, deterministicRow_mass]
  by_cases h1 : q x = y
  · have h2 : ¬ (q x' = y) := fun h2 => hq (h1.trans h2.symm)
    rw [if_pos h1, if_neg h2]
    simp
  · rw [if_neg h1]
    simp

/-- At a merged pair the two rows coincide and the coefficient is one. -/
theorem bhattacharyya_deterministic_merged (q : X → Y) (x x' : X) (hq : q x = q x') :
    bhattacharyya (deterministicRow q x).mass (deterministicRow q x').mass = 1 := by
  unfold bhattacharyya
  simp only [deterministicRow_mass, hq]
  have hterm : ∀ y, Real.sqrt ((if q x' = y then (1 : ℝ) else 0) * (if q x' = y then 1 else 0)) =
      if q x' = y then 1 else 0 := by
    intro y
    split_ifs <;> simp
  simp only [hterm, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- One reading of a deterministic observer at a split pair errs with probability zero and acquires
the whole bit at unit cost. -/
theorem split_pair_one_reading (q : X → Y) (x x' : X) (hq : q x ≠ q x') :
    (∑ h ∈ historySet (Unit × Y) 1,
      stoppedMass (repeatProtocol (deterministicRow q x) (deterministicRow q x') 1) 1
        (!mapDecoder (deterministicRow q x) (deterministicRow q x') h) h) = 0 ∧
    1 ≤ terminalMI (repeatProtocol (deterministicRow q x) (deterministicRow q x') 1) 1
        (historyBank Unit Y 1) ∧
    expectedCost (repeatProtocol (deterministicRow q x) (deterministicRow q x') 1) 1
        (historyBank Unit Y 1) = 1 := by
  have hbc := bhattacharyya_deterministic_split q x x' hq
  refine ⟨?_, ?_, ?_⟩
  · have h := repeat_error_le (deterministicRow q x) (deterministicRow q x') 1
    rw [hbc] at h
    simp only [pow_one, mul_zero] at h
    exact le_antisymm h (Finset.sum_nonneg (fun h _ => stoppedMass_nonnegative _ _ _ h))
  · have h := repeat_information (deterministicRow q x) (deterministicRow q x') 1
    rw [hbc] at h
    simpa using h
  · have h := repeat_cost (deterministicRow q x) (deterministicRow q x') 1
    simpa using h

/-- At a merged pair no protocol of readings of the observer acquires anything, at any horizon. -/
theorem merged_pair_no_information (q : X → Y) (x x' : X) (hq : q x = q x') (N : ℕ) :
    terminalMI (repeatProtocol (deterministicRow q x) (deterministicRow q x') N) N
      (historyBank Unit Y N) = 0 := by
  have hd : discrimination (deterministicRow q x).mass (deterministicRow q x').mass = 0 := by
    apply (discrimination_eq_zero_iff _ _ (deterministicRow q x).nonnegative
      (deterministicRow q x').nonnegative).mpr
    funext y
    rw [deterministicRow_mass, deterministicRow_mass, hq]
  have menu := repeatProtocol_pairMenu (deterministicRow q x) (deterministicRow q x') N
  rw [hd] at menu
  exact pairMenu_zero_discrimination _ menu N _ (historyBank_complete Unit Y N)

end Deterministic

end OperatorKO7.Meta.BoundaryObserver.PairResolution
