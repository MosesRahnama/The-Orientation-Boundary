import OperatorKO7.Meta.BoundaryObserver.ProtocolResolution

set_option autoImplicit false

/-!
# The boundary as the singular set of the resolution cost

The discrimination of two rows is the triangular discrimination of Vincze and Le Cam.
One reading about a binary label, at any prior, carries at most that discrimination over log 2 bits.
A protocol of such readings pays at least c log 2 over the discrimination for c bits, at every
horizon and in the limit; at discrimination zero it acquires nothing.
The deterministic observer has discrimination zero on its merged pairs and two on every other pair.
A full-rank system state keeps positive entropy under every finite thermal operation.
-/

namespace OperatorKO7.Meta.BoundaryObserver.BoundarySingularity

open scoped BigOperators
open ProtocolResolution

/-! ## S1: the discrimination of two rows -/

/-- Triangular discrimination of two rows; a term with zero denominator is zero. -/
noncomputable def discrimination {Y : Type} [Fintype Y] (P Q : Y → ℝ) : ℝ :=
  ∑ y, (P y - Q y) ^ 2 / (P y + Q y)

theorem discrimination_term_nonneg (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ (a - b) ^ 2 / (a + b) :=
  div_nonneg (sq_nonneg _) (add_nonneg ha hb)

theorem discrimination_nonneg {Y : Type} [Fintype Y] (P Q : Y → ℝ)
    (hP : ∀ y, 0 ≤ P y) (hQ : ∀ y, 0 ≤ Q y) : 0 ≤ discrimination P Q :=
  Finset.sum_nonneg (fun y _ => discrimination_term_nonneg _ _ (hP y) (hQ y))

/-- Each term is at most the absolute difference, since that difference is at most the sum. -/
theorem discrimination_term_le_abs (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a - b) ^ 2 / (a + b) ≤ |a - b| := by
  rcases (add_nonneg ha hb).eq_or_lt with h | h
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    simp [ha0, hb0]
  · rw [div_le_iff₀ h]
    have habs : |a - b| ≤ a + b := by
      rw [abs_le]
      constructor <;> linarith
    calc (a - b) ^ 2 = |a - b| * |a - b| := by rw [← sq_abs, sq]
      _ ≤ |a - b| * (a + b) := mul_le_mul_of_nonneg_left habs (abs_nonneg _)

/-- The discrimination is at most twice the total variation distance of the two rows. -/
theorem discrimination_le_sum_abs {Y : Type} [Fintype Y] (P Q : Y → ℝ)
    (hP : ∀ y, 0 ≤ P y) (hQ : ∀ y, 0 ≤ Q y) :
    discrimination P Q ≤ ∑ y, |P y - Q y| :=
  Finset.sum_le_sum (fun y _ => discrimination_term_le_abs _ _ (hP y) (hQ y))

/-- The discrimination vanishes exactly on equal rows. -/
theorem discrimination_eq_zero_iff {Y : Type} [Fintype Y] (P Q : Y → ℝ)
    (hP : ∀ y, 0 ≤ P y) (hQ : ∀ y, 0 ≤ Q y) :
    discrimination P Q = 0 ↔ P = Q := by
  constructor
  · intro h
    have hz := (Finset.sum_eq_zero_iff_of_nonneg
      (fun y _ => discrimination_term_nonneg _ _ (hP y) (hQ y))).mp h
    funext y
    have hy := hz y (Finset.mem_univ y)
    rcases (add_nonneg (hP y) (hQ y)).eq_or_lt with hs | hs
    · have hp0 : P y = 0 := by linarith [hP y, hQ y]
      have hq0 : Q y = 0 := by linarith [hP y, hQ y]
      rw [hp0, hq0]
    · rcases div_eq_zero_iff.mp hy with h1 | h2
      · exact sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h1)
      · exact absurd h2 hs.ne'
  · rintro rfl
    simp [discrimination]

/-- The deterministic observer has discrimination zero on a merged pair and two on a split pair. -/
theorem discrimination_deterministic {X Y : Type} [Fintype Y] [DecidableEq Y]
    (q : X → Y) (x x' : X) :
    discrimination ((StochasticGraph.deterministic q).prob x)
      ((StochasticGraph.deterministic q).prob x') = if q x = q x' then 0 else 2 := by
  by_cases h : q x = q x'
  · rw [if_pos h]
    apply (discrimination_eq_zero_iff _ _ ((StochasticGraph.deterministic q).nonneg x)
      ((StochasticGraph.deterministic q).nonneg x')).mpr
    funext y
    simp [StochasticGraph.deterministic, h]
  · rw [if_neg h]
    unfold discrimination
    have hterm : ∀ y, ((StochasticGraph.deterministic q).prob x y -
        (StochasticGraph.deterministic q).prob x' y) ^ 2 /
        ((StochasticGraph.deterministic q).prob x y + (StochasticGraph.deterministic q).prob x' y) =
        (if q x = y then (1 : ℝ) else 0) + (if q x' = y then 1 else 0) := by
      intro y
      by_cases hy : q x = y
      · subst hy
        simp [StochasticGraph.deterministic, Ne.symm h]
      · by_cases hy' : q x' = y
        · subst hy'
          simp [StochasticGraph.deterministic, h]
        · simp [StochasticGraph.deterministic, hy, hy']
    simp only [hterm, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    norm_num

/-- The two rows of the binary symmetric channel at bias delta have discrimination eight delta squared. -/
theorem discrimination_binaryKernel (δ : ℝ) :
    discrimination (binaryKernel δ true) (binaryKernel δ false) = 8 * δ ^ 2 := by
  simp only [discrimination, binaryKernel, Fintype.sum_bool]
  norm_num
  ring

/-! ## S2: one reading about a binary label -/

/-- The entropy gain of a two-point mixture is at most its chi-square term. -/
theorem negMulLog_mix_le (q a b : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.negMulLog (q * a + (1 - q) * b) - q * Real.negMulLog a - (1 - q) * Real.negMulLog b
      ≤ q * (1 - q) * (a - b) ^ 2 / (q * a + (1 - q) * b) := by
  have hq1' : 0 ≤ 1 - q := by linarith
  have hM0 : 0 ≤ q * a + (1 - q) * b := add_nonneg (mul_nonneg hq0 ha) (mul_nonneg hq1' hb)
  rcases hM0.eq_or_lt with hz | hpos
  · have h1 : q * a = 0 := by
      linarith [mul_nonneg hq0 ha, mul_nonneg hq1' hb]
    have h2 : (1 - q) * b = 0 := by
      linarith [mul_nonneg hq0 ha, mul_nonneg hq1' hb]
    have hqa : q * Real.negMulLog a = 0 := by
      rcases mul_eq_zero.mp h1 with hq | ha0
      · rw [hq, zero_mul]
      · rw [ha0, Real.negMulLog_zero, mul_zero]
    have hqb : (1 - q) * Real.negMulLog b = 0 := by
      rcases mul_eq_zero.mp h2 with hq | hb0
      · rw [hq, zero_mul]
      · rw [hb0, Real.negMulLog_zero, mul_zero]
    rw [← hz, Real.negMulLog_zero, hqa, hqb]
    simp
  · have key : Real.negMulLog (q * a + (1 - q) * b) - q * Real.negMulLog a -
        (1 - q) * Real.negMulLog b =
        q * (a * Real.log a - a * Real.log (q * a + (1 - q) * b)) +
          (1 - q) * (b * Real.log b - b * Real.log (q * a + (1 - q) * b)) := by
      simp only [Real.negMulLog]
      ring
    have bnd : ∀ c : ℝ, 0 ≤ c →
        c * Real.log c - c * Real.log (q * a + (1 - q) * b) ≤
          c * (c - (q * a + (1 - q) * b)) / (q * a + (1 - q) * b) := by
      intro c hc
      rcases hc.eq_or_lt with hc0 | hcpos
      · rw [← hc0]
        simp
      · have hlog : Real.log c - Real.log (q * a + (1 - q) * b) ≤
            c / (q * a + (1 - q) * b) - 1 := by
          rw [← Real.log_div hcpos.ne' hpos.ne']
          exact Real.log_le_sub_one_of_pos (div_pos hcpos hpos)
        calc c * Real.log c - c * Real.log (q * a + (1 - q) * b) =
              c * (Real.log c - Real.log (q * a + (1 - q) * b)) := by ring
          _ ≤ c * (c / (q * a + (1 - q) * b) - 1) :=
              mul_le_mul_of_nonneg_left hlog hcpos.le
          _ = c * (c - (q * a + (1 - q) * b)) / (q * a + (1 - q) * b) := by
              field_simp
    rw [key]
    have hfinal : q * (a * (a - (q * a + (1 - q) * b)) / (q * a + (1 - q) * b)) +
        (1 - q) * (b * (b - (q * a + (1 - q) * b)) / (q * a + (1 - q) * b)) =
        q * (1 - q) * (a - b) ^ 2 / (q * a + (1 - q) * b) := by
      field_simp
      ring
    calc q * (a * Real.log a - a * Real.log (q * a + (1 - q) * b)) +
          (1 - q) * (b * Real.log b - b * Real.log (q * a + (1 - q) * b))
        ≤ q * (a * (a - (q * a + (1 - q) * b)) / (q * a + (1 - q) * b)) +
          (1 - q) * (b * (b - (q * a + (1 - q) * b)) / (q * a + (1 - q) * b)) :=
          add_le_add (mul_le_mul_of_nonneg_left (bnd a ha) hq0)
            (mul_le_mul_of_nonneg_left (bnd b hb) hq1')
      _ = _ := hfinal

/-- The chi-square term of a two-point mixture is at most the discrimination term. -/
theorem chi_term_le_discrimination_term (q a b : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    q * (1 - q) * (a - b) ^ 2 / (q * a + (1 - q) * b) ≤ (a - b) ^ 2 / (a + b) := by
  have hq1' : 0 ≤ 1 - q := by linarith
  have hM0 : 0 ≤ q * a + (1 - q) * b := add_nonneg (mul_nonneg hq0 ha) (mul_nonneg hq1' hb)
  rcases hM0.eq_or_lt with hz | hpos
  · rw [← hz, div_zero]
    exact discrimination_term_nonneg a b ha hb
  · rcases (add_nonneg ha hb).eq_or_lt with hs | hs
    · have ha0 : a = 0 := by linarith
      have hb0 : b = 0 := by linarith
      simp [ha0, hb0]
    · rw [div_le_div_iff₀ hpos hs]
      have h1 : 0 ≤ q * q * a := mul_nonneg (mul_nonneg hq0 hq0) ha
      have h2 : 0 ≤ (1 - q) * (1 - q) * b := mul_nonneg (mul_nonneg hq1' hq1') hb
      have e : q * a + (1 - q) * b - q * (1 - q) * (a + b) =
          q * q * a + (1 - q) * (1 - q) * b := by ring
      have hmix : q * (1 - q) * (a + b) ≤ q * a + (1 - q) * b := by linarith
      calc q * (1 - q) * (a - b) ^ 2 * (a + b) = (a - b) ^ 2 * (q * (1 - q) * (a + b)) := by ring
        _ ≤ (a - b) ^ 2 * (q * a + (1 - q) * b) :=
            mul_le_mul_of_nonneg_left hmix (sq_nonneg _)

/-- One reading about a binary label, at any prior, carries at most the discrimination of its
two rows divided by log 2 bits. -/
theorem binary_information_le_discrimination {Y : Type} [Fintype Y] (q : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (K : Bool → Y → ℝ)
    (hK0 : ∀ b y, 0 ≤ K b y) (hK1 : ∀ b, ∑ y, K b y = 1) :
    jointMI (fun by_ : Bool × Y => binaryPrior q by_.1 * K by_.1 by_.2) ≤
      discrimination (K true) (K false) / Real.log 2 := by
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  rw [jointMI_kernel (binaryPrior q) K hK1]
  have hmix : (fun y => ∑ b, binaryPrior q b * K b y) =
      fun y => q * K true y + (1 - q) * K false y := by
    funext y
    simp [binaryPrior]
  rw [hmix, Fintype.sum_bool]
  simp only [binaryPrior, if_true, Bool.false_eq_true, if_false]
  rw [entropy_eq_sum, entropy_eq_sum, entropy_eq_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, discrimination, Finset.sum_div]
  apply Finset.sum_le_sum
  intro y _
  have hgap : entropyTerm (q * K true y + (1 - q) * K false y) -
      (q * entropyTerm (K true y) + (1 - q) * entropyTerm (K false y)) =
      (Real.negMulLog (q * K true y + (1 - q) * K false y) - q * Real.negMulLog (K true y) -
        (1 - q) * Real.negMulLog (K false y)) / Real.log 2 := by
    simp only [entropyTerm]
    ring
  rw [hgap]
  apply div_le_div_of_nonneg_right _ hlog.le
  calc Real.negMulLog (q * K true y + (1 - q) * K false y) - q * Real.negMulLog (K true y) -
        (1 - q) * Real.negMulLog (K false y)
      ≤ q * (1 - q) * (K true y - K false y) ^ 2 / (q * K true y + (1 - q) * K false y) :=
        negMulLog_mix_le q _ _ hq0 hq1 (hK0 true y) (hK0 false y)
    _ ≤ (K true y - K false y) ^ 2 / (K true y + K false y) :=
        chi_term_le_discrimination_term q _ _ hq0 hq1 (hK0 true y) (hK0 false y)

/-! ## S3: protocols whose readings all have bounded discrimination -/

section PairMenus
variable {A Y : Type} [Fintype A] [Fintype Y]

/-- Every permitted reading has rows for the two labels at most δ apart in discrimination,
at every retained history, and costs at least one. -/
structure PairMenu (p : FiniteProtocol Bool A Y) (δ : ℝ) where
  rows : ∀ h a, discrimination (p.observation h a true).mass (p.observation h a false).mass ≤ δ
  reading_cost : ∀ h a, 1 ≤ p.cost h a

/-- The binary symmetric menu of bias at most ε is a pair menu of discrimination eight ε squared. -/
def BinaryMenu.toPairMenu {p : FiniteProtocol Bool A Bool} {ε : ℝ} (menu : BinaryMenu p ε) :
    PairMenu p (8 * ε ^ 2) where
  rows h a := by
    have hrow : ∀ b, (p.observation h a b).mass = binaryKernel (menu.bias h a) b := by
      intro b
      funext y
      exact menu.source h a b y
    rw [hrow true, hrow false, discrimination_binaryKernel]
    have hb := menu.bound h a
    have hs : (menu.bias h a) ^ 2 ≤ ε ^ 2 := sq_le_sq' (abs_le.mp hb).1 (abs_le.mp hb).2
    linarith
  reading_cost := menu.reading_cost

/-- A reachable binary posterior is the prior determined by its true mass, for any outcome type. -/
theorem posterior_eq_binaryPrior_of_pos (p : FiniteProtocol Bool A Y)
    (h : List (A × Y)) (hw : 0 < historyMass p h) :
    posterior p h = binaryPrior (posterior p h true) := by
  have hp := posterior_total p h hw
  simp only [Fintype.sum_bool] at hp
  funext b
  cases b
  · change posterior p h false = 1 - posterior p h true
    linarith
  · rfl

theorem pairMenu_localGain_le (p : FiniteProtocol Bool A Y) (δ : ℝ) (menu : PairMenu p δ)
    (h : List (A × Y)) (a : A) (hw : 0 < historyMass p h) :
    localGain p h a ≤ δ / Real.log 2 := by
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  unfold localGain
  rw [posterior_eq_binaryPrior_of_pos p h hw]
  calc jointMI (fun zy : Bool × Y =>
        binaryPrior (posterior p h true) zy.1 * (p.observation h a zy.1).mass zy.2)
      ≤ discrimination (p.observation h a true).mass (p.observation h a false).mass /
          Real.log 2 :=
        binary_information_le_discrimination (posterior p h true)
          (posterior_nonnegative p h true) (posterior_le_one p h true)
          (fun b => (p.observation h a b).mass)
          (fun b y => (p.observation h a b).nonnegative y)
          (fun b => (p.observation h a b).total)
    _ ≤ δ / Real.log 2 := div_le_div_of_nonneg_right (menu.rows h a) hlog.le

/-- Every active reading of a pair menu obeys the local capacity bound δ over log 2. -/
theorem pairMenu_capacity (p : FiniteProtocol Bool A Y) (δ : ℝ) (menu : PairMenu p δ)
    (hδ : 0 ≤ δ) : LocalCapacityBound p (δ / Real.log 2) := by
  intro h a hw _ _
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  calc localGain p h a ≤ δ / Real.log 2 := pairMenu_localGain_le p δ menu h a hw
    _ ≤ δ / Real.log 2 * p.cost h a :=
        le_mul_of_one_le_right (div_nonneg hδ hlog.le) (menu.reading_cost h a)

theorem pairMenu_information_bound (p : FiniteProtocol Bool A Y) (δ : ℝ) (menu : PairMenu p δ)
    (hδ : 0 ≤ δ) (n : ℕ) (bank : List (List (A × Y))) (hb : HistoryBank n bank) :
    0 ≤ terminalMI p n bank ∧ terminalMI p n bank ≤ δ / Real.log 2 * expectedCost p n bank :=
  ⟨terminalMI_nonnegative p n bank hb,
    terminalMI_le_expectedCost p _ n bank hb (pairMenu_capacity p δ menu hδ)⟩

/-- Acquiring c bits through readings of discrimination at most δ costs at least c log 2 over δ. -/
theorem pairMenu_cost_lower_bound (p : FiniteProtocol Bool A Y) (δ c : ℝ) (menu : PairMenu p δ)
    (hδ : 0 < δ) (n : ℕ) (bank : List (List (A × Y))) (hb : HistoryBank n bank)
    (hc : c ≤ terminalMI p n bank) : c * Real.log 2 / δ ≤ expectedCost p n bank := by
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hi := hc.trans (pairMenu_information_bound p δ menu hδ.le n bank hb).2
  rw [div_le_iff₀ hδ]
  calc c * Real.log 2 ≤ δ / Real.log 2 * expectedCost p n bank * Real.log 2 :=
        mul_le_mul_of_nonneg_right hi hlog.le
    _ = expectedCost p n bank * δ := by
        field_simp
        ring

/-- Readings of discrimination zero acquire nothing at every finite horizon. -/
theorem pairMenu_zero_discrimination (p : FiniteProtocol Bool A Y) (menu : PairMenu p 0)
    (n : ℕ) (bank : List (List (A × Y))) (hb : HistoryBank n bank) :
    terminalMI p n bank = 0 := by
  have hi := pairMenu_information_bound p 0 menu le_rfl n bank hb
  simp only [zero_div, zero_mul] at hi
  exact le_antisymm hi.2 hi.1

/-- The bound survives the unbounded horizon: c bits in the limit need a budget of at least
c log 2 over δ. -/
theorem pairMenu_limit_cost_lower (p : FiniteProtocol Bool A Y) (δ c budget : ℝ)
    (menu : PairMenu p δ) (hδ : 0 < δ) (hb : 0 ≤ budget) (hc : c ≤ informationLimit p)
    (hcost : extendedCost p ≤ ENNReal.ofReal budget) : c * Real.log 2 / δ ≤ budget := by
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hil := informationLimit_le_budget p (δ / Real.log 2) budget (div_nonneg hδ.le hlog.le)
    hb (pairMenu_capacity p δ menu hδ.le) hcost
  rw [div_le_iff₀ hδ]
  calc c * Real.log 2 ≤ δ / Real.log 2 * budget * Real.log 2 :=
        mul_le_mul_of_nonneg_right (hc.trans hil) hlog.le
    _ = budget * δ := by
        field_simp
        ring

/-- Readings of discrimination zero acquire nothing in the limit, at any total cost. -/
theorem pairMenu_limit_zero (p : FiniteProtocol Bool A Y) (menu : PairMenu p 0) :
    informationLimit p = 0 := by
  apply informationLimit_zero_capacity
  have h := pairMenu_capacity p 0 menu le_rfl
  simpa only [zero_div] using h

end PairMenus

/-- The boundary singularity for a pair of states of a deterministic observer: the discrimination
of the two rows vanishes exactly on a merged pair; every protocol of readings with discrimination
at most δ pays at least c log 2 over δ for c bits at every horizon; and readings of discrimination
zero acquire nothing in the limit. -/
theorem boundary_singularity {X Y : Type} [Fintype Y] [DecidableEq Y] (q : X → Y) (x x' : X) :
    (discrimination ((StochasticGraph.deterministic q).prob x)
      ((StochasticGraph.deterministic q).prob x') = 0 ↔ q x = q x') ∧
    (∀ {A : Type} [Fintype A] (p : FiniteProtocol Bool A Y) (δ c : ℝ), PairMenu p δ →
      0 < δ → ∀ (n : ℕ) (bank : List (List (A × Y))), HistoryBank n bank →
        c ≤ terminalMI p n bank → c * Real.log 2 / δ ≤ expectedCost p n bank) ∧
    (∀ {A : Type} [Fintype A] (p : FiniteProtocol Bool A Y), PairMenu p 0 →
      informationLimit p = 0) := by
  refine ⟨?_, fun p δ c menu hδ n bank hb hc => pairMenu_cost_lower_bound p δ c menu hδ n bank hb hc,
    fun p menu => pairMenu_limit_zero p menu⟩
  rw [discrimination_deterministic]
  by_cases h : q x = q x'
  · simp [h]
  · simp [h]


/-! Conditional pair menus with an arbitrary finite output alphabet. -/
section ConditionalPairMenus
variable {H0 A Y : Type} [Fintype H0] [Fintype A] [Fintype Y]

/-- For every initial record of positive mass, all available actions have
pairwise discrimination at most δ and each action costs at least one. -/
structure ConditionalPairMenu (p : ConditionalProtocol H0 Bool A Y) (δ : ℝ) where
  atRecord : ∀ u, 0 < p.initialRecord.mass u → PairMenu (p.given u) δ

/-- The local conditional capacity is derived from the actual row laws. -/
theorem conditionalPairMenu_capacity (p : ConditionalProtocol H0 Bool A Y)
    (δ : ℝ) (menu : ConditionalPairMenu p δ) (hδ : 0 ≤ δ) :
    ∀ u, 0 < p.initialRecord.mass u →
      LocalCapacityBound (p.given u) (δ / Real.log 2) := by
  intro u hu
  exact pairMenu_capacity (p.given u) δ (menu.atRecord u hu) hδ

/-- Actual conditional stopped information is nonnegative and bounded by
the actual paid conditional reading cost after retaining the initial record. -/
theorem conditionalPairMenu_information_bound (p : ConditionalProtocol H0 Bool A Y)
    (δ : ℝ) (menu : ConditionalPairMenu p δ) (hδ : 0 ≤ δ)
    (n : ℕ) (bank : List (List (A × Y))) (hb : HistoryBank n bank) :
    0 ≤ conditionalJointInfo p n bank ∧
      conditionalJointInfo p n bank ≤
        (δ / Real.log 2) * conditionalExpectedCost p n bank := by
  have hbound := conditionalJointInfo_bounds p n bank hb (δ / Real.log 2)
    (conditionalPairMenu_capacity p δ menu hδ)
  exact ⟨hbound.2.2.2.1, hbound.2.2.2.2⟩

/-- Positive discrimination requires paid cost c log 2 / δ to gain
c conditional bits at a finite stopped horizon. -/
theorem conditionalPairMenu_cost_lower_bound (p : ConditionalProtocol H0 Bool A Y)
    (δ c : ℝ) (menu : ConditionalPairMenu p δ) (hδ : 0 < δ)
    (n : ℕ) (bank : List (List (A × Y))) (hb : HistoryBank n bank)
    (hc : c ≤ conditionalJointInfo p n bank) :
    c * Real.log 2 / δ ≤ conditionalExpectedCost p n bank := by
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hi := hc.trans (conditionalPairMenu_information_bound p δ menu hδ.le n bank hb).2
  rw [div_le_iff₀ hδ]
  calc
    c * Real.log 2 ≤
        ((δ / Real.log 2) * conditionalExpectedCost p n bank) * Real.log 2 :=
      mul_le_mul_of_nonneg_right hi hlog.le
    _ = conditionalExpectedCost p n bank * δ := by
      field_simp
      ring

/-- Identical conditional rows give no acquired information at finite horizons. -/
theorem conditionalPairMenu_zero_discrimination (p : ConditionalProtocol H0 Bool A Y)
    (menu : ConditionalPairMenu p 0) (n : ℕ) (bank : List (List (A × Y)))
    (hb : HistoryBank n bank) : conditionalJointInfo p n bank = 0 := by
  have hi := conditionalPairMenu_information_bound p 0 menu le_rfl n bank hb
  simp only [zero_div, zero_mul] at hi
  exact le_antisymm hi.2 hi.1

/-- The information limit is bounded by actual extended expected costs,
including infinite-cost protocols and retained initial records. -/
theorem conditionalPairMenu_limit_bound (p : ConditionalProtocol H0 Bool A Y)
    (δ : ℝ) (menu : ConditionalPairMenu p δ) (hδ : 0 ≤ δ) :
    ENNReal.ofReal (conditionalInformationLimit p) ≤
      ENNReal.ofReal (δ / Real.log 2) * conditionalExtendedCost p := by
  exact conditionalInformationLimit_le_extendedCost p (δ / Real.log 2)
    (div_nonneg hδ (Real.log_pos one_lt_two).le)
    (conditionalPairMenu_capacity p δ menu hδ)

theorem conditionalPairMenu_limit_cost_lower (p : ConditionalProtocol H0 Bool A Y)
    (δ c budget : ℝ) (menu : ConditionalPairMenu p δ) (hδ : 0 < δ)
    (hb : 0 ≤ budget) (hc : c ≤ conditionalInformationLimit p)
    (hcost : conditionalExtendedCost p ≤ ENNReal.ofReal budget) :
    c * Real.log 2 / δ ≤ budget := by
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hi := conditionalInformationLimit_le_budget p (δ / Real.log 2) budget
    (div_nonneg hδ.le hlog.le) hb
    (conditionalPairMenu_capacity p δ menu hδ.le) hcost
  rw [div_le_iff₀ hδ]
  calc
    c * Real.log 2 ≤ ((δ / Real.log 2) * budget) * Real.log 2 :=
      mul_le_mul_of_nonneg_right (hc.trans hi) hlog.le
    _ = budget * δ := by field_simp; ring

/-- A zero-discrimination conditional menu gains no information even in the limit. -/
theorem conditionalPairMenu_limit_zero (p : ConditionalProtocol H0 Bool A Y)
    (menu : ConditionalPairMenu p 0) :
    conditionalInformationLimit p = 0 := by
  apply conditionalInformationLimit_zero_capacity p
  intro u hu
  have h := conditionalPairMenu_capacity p 0 menu le_rfl u hu
  simpa only [zero_div] using h

end ConditionalPairMenus

end OperatorKO7.Meta.BoundaryObserver.BoundarySingularity
