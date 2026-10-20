import OperatorKO7.Meta.BoundaryObserver.BoundarySingularity

set_option autoImplicit false

/-!
# Attainment of the resolution cost: the singularity is sharp

The majority protocol reads a fair bit through N independent binary symmetric readings of bias ε,
each at unit cost, and stops at N. Its paid cost is N. Decoded by majority over N = 2n + 1 readings,
its error is at most one half of (1 - 4 ε²)^n, and the information it acquires is at least one bit
minus the binary entropy of that error. With n of order log(1/η)/ε² the protocol acquires
1 - h₂(η) bits at a cost of order ε⁻²; the lower bound of ProtocolResolution is c/(4ε²).
The exponent of the singularity is two in both directions.
Relation: finite stopped laws of one named protocol. External trust: none.
-/

namespace OperatorKO7.Meta.BoundaryObserver.ResolutionAttainment

open scoped BigOperators
open ProtocolResolution

/-! ## Depth decompositions of a history bank -/

section Depth
variable {E : Type} [Fintype E]

/-- The product of a function along every history of one depth equals the power of its sum. -/
theorem historySet_level_prod (f : E → ℝ) (N : ℕ) :
    (∑ h ∈ historySet E N, if h.length = N then (h.map f).prod else 0) = (∑ e, f e) ^ N := by
  induction N with
  | zero => simp [historySet]
  | succ N ih =>
    rw [historySet_sum_succ N (fun h => if h.length = N + 1 then (h.map f).prod else 0)]
    have h0 : ¬ (([] : List E).length = N + 1) := by simp
    rw [if_neg h0, zero_add, pow_succ, ← ih, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro h _
    by_cases hl : h.length = N
    · simp [hl, Finset.mul_sum]
    · have hl' : ∀ e : E, ¬ ((h ++ [e]).length = N + 1) := by
        intro e
        simp only [List.length_append, List.length_singleton]
        omega
      simp only [hl', if_false, Finset.sum_const_zero, hl, zero_mul]

/-- A sum over the histories below a horizon is the sum over depths of the sums at each depth. -/
theorem historySet_below_eq_levels (N : ℕ) :
    ∀ F : List E → ℝ, (∑ h ∈ historySet E N, if h.length < N then F h else 0) =
      ∑ ℓ ∈ Finset.range N, ∑ h ∈ historySet E ℓ, if h.length = ℓ then F h else 0 := by
  induction N with
  | zero => intro F; simp [historySet]
  | succ N ih =>
    intro F
    have hlev0 : (∑ h ∈ historySet E 0, if h.length = 0 then F h else 0) = F [] := by
      simp [historySet]
    have hlev : ∀ ℓ, (∑ h ∈ historySet E (ℓ + 1), if h.length = ℓ + 1 then F h else 0) =
        ∑ h ∈ historySet E ℓ, if h.length = ℓ then ∑ e, F (h ++ [e]) else 0 := by
      intro ℓ
      rw [historySet_sum_succ ℓ (fun h => if h.length = ℓ + 1 then F h else 0)]
      have h0 : ¬ (([] : List E).length = ℓ + 1) := by simp
      rw [if_neg h0, zero_add]
      apply Finset.sum_congr rfl
      intro h _
      by_cases hl : h.length = ℓ
      · simp [hl]
      · have hl' : ∀ e : E, ¬ ((h ++ [e]).length = ℓ + 1) := by
          intro e
          simp only [List.length_append, List.length_singleton]
          omega
        simp only [hl', if_false, Finset.sum_const_zero, hl]
    rw [historySet_sum_succ N (fun h => if h.length < N + 1 then F h else 0), Finset.sum_range_succ']
    simp only [hlev, hlev0]
    rw [← ih (fun h => ∑ e, F (h ++ [e]))]
    have h0 : ([] : List E).length < N + 1 := by simp
    rw [if_pos h0, add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro h _
    by_cases hl : h.length < N
    · have hl' : ∀ e : E, (h ++ [e]).length < N + 1 := by
        intro e
        simp only [List.length_append, List.length_singleton]
        omega
      simp only [hl', if_true, hl]
    · have hl' : ∀ e : E, ¬ ((h ++ [e]).length < N + 1) := by
        intro e
        simp only [List.length_append, List.length_singleton]
        omega
      simp only [hl', if_false, Finset.sum_const_zero, hl]

end Depth

/-- Below the first stop, the total mass at every depth is one. -/
theorem levelMass_eq_one {Z A Y : Type} [Fintype Z] [Fintype A] [Fintype Y]
    (p : FiniteProtocol Z A Y) (ℓ : ℕ)
    (hstop : ∀ h : List (A × Y), h.length < ℓ → p.stop h = false) :
    (∑ h ∈ historySet (A × Y) ℓ, if h.length = ℓ then historyMass p h else 0) = 1 := by
  induction ℓ with
  | zero => simp [historySet, historyMass, prefixMass_nil, p.prior.total]
  | succ ℓ ih =>
    rw [historySet_sum_succ ℓ (fun h => if h.length = ℓ + 1 then historyMass p h else 0)]
    have h0 : ¬ (([] : List (A × Y)).length = ℓ + 1) := by simp
    rw [if_neg h0, zero_add, ← ih (fun h hl => hstop h (Nat.lt_succ_of_lt hl))]
    apply Finset.sum_congr rfl
    intro h _
    by_cases hl : h.length = ℓ
    · have hs : p.stop h = false := hstop h (by omega)
      simp only [List.length_append, List.length_singleton, hl, if_true]
      unfold historyMass
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro z _
      rw [Fintype.sum_prod_type]
      have hc := prefixMass_children p h z
      rw [hs] at hc
      simpa using hc
    · have hl' : ∀ e : A × Y, ¬ ((h ++ [e]).length = ℓ + 1) := by
        intro e
        simp only [List.length_append, List.length_singleton]
        omega
      simp only [hl', if_false, Finset.sum_const_zero, hl]

/-! ## T1: the majority protocol -/

/-- The fair prior on a binary label. -/
noncomputable def fairLaw : FiniteLaw Bool where
  mass _ := 1 / 2
  nonnegative _ := by norm_num
  total := by rw [Fintype.sum_bool]; norm_num

theorem fairLaw_entropy : entropy fairLaw.mass = 1 := by
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  rw [entropy_eq_sum, Fintype.sum_bool]
  simp only [fairLaw, entropyTerm, Real.negMulLog, one_div, Real.log_inv]
  field_simp
  ring

/-- One binary symmetric reading of bias ε given the label b. -/
noncomputable def readingLaw (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2) (b : Bool) :
    FiniteLaw Bool where
  mass := binaryKernel ε b
  nonnegative := binaryKernel_nonnegative ε (abs_le.mpr ⟨by linarith, hε1⟩) b
  total := binaryKernel_total ε b

/-- N readings of bias ε about a fair bit: one action, unit cost, stopping at length N. -/
noncomputable def majorityProtocol (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2) (N : ℕ) :
    FiniteProtocol Bool Unit Bool where
  prior := fairLaw
  policy _ := unitLaw
  observation _ _ b := readingLaw ε hε0 hε1 b
  stop h := decide (N ≤ h.length)
  cost _ _ := 1
  cost_nonnegative _ _ := zero_le_one

section Majority
variable (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2) (N : ℕ)

/-- The majority protocol is a binary menu of bias ε. -/
def majorityProtocol_binaryMenu : BinaryMenu (majorityProtocol ε hε0 hε1 N) ε where
  bias _ _ := ε
  bound _ _ := (abs_of_nonneg hε0).le
  source _ _ _ _ := rfl
  reading_cost _ _ := le_rfl

/-- The majority protocol is a pair menu of discrimination eight ε squared. -/
def majorityProtocol_pairMenu :
    BoundarySingularity.PairMenu (majorityProtocol ε hε0 hε1 N) (8 * ε ^ 2) :=
  BoundarySingularity.BinaryMenu.toPairMenu (majorityProtocol_binaryMenu ε hε0 hε1 N)

theorem majorityProtocol_stop (h : List (Unit × Bool)) :
    (majorityProtocol ε hε0 hε1 N).stop h = decide (N ≤ h.length) := rfl

theorem majorityProtocol_stop_false {h : List (Unit × Bool)} (hl : h.length < N) :
    (majorityProtocol ε hε0 hε1 N).stop h = false := by
  rw [majorityProtocol_stop, decide_eq_false_iff_not]
  exact not_le.mpr hl

/-- The likelihood of the readings of a history under the label z. -/
noncomputable def likelihood (z : Bool) (h : List (Unit × Bool)) : ℝ :=
  (h.map (fun ay => binaryKernel ε z ay.2)).prod

theorem likelihood_nil (z : Bool) : likelihood ε z [] = 1 := by simp [likelihood]

theorem likelihood_cons (z : Bool) (ay : Unit × Bool) (h : List (Unit × Bool)) :
    likelihood ε z (ay :: h) = binaryKernel ε z ay.2 * likelihood ε z h := by
  simp [likelihood]

theorem likelihood_append (z : Bool) (h : List (Unit × Bool)) (ay : Unit × Bool) :
    likelihood ε z (h ++ [ay]) = likelihood ε z h * binaryKernel ε z ay.2 := by
  simp [likelihood, List.map_append, List.prod_append]

/-- Before the horizon every prefix carries one half times its likelihood. -/
theorem prefixMass_majority (z : Bool) (h : List (Unit × Bool)) (hl : h.length ≤ N) :
    prefixMass (majorityProtocol ε hε0 hε1 N) z h = 1 / 2 * likelihood ε z h := by
  induction h using List.reverseRecOn with
  | nil => simp [prefixMass_nil, majorityProtocol, fairLaw, likelihood_nil]
  | append_singleton h ay ih =>
    have hlt : h.length < N := by
      simp only [List.length_append, List.length_singleton] at hl
      omega
    rw [prefixMass_append, majorityProtocol_stop_false ε hε0 hε1 N hlt]
    simp only [Bool.false_eq_true, if_false]
    rw [ih hlt.le, likelihood_append]
    change 1 / 2 * likelihood ε z h * 1 * binaryKernel ε z ay.2 = _
    ring

/-- The stopped mass at the horizon lives on the histories of exactly that length. -/
theorem stoppedMass_majority (z : Bool) (h : List (Unit × Bool)) :
    stoppedMass (majorityProtocol ε hε0 hε1 N) N z h =
      if h.length = N then 1 / 2 * likelihood ε z h else 0 := by
  unfold stoppedMass
  by_cases hl : h.length = N
  · rw [if_pos hl, if_pos ⟨hl.le, Or.inr hl⟩, prefixMass_majority ε hε0 hε1 N z h hl.le]
  · rw [if_neg hl, if_neg]
    rintro ⟨hle, hs | he⟩
    · rw [majorityProtocol_stop, decide_eq_true_iff] at hs
      exact hl (le_antisymm hle hs)
    · exact hl he

/-! ## T2: the paid cost at the horizon -/

/-- The majority protocol pays one unit per reading: its cost at horizon N is N. -/
theorem majority_cost :
    expectedCost (majorityProtocol ε hε0 hε1 N) N (historyBank Unit Bool N) = N := by
  unfold expectedCost
  rw [(historyBank_complete Unit Bool N).sum_eq]
  have hterm : ∀ h : List (Unit × Bool),
      (if h.length < N ∧ (majorityProtocol ε hε0 hε1 N).stop h = false then
        historyMass (majorityProtocol ε hε0 hε1 N) h *
          ∑ a : Unit, ((majorityProtocol ε hε0 hε1 N).policy h).mass a *
            (majorityProtocol ε hε0 hε1 N).cost h a
      else 0) = if h.length < N then historyMass (majorityProtocol ε hε0 hε1 N) h else 0 := by
    intro h
    by_cases hl : h.length < N
    · rw [if_pos ⟨hl, majorityProtocol_stop_false ε hε0 hε1 N hl⟩, if_pos hl]
      change historyMass (majorityProtocol ε hε0 hε1 N) h * ∑ _a : Unit, (1 : ℝ) * 1 = _
      simp
    · rw [if_neg (fun hh => hl hh.1), if_neg hl]
  rw [Finset.sum_congr rfl (fun h _ => hterm h), historySet_below_eq_levels N]
  rw [Finset.sum_congr rfl (fun ℓ hℓ => levelMass_eq_one (majorityProtocol ε hε0 hε1 N) ℓ
    (fun h hl => majorityProtocol_stop_false ε hε0 hε1 N
      (lt_of_lt_of_le hl (Finset.mem_range.mp hℓ).le)))]
  simp

/-! ## T4: the majority decoder and its error -/

/-- The number of readings of a history equal to z. -/
def agree (z : Bool) (h : List (Unit × Bool)) : ℕ := h.countP (fun ay => decide (ay.2 = z))

theorem agree_nil (z : Bool) : agree z [] = 0 := rfl

theorem agree_cons (z : Bool) (ay : Unit × Bool) (h : List (Unit × Bool)) :
    agree z (ay :: h) = agree z h + if ay.2 = z then 1 else 0 := by
  simp [agree, List.countP_cons]

theorem agree_le_length (z : Bool) (h : List (Unit × Bool)) : agree z h ≤ h.length :=
  List.countP_le_length

theorem agree_true_add_false (h : List (Unit × Bool)) :
    agree true h + agree false h = h.length := by
  induction h with
  | nil => rfl
  | cons ay h ih =>
    obtain ⟨a, y⟩ := ay
    rw [agree_cons, agree_cons, List.length_cons]
    cases y <;> simp <;> omega

/-- The likelihood is a product of powers in the agreement count. -/
theorem likelihood_eq_pow (z : Bool) (h : List (Unit × Bool)) :
    likelihood ε z h = (1 / 2 + ε) ^ agree z h * (1 / 2 - ε) ^ (h.length - agree z h) := by
  induction h with
  | nil => simp [likelihood_nil, agree_nil]
  | cons ay h ih =>
    rw [likelihood_cons, ih, agree_cons, List.length_cons]
    have hle := agree_le_length z h
    by_cases hy : ay.2 = z
    · rw [if_pos hy]
      simp only [binaryKernel, if_pos hy]
      rw [show h.length + 1 - (agree z h + 1) = h.length - agree z h by omega, pow_succ]
      ring
    · rw [if_neg hy]
      simp only [binaryKernel, if_neg hy]
      rw [show h.length + 1 - (agree z h + 0) = (h.length - agree z h) + 1 by omega, pow_succ]
      ring

/-- The majority value over 2n + 1 readings: true when more than n readings are true. -/
def majority (n : ℕ) (h : List (Unit × Bool)) : Bool := decide (n < agree true h)

/-- The label the majority rejects agrees with at most n of the 2n + 1 readings. -/
theorem agree_not_majority_le (n : ℕ) (h : List (Unit × Bool)) (hl : h.length = 2 * n + 1) :
    agree (!majority n h) h ≤ n := by
  have hs := agree_true_add_false h
  unfold majority
  by_cases hm : n < agree true h
  · rw [decide_eq_true hm, Bool.not_true]
    omega
  · rw [decide_eq_false hm, Bool.not_false]
    omega

/-- The likelihood of the rejected label is at most (1/2 − ε)(1/4 − ε²)^n. -/
theorem likelihood_wrong_le (h0 : 0 ≤ ε) (h1 : ε ≤ 1 / 2) (n : ℕ) (h : List (Unit × Bool))
    (hl : h.length = 2 * n + 1) :
    likelihood ε (!majority n h) h ≤ (1 / 2 - ε) * (1 / 4 - ε ^ 2) ^ n := by
  have hc := agree_not_majority_le n h hl
  rw [likelihood_eq_pow, hl]
  have h1 : (0 : ℝ) ≤ 1 / 2 - ε := by linarith
  have h2 : (1 : ℝ) / 2 - ε ≤ 1 / 2 + ε := by linarith
  have h3 : (0 : ℝ) ≤ 1 / 2 + ε := by linarith
  have hexp : 2 * n + 1 - agree (!majority n h) h = (n + 1) + (n - agree (!majority n h) h) := by
    omega
  rw [hexp, pow_add]
  calc (1 / 2 + ε) ^ agree (!majority n h) h *
        ((1 / 2 - ε) ^ (n + 1) * (1 / 2 - ε) ^ (n - agree (!majority n h) h))
      ≤ (1 / 2 + ε) ^ agree (!majority n h) h *
        ((1 / 2 - ε) ^ (n + 1) * (1 / 2 + ε) ^ (n - agree (!majority n h) h)) := by
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg h3 _)
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg h1 _)
        exact pow_le_pow_left₀ h1 h2 _
    _ = (1 / 2 + ε) ^ (agree (!majority n h) h + (n - agree (!majority n h) h)) *
        (1 / 2 - ε) ^ (n + 1) := by
        rw [pow_add]
        ring
    _ = (1 / 2 - ε) * (1 / 4 - ε ^ 2) ^ n := by
        rw [show agree (!majority n h) h + (n - agree (!majority n h) h) = n by omega, pow_succ,
          show (1 : ℝ) / 4 - ε ^ 2 = (1 / 2 + ε) * (1 / 2 - ε) by ring, mul_pow]
        ring

/-- The mass the stopped law puts on a transcript under the rejected label. -/
theorem wrong_mass_le (h0 : 0 ≤ ε) (h1 : ε ≤ 1 / 2) (n : ℕ) (h : List (Unit × Bool))
    (hl : h.length = 2 * n + 1) :
    1 / 2 * likelihood ε (!majority n h) h ≤
      1 / 2 * (1 - 4 * ε ^ 2) ^ n * (1 / 2) ^ (2 * n + 1) := by
  have hw := likelihood_wrong_le ε h0 h1 n h hl
  have hq : (0 : ℝ) ≤ 1 / 4 - ε ^ 2 := by nlinarith
  have hb : (1 : ℝ) - 4 * ε ^ 2 = 4 * (1 / 4 - ε ^ 2) := by ring
  have h4 : ((4 : ℝ) ^ n) * ((1 / 4) ^ n) = 1 := by
    rw [← mul_pow]
    norm_num
  have hid : (1 / 2 : ℝ) * (1 - 4 * ε ^ 2) ^ n * (1 / 2) ^ (2 * n + 1) =
      1 / 4 * (1 / 4 - ε ^ 2) ^ n := by
    have h2n : ((1 : ℝ) / 2) ^ (2 * n + 1) = (1 / 4) ^ n * (1 / 2) := by
      rw [pow_succ, pow_mul]
      norm_num
    rw [h2n, hb, mul_pow]
    calc 1 / 2 * (4 ^ n * (1 / 4 - ε ^ 2) ^ n) * ((1 / 4) ^ n * (1 / 2)) =
        (4 ^ n * (1 / 4) ^ n) * (1 / 4 * (1 / 4 - ε ^ 2) ^ n) := by ring
      _ = 1 / 4 * (1 / 4 - ε ^ 2) ^ n := by rw [h4, one_mul]
  rw [hid]
  calc 1 / 2 * likelihood ε (!majority n h) h ≤ 1 / 2 * ((1 / 2 - ε) * (1 / 4 - ε ^ 2) ^ n) :=
        mul_le_mul_of_nonneg_left hw (by norm_num)
    _ ≤ 1 / 4 * (1 / 4 - ε ^ 2) ^ n := by
        have hhalf : (1 : ℝ) / 2 - ε ≤ 1 / 2 := by linarith
        have hp := pow_nonneg hq n
        nlinarith

/-- The majority decoder errs with probability at most one half of (1 − 4ε²)^n. -/
theorem majority_error_le (n : ℕ) :
    ∑ h ∈ historySet (Unit × Bool) (2 * n + 1),
        stoppedMass (majorityProtocol ε hε0 hε1 (2 * n + 1)) (2 * n + 1) (!majority n h) h ≤
      1 / 2 * (1 - 4 * ε ^ 2) ^ n := by
  have hlevel := historySet_level_prod (fun _ : Unit × Bool => (1 / 2 : ℝ)) (2 * n + 1)
  have hsum : (∑ _e : Unit × Bool, (1 / 2 : ℝ)) = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_unit,
      Fintype.card_bool, nsmul_eq_mul]
    norm_num
  rw [hsum, one_pow] at hlevel
  calc ∑ h ∈ historySet (Unit × Bool) (2 * n + 1),
        stoppedMass (majorityProtocol ε hε0 hε1 (2 * n + 1)) (2 * n + 1) (!majority n h) h
      ≤ ∑ h ∈ historySet (Unit × Bool) (2 * n + 1), 1 / 2 * (1 - 4 * ε ^ 2) ^ n *
          (if h.length = 2 * n + 1 then (h.map (fun _ : Unit × Bool => (1 / 2 : ℝ))).prod
            else 0) := by
        apply Finset.sum_le_sum
        intro h _
        rw [stoppedMass_majority]
        by_cases hl : h.length = 2 * n + 1
        · rw [if_pos hl, if_pos hl, List.map_const', List.prod_replicate, hl]
          exact wrong_mass_le ε hε0 hε1 n h hl
        · rw [if_neg hl, if_neg hl, mul_zero]
    _ = 1 / 2 * (1 - 4 * ε ^ 2) ^ n := by rw [← Finset.mul_sum, hlevel, mul_one]

/-- Hoeffding's form of the same bound: the error is at most one half of exp(−4nε²). -/
theorem majority_error_le_exp (h0 : 0 ≤ ε) (h1 : ε ≤ 1 / 2) (n : ℕ) :
    1 / 2 * (1 - 4 * ε ^ 2) ^ n ≤ 1 / 2 * Real.exp (-(4 * n * ε ^ 2)) := by
  have h1 : (1 : ℝ) - 4 * ε ^ 2 ≤ Real.exp (-(4 * ε ^ 2)) := by
    have := Real.add_one_le_exp (-(4 * ε ^ 2))
    linarith
  have h0 : (0 : ℝ) ≤ 1 - 4 * ε ^ 2 := by nlinarith
  have hp : (1 - 4 * ε ^ 2) ^ n ≤ Real.exp (-(4 * ε ^ 2)) ^ n := pow_le_pow_left₀ h0 h1 n
  rw [← Real.exp_nat_mul] at hp
  have he : (n : ℝ) * -(4 * ε ^ 2) = -(4 * n * ε ^ 2) := by ring
  rw [he] at hp
  linarith

end Majority

/-! ## T3: the binary Fano bound through concavity -/

/-- The uncertainty of a binary slice is its mass times the binary entropy of its conditional law. -/
theorem massUncertainty_bool (m : Bool → ℝ) (hw : 0 < m true + m false) :
    massUncertainty m =
      (m true + m false) * Real.binEntropy (m true / (m true + m false)) / Real.log 2 := by
  have hne : m true + m false ≠ 0 := hw.ne'
  have hm : m = fun b => (m true + m false) * (m b / (m true + m false)) := by
    funext b
    rw [mul_div_assoc', mul_comm, mul_div_assoc, div_self hne, mul_one]
  have htot : ∑ b, m b / (m true + m false) = 1 := by
    rw [Fintype.sum_bool, div_add_div_same, div_self hne]
  have hf : m false / (m true + m false) = 1 - m true / (m true + m false) := by
    rw [eq_sub_iff_add_eq, div_add_div_same, add_comm, div_self hne]
  conv_lhs => rw [hm]
  rw [massUncertainty_scale, massUncertainty_of_total_one _ htot, entropy_eq_sum,
    Fintype.sum_bool, hf, Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  simp only [entropyTerm]
  ring

/-- Binary Fano: for any decoder, the slice uncertainties of a bank of total mass one sum to at
most the binary entropy of the decoder's error, in bits. -/
theorem sum_massUncertainty_le_binEntropy {H : Type} (s : Finset H) (m : H → Bool → ℝ)
    (hm : ∀ h b, 0 ≤ m h b) (htot : ∑ h ∈ s, (m h true + m h false) = 1) (g : H → Bool) :
    ∑ h ∈ s, massUncertainty (m h) ≤ Real.binEntropy (∑ h ∈ s, m h (!g h)) / Real.log 2 := by
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hterm : ∀ h, massUncertainty (m h) =
      (m h true + m h false) *
        Real.binEntropy (if m h true + m h false = 0 then 0
          else m h (!g h) / (m h true + m h false)) / Real.log 2 := by
    intro h
    by_cases hz : m h true + m h false = 0
    · have h0 : m h true = 0 := by linarith [hm h true, hm h false]
      have h1 : m h false = 0 := by linarith [hm h true, hm h false]
      have hmz : m h = fun _ => 0 := by
        funext b
        cases b
        · exact h1
        · exact h0
      rw [hz, zero_mul, zero_div, hmz]
      exact massUncertainty_zero
    · have hpos : 0 < m h true + m h false :=
        lt_of_le_of_ne (add_nonneg (hm h true) (hm h false)) (Ne.symm hz)
      rw [massUncertainty_bool (m h) hpos, if_neg hz]
      rcases Bool.eq_false_or_eq_true (g h) with hg | hg
      · rw [hg, Bool.not_true,
          show m h false / (m h true + m h false) = 1 - m h true / (m h true + m h false) by
            rw [eq_sub_iff_add_eq, div_add_div_same, add_comm, div_self hz],
          Real.binEntropy_one_sub]
      · rw [hg, Bool.not_false]
  have hwnn : ∀ h ∈ s, 0 ≤ m h true + m h false := fun h _ => add_nonneg (hm h true) (hm h false)
  have hxmem : ∀ h ∈ s, (if m h true + m h false = 0 then (0 : ℝ)
      else m h (!g h) / (m h true + m h false)) ∈ Set.Icc (0 : ℝ) 1 := by
    intro h _
    split_ifs with hz
    · exact ⟨le_rfl, zero_le_one⟩
    · have hpos : 0 < m h true + m h false :=
        lt_of_le_of_ne (add_nonneg (hm h true) (hm h false)) (Ne.symm hz)
      constructor
      · exact div_nonneg (hm h _) hpos.le
      · rw [div_le_one hpos]
        rcases Bool.eq_false_or_eq_true (g h) with hg | hg
        · rw [hg, Bool.not_true]
          linarith [hm h true]
        · rw [hg, Bool.not_false]
          linarith [hm h false]
  have hjensen := Real.strictConcave_binEntropy.concaveOn.le_map_sum hwnn htot hxmem
  simp only [smul_eq_mul] at hjensen
  have hwx : ∑ h ∈ s, (m h true + m h false) * (if m h true + m h false = 0 then (0 : ℝ)
      else m h (!g h) / (m h true + m h false)) = ∑ h ∈ s, m h (!g h) := by
    apply Finset.sum_congr rfl
    intro h _
    split_ifs with hz
    · have h0 : m h (!g h) = 0 := by
        rcases Bool.eq_false_or_eq_true (g h) with hg | hg
        · rw [hg, Bool.not_true]
          linarith [hm h true, hm h false]
        · rw [hg, Bool.not_false]
          linarith [hm h true, hm h false]
      rw [h0, mul_zero]
    · rw [mul_div_assoc', mul_div_cancel_left₀ _ hz]
  calc ∑ h ∈ s, massUncertainty (m h)
      = ∑ h ∈ s, (m h true + m h false) *
          Real.binEntropy (if m h true + m h false = 0 then 0
            else m h (!g h) / (m h true + m h false)) / Real.log 2 :=
        Finset.sum_congr rfl (fun h _ => hterm h)
    _ = (∑ h ∈ s, (m h true + m h false) *
          Real.binEntropy (if m h true + m h false = 0 then 0
            else m h (!g h) / (m h true + m h false))) / Real.log 2 := by
        rw [Finset.sum_div]
    _ ≤ Real.binEntropy (∑ h ∈ s, (m h true + m h false) *
          (if m h true + m h false = 0 then (0 : ℝ)
            else m h (!g h) / (m h true + m h false))) / Real.log 2 :=
        div_le_div_of_nonneg_right hjensen hlog.le
    _ = _ := by rw [hwx]

/-! ## T5: the information of the majority protocol -/

section Target
variable (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2)

/-- The majority protocol over 2n + 1 readings acquires at least one bit minus the binary entropy
of one half of (1 − 4ε²)^n, in bits. -/
theorem majority_information (n : ℕ) :
    1 - Real.binEntropy (1 / 2 * (1 - 4 * ε ^ 2) ^ n) / Real.log 2 ≤
      terminalMI (majorityProtocol ε hε0 hε1 (2 * n + 1)) (2 * n + 1)
        (historyBank Unit Bool (2 * n + 1)) := by
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  rw [terminalMI_eq_entropy_sub _ _ _ (historyBank_complete Unit Bool (2 * n + 1))]
  rw [show (majorityProtocol ε hε0 hε1 (2 * n + 1)).prior.mass = fairLaw.mass from rfl,
    fairLaw_entropy]
  have htot : ∑ h ∈ historySet (Unit × Bool) (2 * n + 1),
      (stoppedMass (majorityProtocol ε hε0 hε1 (2 * n + 1)) (2 * n + 1) true h +
        stoppedMass (majorityProtocol ε hε0 hε1 (2 * n + 1)) (2 * n + 1) false h) = 1 := by
    rw [Finset.sum_add_distrib, historySet_stoppedMass_target_marginal,
      historySet_stoppedMass_target_marginal]
    show fairLaw.mass true + fairLaw.mass false = 1
    norm_num [fairLaw]
  have hfano := sum_massUncertainty_le_binEntropy (historySet (Unit × Bool) (2 * n + 1))
    (fun h z => stoppedMass (majorityProtocol ε hε0 hε1 (2 * n + 1)) (2 * n + 1) z h)
    (fun h z => stoppedMass_nonnegative _ _ z h) htot (majority n)
  have herr := majority_error_le ε hε0 hε1 n
  have hb1 : 1 / 2 * (1 - 4 * ε ^ 2) ^ n ≤ 2⁻¹ := by
    have hp : (1 - 4 * ε ^ 2) ^ n ≤ 1 := pow_le_one₀ (by nlinarith) (by nlinarith)
    linarith
  have hb0 : 0 ≤ ∑ h ∈ historySet (Unit × Bool) (2 * n + 1),
      stoppedMass (majorityProtocol ε hε0 hε1 (2 * n + 1)) (2 * n + 1) (!majority n h) h :=
    Finset.sum_nonneg (fun h _ => stoppedMass_nonnegative _ _ _ h)
  have hnn : (0 : ℝ) ≤ 1 / 2 * (1 - 4 * ε ^ 2) ^ n :=
    mul_nonneg (by norm_num) (pow_nonneg (by nlinarith) n)
  have hmono := Real.binEntropy_strictMonoOn.monotoneOn ⟨hb0, herr.trans hb1⟩ ⟨hnn, hb1⟩ herr
  have hfin := hfano.trans (div_le_div_of_nonneg_right hmono hlog.le)
  linarith

/-- For a target error η in (0, 1/2], the majority protocol with n = ⌈log(1/(2η))/(4ε²)⌉ pairs
acquires 1 − h₂(η)/log 2 bits, pays 2n + 1 readings, and 2n + 1 ≤ log(1/(2η))/(2ε²) + 3. -/
theorem majority_target (hε : 0 < ε) (η : ℝ) (hη0 : 0 < η) (hη1 : η ≤ 1 / 2) :
    1 - Real.binEntropy η / Real.log 2 ≤
        terminalMI (majorityProtocol ε hε0 hε1 (2 * ⌈Real.log (1 / (2 * η)) / (4 * ε ^ 2)⌉₊ + 1))
          (2 * ⌈Real.log (1 / (2 * η)) / (4 * ε ^ 2)⌉₊ + 1)
          (historyBank Unit Bool (2 * ⌈Real.log (1 / (2 * η)) / (4 * ε ^ 2)⌉₊ + 1)) ∧
      expectedCost (majorityProtocol ε hε0 hε1 (2 * ⌈Real.log (1 / (2 * η)) / (4 * ε ^ 2)⌉₊ + 1))
          (2 * ⌈Real.log (1 / (2 * η)) / (4 * ε ^ 2)⌉₊ + 1)
          (historyBank Unit Bool (2 * ⌈Real.log (1 / (2 * η)) / (4 * ε ^ 2)⌉₊ + 1)) =
        ((2 * ⌈Real.log (1 / (2 * η)) / (4 * ε ^ 2)⌉₊ + 1 : ℕ) : ℝ) ∧
      ((2 * ⌈Real.log (1 / (2 * η)) / (4 * ε ^ 2)⌉₊ + 1 : ℕ) : ℝ) ≤
        Real.log (1 / (2 * η)) / (2 * ε ^ 2) + 3 := by
  set n := ⌈Real.log (1 / (2 * η)) / (4 * ε ^ 2)⌉₊ with hn
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hε2 : 0 < 4 * ε ^ 2 := by positivity
  have hL0 : 0 ≤ Real.log (1 / (2 * η)) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hnle : Real.log (1 / (2 * η)) / (4 * ε ^ 2) ≤ n := Nat.le_ceil _
  have hnlt : (n : ℝ) < Real.log (1 / (2 * η)) / (4 * ε ^ 2) + 1 :=
    Nat.ceil_lt_add_one (div_nonneg hL0 hε2.le)
  have herr : 1 / 2 * (1 - 4 * ε ^ 2) ^ n ≤ η := by
    have h1 := majority_error_le_exp ε hε0 hε1 n
    have hle : Real.log (1 / (2 * η)) ≤ 4 * n * ε ^ 2 := by
      rw [div_le_iff₀ hε2] at hnle
      linarith
    have h2 : Real.exp (-(4 * n * ε ^ 2)) ≤ 2 * η := by
      calc Real.exp (-(4 * n * ε ^ 2)) ≤ Real.exp (-Real.log (1 / (2 * η))) :=
            Real.exp_le_exp.mpr (by linarith)
        _ = 2 * η := by rw [Real.exp_neg, Real.exp_log (by positivity), one_div, inv_inv]
    linarith
  refine ⟨?_, majority_cost ε hε0 hε1 (2 * n + 1), ?_⟩
  · have hinfo := majority_information ε hε0 hε1 n
    have hnn : (0 : ℝ) ≤ 1 / 2 * (1 - 4 * ε ^ 2) ^ n :=
      mul_nonneg (by norm_num) (pow_nonneg (by nlinarith) n)
    have hη2 : η ≤ 2⁻¹ := by
      rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num]
      exact hη1
    have hmono := Real.binEntropy_strictMonoOn.monotoneOn ⟨hnn, herr.trans hη2⟩ ⟨hη0.le, hη2⟩ herr
    have hfin := div_le_div_of_nonneg_right hmono hlog.le
    linarith
  · push_cast
    have hhalf : Real.log (1 / (2 * η)) / (4 * ε ^ 2) * 2 = Real.log (1 / (2 * η)) / (2 * ε ^ 2) := by
      field_simp
      ring
    linarith

end Target

/-- The singularity is sharp. Every protocol of binary readings of bias at most ε pays at least
c/(4ε²) readings for c bits at every horizon; and for every target error η in (0, 1/2] the majority
protocol acquires 1 − h₂(η)/log 2 bits at a cost of at most log(1/(2η))/(2ε²) + 3 readings.
Both sides of the resolution cost scale as ε⁻². -/
theorem resolution_cost_two_sided (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2) :
    (∀ {A : Type} [Fintype A] (p : FiniteProtocol Bool A Bool) (c : ℝ), BinaryMenu p ε →
      ∀ (n : ℕ) (bank : List (List (A × Bool))), HistoryBank n bank →
        c ≤ terminalMI p n bank → c / (4 * ε ^ 2) ≤ expectedCost p n bank) ∧
    (∀ η : ℝ, 0 < η → η ≤ 1 / 2 → ∃ N : ℕ,
      1 - Real.binEntropy η / Real.log 2 ≤
          terminalMI (majorityProtocol ε hε0.le hε1 N) N (historyBank Unit Bool N) ∧
        expectedCost (majorityProtocol ε hε0.le hε1 N) N (historyBank Unit Bool N) = N ∧
        (N : ℝ) ≤ Real.log (1 / (2 * η)) / (2 * ε ^ 2) + 3) := by
  refine ⟨fun p c menu n bank hb hc =>
    binaryMenu_cost_lower_bound p ε c menu hε0 hε1 n bank hb hc, ?_⟩
  intro η hη0 hη1
  obtain ⟨h1, h2, h3⟩ := majority_target ε hε0.le hε1 hε0 η hη0 hη1
  exact ⟨_, h1, h2, h3⟩

/-- The same two bounds written with the discrimination δ = 8ε² of the readings: at least
c log 2/δ readings for c bits, and 1 − h₂(η)/log 2 bits within 4 log(1/(2η))/δ + 3 readings. -/
theorem resolution_cost_two_sided_discrimination (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2) :
    (∀ {A : Type} [Fintype A] (p : FiniteProtocol Bool A Bool) (c : ℝ),
      BoundarySingularity.PairMenu p (8 * ε ^ 2) →
      ∀ (n : ℕ) (bank : List (List (A × Bool))), HistoryBank n bank →
        c ≤ terminalMI p n bank → c * Real.log 2 / (8 * ε ^ 2) ≤ expectedCost p n bank) ∧
    (∀ η : ℝ, 0 < η → η ≤ 1 / 2 → ∃ N : ℕ,
      1 - Real.binEntropy η / Real.log 2 ≤
          terminalMI (majorityProtocol ε hε0.le hε1 N) N (historyBank Unit Bool N) ∧
        expectedCost (majorityProtocol ε hε0.le hε1 N) N (historyBank Unit Bool N) = N ∧
        (N : ℝ) ≤ 4 * Real.log (1 / (2 * η)) / (8 * ε ^ 2) + 3) := by
  refine ⟨fun p c menu n bank hb hc =>
    BoundarySingularity.pairMenu_cost_lower_bound p _ c menu (by positivity) n bank hb hc, ?_⟩
  intro η hη0 hη1
  obtain ⟨N, h1, h2, h3⟩ := (resolution_cost_two_sided ε hε0 hε1).2 η hη0 hη1
  refine ⟨N, h1, h2, ?_⟩
  have he : 4 * Real.log (1 / (2 * η)) / (8 * ε ^ 2) = Real.log (1 / (2 * η)) / (2 * ε ^ 2) := by
    field_simp
    ring
  rw [he]
  exact h3

end OperatorKO7.Meta.BoundaryObserver.ResolutionAttainment
