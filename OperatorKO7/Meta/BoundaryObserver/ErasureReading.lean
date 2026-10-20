import OperatorKO7.Meta.BoundaryObserver.TranscriptLaw
import OperatorKO7.Meta.BoundaryObserver.BoundarySingularity
import OperatorKO7.Meta.BoundaryObserver.PairResolution

set_option autoImplicit false

/-!
# The erasure reading and almost-sure recovery

Graph: Audit/ledgers/boundary-theorem/BOUNDARY-THEOREM-MATH-COMPLETION-PROOF-GRAPH.md, N13.
The two label-conditioned rows report the label with probability p and erase otherwise.
The repeated-reading protocol leaves a common all-erasure transcript at every finite horizon.
The first-definite stopping protocol permits exact recovery at finite expected cost.
Relation: the stopped laws of the actual finite protocols. External trust: none.
-/

namespace OperatorKO7.Meta.BoundaryObserver.ErasureReading

open scoped BigOperators ENNReal
open Filter Topology ProtocolResolution TranscriptLaw BoundarySingularity PairResolution

/-- The erasure row reports the input label with mass p and erases with mass 1-p. -/
noncomputable def erasureRow (p : ℝ) (z : Bool) (y : Option Bool) : ℝ :=
  match y with
  | none => 1 - p
  | some b => if b = z then p else 0

/-- Two erasure rows of positive definite-output mass have triangular discrimination 2p. -/
theorem erasure_discrimination (p : ℝ) (hp : 0 < p) :
    discrimination (erasureRow p true) (erasureRow p false) = 2 * p := by
  classical
  have hpne : p ≠ 0 := ne_of_gt hp
  simp [discrimination, erasureRow, Fintype.sum_option]
  field_simp [hpne]
  ring

/-- Each erasure row with 0 < p < 1 is a normalized nonnegative finite law. -/
noncomputable def erasureLaw (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (z : Bool) : FiniteLaw (Option Bool) where
  mass := erasureRow p z
  nonnegative := by
    intro y
    cases y with
    | none =>
      change 0 ≤ 1 - p
      linarith
    | some b =>
      change 0 ≤ if b = z then p else 0
      split_ifs
      · exact hp0.le
      · exact le_rfl
  total := by
    classical
    cases z
    · simp [erasureRow, Fintype.sum_option]
    · simp [erasureRow, Fintype.sum_option]

/-- The transcript containing exactly n erased unit-action readings. -/
def erasureHistory (n : ℕ) : List (Unit × Option Bool) :=
  List.replicate n ((), none)

/-- One more erasure appends one more erased unit-action reading. -/
theorem erasureHistory_succ (n : ℕ) :
    erasureHistory (n + 1) = erasureHistory n ++ [((), none)] := by
  simp [erasureHistory, List.replicate_succ']

/-- The all-erasure transcript has the specified length. -/
theorem erasureHistory_length (n : ℕ) : (erasureHistory n).length = n := by
  simp [erasureHistory]

/-- Every all-erasure length-n record has conditional likelihood (1-p)^n for either label. -/
theorem erasure_likelihood (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (n : ℕ) (z : Bool) :
    PairResolution.likelihood (erasureLaw p hp0 hp1 true)
      (erasureLaw p hp0 hp1 false) z (erasureHistory n) = (1 - p) ^ n := by
  induction n with
  | zero =>
    simp [erasureHistory, PairResolution.likelihood_nil]
  | succ n ih =>
    rw [erasureHistory_succ, PairResolution.likelihood_append, ih, pow_succ]
    cases z <;> simp [PairResolution.row, erasureLaw, erasureRow]

/-- The actual stopped repeated-reading law assigns half the conditional erasure probability to each label. -/
theorem erasure_fixed_horizon_mass (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (n : ℕ) (z : Bool) :
    stoppedMass (PairResolution.repeatProtocol (erasureLaw p hp0 hp1 true)
      (erasureLaw p hp0 hp1 false) n) n z (erasureHistory n) =
      (1 / 2 : ℝ) * (1 - p) ^ n := by
  rw [PairResolution.stoppedMass_repeat]
  simp only [erasureHistory_length, if_true]
  exact congrArg ((1 / 2 : ℝ) * ·) (erasure_likelihood p hp0 hp1 n z)

/-- Every fixed horizon leaves a common positive-mass erasure transcript, so each decoder errs on some label. -/
theorem erasure_fixed_horizon_ambiguous (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (n : ℕ) :
    (∀ z : Bool,
      stoppedMass (PairResolution.repeatProtocol (erasureLaw p hp0 hp1 true)
        (erasureLaw p hp0 hp1 false) n) n z (erasureHistory n) =
        (1 / 2 : ℝ) * (1 - p) ^ n) ∧
    (∀ decoder : List (Unit × Option Bool) → Bool,
      ∃ z : Bool, decoder (erasureHistory n) ≠ z ∧
        0 < stoppedMass (PairResolution.repeatProtocol (erasureLaw p hp0 hp1 true)
          (erasureLaw p hp0 hp1 false) n) n z (erasureHistory n)) := by
  constructor
  · exact erasure_fixed_horizon_mass p hp0 hp1 n
  intro decoder
  have hpos : 0 < (1 / 2 : ℝ) * (1 - p) ^ n :=
    mul_pos (by norm_num) (pow_pos (by linarith) _)
  cases hc : decoder (erasureHistory n) with
  | false =>
    refine ⟨true, by simp, ?_⟩
    simpa [erasure_fixed_horizon_mass] using hpos
  | true =>
    refine ⟨false, by simp, ?_⟩
    simpa [erasure_fixed_horizon_mass] using hpos

/-- The unit-cost protocol reads repeatedly and stops at the first definite label. -/
noncomputable def firstDefinite (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    FiniteProtocol Bool Unit (Option Bool) where
  prior := ResolutionAttainment.fairLaw
  policy _ := unitLaw
  observation _ _ z := erasureLaw p hp0 hp1 z
  stop h := decide (((), some true) ∈ h ∨ ((), some false) ∈ h)
  cost _ _ := 1
  cost_nonnegative _ _ := zero_le_one

/-- The all-erasure transcript has not triggered the first-definite stopping rule. -/
theorem firstDefinite_erasure_stop_false (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (n : ℕ) :
    (firstDefinite p hp0 hp1).stop (erasureHistory n) = false := by
  simp [firstDefinite, erasureHistory]

/-- The common surviving prefix at depth n has mass one half times (1-p)^n per label. -/
theorem firstDefinite_prefixMass_erasure (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (n : ℕ) (z : Bool) :
    prefixMass (firstDefinite p hp0 hp1) z (erasureHistory n) =
      (1 / 2 : ℝ) * (1 - p) ^ n := by
  induction n with
  | zero =>
    simp [erasureHistory, prefixMass_nil, firstDefinite,
      ResolutionAttainment.fairLaw]
  | succ n ih =>
    rw [erasureHistory_succ, prefixMass_append,
      firstDefinite_erasure_stop_false p hp0 hp1 n]
    simp only [Bool.false_eq_true, if_false]
    rw [ih, pow_succ]
    change (1 / 2 : ℝ) * (1 - p) ^ n * 1 * (1 - p) =
      1 / 2 * ((1 - p) ^ n * (1 - p))
    ring

/-- A history containing neither definite symbol is exactly an all-erasure history. -/
private theorem erasure_only_history (h : List (Unit × Option Bool)) :
    ((), some true) ∉ h → ((), some false) ∉ h →
      h = erasureHistory h.length := by
  induction h with
  | nil =>
    intro _ _
    rfl
  | cons x xs ih =>
    intro ht hf
    rcases x with ⟨⟨⟩, o⟩
    cases o with
    | none =>
      have ht' : ((), some true) ∉ xs := by
        intro hm
        exact ht (List.mem_cons_of_mem _ hm)
      have hf' : ((), some false) ∉ xs := by
        intro hm
        exact hf (List.mem_cons_of_mem _ hm)
      have he := ih ht' hf'
      simpa only [erasureHistory, List.length_cons, List.replicate_succ] using
        congrArg (List.cons ((), none)) he
    | some b =>
      cases b with
      | false => exact (hf (by simp)).elim
      | true => exact (ht (by simp)).elim

/-- The only active history at a given depth is the all-erasure history. -/
theorem firstDefinite_active_history (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (h : List (Unit × Option Bool))
    (hs : (firstDefinite p hp0 hp1).stop h = false) :
    h = erasureHistory h.length := by
  have hn : ¬ (((), some true) ∈ h ∨ ((), some false) ∈ h) := by
    simpa [firstDefinite] using hs
  exact erasure_only_history h (fun ht => hn (Or.inl ht))
    (fun hf => hn (Or.inr hf))

/-- At depth n the first-definite protocol retains active label mass (1/2)(1-p)^n. -/
theorem firstDefinite_activeMass (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (n : ℕ) (z : Bool) :
    activeMass (firstDefinite p hp0 hp1) n z = (1 / 2 : ℝ) * (1 - p) ^ n := by
  unfold activeMass
  have hm : erasureHistory n ∈ historySet (Unit × Option Bool) n :=
    (mem_historySet n _).mpr (by simp [erasureHistory])
  rw [Finset.sum_eq_single (erasureHistory n)]
  · simp [erasureHistory_length, firstDefinite_erasure_stop_false,
      firstDefinite_prefixMass_erasure]
  · intro h hh hne
    by_cases hv : h.length = n ∧ (firstDefinite p hp0 hp1).stop h = false
    · have he := firstDefinite_active_history p hp0 hp1 h hv.2
      have he' : h = erasureHistory n := by simpa [hv.1] using he
      exact (hne he').elim
    · simp [hv]
  · intro hn
    exact (hn hm).elim

/-- Every label's active mass tends to zero, so the protocol stops almost surely. -/
theorem firstDefinite_stops (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (z : Bool) :
    Tendsto (fun n => activeMass (firstDefinite p hp0 hp1) n z) atTop (𝓝 0) := by
  have hq0 : (0 : ℝ) ≤ 1 - p := by linarith
  have hq1 : (1 : ℝ) - p < 1 := by linarith
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul (1 / 2 : ℝ)
  simpa [firstDefinite_activeMass] using ht

/-- The geometric recovery cost stays within the stated factor of the information lower bound. -/
theorem erasure_cost_within_factor (p : ℝ) (hp0 : 0 < p) :
    Real.log 2 / (2 * p) ≤ 1 / p := by
  have hlog : Real.log (2 : ℝ) ≤ 1 := by
    calc
      Real.log (2 : ℝ) ≤ 2 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
      _ = 1 := by ring
  have hden : (0 : ℝ) < 2 * p := mul_pos (by norm_num) hp0
  apply (div_le_iff₀ hden).2
  have heq : (1 / p) * (2 * p) = (2 : ℝ) := by
    field_simp [ne_of_gt hp0]
  rw [heq]
  linarith

/-- Any history containing a definite report of another label has zero prefix mass. -/
theorem firstDefinite_prefixMass_wrong (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (z b : Bool) (h : List (Unit × Option Bool)) :
    ((), some b) ∈ h → b ≠ z →
      prefixMass (firstDefinite p hp0 hp1) z h = 0 := by
  induction h using List.reverseRecOn with
  | nil =>
    intro hm _
    simp at hm
  | append_singleton h ay ih =>
    intro hm hb
    have hm' : ((), some b) ∈ h ∨ ((), some b) = ay := by
      simpa [List.mem_append] using hm
    rcases ay with ⟨a, y⟩
    rw [prefixMass_append]
    rcases hm' with hprev | hlast
    · have hz := ih hprev hb
      by_cases hs : (firstDefinite p hp0 hp1).stop h = true
      · simp [hs]
      · simp [hs, hz]
    · have hy : y = some b := (Prod.mk.inj hlast.symm).2
      subst y
      by_cases hs : (firstDefinite p hp0 hp1).stop h = true
      · simp [hs]
      · simp [firstDefinite, erasureLaw, erasureRow, hb]

/-- The decoder returns true exactly when its transcript contains a true report. -/
def firstDefiniteDecoder (h : List (Unit × Option Bool)) : Bool :=
  decide (((), some true) ∈ h)

/-- The decoder never assigns a wrong label to a positive-mass stopped transcript. -/
theorem firstDefinite_zero_error (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (z : Bool) (h : List (Unit × Option Bool))
    (hw : firstDefiniteDecoder h ≠ z) :
    transcriptMass (firstDefinite p hp0 hp1) z h = 0 := by
  by_cases hs : (firstDefinite p hp0 hp1).stop h = true
  · have he : ((), some true) ∈ h ∨ ((), some false) ∈ h := by
      simpa [firstDefinite] using hs
    rw [transcriptMass, if_pos hs]
    cases z with
    | false =>
      have ht : ((), some true) ∈ h := by
        by_contra hn
        exact hw (by simp [firstDefiniteDecoder, hn])
      exact firstDefinite_prefixMass_wrong p hp0 hp1 false true h ht (by decide)
    | true =>
      have hn : ((), some true) ∉ h := by
        intro ht
        exact hw (by simp [firstDefiniteDecoder, ht])
      have hf : ((), some false) ∈ h := he.resolve_left hn
      exact firstDefinite_prefixMass_wrong p hp0 hp1 true false h hf (by decide)
  · simp [transcriptMass, hs]

/-- A binary posterior supported on at most one label has zero conditional uncertainty. -/
private theorem massUncertainty_bool_zero (m : Bool → ℝ)
    (hm : m true = 0 ∨ m false = 0) : massUncertainty m = 0 := by
  rcases hm with ht | hf
  · simp [massUncertainty, entropy_eq_sum, ht, entropyTerm_zero]
  · simp [massUncertainty, entropy_eq_sum, hf, entropyTerm_zero]

/-- Every stopped transcript carries no uncertainty about the fair binary label. -/
theorem firstDefinite_transcript_uncertainty_zero (p : ℝ) (hp0 : 0 < p)
    (hp1 : p < 1) (h : List (Unit × Option Bool)) :
    massUncertainty (fun z => transcriptMass (firstDefinite p hp0 hp1) z h) = 0 := by
  cases hd : firstDefiniteDecoder h with
  | false =>
    apply massUncertainty_bool_zero
    left
    exact firstDefinite_zero_error p hp0 hp1 true h (by simp [hd])
  | true =>
    apply massUncertainty_bool_zero
    right
    exact firstDefinite_zero_error p hp0 hp1 false h (by simp [hd])

/-- Under almost-sure stopping, the transcript information limit is exactly one bit. -/
theorem firstDefinite_information (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    informationLimit (firstDefinite p hp0 hp1) = 1 := by
  rw [informationLimit_eq_transcriptInformation (firstDefinite p hp0 hp1)
    (fun z => firstDefinite_stops p hp0 hp1 z)]
  unfold transcriptInformation transcriptUncertainty
  simp_rw [firstDefinite_transcript_uncertainty_zero p hp0 hp1]
  simp [firstDefinite, ResolutionAttainment.fairLaw_entropy]

/-- Each active history pays its total mass, and stopped histories pay nothing. -/
theorem firstDefinite_historyCost (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (h : List (Unit × Option Bool)) :
    historyCost (firstDefinite p hp0 hp1) h =
      if (firstDefinite p hp0 hp1).stop h = false
      then historyMass (firstDefinite p hp0 hp1) h else 0 := by
  by_cases hs : (firstDefinite p hp0 hp1).stop h = false
  · simp [historyCost, firstDefinite, unitLaw]
  · simp [historyCost, hs]

/-- Paid readings through depth n equal the sum of active probability mass at each prior depth. -/
theorem firstDefinite_expectedCost_sum_active (p : ℝ) (hp0 : 0 < p)
    (hp1 : p < 1) (n : ℕ) :
    expectedCost (firstDefinite p hp0 hp1) n (historyBank Unit (Option Bool) n) =
      ∑ ℓ ∈ Finset.range n, ∑ z : Bool, activeMass (firstDefinite p hp0 hp1) ℓ z := by
  rw [expectedCost_eq_historyCost]
  unfold chargedHistorySet
  rw [Finset.sum_filter]
  rw [ResolutionAttainment.historySet_below_eq_levels n]
  apply Finset.sum_congr rfl
  intro ℓ _
  calc
    (∑ h ∈ historySet (Unit × Option Bool) ℓ,
       if h.length = ℓ then historyCost (firstDefinite p hp0 hp1) h else 0) =
      ∑ h ∈ historySet (Unit × Option Bool) ℓ,
        if h.length = ℓ ∧ (firstDefinite p hp0 hp1).stop h = false
        then historyMass (firstDefinite p hp0 hp1) h else 0 := by
          apply Finset.sum_congr rfl
          intro h _
          rw [firstDefinite_historyCost]
          by_cases hl : h.length = ℓ
          · simp [hl]
          · simp [hl]
    _ = ∑ z : Bool, activeMass (firstDefinite p hp0 hp1) ℓ z := by
          unfold activeMass historyMass
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro h _
          by_cases hv : h.length = ℓ ∧ (firstDefinite p hp0 hp1).stop h = false
          · simp [hv]
          · simp [hv]

/-- The finite expected reading count is the partial geometric sum. -/
theorem firstDefinite_expectedCost_at (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (n : ℕ) :
    expectedCost (firstDefinite p hp0 hp1) n (historyBank Unit (Option Bool) n) =
      ∑ ℓ ∈ Finset.range n, (1 - p) ^ ℓ := by
  rw [firstDefinite_expectedCost_sum_active]
  apply Finset.sum_congr rfl
  intro ℓ _
  calc
    (∑ z : Bool, activeMass (firstDefinite p hp0 hp1) ℓ z) =
      (1 / 2 : ℝ) * (1 - p) ^ ℓ + (1 / 2 : ℝ) * (1 - p) ^ ℓ := by
        simp only [Fintype.sum_bool, firstDefinite_activeMass]
    _ = (1 - p) ^ ℓ := by ring

/-- The finite expected reading count has closed geometric form. -/
theorem firstDefinite_expectedCost_geom (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (n : ℕ) :
    expectedCost (firstDefinite p hp0 hp1) n (historyBank Unit (Option Bool) n) =
      (1 - (1 - p) ^ n) / p := by
  rw [firstDefinite_expectedCost_at]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    have hpne : p ≠ 0 := ne_of_gt hp0
    field_simp [hpne]
    ring

/-- The actual infinite expected reading cost is the finite geometric mean 1/p. -/
theorem firstDefinite_expected_cost (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    extendedCost (firstDefinite p hp0 hp1) = ENNReal.ofReal (1 / p) := by
  have hq0 : (0 : ℝ) ≤ 1 - p := by linarith
  have hq1 : (1 : ℝ) - p < 1 := by linarith
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
  have hgeom : Tendsto (fun n : ℕ => (1 - (1 - p) ^ n) / p)
      atTop (𝓝 (1 / p)) := by
    have hconst : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 (1 : ℝ)) :=
      tendsto_const_nhds
    simpa only [sub_zero] using (hconst.sub hpow).div_const p
  have hcost : Tendsto (fun n : ℕ =>
      expectedCost (firstDefinite p hp0 hp1) n (historyBank Unit (Option Bool) n))
      atTop (𝓝 (1 / p)) := by
    simpa only [firstDefinite_expectedCost_geom] using hgeom
  exact tendsto_nhds_unique
    (finiteCost_tendsto_extendedCost (firstDefinite p hp0 hp1))
    (ENNReal.tendsto_ofReal hcost)

/-- Positive definite-output mass gives discrimination exactly twice that mass for the two erasure rows. -/
theorem erasure_discrimination_eq_two_mul (p : ℝ) (hp0 : 0 < p) :
    discrimination (erasureRow p true) (erasureRow p false) = 2 * p :=
  erasure_discrimination p hp0

/-- Every finite horizon gives both labels a positive all-erasure likelihood and gives every decoder positive joint error mass. -/
theorem erasure_fixed_horizon_positive_error
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (n : ℕ) :
    (∀ z : Bool,
      PairResolution.likelihood (erasureLaw p hp0 hp1 true)
        (erasureLaw p hp0 hp1 false) z (erasureHistory n) =
        (1 - p) ^ n) ∧
    0 < (1 - p) ^ n ∧
    (∀ decoder : List (Unit × Option Bool) → Bool,
      ∃ z : Bool, decoder (erasureHistory n) ≠ z ∧
        0 < stoppedMass (PairResolution.repeatProtocol (erasureLaw p hp0 hp1 true)
          (erasureLaw p hp0 hp1 false) n) n z (erasureHistory n)) := by
  exact ⟨erasure_likelihood p hp0 hp1 n,
    pow_pos (by linarith) n,
    (erasure_fixed_horizon_ambiguous p hp0 hp1 n).2⟩

/-- The first-definite protocol stops almost surely and assigns zero mass to every wrongly decoded stopped transcript. -/
theorem erasure_stop_zero_error (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    (∀ z : Bool, Tendsto
      (fun n => activeMass (firstDefinite p hp0 hp1) n z) atTop (𝓝 0)) ∧
    (∀ z : Bool, ∀ h : List (Unit × Option Bool),
      firstDefiniteDecoder h ≠ z →
        transcriptMass (firstDefinite p hp0 hp1) z h = 0) := by
  exact ⟨firstDefinite_stops p hp0 hp1,
    firstDefinite_zero_error p hp0 hp1⟩

/-- The first-definite protocol costs 1/p on average, meets the information lower bound, and has exact ratio 2/log 2 to that bound. -/
theorem erasure_expected_cost_eq_inv (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    extendedCost (firstDefinite p hp0 hp1) = ENNReal.ofReal (1 / p) ∧
    Real.log 2 / (2 * p) ≤ 1 / p ∧
    1 / p = (2 / Real.log 2) * (Real.log 2 / (2 * p)) := by
  refine ⟨firstDefinite_expected_cost p hp0 hp1,
    erasure_cost_within_factor p hp0, ?_⟩
  have hpne : p ≠ 0 := ne_of_gt hp0
  have hlog : Real.log (2 : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by norm_num))
  field_simp [hpne, hlog]

/-! ## Arbitrary rows: the first output that one row excludes

Graph: Audit/ledgers/boundary-theorem/WAVE6-PROOF-GRAPH.md, node N29. Manuscript: the last three
sentences of `rem:erasure` in `Rahnama_The_Boundary_Theorem.tex`.
The rows `P` and `Q` of a binary-label reading on a finite alphabet are two laws. If each row gives
positive chance to an output that the other row excludes, the unit-cost protocol that stops at the
first such output stops with probability one under both labels, decodes with zero error, acquires
the whole bit of the fair label, and costs, under the label `z`, the reciprocal of the chance under
`z` of an output that the other row excludes. If one support contains the other, a zero-error
protocol of these readings never stops under the label of the smaller support, and its extended
cost is infinite. The erasure protocol `firstDefinite` is the instance at the erasure rows.
-/

/-! ### The cost under one label -/

section LabelCost

variable {Z A W : Type} [Fintype Z] [DecidableEq Z] [Fintype A] [Fintype W]

/-- The point mass at the label `z`. -/
noncomputable def pointLaw (z : Z) : FiniteLaw Z where
  mass w := if w = z then 1 else 0
  nonnegative w := by
    split_ifs
    · exact zero_le_one
    · exact le_rfl
  total := by simp

/-- The protocol run with the label fixed at `z`: the prior is the point mass at `z`, and the
policy, the readings, the stopping rule and the costs are those of `p`. -/
noncomputable def atLabel (p : FiniteProtocol Z A W) (z : Z) : FiniteProtocol Z A W :=
  { p with prior := pointLaw z }

/-- The expected cost of `p` under the label `z`: the extended cost of the run with the label
fixed at `z`, with the value `⊤` for an infinite expectation. -/
noncomputable def labelCost (p : FiniteProtocol Z A W) (z : Z) : ℝ≥0∞ :=
  extendedCost (atLabel p z)

/-- A prefix mass is the prior mass of its label times the prefix mass of the run with that
label fixed. -/
theorem prefixMass_atLabel_self (p : FiniteProtocol Z A W) (z : Z) (h : List (A × W)) :
    prefixMass p z h = p.prior.mass z * prefixMass (atLabel p z) z h := by
  induction h using List.reverseRecOn with
  | nil =>
    rw [prefixMass_nil, prefixMass_nil]
    change p.prior.mass z = p.prior.mass z * (if z = z then (1 : ℝ) else 0)
    rw [if_pos rfl, mul_one]
  | append_singleton h b ih =>
    obtain ⟨a, y⟩ := b
    rw [prefixMass_append, prefixMass_append, ih]
    change _ = p.prior.mass z * (if p.stop h then 0 else
      prefixMass (atLabel p z) z h * (p.policy h).mass a * (p.observation h a z).mass y)
    split_ifs <;> ring

/-- The run with the label fixed at `z` gives zero mass to every other label. -/
theorem prefixMass_atLabel_ne (p : FiniteProtocol Z A W) {z w : Z} (hw : w ≠ z)
    (h : List (A × W)) : prefixMass (atLabel p z) w h = 0 := by
  induction h using List.reverseRecOn with
  | nil =>
    rw [prefixMass_nil]
    change (if w = z then (1 : ℝ) else 0) = 0
    rw [if_neg hw]
  | append_singleton h b ih =>
    obtain ⟨a, y⟩ := b
    rw [prefixMass_append, ih]
    split_ifs <;> ring

/-- The charge of a history is the prior average of its charges under the labels. -/
theorem historyCost_eq_sum_atLabel (p : FiniteProtocol Z A W) (h : List (A × W)) :
    historyCost p h = ∑ z, p.prior.mass z * historyCost (atLabel p z) h := by
  have hm : ∀ z, historyMass (atLabel p z) h = prefixMass (atLabel p z) z h := by
    intro z
    unfold historyMass
    exact Finset.sum_eq_single z (fun w _ hw => prefixMass_atLabel_ne p hw h)
      (fun hz => absurd (Finset.mem_univ z) hz)
  unfold historyCost
  change (if p.stop h = false then
      historyMass p h * ∑ a, (p.policy h).mass a * p.cost h a else 0) =
    ∑ z, p.prior.mass z * (if p.stop h = false then
      historyMass (atLabel p z) h * ∑ a, (p.policy h).mass a * p.cost h a else 0)
  split_ifs
  · rw [show historyMass p h = ∑ z, p.prior.mass z * prefixMass (atLabel p z) z h from
        Finset.sum_congr rfl (fun z _ => prefixMass_atLabel_self p z h), Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro z _
    rw [hm z]
    ring
  · simp

/-- The law of total expectation for the extended cost: the cost of `p` is the prior average of
its costs under the labels, in `ℝ≥0∞`. -/
theorem extendedCost_eq_sum_labelCost (p : FiniteProtocol Z A W) :
    extendedCost p = ∑ z, ENNReal.ofReal (p.prior.mass z) * labelCost p z := by
  have hterm : ∀ h, ENNReal.ofReal (historyCost p h) =
      ∑ z, ENNReal.ofReal (p.prior.mass z) * ENNReal.ofReal (historyCost (atLabel p z) h) := by
    intro h
    rw [historyCost_eq_sum_atLabel, ENNReal.ofReal_sum_of_nonneg]
    · apply Finset.sum_congr rfl
      intro z _
      exact ENNReal.ofReal_mul (p.prior.nonnegative z)
    · intro z _
      exact mul_nonneg (p.prior.nonnegative z) (historyCost_nonnegative _ h)
  rw [extendedCost_eq_tsum_historyCost]
  simp_rw [hterm]
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  apply Finset.sum_congr rfl
  intro z _
  rw [ENNReal.tsum_mul_left, labelCost, extendedCost_eq_tsum_historyCost]

end LabelCost

/-! ### The protocol of the first exclusive output -/

section FirstExclusive

variable {Y : Type} [Fintype Y]

/-- The chance under the row `P` of an output that the row `Q` excludes. -/
noncomputable def exclusiveMass (P Q : FiniteLaw Y) : ℝ :=
  ∑ y, if Q.mass y = 0 then P.mass y else 0

theorem exclusiveMass_nonneg (P Q : FiniteLaw Y) : 0 ≤ exclusiveMass P Q := by
  unfold exclusiveMass
  apply Finset.sum_nonneg
  intro y _
  split_ifs
  · exact P.nonnegative y
  · exact le_rfl

theorem exclusiveMass_le_one (P Q : FiniteLaw Y) : exclusiveMass P Q ≤ 1 := by
  unfold exclusiveMass
  calc (∑ y, if Q.mass y = 0 then P.mass y else 0) ≤ ∑ y, P.mass y := by
        apply Finset.sum_le_sum
        intro y _
        split_ifs
        · exact le_rfl
        · exact P.nonnegative y
    _ = 1 := P.total

/-- The exclusive chance is positive exactly if some output of positive `P`-chance has zero
`Q`-chance. -/
theorem exclusiveMass_pos_iff (P Q : FiniteLaw Y) :
    0 < exclusiveMass P Q ↔ ∃ y, 0 < P.mass y ∧ Q.mass y = 0 := by
  constructor
  · intro h
    by_contra hn
    push_neg at hn
    have hz : exclusiveMass P Q = 0 := by
      unfold exclusiveMass
      apply Finset.sum_eq_zero
      intro y _
      split_ifs with hq
      · exact le_antisymm (not_lt.mp fun hp => hn y hp hq) (P.nonnegative y)
      · rfl
    linarith
  · rintro ⟨y, hy, hq⟩
    unfold exclusiveMass
    apply Finset.sum_pos'
    · intro w _
      split_ifs
      · exact P.nonnegative w
      · exact le_rfl
    · exact ⟨y, Finset.mem_univ y, by rw [if_pos hq]; exact hy⟩

/-- The chance under the label `z` of an output that the row of the other label excludes. -/
noncomputable def labelExclusive (P Q : FiniteLaw Y) (z : Bool) : ℝ :=
  exclusiveMass (row P Q z) (row P Q (!z))

theorem labelExclusive_true (P Q : FiniteLaw Y) :
    labelExclusive P Q true = exclusiveMass P Q := rfl

theorem labelExclusive_false (P Q : FiniteLaw Y) :
    labelExclusive P Q false = exclusiveMass Q P := rfl

theorem labelExclusive_nonneg (P Q : FiniteLaw Y) (z : Bool) : 0 ≤ labelExclusive P Q z :=
  exclusiveMass_nonneg _ _

theorem labelExclusive_le_one (P Q : FiniteLaw Y) (z : Bool) : labelExclusive P Q z ≤ 1 :=
  exclusiveMass_le_one _ _

/-- An output is decisive if one of the two rows excludes it. -/
def Decisive (P Q : FiniteLaw Y) (y : Y) : Prop :=
  P.mass y = 0 ∨ Q.mass y = 0

noncomputable instance decisiveDecidable (P Q : FiniteLaw Y) : DecidablePred (Decisive P Q) :=
  fun y => inferInstanceAs (Decidable (P.mass y = 0 ∨ Q.mass y = 0))

/-- Unit-cost readings with rows `P` and `Q` under the label prior `μ`, stopped at the first
decisive output. -/
noncomputable def firstExclusiveWith (μ : FiniteLaw Bool) (P Q : FiniteLaw Y) :
    FiniteProtocol Bool Unit Y where
  prior := μ
  policy _ := unitLaw
  observation _ _ z := row P Q z
  stop h := decide (∃ ay ∈ h, Decisive P Q ay.2)
  cost _ _ := 1
  cost_nonnegative _ _ := zero_le_one

/-- The protocol of the remark: the fair label, read until the first decisive output. -/
noncomputable def firstExclusive (P Q : FiniteLaw Y) : FiniteProtocol Bool Unit Y :=
  firstExclusiveWith ResolutionAttainment.fairLaw P Q

/-- The decoder returns `true` exactly if the transcript holds an output that `Q` excludes. On a
stopped transcript of positive chance the stopping output is the only decisive output, so the
decoder returns the label of the row that keeps the stopping output. -/
noncomputable def firstExclusiveDecoder (Q : FiniteLaw Y) (h : List (Unit × Y)) : Bool :=
  decide (∃ ay ∈ h, Q.mass ay.2 = 0)

/-- The run with the label fixed at `z` is the same protocol with the point-mass prior. -/
theorem firstExclusive_atLabel (P Q : FiniteLaw Y) (z : Bool) :
    atLabel (firstExclusive P Q) z = firstExclusiveWith (pointLaw z) P Q := rfl

theorem firstExclusiveWith_stop_iff (μ : FiniteLaw Bool) (P Q : FiniteLaw Y)
    (h : List (Unit × Y)) :
    (firstExclusiveWith μ P Q).stop h = true ↔ ∃ ay ∈ h, Decisive P Q ay.2 := by
  change decide (∃ ay ∈ h, Decisive P Q ay.2) = true ↔ _
  exact decide_eq_true_iff

theorem firstExclusiveWith_stop_nil (μ : FiniteLaw Bool) (P Q : FiniteLaw Y) :
    (firstExclusiveWith μ P Q).stop [] = false := by
  cases hs : (firstExclusiveWith μ P Q).stop [] with
  | false => rfl
  | true =>
    obtain ⟨ay, hm, _⟩ := (firstExclusiveWith_stop_iff μ P Q []).mp hs
    simp at hm

/-- One more reading stops the protocol exactly if it had stopped or the new output is decisive. -/
theorem firstExclusiveWith_stop_append (μ : FiniteLaw Bool) (P Q : FiniteLaw Y)
    (h : List (Unit × Y)) (ay : Unit × Y) :
    (firstExclusiveWith μ P Q).stop (h ++ [ay]) = true ↔
      (firstExclusiveWith μ P Q).stop h = true ∨ Decisive P Q ay.2 := by
  rw [firstExclusiveWith_stop_iff, firstExclusiveWith_stop_iff]
  constructor
  · rintro ⟨b, hb, hd⟩
    rcases List.mem_append.mp hb with hb | hb
    · exact Or.inl ⟨b, hb, hd⟩
    · rw [List.mem_singleton] at hb
      subst hb
      exact Or.inr hd
  · rintro (⟨b, hb, hd⟩ | hd)
    · exact ⟨b, List.mem_append_left _ hb, hd⟩
    · exact ⟨ay, List.mem_append_right _ (List.mem_singleton_self ay), hd⟩

theorem firstExclusiveWith_stop_append_false (μ : FiniteLaw Bool) (P Q : FiniteLaw Y)
    (h : List (Unit × Y)) (ay : Unit × Y) :
    (firstExclusiveWith μ P Q).stop (h ++ [ay]) = false ↔
      (firstExclusiveWith μ P Q).stop h = false ∧ ¬ Decisive P Q ay.2 := by
  have key := firstExclusiveWith_stop_append μ P Q h ay
  constructor
  · intro hf
    constructor
    · cases hs : (firstExclusiveWith μ P Q).stop h with
      | false => rfl
      | true =>
        have hc := key.mpr (Or.inl hs)
        rw [hf] at hc
        exact absurd hc Bool.false_ne_true
    · intro hd
      have hc := key.mpr (Or.inr hd)
      rw [hf] at hc
      exact absurd hc Bool.false_ne_true
  · rintro ⟨hs, hd⟩
    cases hc : (firstExclusiveWith μ P Q).stop (h ++ [ay]) with
    | false => rfl
    | true =>
      rcases key.mp hc with h1 | h1
      · rw [hs] at h1
        exact absurd h1 Bool.false_ne_true
      · exact absurd h1 hd

/-- A history holding an output of zero chance under the label `z` has zero mass under `z`. -/
theorem firstExclusiveWith_prefixMass_eq_zero (μ : FiniteLaw Bool) (P Q : FiniteLaw Y)
    (z : Bool) (h : List (Unit × Y)) :
    (∃ ay ∈ h, (row P Q z).mass ay.2 = 0) → prefixMass (firstExclusiveWith μ P Q) z h = 0 := by
  induction h using List.reverseRecOn with
  | nil =>
    rintro ⟨ay, hm, _⟩
    simp at hm
  | append_singleton h b ih =>
    rintro ⟨c, hm, hz⟩
    obtain ⟨a, y⟩ := b
    rw [prefixMass_append]
    split_ifs with hs
    · rfl
    · rcases List.mem_append.mp hm with hprev | hlast
      · rw [ih ⟨c, hprev, hz⟩, zero_mul, zero_mul]
      · have hc : c = (a, y) := List.mem_singleton.mp hlast
        subst hc
        change prefixMass (firstExclusiveWith μ P Q) z h * unitLaw.mass a *
          (row P Q z).mass y = 0
        rw [show (row P Q z).mass y = 0 from hz, mul_zero]

/-- The chance under the label `z` of a non-decisive output. -/
theorem continue_mass (P Q : FiniteLaw Y) (z : Bool) :
    (∑ y, if Decisive P Q y then 0 else (row P Q z).mass y) = 1 - labelExclusive P Q z := by
  have hsplit : ∀ y, (if Decisive P Q y then 0 else (row P Q z).mass y) =
      (row P Q z).mass y -
        (if (row P Q (!z)).mass y = 0 then (row P Q z).mass y else 0) := by
    intro y
    cases z with
    | true =>
      change (if Decisive P Q y then 0 else P.mass y) =
        P.mass y - (if Q.mass y = 0 then P.mass y else 0)
      by_cases hq : Q.mass y = 0
      · rw [if_pos (show Decisive P Q y from Or.inr hq), if_pos hq, sub_self]
      · by_cases hp : P.mass y = 0
        · rw [if_pos (show Decisive P Q y from Or.inl hp), if_neg hq, hp, sub_zero]
        · rw [if_neg (show ¬ Decisive P Q y from fun hd => hd.elim hp hq), if_neg hq,
            sub_zero]
    | false =>
      change (if Decisive P Q y then 0 else Q.mass y) =
        Q.mass y - (if P.mass y = 0 then Q.mass y else 0)
      by_cases hp : P.mass y = 0
      · rw [if_pos (show Decisive P Q y from Or.inl hp), if_pos hp, sub_self]
      · by_cases hq : Q.mass y = 0
        · rw [if_pos (show Decisive P Q y from Or.inr hq), if_neg hp, hq, sub_zero]
        · rw [if_neg (show ¬ Decisive P Q y from fun hd => hd.elim hp hq), if_neg hp,
            sub_zero]
  rw [Finset.sum_congr rfl (fun y _ => hsplit y), Finset.sum_sub_distrib, (row P Q z).total]
  rfl

/-- One more reading multiplies the running mass of a history by the chance of a non-decisive
output. -/
theorem firstExclusiveWith_active_children (μ : FiniteLaw Bool) (P Q : FiniteLaw Y)
    (n : ℕ) (z : Bool) (h : List (Unit × Y)) :
    (∑ e : Unit × Y,
      if (h ++ [e]).length = n + 1 ∧ (firstExclusiveWith μ P Q).stop (h ++ [e]) = false
      then prefixMass (firstExclusiveWith μ P Q) z (h ++ [e]) else 0) =
    (if h.length = n ∧ (firstExclusiveWith μ P Q).stop h = false
      then prefixMass (firstExclusiveWith μ P Q) z h else 0) * (1 - labelExclusive P Q z) := by
  by_cases hc : h.length = n ∧ (firstExclusiveWith μ P Q).stop h = false
  · rw [if_pos hc, ← continue_mass P Q z, Finset.mul_sum, Fintype.sum_prod_type,
      Fintype.sum_unique]
    apply Finset.sum_congr rfl
    intro y _
    by_cases hd : Decisive P Q y
    · rw [if_pos hd, mul_zero, if_neg]
      rintro ⟨_, hs⟩
      exact ((firstExclusiveWith_stop_append_false μ P Q h (default, y)).mp hs).2 hd
    · rw [if_neg hd, if_pos]
      · rw [prefixMass_append, if_neg (by rw [hc.2]; decide)]
        change prefixMass (firstExclusiveWith μ P Q) z h * unitLaw.mass default *
          (row P Q z).mass y = prefixMass (firstExclusiveWith μ P Q) z h * (row P Q z).mass y
        simp [unitLaw]
      · refine ⟨by simp [hc.1], ?_⟩
        exact (firstExclusiveWith_stop_append_false μ P Q h (default, y)).mpr ⟨hc.2, hd⟩
  · rw [if_neg hc, zero_mul]
    apply Finset.sum_eq_zero
    intro e _
    rw [if_neg]
    rintro ⟨hl, hs⟩
    apply hc
    refine ⟨?_, ((firstExclusiveWith_stop_append_false μ P Q h e).mp hs).1⟩
    simp only [List.length_append, List.length_singleton] at hl
    omega

/-- At depth `n` the label `z` keeps the running mass `μ z (1 - a_z)^n`, with `a_z` the chance
under `z` of an output that the other row excludes. -/
theorem firstExclusiveWith_activeMass (μ : FiniteLaw Bool) (P Q : FiniteLaw Y)
    (n : ℕ) (z : Bool) :
    activeMass (firstExclusiveWith μ P Q) n z = μ.mass z * (1 - labelExclusive P Q z) ^ n := by
  induction n with
  | zero =>
    unfold activeMass
    simp only [historySet, Finset.sum_singleton]
    rw [if_pos ⟨rfl, firstExclusiveWith_stop_nil μ P Q⟩, prefixMass_nil, pow_zero, mul_one]
    rfl
  | succ n ih =>
    unfold activeMass at ih ⊢
    have h0 : (if ([] : List (Unit × Y)).length = n + 1 ∧
        (firstExclusiveWith μ P Q).stop [] = false
        then prefixMass (firstExclusiveWith μ P Q) z [] else 0) = 0 :=
      if_neg (fun hc => Nat.succ_ne_zero n hc.1.symm)
    rw [historySet_sum_succ, h0, zero_add,
      Finset.sum_congr rfl (fun h _ => firstExclusiveWith_active_children μ P Q n z h),
      ← Finset.sum_mul, ih, pow_succ]
    ring

/-- A label with a positive exclusive chance stops with probability one. -/
theorem firstExclusiveWith_stops (μ : FiniteLaw Bool) (P Q : FiniteLaw Y) (z : Bool)
    (hz : 0 < labelExclusive P Q z) :
    Tendsto (fun n => activeMass (firstExclusiveWith μ P Q) n z) atTop (𝓝 0) := by
  have hq0 : 0 ≤ 1 - labelExclusive P Q z := by linarith [labelExclusive_le_one P Q z]
  have hq1 : 1 - labelExclusive P Q z < 1 := by linarith
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul (μ.mass z)
  simpa [firstExclusiveWith_activeMass] using ht

/-- The decoder never assigns a wrong label to a transcript of positive mass. -/
theorem firstExclusiveWith_zero_error (μ : FiniteLaw Bool) (P Q : FiniteLaw Y)
    (z : Bool) (h : List (Unit × Y)) (hw : firstExclusiveDecoder Q h ≠ z) :
    transcriptMass (firstExclusiveWith μ P Q) z h = 0 := by
  cases z with
  | true =>
    have hn : ¬ ∃ ay ∈ h, Q.mass ay.2 = 0 := fun he => hw (decide_eq_true he)
    unfold transcriptMass
    split_ifs with hs
    · obtain ⟨ay, hm, hd⟩ := (firstExclusiveWith_stop_iff μ P Q h).mp hs
      have hp : P.mass ay.2 = 0 := hd.resolve_right (fun hq => hn ⟨ay, hm, hq⟩)
      exact firstExclusiveWith_prefixMass_eq_zero μ P Q true h ⟨ay, hm, hp⟩
    · rfl
  | false =>
    have he : ∃ ay ∈ h, Q.mass ay.2 = 0 := by
      by_contra hn
      exact hw (decide_eq_false hn)
    unfold transcriptMass
    split_ifs
    · exact firstExclusiveWith_prefixMass_eq_zero μ P Q false h he
    · rfl

/-- Every stopped transcript carries no uncertainty about the label. -/
theorem firstExclusiveWith_transcript_uncertainty_zero (μ : FiniteLaw Bool)
    (P Q : FiniteLaw Y) (h : List (Unit × Y)) :
    massUncertainty (fun z => transcriptMass (firstExclusiveWith μ P Q) z h) = 0 := by
  cases hd : firstExclusiveDecoder Q h with
  | false =>
    apply massUncertainty_bool_zero
    left
    exact firstExclusiveWith_zero_error μ P Q true h (by simp [hd])
  | true =>
    apply massUncertainty_bool_zero
    right
    exact firstExclusiveWith_zero_error μ P Q false h (by simp [hd])

/-- The protocol acquires the whole entropy of the label prior. -/
theorem firstExclusiveWith_information (μ : FiniteLaw Bool) (P Q : FiniteLaw Y)
    (hpos : ∀ z, 0 < μ.mass z → 0 < labelExclusive P Q z) :
    informationLimit (firstExclusiveWith μ P Q) = entropy μ.mass := by
  rw [informationLimit_eq_transcriptInformation (firstExclusiveWith μ P Q)
    (stops_of_positive_prior (firstExclusiveWith μ P Q)
      (fun z hz => firstExclusiveWith_stops μ P Q z (hpos z hz)))]
  unfold transcriptInformation transcriptUncertainty
  simp_rw [firstExclusiveWith_transcript_uncertainty_zero μ P Q]
  rw [tsum_zero, sub_zero]
  rfl

/-- Each active history pays its total mass, and stopped histories pay nothing. -/
theorem firstExclusiveWith_historyCost (μ : FiniteLaw Bool) (P Q : FiniteLaw Y)
    (h : List (Unit × Y)) :
    historyCost (firstExclusiveWith μ P Q) h =
      if (firstExclusiveWith μ P Q).stop h = false
      then historyMass (firstExclusiveWith μ P Q) h else 0 := by
  unfold historyCost
  by_cases hs : (firstExclusiveWith μ P Q).stop h = false
  · rw [if_pos hs, if_pos hs, Fintype.sum_unique]
    change historyMass (firstExclusiveWith μ P Q) h * ((1 : ℝ) * 1) = _
    ring
  · rw [if_neg hs, if_neg hs]

/-- Paid readings through depth `n` are the running mass summed over the earlier depths. -/
theorem firstExclusiveWith_expectedCost_sum_active (μ : FiniteLaw Bool) (P Q : FiniteLaw Y)
    (n : ℕ) :
    expectedCost (firstExclusiveWith μ P Q) n (historyBank Unit Y n) =
      ∑ ℓ ∈ Finset.range n, ∑ z : Bool, activeMass (firstExclusiveWith μ P Q) ℓ z := by
  rw [expectedCost_eq_historyCost]
  unfold chargedHistorySet
  rw [Finset.sum_filter]
  rw [ResolutionAttainment.historySet_below_eq_levels n]
  apply Finset.sum_congr rfl
  intro ℓ _
  calc
    (∑ h ∈ historySet (Unit × Y) ℓ,
       if h.length = ℓ then historyCost (firstExclusiveWith μ P Q) h else 0) =
      ∑ h ∈ historySet (Unit × Y) ℓ,
        if h.length = ℓ ∧ (firstExclusiveWith μ P Q).stop h = false
        then historyMass (firstExclusiveWith μ P Q) h else 0 := by
          apply Finset.sum_congr rfl
          intro h _
          rw [firstExclusiveWith_historyCost]
          by_cases hl : h.length = ℓ
          · simp [hl]
          · simp [hl]
    _ = ∑ z : Bool, activeMass (firstExclusiveWith μ P Q) ℓ z := by
          unfold activeMass historyMass
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro h _
          by_cases hv : h.length = ℓ ∧ (firstExclusiveWith μ P Q).stop h = false
          · simp [hv]
          · simp [hv]

/-- The finite expected reading count is a prior average of partial geometric sums. -/
theorem firstExclusiveWith_expectedCost_at (μ : FiniteLaw Bool) (P Q : FiniteLaw Y)
    (n : ℕ) :
    expectedCost (firstExclusiveWith μ P Q) n (historyBank Unit Y n) =
      ∑ z : Bool, μ.mass z * ∑ ℓ ∈ Finset.range n, (1 - labelExclusive P Q z) ^ ℓ := by
  rw [firstExclusiveWith_expectedCost_sum_active, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ℓ _
  rw [firstExclusiveWith_activeMass]

/-- The finite expected reading counts converge to the prior average of the reciprocal
exclusive chances. -/
theorem firstExclusiveWith_cost_tendsto (μ : FiniteLaw Bool) (P Q : FiniteLaw Y)
    (hpos : ∀ z, 0 < μ.mass z → 0 < labelExclusive P Q z) :
    Tendsto (fun n => expectedCost (firstExclusiveWith μ P Q) n (historyBank Unit Y n))
      atTop (𝓝 (∑ z : Bool, μ.mass z / labelExclusive P Q z)) := by
  simp_rw [firstExclusiveWith_expectedCost_at]
  apply tendsto_finset_sum
  intro z _
  rcases (μ.nonnegative z).eq_or_lt with h0 | h0
  · rw [← h0]
    simp
  · have ha := hpos z h0
    have hgeom : HasSum (fun ℓ : ℕ => (1 - labelExclusive P Q z) ^ ℓ)
        (1 - (1 - labelExclusive P Q z))⁻¹ :=
      hasSum_geometric_of_lt_one (by linarith [labelExclusive_le_one P Q z]) (by linarith)
    have ht := hgeom.tendsto_sum_nat.const_mul (μ.mass z)
    rw [sub_sub_cancel] at ht
    simpa [div_eq_mul_inv] using ht

/-- The extended cost is the prior average of the reciprocal exclusive chances. -/
theorem firstExclusiveWith_extendedCost (μ : FiniteLaw Bool) (P Q : FiniteLaw Y)
    (hpos : ∀ z, 0 < μ.mass z → 0 < labelExclusive P Q z) :
    extendedCost (firstExclusiveWith μ P Q) =
      ENNReal.ofReal (∑ z : Bool, μ.mass z / labelExclusive P Q z) :=
  tendsto_nhds_unique (finiteCost_tendsto_extendedCost (firstExclusiveWith μ P Q))
    (ENNReal.tendsto_ofReal (firstExclusiveWith_cost_tendsto μ P Q hpos))

/-- Under every label prior the extended cost is at most the larger reciprocal exclusive chance. -/
theorem firstExclusiveWith_extendedCost_le_max (μ : FiniteLaw Bool) (P Q : FiniteLaw Y)
    (hP : 0 < exclusiveMass P Q) (hQ : 0 < exclusiveMass Q P) :
    extendedCost (firstExclusiveWith μ P Q) ≤
      ENNReal.ofReal (max (1 / exclusiveMass P Q) (1 / exclusiveMass Q P)) := by
  rw [firstExclusiveWith_extendedCost μ P Q
    (fun z _ => by cases z with | false => exact hQ | true => exact hP)]
  apply ENNReal.ofReal_le_ofReal
  have htot := μ.total
  rw [Fintype.sum_bool] at htot ⊢
  have h1 : μ.mass true / labelExclusive P Q true ≤
      μ.mass true * max (1 / exclusiveMass P Q) (1 / exclusiveMass Q P) := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left (le_max_left _ _) (μ.nonnegative true)
  have h2 : μ.mass false / labelExclusive P Q false ≤
      μ.mass false * max (1 / exclusiveMass P Q) (1 / exclusiveMass Q P) := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left (le_max_right _ _) (μ.nonnegative false)
  calc μ.mass true / labelExclusive P Q true + μ.mass false / labelExclusive P Q false ≤
      μ.mass true * max (1 / exclusiveMass P Q) (1 / exclusiveMass Q P) +
        μ.mass false * max (1 / exclusiveMass P Q) (1 / exclusiveMass Q P) := add_le_add h1 h2
    _ = max (1 / exclusiveMass P Q) (1 / exclusiveMass Q P) := by
      rw [← add_mul, htot, one_mul]

/-- The expected cost under the label `z` is the reciprocal of the chance under `z` of an output
that the other row excludes. -/
theorem firstExclusive_labelCost (P Q : FiniteLaw Y) (z : Bool)
    (hz : 0 < labelExclusive P Q z) :
    labelCost (firstExclusive P Q) z = ENNReal.ofReal (1 / labelExclusive P Q z) := by
  unfold labelCost
  rw [firstExclusive_atLabel, firstExclusiveWith_extendedCost (pointLaw z) P Q]
  · congr 1
    rw [Fintype.sum_bool]
    cases z <;> simp [pointLaw]
  · intro w hw
    by_cases hwz : w = z
    · rw [hwz]
      exact hz
    · simp [pointLaw, hwz] at hw

/-- Each label's expected cost is at most the larger of the two reciprocals. -/
theorem firstExclusive_labelCost_le_max (P Q : FiniteLaw Y) (hP : 0 < exclusiveMass P Q)
    (hQ : 0 < exclusiveMass Q P) (z : Bool) :
    labelCost (firstExclusive P Q) z ≤
      ENNReal.ofReal (max (1 / exclusiveMass P Q) (1 / exclusiveMass Q P)) := by
  cases z with
  | false =>
    rw [firstExclusive_labelCost P Q false hQ]
    exact ENNReal.ofReal_le_ofReal (le_max_right _ _)
  | true =>
    rw [firstExclusive_labelCost P Q true hP]
    exact ENNReal.ofReal_le_ofReal (le_max_left _ _)

/-- The expected cost for the fair label is the mean of the two reciprocal exclusive chances. -/
theorem firstExclusive_extendedCost (P Q : FiniteLaw Y) (hP : 0 < exclusiveMass P Q)
    (hQ : 0 < exclusiveMass Q P) :
    extendedCost (firstExclusive P Q) =
      ENNReal.ofReal ((1 / exclusiveMass P Q + 1 / exclusiveMass Q P) / 2) := by
  unfold firstExclusive
  rw [firstExclusiveWith_extendedCost ResolutionAttainment.fairLaw P Q
    (fun z _ => by cases z with | false => exact hQ | true => exact hP)]
  congr 1
  rw [Fintype.sum_bool]
  simp only [ResolutionAttainment.fairLaw, labelExclusive_true, labelExclusive_false]
  ring

/-- The protocol of the remark acquires the whole bit of the fair label. -/
theorem firstExclusive_information (P Q : FiniteLaw Y) (hP : 0 < exclusiveMass P Q)
    (hQ : 0 < exclusiveMass Q P) : informationLimit (firstExclusive P Q) = 1 := by
  unfold firstExclusive
  rw [firstExclusiveWith_information ResolutionAttainment.fairLaw P Q
    (fun z _ => by cases z with | false => exact hQ | true => exact hP),
    ResolutionAttainment.fairLaw_entropy]

/--
`rem:erasure`, zero-error recovery for arbitrary rows.

Proves: if some output has positive `P`-chance and zero `Q`-chance, and some output has positive
`Q`-chance and zero `P`-chance, then the unit-cost protocol of the fair label that stops at the
first output one row excludes stops with probability one under both labels, its decoder has zero
error, it acquires one bit, its expected cost under the label `true` is `1 / a`, under `false` is
`1 / b`, each at most `max (1 / a) (1 / b)`, and its expected cost for the fair label is
`(1 / a + 1 / b) / 2`, at most the same maximum; `a` is the `P`-chance of the outputs that `Q`
excludes and `b` the `Q`-chance of the outputs that `P` excludes.
Relation: the stopped laws of the actual finite protocol. Trust: kernel-only.
-/
theorem exclusive_outputs_recovery (P Q : FiniteLaw Y)
    (hP : ∃ y, 0 < P.mass y ∧ Q.mass y = 0) (hQ : ∃ y, 0 < Q.mass y ∧ P.mass y = 0) :
    (∀ z : Bool, Tendsto (fun n => activeMass (firstExclusive P Q) n z) atTop (𝓝 0)) ∧
    (∀ z : Bool, ∀ h : List (Unit × Y), firstExclusiveDecoder Q h ≠ z →
      transcriptMass (firstExclusive P Q) z h = 0) ∧
    informationLimit (firstExclusive P Q) = 1 ∧
    labelCost (firstExclusive P Q) true = ENNReal.ofReal (1 / exclusiveMass P Q) ∧
    labelCost (firstExclusive P Q) false = ENNReal.ofReal (1 / exclusiveMass Q P) ∧
    (∀ z : Bool, labelCost (firstExclusive P Q) z ≤
      ENNReal.ofReal (max (1 / exclusiveMass P Q) (1 / exclusiveMass Q P))) ∧
    extendedCost (firstExclusive P Q) =
      ENNReal.ofReal ((1 / exclusiveMass P Q + 1 / exclusiveMass Q P) / 2) ∧
    extendedCost (firstExclusive P Q) ≤
      ENNReal.ofReal (max (1 / exclusiveMass P Q) (1 / exclusiveMass Q P)) := by
  have ha := (exclusiveMass_pos_iff P Q).mpr hP
  have hb := (exclusiveMass_pos_iff Q P).mpr hQ
  refine ⟨fun z => ?_, fun z h hw => firstExclusiveWith_zero_error _ P Q z h hw,
    firstExclusive_information P Q ha hb, firstExclusive_labelCost P Q true ha,
    firstExclusive_labelCost P Q false hb, firstExclusive_labelCost_le_max P Q ha hb,
    firstExclusive_extendedCost P Q ha hb, firstExclusiveWith_extendedCost_le_max _ P Q ha hb⟩
  cases z with
  | false => exact firstExclusiveWith_stops _ P Q false hb
  | true => exact firstExclusiveWith_stops _ P Q true ha

end FirstExclusive

/-! ### Nested supports: no zero-error recovery at finite expected cost -/

section NestedSupports

variable {Z A W : Type} [Fintype Z] [Fintype A] [Fintype W]

/-- A decoder of the transcript has zero error if no stopped transcript of positive chance under a
label is decoded to another label. -/
def ZeroError (p : FiniteProtocol Z A W) (d : List (A × W) → Z) : Prop :=
  ∀ z h, d h ≠ z → transcriptMass p z h = 0

/-- At every history and action, each output of positive chance under the label `z₀` has positive
chance under the label `z₁`: the support of `z₀` lies in the support of `z₁`. -/
def SupportWithin (p : FiniteProtocol Z A W) (z₀ z₁ : Z) : Prop :=
  ∀ h a y, 0 < (p.observation h a z₀).mass y → 0 < (p.observation h a z₁).mass y

/-- Every finite transcript of positive chance under the label of the smaller support has
positive chance under the other label. -/
theorem prefixMass_pos_of_supportWithin (p : FiniteProtocol Z A W) {z₀ z₁ : Z}
    (hs : SupportWithin p z₀ z₁) (h1 : 0 < p.prior.mass z₁) (h : List (A × W)) :
    0 < prefixMass p z₀ h → 0 < prefixMass p z₁ h := by
  induction h using List.reverseRecOn with
  | nil =>
    intro _
    exact h1
  | append_singleton h b ih =>
    obtain ⟨a, y⟩ := b
    rw [prefixMass_append, prefixMass_append]
    split_ifs with hstop
    · intro h0
      exact absurd h0 (lt_irrefl 0)
    · intro hpos
      have hm0 := prefixMass_nonnegative p z₀ h
      have hpol := (p.policy h).nonnegative a
      have hobs := (p.observation h a z₀).nonnegative y
      have hobs_pos : 0 < (p.observation h a z₀).mass y := by
        rcases hobs.eq_or_lt with he | he
        · rw [← he, mul_zero] at hpos
          exact absurd hpos (lt_irrefl 0)
        · exact he
      have hab_pos : 0 < prefixMass p z₀ h * (p.policy h).mass a := by
        rcases (mul_nonneg hm0 hpol).eq_or_lt with he | he
        · rw [← he, zero_mul] at hpos
          exact absurd hpos (lt_irrefl 0)
        · exact he
      have hpol_pos : 0 < (p.policy h).mass a := by
        rcases hpol.eq_or_lt with he | he
        · rw [← he, mul_zero] at hab_pos
          exact absurd hab_pos (lt_irrefl 0)
        · exact he
      have hm_pos : 0 < prefixMass p z₀ h := by
        rcases hm0.eq_or_lt with he | he
        · rw [← he, zero_mul] at hab_pos
          exact absurd hab_pos (lt_irrefl 0)
        · exact he
      exact mul_pos (mul_pos (ih hm_pos) hpol_pos) (hs h a y hobs_pos)

/-- A zero-error protocol stops on no transcript of positive chance under the label of the
smaller support. -/
theorem zeroError_transcriptMass_eq_zero (p : FiniteProtocol Z A W) {d : List (A × W) → Z}
    (hd : ZeroError p d) {z₀ z₁ : Z} (hne : z₀ ≠ z₁) (hs : SupportWithin p z₀ z₁)
    (h1 : 0 < p.prior.mass z₁) (h : List (A × W)) : transcriptMass p z₀ h = 0 := by
  by_contra hne0
  have hpos : 0 < transcriptMass p z₀ h :=
    lt_of_le_of_ne (transcriptMass_nonneg p z₀ h) (Ne.symm hne0)
  unfold transcriptMass at hpos
  split_ifs at hpos with hstop
  · have hpos1 : 0 < transcriptMass p z₁ h := by
      unfold transcriptMass
      rw [if_pos hstop]
      exact prefixMass_pos_of_supportWithin p hs h1 h hpos
    have hd0 : d h = z₀ := by
      by_contra hn
      exact hne0 (hd z₀ h hn)
    have hd1 : d h = z₁ := by
      by_contra hn
      exact hpos1.ne' (hd z₁ h hn)
    exact hne (hd0.symm.trans hd1)
  · exact lt_irrefl 0 hpos

/-- Under the label of the smaller support a zero-error protocol never stops: its running mass
stays at the prior mass at every depth. -/
theorem zeroError_activeMass_eq_prior (p : FiniteProtocol Z A W) {d : List (A × W) → Z}
    (hd : ZeroError p d) {z₀ z₁ : Z} (hne : z₀ ≠ z₁) (hs : SupportWithin p z₀ z₁)
    (h1 : 0 < p.prior.mass z₁) (n : ℕ) : activeMass p n z₀ = p.prior.mass z₀ := by
  have hbal := transcript_add_active_eq_prior p n z₀
  rw [Finset.sum_eq_zero (fun h _ => zeroError_transcriptMass_eq_zero p hd hne hs h1 h),
    zero_add] at hbal
  exact hbal

/-- The stopping chance under the label of the smaller support is zero. -/
theorem zeroError_transcriptTotal_eq_zero (p : FiniteProtocol Z A W) {d : List (A × W) → Z}
    (hd : ZeroError p d) {z₀ z₁ : Z} (hne : z₀ ≠ z₁) (hs : SupportWithin p z₀ z₁)
    (h1 : 0 < p.prior.mass z₁) : transcriptTotal p z₀ = 0 := by
  unfold transcriptTotal
  rw [tsum_congr (zeroError_transcriptMass_eq_zero p hd hne hs h1), tsum_zero]

/-- A positive prior mass on the label of the smaller support never drains. -/
theorem zeroError_not_stops (p : FiniteProtocol Z A W) {d : List (A × W) → Z}
    (hd : ZeroError p d) {z₀ z₁ : Z} (hne : z₀ ≠ z₁) (hs : SupportWithin p z₀ z₁)
    (h0 : 0 < p.prior.mass z₀) (h1 : 0 < p.prior.mass z₁) :
    ¬ Tendsto (fun n => activeMass p n z₀) atTop (𝓝 0) := by
  intro ht
  have hconst : (fun n => activeMass p n z₀) = fun _ => p.prior.mass z₀ :=
    funext (zeroError_activeMass_eq_prior p hd hne hs h1)
  rw [hconst] at ht
  exact h0.ne' (tendsto_nhds_unique tendsto_const_nhds ht)

/-- With every reading costing at least `c ≥ 0`, the cost through depth `n` is at least `c` times
the running mass of a label summed over the earlier depths. -/
theorem expectedCost_ge_activeMass (p : FiniteProtocol Z A W) {c : ℝ} (hc : 0 ≤ c)
    (hcost : ∀ h a, c ≤ p.cost h a) (z : Z) (n : ℕ) :
    c * ∑ ℓ ∈ Finset.range n, activeMass p ℓ z ≤ expectedCost p n (historyBank A W n) := by
  rw [expectedCost_eq_historyCost]
  unfold chargedHistorySet
  rw [Finset.sum_filter, ResolutionAttainment.historySet_below_eq_levels n, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro ℓ _
  unfold activeMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro h _
  by_cases hl : h.length = ℓ
  · rw [if_pos hl]
    unfold historyCost
    by_cases hs : p.stop h = false
    · rw [if_pos ⟨hl, hs⟩, if_pos hs]
      have hsum : c ≤ ∑ a, (p.policy h).mass a * p.cost h a := by
        calc c = ∑ a, (p.policy h).mass a * c := by
              rw [← Finset.sum_mul, (p.policy h).total, one_mul]
          _ ≤ ∑ a, (p.policy h).mass a * p.cost h a :=
              Finset.sum_le_sum fun a _ =>
                mul_le_mul_of_nonneg_left (hcost h a) ((p.policy h).nonnegative a)
      calc c * prefixMass p z h = prefixMass p z h * c := mul_comm _ _
        _ ≤ historyMass p h * ∑ a, (p.policy h).mass a * p.cost h a :=
          mul_le_mul (prefixMass_le_historyMass p h z) hsum hc (historyMass_nonnegative p h)
    · rw [if_neg (fun hv => hs hv.2), if_neg hs, mul_zero]
  · rw [if_neg hl, if_neg (fun hv => hl hv.1), mul_zero]

/-- With every reading costing at least `c > 0`, a zero-error protocol has infinite extended cost
if the label of the smaller support has positive prior mass. -/
theorem zeroError_extendedCost_eq_top (p : FiniteProtocol Z A W) {d : List (A × W) → Z}
    (hd : ZeroError p d) {z₀ z₁ : Z} (hne : z₀ ≠ z₁) (hs : SupportWithin p z₀ z₁)
    (h0 : 0 < p.prior.mass z₀) (h1 : 0 < p.prior.mass z₁) {c : ℝ} (hc : 0 < c)
    (hcost : ∀ h a, c ≤ p.cost h a) : extendedCost p = ⊤ := by
  apply ENNReal.eq_top_of_forall_nnreal_le
  intro r
  have hcm : 0 < c * p.prior.mass z₀ := mul_pos hc h0
  obtain ⟨n, hn⟩ := exists_nat_ge ((r : ℝ) / (c * p.prior.mass z₀))
  have hlow : (r : ℝ) ≤ c * ∑ ℓ ∈ Finset.range n, activeMass p ℓ z₀ := by
    rw [Finset.sum_congr rfl (fun ℓ _ => zeroError_activeMass_eq_prior p hd hne hs h1 ℓ),
      Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    calc (r : ℝ) ≤ n * (c * p.prior.mass z₀) := (div_le_iff₀ hcm).mp hn
      _ = c * (n * p.prior.mass z₀) := by ring
  calc (r : ℝ≥0∞) = ENNReal.ofReal r := ENNReal.ofReal_coe_nnreal.symm
    _ ≤ ENNReal.ofReal (expectedCost p n (historyBank A W n)) :=
      ENNReal.ofReal_le_ofReal (hlow.trans (expectedCost_ge_activeMass p hc.le hcost z₀ n))
    _ ≤ extendedCost p := finiteCost_le_extendedCost p n

/--
`rem:erasure`, nested supports.

Proves: if the support of the label `z₀` lies in the support of `z₁ ≠ z₀` at every reading, both
labels have positive prior mass and every reading costs at least `c > 0`, then no decoder gives
the protocol zero error at finite expected cost.
Relation: the stopped laws of an arbitrary finite protocol. Trust: kernel-only.
-/
theorem no_zeroError_finite_cost_of_supportWithin (p : FiniteProtocol Z A W)
    (d : List (A × W) → Z) {z₀ z₁ : Z} (hne : z₀ ≠ z₁) (hs : SupportWithin p z₀ z₁)
    (h0 : 0 < p.prior.mass z₀) (h1 : 0 < p.prior.mass z₁) {c : ℝ} (hc : 0 < c)
    (hcost : ∀ h a, c ≤ p.cost h a) : ¬ (ZeroError p d ∧ extendedCost p < ⊤) := by
  rintro ⟨hd, hfin⟩
  rw [zeroError_extendedCost_eq_top p hd hne hs h0 h1 hc hcost] at hfin
  exact lt_irrefl _ hfin

/-- A protocol of the readings with rows `P` and `Q` inherits the inclusion of the row supports. -/
theorem rows_supportWithin (p : FiniteProtocol Bool A W) (P Q : FiniteLaw W)
    (hr : ∀ h a z, p.observation h a z = row P Q z) {z₀ z₁ : Bool}
    (hs : ∀ y, 0 < (row P Q z₀).mass y → 0 < (row P Q z₁).mass y) :
    SupportWithin p z₀ z₁ := by
  intro h a y hy
  rw [hr] at hy ⊢
  exact hs y hy

/--
`rem:erasure`, nested supports, for the reading with rows `P` and `Q`.

Proves: if one row's support contains the other's, every protocol whose readings all have the rows
`P` and `Q`, with positive prior mass on both labels and cost at least `c > 0` per reading, has no
decoder of zero error at finite expected cost.
Relation: the stopped laws of an arbitrary finite protocol of these readings. Trust: kernel-only.
-/
theorem nested_rows_no_zeroError_finite_cost (p : FiniteProtocol Bool A W) (P Q : FiniteLaw W)
    (hr : ∀ h a z, p.observation h a z = row P Q z)
    (hsupp : (∀ y, 0 < Q.mass y → 0 < P.mass y) ∨ (∀ y, 0 < P.mass y → 0 < Q.mass y))
    (hprior : ∀ z, 0 < p.prior.mass z) {c : ℝ} (hc : 0 < c)
    (hcost : ∀ h a, c ≤ p.cost h a) (d : List (A × W) → Bool) :
    ¬ (ZeroError p d ∧ extendedCost p < ⊤) := by
  rcases hsupp with hQP | hPQ
  · exact no_zeroError_finite_cost_of_supportWithin p d (z₀ := false) (z₁ := true)
      Bool.false_ne_true (rows_supportWithin p P Q hr hQP) (hprior false) (hprior true) hc hcost
  · exact no_zeroError_finite_cost_of_supportWithin p d (z₀ := true) (z₁ := false)
      (by decide) (rows_supportWithin p P Q hr hPQ) (hprior true) (hprior false) hc hcost

/--
`rem:erasure`, the two cases together.

Proves: for two laws `P` and `Q` on a finite alphabet, a protocol of the fair label whose readings
have the rows `P` and `Q` and cost at least one each, with a decoder of zero error and finite
expected cost, exists exactly if each row gives positive chance to an output that the other row
excludes; the protocol `firstExclusive P Q` and its decoder attain it.
Relation: the stopped laws of finite protocols of these readings. Trust: kernel-only.
-/
theorem exists_zeroError_finite_cost_iff (P Q : FiniteLaw W) :
    (∃ (p : FiniteProtocol Bool Unit W) (d : List (Unit × W) → Bool),
      p.prior = ResolutionAttainment.fairLaw ∧ (∀ h a z, p.observation h a z = row P Q z) ∧
      (∀ h a, 1 ≤ p.cost h a) ∧ ZeroError p d ∧ extendedCost p < ⊤) ↔
      (∃ y, 0 < P.mass y ∧ Q.mass y = 0) ∧ (∃ y, 0 < Q.mass y ∧ P.mass y = 0) := by
  constructor
  · rintro ⟨p, d, hprior, hr, hcost, hd, hfin⟩
    by_contra hn
    have hfair : ∀ z, 0 < p.prior.mass z := by
      intro z
      rw [hprior]
      norm_num [ResolutionAttainment.fairLaw]
    have hsupp : (∀ y, 0 < Q.mass y → 0 < P.mass y) ∨ (∀ y, 0 < P.mass y → 0 < Q.mass y) := by
      rcases not_and_or.mp hn with hA | hB
      · right
        intro y hy
        rcases (Q.nonnegative y).eq_or_lt with h0 | h0
        · exact absurd ⟨y, hy, h0.symm⟩ hA
        · exact h0
      · left
        intro y hy
        rcases (P.nonnegative y).eq_or_lt with h0 | h0
        · exact absurd ⟨y, hy, h0.symm⟩ hB
        · exact h0
    exact nested_rows_no_zeroError_finite_cost p P Q hr hsupp hfair one_pos hcost d ⟨hd, hfin⟩
  · rintro ⟨hP, hQ⟩
    have ha := (exclusiveMass_pos_iff P Q).mpr hP
    have hb := (exclusiveMass_pos_iff Q P).mpr hQ
    refine ⟨firstExclusive P Q, firstExclusiveDecoder Q, rfl, fun _ _ _ => rfl,
      fun _ _ => le_rfl, fun z h hw => firstExclusiveWith_zero_error _ P Q z h hw, ?_⟩
    rw [firstExclusive_extendedCost P Q ha hb]
    exact ENNReal.ofReal_lt_top

end NestedSupports

/-! ### The erasure reading as an instance -/

theorem erasure_decisive_iff (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (y : Option Bool) :
    Decisive (erasureLaw p hp0 hp1 true) (erasureLaw p hp0 hp1 false) y ↔
      y = some true ∨ y = some false := by
  have hq : (1 : ℝ) - p ≠ 0 := ne_of_gt (by linarith)
  have hp : p ≠ 0 := ne_of_gt hp0
  cases y with
  | none => simp [Decisive, erasureLaw, erasureRow, hq]
  | some b => cases b <;> simp [Decisive, erasureLaw, erasureRow, hp]

/-- Under either label of the erasure reading the exclusive chance is `p`. -/
theorem erasure_labelExclusive (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (z : Bool) :
    labelExclusive (erasureLaw p hp0 hp1 true) (erasureLaw p hp0 hp1 false) z = p := by
  have hq : (1 : ℝ) - p ≠ 0 := ne_of_gt (by linarith)
  have hp : p ≠ 0 := ne_of_gt hp0
  cases z <;> simp [labelExclusive, exclusiveMass, row, erasureLaw, erasureRow,
    Fintype.sum_option, hp, hq]

theorem erasure_stop_iff (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (h : List (Unit × Option Bool)) :
    (((), some true) ∈ h ∨ ((), some false) ∈ h) ↔
      ∃ ay ∈ h, Decisive (erasureLaw p hp0 hp1 true) (erasureLaw p hp0 hp1 false) ay.2 := by
  constructor
  · rintro (ht | hf)
    · exact ⟨_, ht, (erasure_decisive_iff p hp0 hp1 _).mpr (Or.inl rfl)⟩
    · exact ⟨_, hf, (erasure_decisive_iff p hp0 hp1 _).mpr (Or.inr rfl)⟩
  · rintro ⟨⟨⟨⟩, y⟩, hm, hd⟩
    rcases (erasure_decisive_iff p hp0 hp1 y).mp hd with rfl | rfl
    · exact Or.inl hm
    · exact Or.inr hm

/-- The first-definite protocol of the erasure reading is the first-exclusive protocol of its
rows. -/
theorem firstDefinite_eq_firstExclusive (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    firstDefinite p hp0 hp1 =
      firstExclusive (erasureLaw p hp0 hp1 true) (erasureLaw p hp0 hp1 false) := by
  unfold firstDefinite firstExclusive firstExclusiveWith
  congr 1
  · funext h a z
    cases z <;> rfl
  · funext h
    exact decide_eq_decide.mpr (erasure_stop_iff p hp0 hp1 h)

/-- The first-definite decoder is the first-exclusive decoder of the erasure rows. -/
theorem firstDefiniteDecoder_eq_firstExclusiveDecoder (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    firstDefiniteDecoder = firstExclusiveDecoder (erasureLaw p hp0 hp1 false) := by
  have hq : (1 : ℝ) - p ≠ 0 := ne_of_gt (by linarith)
  have hp : p ≠ 0 := ne_of_gt hp0
  funext h
  apply decide_eq_decide.mpr
  constructor
  · intro ht
    exact ⟨_, ht, by simp [erasureLaw, erasureRow]⟩
  · rintro ⟨⟨⟨⟩, y⟩, hm, hz⟩
    cases y with
    | none => simp [erasureLaw, erasureRow, hq] at hz
    | some b =>
      cases b with
      | true => exact hm
      | false => simp [erasureLaw, erasureRow, hp] at hz

/-- The erasure reading costs `1 / p` under each label. -/
theorem firstDefinite_labelCost (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (z : Bool) :
    labelCost (firstDefinite p hp0 hp1) z = ENNReal.ofReal (1 / p) := by
  rw [firstDefinite_eq_firstExclusive, firstExclusive_labelCost _ _ z
    (by rw [erasure_labelExclusive]; exact hp0), erasure_labelExclusive]

end OperatorKO7.Meta.BoundaryObserver.ErasureReading
