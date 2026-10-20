import OperatorKO7.Meta.BoundaryObserver.ErasureReading
import OperatorKO7.Meta.BoundaryObserver.TranscriptLaw

set_option autoImplicit false

/-!
# Positive-prior exclusive-output completion

The laws, decoder, and stopped mass are the existing finite-protocol
constructions. The prior is arbitrary, normalized, and strictly positive on both
binary labels in the exact recovery equivalence. No independent observation
copies are assumed across an initial seed.
-/

namespace OperatorKO7.Meta.BoundaryObserver.ErasurePriorCompletion

open scoped BigOperators ENNReal
open Filter Topology ProtocolResolution TranscriptLaw ErasureReading

variable {Y : Type} [Fintype Y]

/-- Zero-error recovery under every positive binary prior is equivalent to
the two strict exclusive-output support conditions. Necessity permits every
adaptive stop rule and decoder with the stated fixed conditional rows. -/
theorem exists_zeroError_finite_cost_arbitrary_prior_iff
    (μ : FiniteLaw Bool) (hμ : ∀ z, 0 < μ.mass z)
    (P Q : FiniteLaw Y) :
    (∃ (p : FiniteProtocol Bool Unit Y) (d : List (Unit × Y) → Bool),
      p.prior = μ ∧
      (∀ h a z, p.observation h a z = PairResolution.row P Q z) ∧
      (∀ h a, 1 ≤ p.cost h a) ∧
      ZeroError p d ∧ extendedCost p < ⊤) ↔
      (∃ y, 0 < P.mass y ∧ Q.mass y = 0) ∧
      (∃ y, 0 < Q.mass y ∧ P.mass y = 0) := by
  constructor
  · rintro ⟨p, d, hprior, hr, hcost, hd, hfin⟩
    by_contra hn
    have hp : ∀ z, 0 < p.prior.mass z := by
      intro z
      rw [hprior]
      exact hμ z
    have hsupp :
        (∀ y, 0 < Q.mass y → 0 < P.mass y) ∨
        (∀ y, 0 < P.mass y → 0 < Q.mass y) := by
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
    exact nested_rows_no_zeroError_finite_cost p P Q hr hsupp hp
      one_pos hcost d ⟨hd, hfin⟩
  · rintro ⟨hP, hQ⟩
    have ha : 0 < exclusiveMass P Q := (exclusiveMass_pos_iff P Q).mpr hP
    have hb : 0 < exclusiveMass Q P := (exclusiveMass_pos_iff Q P).mpr hQ
    refine ⟨firstExclusiveWith μ P Q, firstExclusiveDecoder Q,
      rfl, (fun _ _ _ => rfl), (fun _ _ => le_rfl),
      (fun z h hw => firstExclusiveWith_zero_error μ P Q z h hw), ?_⟩
    rw [firstExclusiveWith_extendedCost μ P Q
      (fun z _ => by cases z with | false => exact hb | true => exact ha)]
    exact ENNReal.ofReal_lt_top

/-- The actual geometric survival law holds separately for each label. -/
theorem firstExclusiveWith_survival_law
    (μ : FiniteLaw Bool) (P Q : FiniteLaw Y) (n : ℕ) :
    activeMass (firstExclusiveWith μ P Q) n true =
        μ.mass true * (1 - exclusiveMass P Q) ^ n ∧
      activeMass (firstExclusiveWith μ P Q) n false =
        μ.mass false * (1 - exclusiveMass Q P) ^ n := by
  constructor
  · simpa only [labelExclusive_true] using
      firstExclusiveWith_activeMass μ P Q n true
  · simpa only [labelExclusive_false] using
      firstExclusiveWith_activeMass μ P Q n false

/-- The stopped joint masses are normalized on every label: no escaping
probability remains under the two strict support conditions. -/
theorem firstExclusiveWith_stopped_law_normalized
    (μ : FiniteLaw Bool) (P Q : FiniteLaw Y)
    (ha : 0 < exclusiveMass P Q) (hb : 0 < exclusiveMass Q P) :
    ∀ z, (∑' h : List (Unit × Y),
      transcriptMass (firstExclusiveWith μ P Q) z h) = μ.mass z := by
  intro z
  change transcriptTotal (firstExclusiveWith μ P Q) z = μ.mass z
  exact transcriptTotal_eq_prior_of_stops (firstExclusiveWith μ P Q) z
    (by cases z with
        | false => exact firstExclusiveWith_stops μ P Q false hb
        | true => exact firstExclusiveWith_stops μ P Q true ha)

/-- The independently normalized countable law of actual stopped transcripts
has mutual information equal to the entropy of the source prior. -/
theorem firstExclusiveWith_stopped_law_information
    (μ : FiniteLaw Bool) (P Q : FiniteLaw Y)
    (ha : 0 < exclusiveMass P Q) (hb : 0 < exclusiveMass Q P) :
    ∃ hstop : ∀ z, Tendsto
        (fun n => activeMass (firstExclusiveWith μ P Q) n z) atTop (𝓝 0),
      (stoppedTranscriptJointLaw (firstExclusiveWith μ P Q) hstop).information =
        entropy μ.mass := by
  have hs : ∀ z, Tendsto
      (fun n => activeMass (firstExclusiveWith μ P Q) n z) atTop (𝓝 0) := by
    intro z
    cases z with
    | false => exact firstExclusiveWith_stops μ P Q false hb
    | true => exact firstExclusiveWith_stops μ P Q true ha
  refine ⟨hs, ?_⟩
  calc
    (stoppedTranscriptJointLaw (firstExclusiveWith μ P Q) hs).information =
        informationLimit (firstExclusiveWith μ P Q) :=
      (informationLimit_eq_countableTranscriptInformation
        (firstExclusiveWith μ P Q) hs).symm
    _ = entropy μ.mass :=
      firstExclusiveWith_information μ P Q
        (fun z _ => by cases z with | false => exact hb | true => exact ha)

/-- The exact expected total number of unit-cost readings, under any binary
prior, is w/a + (1-w)/b, where w is the mass of the true label. -/
theorem firstExclusiveWith_weighted_cost
    (μ : FiniteLaw Bool) (P Q : FiniteLaw Y)
    (ha : 0 < exclusiveMass P Q) (hb : 0 < exclusiveMass Q P) :
    extendedCost (firstExclusiveWith μ P Q) =
      ENNReal.ofReal
        (μ.mass true / exclusiveMass P Q +
          (1 - μ.mass true) / exclusiveMass Q P) := by
  have hm : μ.mass false = 1 - μ.mass true := by
    have htotal := μ.total
    rw [Fintype.sum_bool] at htotal
    linarith
  rw [firstExclusiveWith_extendedCost μ P Q
    (fun z _ => by cases z with | false => exact hb | true => exact ha)]
  simp only [Fintype.sum_bool, labelExclusive_true, labelExclusive_false, hm]

/-- The same expected cost is bounded by the larger reciprocal exclusive
mass, with no restriction to the fair prior. -/
theorem firstExclusiveWith_weighted_cost_le_max
    (μ : FiniteLaw Bool) (P Q : FiniteLaw Y)
    (ha : 0 < exclusiveMass P Q) (hb : 0 < exclusiveMass Q P) :
    extendedCost (firstExclusiveWith μ P Q) ≤
      ENNReal.ofReal
        (max (1 / exclusiveMass P Q) (1 / exclusiveMass Q P)) :=
  firstExclusiveWith_extendedCost_le_max μ P Q ha hb

/-- A zero-prior label has zero active probability at every horizon; this
control imposes no positive exclusive-output condition for that label. -/
theorem firstExclusiveWith_zero_prior_active
    (μ : FiniteLaw Bool) (P Q : FiniteLaw Y) (z : Bool)
    (hz : μ.mass z = 0) (n : ℕ) :
    activeMass (firstExclusiveWith μ P Q) n z = 0 :=
  activeMass_eq_zero_of_prior_zero (firstExclusiveWith μ P Q) z hz n

/-- The full positive-prior witness gives almost-sure stopping, zero error,
the entropy limit, exact weighted cost, and the universal reciprocal bound. -/
theorem firstExclusiveWith_positive_prior_recovery
    (μ : FiniteLaw Bool) (P Q : FiniteLaw Y)
    (ha : 0 < exclusiveMass P Q) (hb : 0 < exclusiveMass Q P) :
    (∀ z, Tendsto (fun n => activeMass (firstExclusiveWith μ P Q) n z)
      atTop (𝓝 0)) ∧
    ZeroError (firstExclusiveWith μ P Q) (firstExclusiveDecoder Q) ∧
    informationLimit (firstExclusiveWith μ P Q) = entropy μ.mass ∧
    extendedCost (firstExclusiveWith μ P Q) =
      ENNReal.ofReal
        (μ.mass true / exclusiveMass P Q +
          (1 - μ.mass true) / exclusiveMass Q P) ∧
    extendedCost (firstExclusiveWith μ P Q) ≤
      ENNReal.ofReal (max (1 / exclusiveMass P Q) (1 / exclusiveMass Q P)) := by
  refine ⟨?_, ?_, ?_, firstExclusiveWith_weighted_cost μ P Q ha hb,
    firstExclusiveWith_weighted_cost_le_max μ P Q ha hb⟩
  · intro z
    cases z with
    | false => exact firstExclusiveWith_stops μ P Q false hb
    | true => exact firstExclusiveWith_stops μ P Q true ha
  · intro z h hw
    exact firstExclusiveWith_zero_error μ P Q z h hw
  · exact firstExclusiveWith_information μ P Q
      (fun z _ => by cases z with | false => exact hb | true => exact ha)


/-! ## Optimality of stopping at the first decisive output -/

section Optimality

variable {A : Type} [Fintype A]

def NoDecisive (P Q : FiniteLaw Y) (h : List (A × Y)) : Prop :=
  ∀ e ∈ h, ¬ Decisive P Q e.2

omit [Fintype A] in
theorem noDecisive_append (P Q : FiniteLaw Y) (h : List (A × Y)) (e : A × Y) :
    NoDecisive P Q (h ++ [e]) ↔ NoDecisive P Q h ∧ ¬ Decisive P Q e.2 := by
  constructor
  · intro hN
    exact ⟨fun a ha => hN a (List.mem_append_left _ ha),
      hN e (List.mem_append_right _ (List.mem_singleton_self e))⟩
  · rintro ⟨hN, he⟩ a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hN a ha
    · have hae := List.mem_singleton.mp ha
      subst a
      exact he

theorem row_pos_of_not_decisive (P Q : FiniteLaw Y) (y : Y)
    (hy : ¬ Decisive P Q y) (z : Bool) : 0 < (PairResolution.row P Q z).mass y := by
  cases z with
  | false =>
    exact lt_of_le_of_ne (Q.nonnegative y) (Ne.symm (fun h => hy (Or.inr h)))
  | true =>
    exact lt_of_le_of_ne (P.nonnegative y) (Ne.symm (fun h => hy (Or.inl h)))

/-- Positive undecided prefixes have positive mass under both labels. -/
theorem prefixMass_pos_on_common_history (p : FiniteProtocol Bool A Y)
    (P Q : FiniteLaw Y)
    (hr : ∀ h a z, p.observation h a z = PairResolution.row P Q z)
    (hprior : ∀ z, 0 < p.prior.mass z) (z z' : Bool) (h : List (A × Y)) :
    NoDecisive P Q h → 0 < prefixMass p z h → 0 < prefixMass p z' h := by
  induction h using List.reverseRecOn with
  | nil =>
    intro _ _
    exact hprior z'
  | append_singleton h e ih =>
    obtain ⟨a, y⟩ := e
    intro hN hp
    obtain ⟨hNh, hy⟩ := (noDecisive_append P Q h (a, y)).mp hN
    by_cases hs : p.stop h = true
    · rw [prefixMass_append, if_pos hs] at hp
      exact False.elim (lt_irrefl 0 hp)
    · rw [prefixMass_append, if_neg hs, hr h a z] at hp
      rw [prefixMass_append, if_neg hs, hr h a z']
      have hprod : 0 < prefixMass p z h * (p.policy h).mass a :=
        (mul_pos_iff_of_pos_right (row_pos_of_not_decisive P Q y hy z)).mp hp
      rcases mul_pos_iff.mp hprod with hpos | hneg
      · exact mul_pos (mul_pos (ih hNh hpos.1) hpos.2)
          (row_pos_of_not_decisive P Q y hy z')
      · exact False.elim (not_lt_of_ge (prefixMass_nonnegative p z h) hneg.1)

/-- A zero-error decoder cannot stop at any positive undecided prefix. -/
theorem zeroError_continue_on_common_history (p : FiniteProtocol Bool A Y)
    (P Q : FiniteLaw Y)
    (hr : ∀ h a z, p.observation h a z = PairResolution.row P Q z)
    (hprior : ∀ z, 0 < p.prior.mass z) (d : List (A × Y) → Bool)
    (hd : ZeroError p d) (h : List (A × Y)) (hN : NoDecisive P Q h)
    (z : Bool) (hp : 0 < prefixMass p z h) : p.stop h = false := by
  cases hs : p.stop h with
  | false => rfl
  | true =>
    have ho := prefixMass_pos_on_common_history p P Q hr hprior z (!z) h hN hp
    by_cases he : d h = z
    · have hb := hd (!z) h (by rw [he]; cases z <;> decide)
      rw [transcriptMass, if_pos hs] at hb
      exact False.elim (ne_of_gt ho hb)
    · have hb := hd z h he
      rw [transcriptMass, if_pos hs] at hb
      exact False.elim (ne_of_gt hp hb)

/-- Cut the original adaptive policy at its first decisive output, charging one per reading. -/
noncomputable def exclusiveCut (p : FiniteProtocol Bool A Y) (P Q : FiniteLaw Y) :
    FiniteProtocol Bool A Y where
  prior := p.prior
  policy := p.policy
  observation := p.observation
  stop h := decide (∃ e ∈ h, Decisive P Q e.2)
  cost _ _ := 1
  cost_nonnegative _ _ := zero_le_one

theorem exclusiveCut_stop_false_iff (p : FiniteProtocol Bool A Y)
    (P Q : FiniteLaw Y) (h : List (A × Y)) :
    (exclusiveCut p P Q).stop h = false ↔ NoDecisive P Q h := by
  classical
  simp [exclusiveCut, NoDecisive]

theorem exclusiveCut_prefixMass (p : FiniteProtocol Bool A Y)
    (P Q : FiniteLaw Y)
    (hr : ∀ h a z, p.observation h a z = PairResolution.row P Q z)
    (hprior : ∀ z, 0 < p.prior.mass z) (d : List (A × Y) → Bool)
    (hd : ZeroError p d) (z : Bool) (h : List (A × Y)) :
    NoDecisive P Q h →
      prefixMass (exclusiveCut p P Q) z h = prefixMass p z h := by
  induction h using List.reverseRecOn with
  | nil => intro _; rfl
  | append_singleton h e ih =>
    obtain ⟨a, y⟩ := e
    intro hN
    have hNh := ((noDecisive_append P Q h (a, y)).mp hN).1
    have hcut := (exclusiveCut_stop_false_iff p P Q h).mpr hNh
    rw [prefixMass_append, prefixMass_append, if_neg (by rw [hcut]; decide), ih hNh]
    cases hs : p.stop h with
    | false => simp [exclusiveCut]
    | true =>
      have hz : prefixMass p z h = 0 := by
        by_contra hn
        have hp := lt_of_le_of_ne (prefixMass_nonnegative p z h) (Ne.symm hn)
        have hf := zeroError_continue_on_common_history p P Q hr hprior d hd h hNh z hp
        rw [hs] at hf
        cases hf
      simp [hz]

/-- Every charge of the first-decisive cut is bounded by the original charge. -/
theorem exclusiveCut_historyCost_le (p : FiniteProtocol Bool A Y)
    (P Q : FiniteLaw Y)
    (hr : ∀ h a z, p.observation h a z = PairResolution.row P Q z)
    (hprior : ∀ z, 0 < p.prior.mass z) (d : List (A × Y) → Bool)
    (hd : ZeroError p d) (hc : ∀ h a, 1 ≤ p.cost h a) (h : List (A × Y)) :
    historyCost (exclusiveCut p P Q) h ≤ historyCost p h := by
  by_cases hN : NoDecisive P Q h
  · have hcut := (exclusiveCut_stop_false_iff p P Q h).mpr hN
    have hm : historyMass (exclusiveCut p P Q) h = historyMass p h :=
      Finset.sum_congr rfl (fun z _ => exclusiveCut_prefixMass p P Q hr hprior d hd z h hN)
    have hcharge : historyCost (exclusiveCut p P Q) h = historyMass p h := by
      rw [historyCost, if_pos hcut, hm]
      change historyMass p h * (∑ a, (p.policy h).mass a * 1) = _
      simp only [mul_one, (p.policy h).total]
    rw [hcharge]
    cases hs : p.stop h with
    | false =>
      rw [historyCost, if_pos hs]
      apply le_mul_of_one_le_right (historyMass_nonnegative p h)
      calc
        1 = ∑ a, (p.policy h).mass a := (p.policy h).total.symm
        _ ≤ ∑ a, (p.policy h).mass a * p.cost h a := by
          apply Finset.sum_le_sum
          intro a _
          exact le_mul_of_one_le_right ((p.policy h).nonnegative a) (hc h a)
    | true =>
      have hm0 : historyMass p h = 0 := by
        apply Finset.sum_eq_zero
        intro z _
        by_contra hn
        have hp := lt_of_le_of_ne (prefixMass_nonnegative p z h) (Ne.symm hn)
        have hf := zeroError_continue_on_common_history p P Q hr hprior d hd h hN z hp
        rw [hs] at hf
        cases hf
      rw [hm0]
      exact historyCost_nonnegative p h
  · have hcut : (exclusiveCut p P Q).stop h ≠ false :=
      fun hs => hN ((exclusiveCut_stop_false_iff p P Q h).mp hs)
    rw [historyCost, if_neg hcut]
    exact historyCost_nonnegative p h

theorem exclusiveCut_extendedCost_le (p : FiniteProtocol Bool A Y)
    (P Q : FiniteLaw Y)
    (hr : ∀ h a z, p.observation h a z = PairResolution.row P Q z)
    (hprior : ∀ z, 0 < p.prior.mass z) (d : List (A × Y) → Bool)
    (hd : ZeroError p d) (hc : ∀ h a, 1 ≤ p.cost h a) :
    extendedCost (exclusiveCut p P Q) ≤ extendedCost p := by
  rw [extendedCost_eq_tsum_historyCost, extendedCost_eq_tsum_historyCost]
  exact ENNReal.tsum_le_tsum (fun h => ENNReal.ofReal_le_ofReal
    (exclusiveCut_historyCost_le p P Q hr hprior d hd hc h))


/-- Appending a common output is exactly the continuation condition for the cut. -/
theorem exclusiveCut_stop_append_false (p : FiniteProtocol Bool A Y)
    (P Q : FiniteLaw Y) (h : List (A × Y)) (e : A × Y) :
    (exclusiveCut p P Q).stop (h ++ [e]) = false ↔
      (exclusiveCut p P Q).stop h = false ∧ ¬ Decisive P Q e.2 := by
  rw [exclusiveCut_stop_false_iff, noDecisive_append, exclusiveCut_stop_false_iff]

/-- Adaptive action probabilities sum to one, so the cut has the fixed row's survival factor. -/
theorem exclusiveCut_active_children (p : FiniteProtocol Bool A Y)
    (P Q : FiniteLaw Y)
    (hr : ∀ h a z, p.observation h a z = PairResolution.row P Q z)
    (n : ℕ) (z : Bool) (h : List (A × Y)) :
    (∑ e : A × Y,
      if (h ++ [e]).length = n + 1 ∧ (exclusiveCut p P Q).stop (h ++ [e]) = false
      then prefixMass (exclusiveCut p P Q) z (h ++ [e]) else 0) =
    (if h.length = n ∧ (exclusiveCut p P Q).stop h = false
      then prefixMass (exclusiveCut p P Q) z h else 0) * (1 - labelExclusive P Q z) := by
  classical
  by_cases hc : h.length = n ∧ (exclusiveCut p P Q).stop h = false
  · rw [if_pos hc, Fintype.sum_prod_type]
    calc
      _ = ∑ a, prefixMass (exclusiveCut p P Q) z h * (p.policy h).mass a *
          ∑ y, (if Decisive P Q y then 0 else (PairResolution.row P Q z).mass y) := by
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y _
        by_cases hd : Decisive P Q y
        · rw [if_pos hd, mul_zero, if_neg]
          rintro ⟨_, hs⟩
          exact ((exclusiveCut_stop_append_false p P Q h (a, y)).mp hs).2 hd
        · rw [if_neg hd, if_pos]
          · rw [prefixMass_append, if_neg (by rw [hc.2]; decide)]
            change prefixMass (exclusiveCut p P Q) z h * (p.policy h).mass a *
              (p.observation h a z).mass y = _
            rw [hr]
          · exact ⟨by simp [hc.1],
              (exclusiveCut_stop_append_false p P Q h (a, y)).mpr ⟨hc.2, hd⟩⟩
      _ = _ := by
        simp_rw [continue_mass P Q z]
        rw [← Finset.sum_mul, ← Finset.mul_sum, (p.policy h).total, mul_one]
  · rw [if_neg hc, zero_mul]
    apply Finset.sum_eq_zero
    intro e _
    rw [if_neg]
    rintro ⟨hl, hs⟩
    apply hc
    refine ⟨?_, ((exclusiveCut_stop_append_false p P Q h e).mp hs).1⟩
    simp only [List.length_append, List.length_singleton] at hl
    omega

/-- The first-decisive cut has geometric survival under every adaptive finite action policy. -/
theorem exclusiveCut_activeMass (p : FiniteProtocol Bool A Y)
    (P Q : FiniteLaw Y)
    (hr : ∀ h a z, p.observation h a z = PairResolution.row P Q z)
    (n : ℕ) (z : Bool) :
    activeMass (exclusiveCut p P Q) n z =
      p.prior.mass z * (1 - labelExclusive P Q z) ^ n := by
  classical
  induction n with
  | zero =>
    unfold activeMass
    simp only [historySet, Finset.sum_singleton]
    have hs : (exclusiveCut p P Q).stop [] = false :=
      (exclusiveCut_stop_false_iff p P Q []).mpr (by simp [NoDecisive])
    rw [if_pos ⟨rfl, hs⟩, prefixMass_nil, pow_zero, mul_one]
    rfl
  | succ n ih =>
    unfold activeMass at ih ⊢
    have h0 : (if ([] : List (A × Y)).length = n + 1 ∧
        (exclusiveCut p P Q).stop [] = false
        then prefixMass (exclusiveCut p P Q) z [] else 0) = 0 :=
      if_neg (fun hc => Nat.succ_ne_zero n hc.1.symm)
    rw [historySet_sum_succ, h0, zero_add,
      Finset.sum_congr rfl (fun h _ => exclusiveCut_active_children p P Q hr n z h),
      ← Finset.sum_mul, ih, pow_succ]
    ring

theorem exclusiveCut_historyCost (p : FiniteProtocol Bool A Y)
    (P Q : FiniteLaw Y) (h : List (A × Y)) :
    historyCost (exclusiveCut p P Q) h =
      if (exclusiveCut p P Q).stop h = false
      then historyMass (exclusiveCut p P Q) h else 0 := by
  unfold historyCost
  by_cases hs : (exclusiveCut p P Q).stop h = false
  · rw [if_pos hs, if_pos hs]
    change historyMass (exclusiveCut p P Q) h * (∑ a, (p.policy h).mass a * 1) = _
    simp only [mul_one, (p.policy h).total]
  · rw [if_neg hs, if_neg hs]

theorem exclusiveCut_expectedCost_sum_active (p : FiniteProtocol Bool A Y)
    (P Q : FiniteLaw Y) (n : ℕ) :
    expectedCost (exclusiveCut p P Q) n (historyBank A Y n) =
      ∑ ℓ ∈ Finset.range n, ∑ z : Bool, activeMass (exclusiveCut p P Q) ℓ z := by
  classical
  rw [expectedCost_eq_historyCost]
  unfold chargedHistorySet
  rw [Finset.sum_filter, ResolutionAttainment.historySet_below_eq_levels n]
  apply Finset.sum_congr rfl
  intro ℓ _
  calc
    (∑ h ∈ historySet (A × Y) ℓ,
       if h.length = ℓ then historyCost (exclusiveCut p P Q) h else 0) =
      ∑ h ∈ historySet (A × Y) ℓ,
        if h.length = ℓ ∧ (exclusiveCut p P Q).stop h = false
        then historyMass (exclusiveCut p P Q) h else 0 := by
          apply Finset.sum_congr rfl
          intro h _
          rw [exclusiveCut_historyCost]
          by_cases hl : h.length = ℓ <;> simp [hl]
    _ = ∑ z : Bool, activeMass (exclusiveCut p P Q) ℓ z := by
          unfold activeMass historyMass
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro h _
          by_cases hv : h.length = ℓ ∧ (exclusiveCut p P Q).stop h = false <;> simp [hv]

/-- Adaptive actions do not change the exact cost of the first-decisive cut. -/
theorem exclusiveCut_extendedCost_eq_firstExclusive (p : FiniteProtocol Bool A Y)
    (P Q : FiniteLaw Y)
    (hr : ∀ h a z, p.observation h a z = PairResolution.row P Q z) :
    extendedCost (exclusiveCut p P Q) = extendedCost (firstExclusiveWith p.prior P Q) := by
  unfold extendedCost
  congr 1
  funext n
  rw [exclusiveCut_expectedCost_sum_active, firstExclusiveWith_expectedCost_sum_active]
  simp_rw [exclusiveCut_activeMass p P Q hr, firstExclusiveWith_activeMass]

/-- The weighted reciprocal exclusive mass is a universal lower bound on every zero-error
adaptive protocol with the fixed rows and at least unit cost per reading. -/
theorem zeroError_cost_ge_weighted_reciprocal (p : FiniteProtocol Bool A Y)
    (P Q : FiniteLaw Y)
    (hr : ∀ h a z, p.observation h a z = PairResolution.row P Q z)
    (hprior : ∀ z, 0 < p.prior.mass z) (d : List (A × Y) → Bool)
    (hd : ZeroError p d) (hc : ∀ h a, 1 ≤ p.cost h a)
    (ha : 0 < exclusiveMass P Q) (hb : 0 < exclusiveMass Q P) :
    ENNReal.ofReal (p.prior.mass true / exclusiveMass P Q +
      (1 - p.prior.mass true) / exclusiveMass Q P) ≤ extendedCost p := by
  rw [← firstExclusiveWith_weighted_cost p.prior P Q ha hb,
    ← exclusiveCut_extendedCost_eq_firstExclusive p P Q hr]
  exact exclusiveCut_extendedCost_le p P Q hr hprior d hd hc

/-- The unit-action first-exclusive protocol attains the universal minimum. -/
theorem firstExclusiveWith_is_optimal (p : FiniteProtocol Bool A Y)
    (P Q : FiniteLaw Y)
    (hr : ∀ h a z, p.observation h a z = PairResolution.row P Q z)
    (hprior : ∀ z, 0 < p.prior.mass z) (d : List (A × Y) → Bool)
    (hd : ZeroError p d) (hc : ∀ h a, 1 ≤ p.cost h a) :
    extendedCost (firstExclusiveWith p.prior P Q) ≤ extendedCost p := by
  rw [← exclusiveCut_extendedCost_eq_firstExclusive p P Q hr]
  exact exclusiveCut_extendedCost_le p P Q hr hprior d hd hc

/-! ## No zero error at a finite horizon

The protocols are finite and adaptive, and the conditional rows are fixed. -/

/-- A finite law gives positive mass to some point. -/
theorem finiteLaw_exists_pos (L : FiniteLaw A) : ∃ a, 0 < L.mass a := by
  by_contra hn
  push_neg at hn
  have h0 : ∑ a, L.mass a = 0 :=
    Finset.sum_eq_zero (fun a _ => le_antisymm (hn a) (L.nonnegative a))
  have h1 := L.total
  rw [h0] at h1
  exact zero_ne_one h1

/-- Fixed rows sharing an output and positive priors: a zero-error protocol has, at every length,
a history without decisive outputs, of positive mass under the label, at which it has not
stopped. -/
theorem zeroError_common_history_of_length (p : FiniteProtocol Bool A Y)
    (P Q : FiniteLaw Y)
    (hr : ∀ h a z, p.observation h a z = PairResolution.row P Q z)
    (hprior : ∀ z, 0 < p.prior.mass z) (d : List (A × Y) → Bool)
    (hd : ZeroError p d) (y : Y) (hPy : 0 < P.mass y) (hQy : 0 < Q.mass y)
    (z : Bool) (n : ℕ) :
    ∃ h : List (A × Y), h.length = n ∧ NoDecisive P Q h ∧ 0 < prefixMass p z h ∧
      p.stop h = false := by
  have hy : ¬ Decisive P Q y := fun h => Or.elim h hPy.ne' hQy.ne'
  induction n with
  | zero =>
    have hN : NoDecisive P Q ([] : List (A × Y)) := fun _ he => by simp at he
    have hpos : 0 < prefixMass p z ([] : List (A × Y)) := by
      rw [prefixMass_nil]
      exact hprior z
    exact ⟨[], rfl, hN, hpos,
      zeroError_continue_on_common_history p P Q hr hprior d hd [] hN z hpos⟩
  | succ n ih =>
    obtain ⟨h, hlen, hN, hpos, hstop⟩ := ih
    obtain ⟨a, ha⟩ := finiteLaw_exists_pos (p.policy h)
    have hs : ¬ p.stop h = true := by simp [hstop]
    have hN' : NoDecisive P Q (h ++ [(a, y)]) :=
      (noDecisive_append P Q h (a, y)).mpr ⟨hN, hy⟩
    have hpos' : 0 < prefixMass p z (h ++ [(a, y)]) := by
      rw [prefixMass_append, if_neg hs, hr h a z]
      exact mul_pos (mul_pos hpos ha) (row_pos_of_not_decisive P Q y hy z)
    exact ⟨h ++ [(a, y)], by simp [hlen], hN', hpos',
      zeroError_continue_on_common_history p P Q hr hprior d hd _ hN' z hpos'⟩

/-- Under fixed rows sharing an output and positive priors, every zero-error protocol has
positive running mass under each label after every number of readings. -/
theorem zeroError_activeMass_pos (p : FiniteProtocol Bool A Y)
    (P Q : FiniteLaw Y)
    (hr : ∀ h a z, p.observation h a z = PairResolution.row P Q z)
    (hprior : ∀ z, 0 < p.prior.mass z) (d : List (A × Y) → Bool)
    (hd : ZeroError p d) (y : Y) (hPy : 0 < P.mass y) (hQy : 0 < Q.mass y)
    (n : ℕ) (z : Bool) :
    0 < activeMass p n z := by
  obtain ⟨h, hlen, -, hpos, hstop⟩ :=
    zeroError_common_history_of_length p P Q hr hprior d hd y hPy hQy z n
  have hmem : h ∈ historySet (A × Y) n := (mem_historySet n h).mpr hlen.le
  have hterm : (if h.length = n ∧ p.stop h = false then prefixMass p z h else 0) =
      prefixMass p z h := if_pos ⟨hlen, hstop⟩
  unfold activeMass
  refine lt_of_lt_of_le hpos (le_of_eq_of_le hterm.symm ?_)
  refine Finset.single_le_sum
    (f := fun g => if g.length = n ∧ p.stop g = false then prefixMass p z g else 0)
    (fun g _ => ?_) hmem
  show 0 ≤ (if g.length = n ∧ p.stop g = false then prefixMass p z g else 0)
  split_ifs
  · exact prefixMass_nonnegative p z g
  · exact le_rfl

/-- Under the same hypotheses, no protocol that stops at every history of some length `N`
recovers the label with zero error. -/
theorem zeroError_no_finite_horizon (p : FiniteProtocol Bool A Y)
    (P Q : FiniteLaw Y)
    (hr : ∀ h a z, p.observation h a z = PairResolution.row P Q z)
    (hprior : ∀ z, 0 < p.prior.mass z) (d : List (A × Y) → Bool)
    (hd : ZeroError p d) (y : Y) (hPy : 0 < P.mass y) (hQy : 0 < Q.mass y)
    (N : ℕ) (hN : ∀ h : List (A × Y), h.length = N → p.stop h = true) : False := by
  obtain ⟨h, hlen, -, -, hstop⟩ :=
    zeroError_common_history_of_length p P Q hr hprior d hd y hPy hQy true N
  rw [hN h hlen] at hstop
  cases hstop

/-- The hypotheses of the positive-mass result are satisfiable: the erasure rows have the common
output `none` and exclusive outputs, and the first-definite protocol meets every hypothesis. -/
theorem firstDefinite_activeMass_pos (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) (n : ℕ) (z : Bool) :
    0 < activeMass (firstDefinite q hq0 hq1) n z :=
  zeroError_activeMass_pos (firstDefinite q hq0 hq1)
    (erasureLaw q hq0 hq1 true) (erasureLaw q hq0 hq1 false)
    (fun _ _ z => by cases z <;> rfl)
    (fun _ => by change (0 : ℝ) < 1 / 2; norm_num)
    firstDefiniteDecoder (fun z h hw => firstDefinite_zero_error q hq0 hq1 z h hw)
    none (by change 0 < 1 - q; linarith) (by change 0 < 1 - q; linarith) n z

end Optimality

#check @NoDecisive
#print axioms NoDecisive
#check @noDecisive_append
#print axioms noDecisive_append
#check @row_pos_of_not_decisive
#print axioms row_pos_of_not_decisive
#check @prefixMass_pos_on_common_history
#print axioms prefixMass_pos_on_common_history
#check @zeroError_continue_on_common_history
#print axioms zeroError_continue_on_common_history
#check @exclusiveCut
#print axioms exclusiveCut
#check @exclusiveCut_stop_false_iff
#print axioms exclusiveCut_stop_false_iff
#check @exclusiveCut_prefixMass
#print axioms exclusiveCut_prefixMass
#check @exclusiveCut_historyCost_le
#print axioms exclusiveCut_historyCost_le
#check @exclusiveCut_extendedCost_le
#print axioms exclusiveCut_extendedCost_le

#check @exclusiveCut_stop_append_false
#print axioms exclusiveCut_stop_append_false
#check @exclusiveCut_active_children
#print axioms exclusiveCut_active_children
#check @exclusiveCut_activeMass
#print axioms exclusiveCut_activeMass
#check @exclusiveCut_historyCost
#print axioms exclusiveCut_historyCost
#check @exclusiveCut_expectedCost_sum_active
#print axioms exclusiveCut_expectedCost_sum_active
#check @exclusiveCut_extendedCost_eq_firstExclusive
#print axioms exclusiveCut_extendedCost_eq_firstExclusive
#check @zeroError_cost_ge_weighted_reciprocal
#print axioms zeroError_cost_ge_weighted_reciprocal
#check @firstExclusiveWith_is_optimal
#print axioms firstExclusiveWith_is_optimal
#check @finiteLaw_exists_pos
#print axioms finiteLaw_exists_pos
#check @zeroError_common_history_of_length
#print axioms zeroError_common_history_of_length
#check @zeroError_activeMass_pos
#print axioms zeroError_activeMass_pos
#check @zeroError_no_finite_horizon
#print axioms zeroError_no_finite_horizon
#check @firstDefinite_activeMass_pos
#print axioms firstDefinite_activeMass_pos

end OperatorKO7.Meta.BoundaryObserver.ErasurePriorCompletion
