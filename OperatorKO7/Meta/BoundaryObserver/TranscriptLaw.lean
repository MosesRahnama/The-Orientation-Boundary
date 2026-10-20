import OperatorKO7.Meta.BoundaryObserver.ProtocolResolution
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option autoImplicit false

/-!
# The information of the infinite transcript

The transcript mass of a protocol is its prefix mass at the histories where it stops. These masses
are summable over all finite histories, their total is at most the prior, and the deficit is the
limit of the mass still running at horizon n. The finite-horizon conditional uncertainty splits
into the uncertainty of the transcripts stopped by n and the uncertainty of the runs still active
at n; the first increases to the transcript uncertainty, so the information limit of
ProtocolResolution equals the prior entropy minus the transcript uncertainty minus the limit of
the active uncertainty. Under almost sure stopping the active uncertainty tends to zero and the
information limit is the mutual information of the transcript law.
Relation: finite protocols and their countable transcript laws. External trust: none.
-/

namespace OperatorKO7.Meta.BoundaryObserver.TranscriptLaw

open scoped BigOperators
open ProtocolResolution Filter Topology

variable {Z A Y : Type} [Fintype Z] [Fintype A] [Fintype Y]

/-! ## L1: the transcript mass and the split of the stopped mass -/

/-- The mass of the experiment that runs until it stops, at a stopped history. -/
noncomputable def transcriptMass (p : FiniteProtocol Z A Y) (z : Z) (h : List (A × Y)) : ℝ :=
  if p.stop h = true then prefixMass p z h else 0

theorem transcriptMass_nonneg (p : FiniteProtocol Z A Y) (z : Z) (h : List (A × Y)) :
    0 ≤ transcriptMass p z h := by
  unfold transcriptMass
  split_ifs
  · exact prefixMass_nonnegative p z h
  · exact le_rfl

/-- The mass still running at horizon n. -/
noncomputable def activeMass (p : FiniteProtocol Z A Y) (n : ℕ) (z : Z) : ℝ :=
  ∑ h ∈ historySet (A × Y) n, if h.length = n ∧ p.stop h = false then prefixMass p z h else 0

theorem activeMass_nonneg (p : FiniteProtocol Z A Y) (n : ℕ) (z : Z) : 0 ≤ activeMass p n z := by
  apply Finset.sum_nonneg
  intro h _
  split_ifs
  · exact prefixMass_nonnegative p z h
  · exact le_rfl

/-- The stopped mass at horizon n is the transcript mass below the horizon plus the active mass. -/
theorem stoppedMass_eq_transcript_add_active (p : FiniteProtocol Z A Y) (n : ℕ) (z : Z)
    (h : List (A × Y)) :
    stoppedMass p n z h = (if h.length ≤ n then transcriptMass p z h else 0) +
      (if h.length = n ∧ p.stop h = false then prefixMass p z h else 0) := by
  unfold stoppedMass transcriptMass
  cases hs : p.stop h
  · by_cases he : h.length = n <;> simp [he]
  · simp

/-- The transcript masses of a bank and the active mass at its horizon add to the prior. -/
theorem transcript_add_active_eq_prior (p : FiniteProtocol Z A Y) (n : ℕ) (z : Z) :
    (∑ h ∈ historySet (A × Y) n, transcriptMass p z h) + activeMass p n z = p.prior.mass z := by
  rw [← historySet_stoppedMass_target_marginal p n z, activeMass, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro h hh
  rw [stoppedMass_eq_transcript_add_active, if_pos ((mem_historySet n h).mp hh)]

/-! ## L2: the transcript total and the escaping mass -/

/-- The banks of bounded length exhaust the finite histories. -/
theorem historySet_tendsto_atTop :
    Tendsto (fun n => historySet (A × Y) n) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro s
  refine ⟨s.sup List.length, fun n hn => ?_⟩
  intro h hh
  exact (mem_historySet n h).mpr ((Finset.le_sup (f := List.length) hh).trans hn)

theorem transcript_sum_le_prior (p : FiniteProtocol Z A Y) (z : Z)
    (s : Finset (List (A × Y))) : ∑ h ∈ s, transcriptMass p z h ≤ p.prior.mass z := by
  obtain ⟨n, hn⟩ := (tendsto_atTop_atTop.mp historySet_tendsto_atTop) s
  have hsub : s ⊆ historySet (A × Y) n := hn n le_rfl
  calc ∑ h ∈ s, transcriptMass p z h
      ≤ ∑ h ∈ historySet (A × Y) n, transcriptMass p z h :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun h _ _ => transcriptMass_nonneg p z h)
    _ ≤ p.prior.mass z := by
        have hp := transcript_add_active_eq_prior p n z
        have ha := activeMass_nonneg p n z
        linarith

/-- The transcript masses are summable over all finite histories. -/
theorem transcriptMass_summable (p : FiniteProtocol Z A Y) (z : Z) :
    Summable (transcriptMass p z) :=
  summable_of_sum_le (fun h => transcriptMass_nonneg p z h) (transcript_sum_le_prior p z)

/-- The total transcript mass of a target. -/
noncomputable def transcriptTotal (p : FiniteProtocol Z A Y) (z : Z) : ℝ :=
  ∑' h, transcriptMass p z h

theorem transcript_sum_tendsto (p : FiniteProtocol Z A Y) (z : Z) :
    Tendsto (fun n => ∑ h ∈ historySet (A × Y) n, transcriptMass p z h) atTop
      (𝓝 (transcriptTotal p z)) :=
  (transcriptMass_summable p z).hasSum.comp historySet_tendsto_atTop

theorem transcriptTotal_le_prior (p : FiniteProtocol Z A Y) (z : Z) :
    transcriptTotal p z ≤ p.prior.mass z :=
  le_of_tendsto' (transcript_sum_tendsto p z) (fun _ => transcript_sum_le_prior p z _)

theorem activeMass_eq (p : FiniteProtocol Z A Y) (n : ℕ) (z : Z) :
    activeMass p n z = p.prior.mass z - ∑ h ∈ historySet (A × Y) n, transcriptMass p z h := by
  have hp := transcript_add_active_eq_prior p n z
  linarith

/-- The running mass decreases with the horizon. -/
theorem activeMass_antitone (p : FiniteProtocol Z A Y) (z : Z) :
    Antitone (fun n => activeMass p n z) := by
  intro n m hnm
  simp only [activeMass_eq]
  have hs : ∑ h ∈ historySet (A × Y) n, transcriptMass p z h ≤
      ∑ h ∈ historySet (A × Y) m, transcriptMass p z h :=
    Finset.sum_le_sum_of_subset_of_nonneg (historySet_mono hnm)
      (fun h _ _ => transcriptMass_nonneg p z h)
  linarith

/-- The running mass converges to the escaping mass, the prior minus the transcript total. -/
theorem activeMass_tendsto (p : FiniteProtocol Z A Y) (z : Z) :
    Tendsto (fun n => activeMass p n z) atTop (𝓝 (p.prior.mass z - transcriptTotal p z)) := by
  simp only [activeMass_eq]
  exact tendsto_const_nhds.sub (transcript_sum_tendsto p z)

/-- Almost sure stopping of a target makes its transcript law carry the whole prior mass. -/
theorem transcriptTotal_eq_prior_of_stops (p : FiniteProtocol Z A Y) (z : Z)
    (hstop : Tendsto (fun n => activeMass p n z) atTop (𝓝 0)) :
    transcriptTotal p z = p.prior.mass z := by
  have hu := tendsto_nhds_unique (activeMass_tendsto p z) hstop
  linarith

/-- A target's stopped transcript mass is its complete prior mass exactly
when that target has vanishing active mass. The converse needs no finite
expected stopping time. -/
theorem activeMass_tendsto_zero_iff_transcriptTotal_eq_prior
    (p : FiniteProtocol Z A Y) (z : Z) :
    Tendsto (fun n => activeMass p n z) atTop (𝓝 0) ↔
      transcriptTotal p z = p.prior.mass z := by
  constructor
  · exact transcriptTotal_eq_prior_of_stops p z
  · intro htotal
    simpa [htotal] using activeMass_tendsto p z

/-- A zero-prior target has zero active mass at every horizon, regardless
of the stopping rule. -/
theorem activeMass_eq_zero_of_prior_zero (p : FiniteProtocol Z A Y) (z : Z)
    (hz : p.prior.mass z = 0) (n : ℕ) : activeMass p n z = 0 := by
  have hbal := transcript_add_active_eq_prior p n z
  have hstop : 0 ≤ ∑ h ∈ historySet (A × Y) n, transcriptMass p z h :=
    Finset.sum_nonneg (fun h _ => transcriptMass_nonneg p z h)
  have hact := activeMass_nonneg p n z
  rw [hz] at hbal
  linarith

/-- Targetwise stopping follows from stopping on the positive-prior
targets only; zero-prior targets contribute no active mass. -/
theorem stops_of_positive_prior (p : FiniteProtocol Z A Y)
    (hstop : ∀ z, 0 < p.prior.mass z →
      Tendsto (fun n => activeMass p n z) atTop (𝓝 0)) :
    ∀ z, Tendsto (fun n => activeMass p n z) atTop (𝓝 0) := by
  intro z
  rcases (p.prior.nonnegative z).eq_or_lt with hz | hz
  · have hzero : ∀ n, activeMass p n z = 0 :=
      activeMass_eq_zero_of_prior_zero p z hz.symm
    simp [hzero]
  · exact hstop z hz


/-! ## L3: the finite uncertainty cut along stopped and active histories -/

/-- The conditional uncertainty carried by the stopped transcripts. -/
noncomputable def transcriptUncertainty (p : FiniteProtocol Z A Y) : ℝ :=
  ∑' h, massUncertainty (fun z => transcriptMass p z h)

/-- The conditional uncertainty carried by the runs still active at horizon n. -/
noncomputable def activeUncertainty (p : FiniteProtocol Z A Y) (n : ℕ) : ℝ :=
  ∑ h ∈ historySet (A × Y) n,
    if h.length = n ∧ p.stop h = false then historyUncertainty p h else 0

theorem massUncertainty_transcript (p : FiniteProtocol Z A Y) (h : List (A × Y)) :
    massUncertainty (fun z => transcriptMass p z h) =
      if p.stop h = true then historyUncertainty p h else 0 := by
  unfold transcriptMass historyUncertainty
  cases hs : p.stop h <;> simp [massUncertainty_zero]

theorem transcriptUncertainty_term_nonneg (p : FiniteProtocol Z A Y) (h : List (A × Y)) :
    0 ≤ massUncertainty (fun z => transcriptMass p z h) := by
  rw [massUncertainty_transcript]
  split_ifs
  · exact historyUncertainty_nonnegative p h
  · exact le_rfl

theorem activeUncertainty_nonneg (p : FiniteProtocol Z A Y) (n : ℕ) :
    0 ≤ activeUncertainty p n := by
  apply Finset.sum_nonneg
  intro h _
  split_ifs
  · exact historyUncertainty_nonnegative p h
  · exact le_rfl

/-- The uncertainty of a stopped slice is its transcript part plus its active part. -/
theorem massUncertainty_stopped_split (p : FiniteProtocol Z A Y) (n : ℕ) (h : List (A × Y))
    (hh : h.length ≤ n) :
    massUncertainty (fun z => stoppedMass p n z h) =
      massUncertainty (fun z => transcriptMass p z h) +
        (if h.length = n ∧ p.stop h = false then historyUncertainty p h else 0) := by
  rw [massUncertainty_stopped, massUncertainty_transcript]
  unfold boundaryValue
  cases hs : p.stop h
  · by_cases he : h.length = n
    · simp [he]
    · simp [he]
  · simp [hh]

theorem transcriptUncertainty_sum_le (p : FiniteProtocol Z A Y) (s : Finset (List (A × Y))) :
    ∑ h ∈ s, massUncertainty (fun z => transcriptMass p z h) ≤ entropy p.prior.mass := by
  obtain ⟨n, hn⟩ := (tendsto_atTop_atTop.mp historySet_tendsto_atTop) s
  have hsub : s ⊆ historySet (A × Y) n := hn n le_rfl
  calc ∑ h ∈ s, massUncertainty (fun z => transcriptMass p z h)
      ≤ ∑ h ∈ historySet (A × Y) n, massUncertainty (fun z => transcriptMass p z h) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun h _ _ => transcriptUncertainty_term_nonneg p h)
    _ ≤ ∑ h ∈ historySet (A × Y) n, massUncertainty (fun z => stoppedMass p n z h) := by
        apply Finset.sum_le_sum
        intro h hh
        rw [massUncertainty_stopped_split p n h ((mem_historySet n h).mp hh)]
        have ha : 0 ≤ (if h.length = n ∧ p.stop h = false then historyUncertainty p h else 0) := by
          split_ifs
          · exact historyUncertainty_nonnegative p h
          · exact le_rfl
        linarith
    _ ≤ entropy p.prior.mass := by
        have he := terminalMI_eq_entropy_sub p n _ (historyBank_complete A Y n)
        have hn0 := terminalMI_nonnegative p n _ (historyBank_complete A Y n)
        linarith

theorem transcriptUncertainty_summable (p : FiniteProtocol Z A Y) :
    Summable (fun h => massUncertainty (fun z => transcriptMass p z h)) :=
  summable_of_sum_le (fun h => transcriptUncertainty_term_nonneg p h)
    (transcriptUncertainty_sum_le p)

theorem transcriptUncertainty_tendsto (p : FiniteProtocol Z A Y) :
    Tendsto (fun n => ∑ h ∈ historySet (A × Y) n, massUncertainty (fun z => transcriptMass p z h))
      atTop (𝓝 (transcriptUncertainty p)) :=
  (transcriptUncertainty_summable p).hasSum.comp historySet_tendsto_atTop

theorem transcriptUncertainty_le_entropy (p : FiniteProtocol Z A Y) :
    transcriptUncertainty p ≤ entropy p.prior.mass :=
  le_of_tendsto' (transcriptUncertainty_tendsto p) (fun _ => transcriptUncertainty_sum_le p _)

/-- The finite-horizon information is the prior entropy minus the transcript part minus the
active part of the conditional uncertainty. -/
theorem terminalMI_eq_transcript_sub_active (p : FiniteProtocol Z A Y) (n : ℕ) :
    terminalMI p n (historyBank A Y n) = entropy p.prior.mass -
      (∑ h ∈ historySet (A × Y) n, massUncertainty (fun z => transcriptMass p z h)) -
        activeUncertainty p n := by
  rw [terminalMI_eq_entropy_sub p n _ (historyBank_complete A Y n)]
  have hs : (∑ h ∈ historySet (A × Y) n, massUncertainty (fun z => stoppedMass p n z h)) =
      (∑ h ∈ historySet (A × Y) n, massUncertainty (fun z => transcriptMass p z h)) +
        activeUncertainty p n := by
    rw [activeUncertainty, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro h hh
    exact massUncertainty_stopped_split p n h ((mem_historySet n h).mp hh)
  rw [hs]
  ring

/-! ## L4: the information limit and the tail -/

/-- The uncertainty carried by the runs that never stop, as the limit of the active part. -/
noncomputable def tailUncertainty (p : FiniteProtocol Z A Y) : ℝ :=
  entropy p.prior.mass - transcriptUncertainty p - informationLimit p

theorem activeUncertainty_tendsto (p : FiniteProtocol Z A Y) :
    Tendsto (fun n => activeUncertainty p n) atTop (𝓝 (tailUncertainty p)) := by
  have h1 := terminalMI_tendsto_informationLimit p
  have h2 := transcriptUncertainty_tendsto p
  have he : (fun n => activeUncertainty p n) = fun n => entropy p.prior.mass -
      (∑ h ∈ historySet (A × Y) n, massUncertainty (fun z => transcriptMass p z h)) -
        terminalMI p n (historyBank A Y n) := by
    funext n
    rw [terminalMI_eq_transcript_sub_active]
    ring
  rw [he]
  exact (tendsto_const_nhds.sub h2).sub h1

theorem tail_nonneg (p : FiniteProtocol Z A Y) : 0 ≤ tailUncertainty p :=
  ge_of_tendsto' (activeUncertainty_tendsto p) (activeUncertainty_nonneg p)

/-- The information limit is the prior entropy minus the transcript uncertainty minus the tail. -/
theorem informationLimit_eq_transcript (p : FiniteProtocol Z A Y) :
    informationLimit p = entropy p.prior.mass - transcriptUncertainty p - tailUncertainty p := by
  unfold tailUncertainty
  ring

/-! ## L5: almost sure stopping -/

/-- A normalized law on a finite carrier has entropy at most log₂ of the carrier's size. -/
theorem entropy_le_logb_card [Nonempty Z] (m : Z → ℝ) (hm0 : ∀ z, 0 ≤ m z)
    (hm1 : ∑ z, m z = 1) : entropy m ≤ Real.logb 2 (Fintype.card Z) := by
  rw [entropy_eq_HBits]
  exact OperatorKO7.Meta.InformationalIncompleteness.FiniteSupportEntropy.HBits_le_logb_card m hm0 hm1

theorem historyUncertainty_le [Nonempty Z] (p : FiniteProtocol Z A Y) (h : List (A × Y)) :
    historyUncertainty p h ≤ historyMass p h * Real.logb 2 (Fintype.card Z) := by
  unfold historyUncertainty
  rw [massUncertainty_prefix]
  rcases (historyMass_nonnegative p h).eq_or_lt with hw | hw
  · rw [← hw]
    simp
  · exact mul_le_mul_of_nonneg_left
      (entropy_le_logb_card _ (posterior_nonnegative p h) (posterior_total p h hw)) hw.le

/-- The active uncertainty is at most the active mass times log₂ of the target count. -/
theorem activeUncertainty_le_activeMass [Nonempty Z] (p : FiniteProtocol Z A Y) (n : ℕ) :
    activeUncertainty p n ≤ (∑ z, activeMass p n z) * Real.logb 2 (Fintype.card Z) := by
  have hz : (∑ z, activeMass p n z) = ∑ h ∈ historySet (A × Y) n,
      if h.length = n ∧ p.stop h = false then historyMass p h else 0 := by
    unfold activeMass historyMass
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro h _
    split_ifs <;> simp
  rw [hz, Finset.sum_mul, activeUncertainty]
  apply Finset.sum_le_sum
  intro h _
  split_ifs
  · exact historyUncertainty_le p h
  · simp

/-- Under almost sure stopping the tail vanishes. -/
theorem tail_eq_zero_of_stops [Nonempty Z] (p : FiniteProtocol Z A Y)
    (hstop : ∀ z, Tendsto (fun n => activeMass p n z) atTop (𝓝 0)) :
    tailUncertainty p = 0 := by
  have hsum : Tendsto (fun n => (∑ z, activeMass p n z) * Real.logb 2 (Fintype.card Z)) atTop
      (𝓝 0) := by
    have ht := tendsto_finset_sum (Finset.univ : Finset Z) (fun z _ => hstop z)
    simpa using ht.mul_const (Real.logb 2 (Fintype.card Z))
  apply le_antisymm _ (tail_nonneg p)
  exact le_of_tendsto_of_tendsto' (activeUncertainty_tendsto p) hsum
    (fun n => activeUncertainty_le_activeMass p n)

/-- The mutual information of the transcript law: prior entropy minus transcript uncertainty. -/
noncomputable def transcriptInformation (p : FiniteProtocol Z A Y) : ℝ :=
  entropy p.prior.mass - transcriptUncertainty p

/-- Under almost sure stopping the information of all finite prefixes is the information of the
transcript law: the information of the infinite experiment. -/
theorem informationLimit_eq_transcriptInformation [Nonempty Z] (p : FiniteProtocol Z A Y)
    (hstop : ∀ z, Tendsto (fun n => activeMass p n z) atTop (𝓝 0)) :
    informationLimit p = transcriptInformation p := by
  rw [informationLimit_eq_transcript, tail_eq_zero_of_stops p hstop, sub_zero]
  rfl

/-- The conditional information limit is the initial-record average of the transcript
informations when every initial record stops almost surely. -/
theorem conditionalInformationLimit_eq_transcript {H0 : Type} [Fintype H0] [Nonempty Z]
    (p : ConditionalProtocol H0 Z A Y)
    (hstop : ∀ u z, Tendsto (fun n => activeMass (p.given u) n z) atTop (𝓝 0)) :
    conditionalInformationLimit p =
      ∑ u, p.initialRecord.mass u * transcriptInformation (p.given u) := by
  unfold conditionalInformationLimit
  apply Finset.sum_congr rfl
  intro u _
  rw [informationLimit_eq_transcriptInformation (p.given u) (hstop u)]


/-! ## A normalized joint law on the countable set of stopped histories -/

/-- A target-finite joint probability law with summable history masses.
The target marginal and conditional-uncertainty sum are part of its verified
probability data, not a supplied mutual-information conclusion. -/
structure CountableTranscriptJointLaw (Z E : Type) [Fintype Z] where
  prior : FiniteLaw Z
  cell : Z → E → ℝ
  nonnegative : ∀ z h, 0 ≤ cell z h
  summable : ∀ z, Summable (cell z)
  target_marginal : ∀ z, (∑' h, cell z h) = prior.mass z
  uncertainty_summable : Summable (fun h => massUncertainty (fun z => cell z h))

namespace CountableTranscriptJointLaw

variable {Z E : Type} [Fintype Z]

/-- The iterated total of this genuine joint law is one. -/
theorem total (L : CountableTranscriptJointLaw Z E) :
    (∑ z, ∑' h, L.cell z h) = 1 := by
  calc
    (∑ z, ∑' h, L.cell z h) = ∑ z, L.prior.mass z := by
      apply Finset.sum_congr rfl
      intro z _
      exact L.target_marginal z
    _ = 1 := L.prior.total

/-- The probability of a stopped history under the joint law. -/
noncomputable def historyMass (L : CountableTranscriptJointLaw Z E) (h : E) : ℝ :=
  ∑ z, L.cell z h

/-- The posterior given a positive-mass stopped history. -/
noncomputable def posterior (L : CountableTranscriptJointLaw Z E) (h : E) (z : Z) : ℝ :=
  L.cell z h / L.historyMass h

theorem historyMass_nonnegative (L : CountableTranscriptJointLaw Z E) (h : E) :
    0 ≤ L.historyMass h :=
  Finset.sum_nonneg (fun z _ => L.nonnegative z h)

theorem cell_le_historyMass (L : CountableTranscriptJointLaw Z E) (h : E) (z : Z) :
    L.cell z h ≤ L.historyMass h :=
  Finset.single_le_sum (fun y _ => L.nonnegative y h) (Finset.mem_univ z)

/-- Each joint cell is bounded by its target marginal. In particular, a
positive joint cell forces a positive prior, with no support axiom added. -/
theorem cell_le_prior (L : CountableTranscriptJointLaw Z E) (h : E) (z : Z) :
    L.cell z h ≤ L.prior.mass z := by
  calc
    L.cell z h ≤ ∑' t, L.cell z t :=
      (L.summable z).le_tsum h (fun t _ => L.nonnegative z t)
    _ = L.prior.mass z := L.target_marginal z

theorem cell_zero_of_historyMass_zero (L : CountableTranscriptJointLaw Z E) (h : E)
    (hw : L.historyMass h = 0) (z : Z) : L.cell z h = 0 := by
  exact le_antisymm ((L.cell_le_historyMass h z).trans_eq hw) (L.nonnegative z h)

theorem posterior_total (L : CountableTranscriptJointLaw Z E) (h : E)
    (hw : 0 < L.historyMass h) :
    ∑ z, L.posterior h z = 1 := by
  unfold posterior
  rw [← Finset.sum_div]
  exact div_self hw.ne'

theorem historyMass_mul_posterior (L : CountableTranscriptJointLaw Z E) (h : E) (z : Z) :
    L.historyMass h * L.posterior h z = L.cell z h := by
  by_cases hw : L.historyMass h = 0
  · rw [hw, zero_mul, L.cell_zero_of_historyMass_zero h hw z]
  · unfold posterior
    calc
      L.historyMass h * (L.cell z h / L.historyMass h) =
          L.cell z h * (L.historyMass h / L.historyMass h) := by ring
      _ = L.cell z h := by rw [div_self hw, mul_one]

/-- Each stopped-history uncertainty is exactly its probability times
the entropy of the posterior law; zero-mass histories contribute zero. -/
theorem uncertainty_eq_weighted_posterior (L : CountableTranscriptJointLaw Z E) (h : E) :
    massUncertainty (fun z => L.cell z h) =
      L.historyMass h * entropy (L.posterior h) := by
  rcases (L.historyMass_nonnegative h).eq_or_lt with hw | hw
  · have hm : (fun z => L.cell z h) = (fun _ : Z => 0) := by
      funext z
      exact L.cell_zero_of_historyMass_zero h hw.symm z
    rw [hm, massUncertainty_zero, ← hw, zero_mul]
  · have hm : (fun z => L.cell z h) =
        (fun z => L.historyMass h * L.posterior h z) := by
      funext z
      exact (L.historyMass_mul_posterior h z).symm
    rw [hm, massUncertainty_scale,
      massUncertainty_of_total_one _ (L.posterior_total h hw)]

/-- Actual logarithmic joint/product ratio contribution in bits.
A zero joint cell contributes zero, including zero-marginal cases. -/
noncomputable def logRatioTerm (L : CountableTranscriptJointLaw Z E) (z : Z) (h : E) : ℝ :=
  if L.cell z h = 0 then 0
  else L.cell z h * Real.log
    (L.cell z h / (L.prior.mass z * L.historyMass h)) / Real.log 2

/-- The logarithmic ratio is well-formed on every positive joint cell,
because both of its marginals are then positive. -/
theorem logRatioTerm_eq_expanded (L : CountableTranscriptJointLaw Z E) (z : Z) (h : E) :
    L.logRatioTerm z h =
      (L.cell z h * Real.log (L.cell z h) -
        L.cell z h * Real.log (L.prior.mass z) -
        L.cell z h * Real.log (L.historyMass h)) / Real.log 2 := by
  rcases (L.nonnegative z h).eq_or_lt with hc | hc
  · have hz : L.cell z h = 0 := hc.symm
    simp [logRatioTerm, hz]
  · have hprior : 0 < L.prior.mass z := hc.trans_le (L.cell_le_prior h z)
    have hhist : 0 < L.historyMass h := hc.trans_le (L.cell_le_historyMass h z)
    have hcell : L.cell z h ≠ 0 := hc.ne'
    simp only [logRatioTerm, hcell, if_false]
    rw [Real.log_div hcell (mul_ne_zero hprior.ne' hhist.ne'),
      Real.log_mul hprior.ne' hhist.ne']
    ring

/-- Entropy paid by the prior labels at this recorded history, with genuine
joint-cell weights instead of a postulated information number. -/
noncomputable def crossEntropyAt (L : CountableTranscriptJointLaw Z E) (h : E) : ℝ :=
  ∑ z, -(L.cell z h * Real.log (L.prior.mass z)) / Real.log 2

/-- The prior-weighted countable cross-entropy series is summable. -/
theorem crossEntropyAt_summable (L : CountableTranscriptJointLaw Z E) :
    Summable L.crossEntropyAt := by
  unfold crossEntropyAt
  apply summable_sum
  intro z _
  have hrewrite :
      (fun h => -(L.cell z h * Real.log (L.prior.mass z)) / Real.log 2) =
        (fun h => L.cell z h * (-Real.log (L.prior.mass z) / Real.log 2)) := by
    funext h
    ring
  rw [hrewrite]
  exact (L.summable z).mul_right _

/-- Summing the prior log-weights over the actual target marginal gives its
ordinary finite Shannon entropy, without assuming the desired MI equality. -/
theorem crossEntropyAt_tsum_eq_entropy (L : CountableTranscriptJointLaw Z E) :
    (∑' h, L.crossEntropyAt h) = entropy L.prior.mass := by
  unfold crossEntropyAt
  rw [Summable.tsum_finsetSum (fun z _ => by
    have hrewrite :
        (fun h => -(L.cell z h * Real.log (L.prior.mass z)) / Real.log 2) =
          (fun h => L.cell z h * (-Real.log (L.prior.mass z) / Real.log 2)) := by
      funext h
      ring
    rw [hrewrite]
    exact (L.summable z).mul_right _)]
  rw [entropy_eq_sum]
  apply Finset.sum_congr rfl
  intro z _
  calc
    (∑' h, -(L.cell z h * Real.log (L.prior.mass z)) / Real.log 2) =
        ∑' h, L.cell z h * (-Real.log (L.prior.mass z) / Real.log 2) := by
      congr 1
      funext h
      ring
    _ = (∑' h, L.cell z h) * (-Real.log (L.prior.mass z) / Real.log 2) :=
      (L.summable z).tsum_mul_right _
    _ = entropyTerm (L.prior.mass z) := by
      rw [L.target_marginal z]
      unfold entropyTerm Real.negMulLog
      ring

/-- The finite sum of actual log joint/product ratios at a history equals
that history's prior-label entropy charge minus its posterior uncertainty. -/
theorem logRatioSum_eq_crossEntropy_sub_uncertainty (L : CountableTranscriptJointLaw Z E)
    (h : E) :
    (∑ z, L.logRatioTerm z h) =
      L.crossEntropyAt h - massUncertainty (fun z => L.cell z h) := by
  calc
    (∑ z, L.logRatioTerm z h) =
        ∑ z, (L.cell z h * Real.log (L.cell z h) -
          L.cell z h * Real.log (L.prior.mass z) -
          L.cell z h * Real.log (L.historyMass h)) / Real.log 2 := by
      apply Finset.sum_congr rfl
      intro z _
      exact L.logRatioTerm_eq_expanded z h
    _ = L.crossEntropyAt h - massUncertainty (fun z => L.cell z h) := by
      have hmass :
          (∑ z, L.cell z h * Real.log (L.historyMass h)) =
            (∑ z, L.cell z h) * Real.log (∑ z, L.cell z h) := by
        rw [← Finset.sum_mul]
        rfl
      unfold crossEntropyAt massUncertainty
      rw [entropy_eq_sum]
      simp only [entropyTerm, Real.negMulLog, neg_mul, ← Finset.sum_div,
        Finset.sum_sub_distrib, Finset.sum_neg_distrib]
      linear_combination (-1 / Real.log 2) * hmass

/-- The log-ratio contributions over the countable history space are
summable. This rules out assigning the total a default value for divergence. -/
theorem logRatio_summable (L : CountableTranscriptJointLaw Z E) :
    Summable (fun h => ∑ z, L.logRatioTerm z h) := by
  have hfun : (fun h => ∑ z, L.logRatioTerm z h) =
      (fun h => L.crossEntropyAt h - massUncertainty (fun z => L.cell z h)) := by
    funext h
    exact L.logRatioSum_eq_crossEntropy_sub_uncertainty h
  rw [hfun]
  exact (L.crossEntropyAt_summable).sub L.uncertainty_summable

/-- Shannon mutual information between the finite target and the countable
history, defined by a convergent sum of actual log joint/product ratios. -/
noncomputable def information (L : CountableTranscriptJointLaw Z E) : ℝ :=
  ∑' h, ∑ z, L.logRatioTerm z h

/-- Derived Shannon identity: the independently normalized joint-law
log-ratio information equals prior entropy minus conditional uncertainty. -/
theorem information_eq_entropy_sub (L : CountableTranscriptJointLaw Z E) :
    L.information =
      entropy L.prior.mass - ∑' h, massUncertainty (fun z => L.cell z h) := by
  unfold information
  simp_rw [L.logRatioSum_eq_crossEntropy_sub_uncertainty]
  rw [(L.crossEntropyAt_summable).tsum_sub L.uncertainty_summable,
    L.crossEntropyAt_tsum_eq_entropy]

/-- The genuine joint-law information also equals prior entropy minus the
expected posterior entropy of the recorded countable histories. -/
theorem information_eq_expected_posterior (L : CountableTranscriptJointLaw Z E) :
    L.information = entropy L.prior.mass -
      ∑' h, L.historyMass h * entropy (L.posterior h) := by
  have heq : (fun h => massUncertainty (fun z => L.cell z h)) =
      (fun h => L.historyMass h * entropy (L.posterior h)) := by
    funext h
    exact L.uncertainty_eq_weighted_posterior h
  rw [L.information_eq_entropy_sub, heq]

end CountableTranscriptJointLaw

/-- Almost sure stopping constructs a normalized countable joint law from
the source prefix probabilities; no target/transcript MI result is assumed. -/
noncomputable def stoppedTranscriptJointLaw (p : FiniteProtocol Z A Y)
    (hstop : ∀ z, Tendsto (fun n => activeMass p n z) atTop (𝓝 0)) :
    CountableTranscriptJointLaw Z (List (A × Y)) where
  prior := p.prior
  cell := transcriptMass p
  nonnegative := transcriptMass_nonneg p
  summable := transcriptMass_summable p
  target_marginal := fun z => transcriptTotal_eq_prior_of_stops p z (hstop z)
  uncertainty_summable := transcriptUncertainty_summable p

/-- Under targetwise almost sure stopping, the limit information equals
Shannon mutual information of the independently normalized joint law of all
finite stopped transcripts, with its posterior entropy interpretation. -/
theorem informationLimit_eq_countableTranscriptInformation [Nonempty Z]
    (p : FiniteProtocol Z A Y)
    (hstop : ∀ z, Tendsto (fun n => activeMass p n z) atTop (𝓝 0)) :
    informationLimit p = (stoppedTranscriptJointLaw p hstop).information := by
  calc
    informationLimit p = transcriptInformation p :=
      informationLimit_eq_transcriptInformation p hstop
    _ = (stoppedTranscriptJointLaw p hstop).information := by
      rw [CountableTranscriptJointLaw.information_eq_entropy_sub]
      rfl


/-! ## Positive-weight conditional stopping and countable information -/

/-- It suffices that the protocol stops on initial records and targets
that actually carry positive prior mass. -/
def PositiveBranchStopping {H0 : Type} [Fintype H0]
    (p : ConditionalProtocol H0 Z A Y) : Prop :=
  ∀ u z, 0 < p.initialRecord.mass u → 0 < (p.given u).prior.mass z →
    Tendsto (fun n => activeMass (p.given u) n z) atTop (𝓝 0)

/-- A normalized stopped-transcript law is constructed only for an initial
record of positive probability. The zero-target-prior cases follow from
nonnegative mass conservation and require no stopping assumption. -/
noncomputable def positiveRecordTranscriptJointLaw {H0 : Type} [Fintype H0]
    (p : ConditionalProtocol H0 Z A Y) (hstop : PositiveBranchStopping p)
    (u : H0) (hu : 0 < p.initialRecord.mass u) :
    CountableTranscriptJointLaw Z (List (A × Y)) :=
  stoppedTranscriptJointLaw (p.given u)
    (stops_of_positive_prior (p.given u) (fun z hz => hstop u z hu hz))

/-- Countable conditional mutual information is the weighted sum of actual
joint/product log-ratio informations from the positive-probability records.
Zero-probability records contribute zero and need no stopped law. -/
noncomputable def conditionalCountableTranscriptInformation {H0 : Type} [Fintype H0]
    (p : ConditionalProtocol H0 Z A Y) (hstop : PositiveBranchStopping p) : ℝ :=
  ∑ u, if hu : 0 < p.initialRecord.mass u then
    p.initialRecord.mass u * (positiveRecordTranscriptJointLaw p hstop u hu).information
  else 0

/-- The finite stopped-information limit equals conditional countable
log-ratio mutual information even if impossible initial records and targets
do not stop. -/
theorem conditionalInformationLimit_eq_countable_of_positive [Nonempty Z]
    {H0 : Type} [Fintype H0]
    (p : ConditionalProtocol H0 Z A Y) (hstop : PositiveBranchStopping p) :
    conditionalInformationLimit p = conditionalCountableTranscriptInformation p hstop := by
  unfold conditionalInformationLimit conditionalCountableTranscriptInformation
  apply Finset.sum_congr rfl
  intro u _
  by_cases hu : 0 < p.initialRecord.mass u
  · rw [dif_pos hu]
    have hs : ∀ z, Tendsto (fun n => activeMass (p.given u) n z) atTop (𝓝 0) :=
      stops_of_positive_prior (p.given u) (fun z hz => hstop u z hu hz)
    change p.initialRecord.mass u * informationLimit (p.given u) =
      p.initialRecord.mass u * (stoppedTranscriptJointLaw (p.given u) hs).information
    rw [informationLimit_eq_countableTranscriptInformation (p.given u) hs]
  · have hz : p.initialRecord.mass u = 0 :=
      le_antisymm (le_of_not_gt hu) (p.initialRecord.nonnegative u)
    simp [hz]


/-! ## Controls: a real stopped law and an escaping no-stop law -/

/-- A fair hidden bit produces only a constant outcome, pays no cost and never
stops. Its finite records disclose no information even though its prior has
one bit of entropy. -/
noncomputable def neverStopFairProtocol : FiniteProtocol Bool Unit Unit where
  prior := binaryPriorLaw (1 / 2) (by norm_num) (by norm_num)
  policy _ := unitLaw
  observation _ _ _ := unitLaw
  stop _ := false
  cost _ _ := 0
  cost_nonnegative _ _ := le_rfl

theorem neverStopFair_transcriptMass_zero (z : Bool) (h : List (Unit × Unit)) :
    transcriptMass neverStopFairProtocol z h = 0 := by
  simp [transcriptMass, neverStopFairProtocol]

theorem neverStopFair_transcriptTotal_zero (z : Bool) :
    transcriptTotal neverStopFairProtocol z = 0 := by
  unfold transcriptTotal
  simp [neverStopFair_transcriptMass_zero]

theorem neverStopFair_prior_entropy :
    entropy neverStopFairProtocol.prior.mass = 1 := by
  change BitDivision.entropy (binaryPrior (1 / 2)) / Real.log 2 = 1
  rw [binaryPrior_entropy]
  have hbin : Real.binEntropy (1 / 2 : ℝ) = Real.log 2 := by
    simpa only [one_div] using Real.binEntropy_two_inv
  rw [hbin]
  exact div_self (Real.log_pos one_lt_two).ne'

theorem neverStopFair_transcriptUncertainty_zero :
    transcriptUncertainty neverStopFairProtocol = 0 := by
  unfold transcriptUncertainty
  have hzero :
      ∀ h : List (Unit × Unit),
        massUncertainty (fun z => transcriptMass neverStopFairProtocol z h) = 0 := by
    intro h
    have hz : (fun z => transcriptMass neverStopFairProtocol z h) =
        (fun _ : Bool => 0) := by
      funext z
      exact neverStopFair_transcriptMass_zero z h
    rw [hz, massUncertainty_zero]
  simp [hzero]

/-- The truly observed no-stop experiment has zero information, because
each positive history receives a constant outcome independent of the bit. -/
theorem neverStopFair_informationLimit_zero :
    informationLimit neverStopFairProtocol = 0 := by
  apply informationLimit_zero_capacity
  intro h a hw _ _
  have hlocal : localGain neverStopFairProtocol h a = 0 := by
    unfold localGain
    change jointMI (fun zy : Bool × Unit =>
      posterior neverStopFairProtocol h zy.1 * unitLaw.mass zy.2) = 0
    exact jointMI_product_zero _ _ (posterior_total neverStopFairProtocol h hw) unitLaw.total
  simp [hlocal]

/-- The old H-U formula is NOT countable mutual information in a no-stop
experiment. Its missing bit is exactly the active uncertainty tail. -/
theorem neverStopFair_residual_control :
    transcriptInformation neverStopFairProtocol = 1 ∧
    informationLimit neverStopFairProtocol = 0 ∧
    tailUncertainty neverStopFairProtocol = 1 := by
  have hraw : transcriptInformation neverStopFairProtocol = 1 := by
    unfold transcriptInformation
    rw [neverStopFair_prior_entropy, neverStopFair_transcriptUncertainty_zero]
    norm_num
  have htail : tailUncertainty neverStopFairProtocol = 1 := by
    unfold tailUncertainty
    rw [neverStopFair_prior_entropy, neverStopFair_transcriptUncertainty_zero,
      neverStopFair_informationLimit_zero]
    norm_num
  exact ⟨hraw, neverStopFair_informationLimit_zero, htail⟩

/-- The no-stop fixture cannot satisfy the almost-sure stopping premise that
normalizes a stopped-transcript law. -/
theorem neverStopFair_not_stopping :
    ¬ ∀ z, Tendsto (fun n => activeMass neverStopFairProtocol n z) atTop (𝓝 0) := by
  intro hstop
  have hmass := transcriptTotal_eq_prior_of_stops neverStopFairProtocol true (hstop true)
  rw [neverStopFair_transcriptTotal_zero] at hmass
  have hprior : neverStopFairProtocol.prior.mass true = (1 : ℝ) / 2 := by
    norm_num [neverStopFairProtocol, binaryPriorLaw, binaryPrior]
  rw [hprior] at hmass
  norm_num at hmass

/-- The same fair prior with immediate stopping provides an actual normalized
joint law on finite stopped histories, without any assumption of information gain. -/
noncomputable def stoppedFairProtocol : FiniteProtocol Bool Unit Unit where
  prior := neverStopFairProtocol.prior
  policy := neverStopFairProtocol.policy
  observation := neverStopFairProtocol.observation
  stop _ := true
  cost := neverStopFairProtocol.cost
  cost_nonnegative := neverStopFairProtocol.cost_nonnegative

theorem stoppedFair_activeMass_zero (n : ℕ) (z : Bool) :
    activeMass stoppedFairProtocol n z = 0 := by
  unfold activeMass
  apply Finset.sum_eq_zero
  intro h _
  simp [stoppedFairProtocol]

theorem stoppedFair_stops :
    ∀ z, Tendsto (fun n => activeMass stoppedFairProtocol n z) atTop (𝓝 0) := by
  intro z
  have hzero : ∀ n, activeMass stoppedFairProtocol n z = 0 :=
    fun n => stoppedFair_activeMass_zero n z
  simp [hzero]

noncomputable def stoppedFairJointLaw :
    CountableTranscriptJointLaw Bool (List (Unit × Unit)) :=
  stoppedTranscriptJointLaw stoppedFairProtocol stoppedFair_stops

theorem stoppedFairJointLaw_total :
    (∑ z, ∑' h, stoppedFairJointLaw.cell z h) = 1 :=
  stoppedFairJointLaw.total

/-- This normalized stopped law carries no information about its fair target:
stopping immediately yields only the empty history. -/
theorem stoppedFairJointLaw_information_zero :
    stoppedFairJointLaw.information = 0 := by
  have hcap : LocalCapacityBound stoppedFairProtocol 0 := by
    intro h a _ hs _
    simp [stoppedFairProtocol] at hs
  have hzero := informationLimit_zero_capacity stoppedFairProtocol hcap
  have hbridge :=
    informationLimit_eq_countableTranscriptInformation stoppedFairProtocol stoppedFair_stops
  change (stoppedTranscriptJointLaw stoppedFairProtocol stoppedFair_stops).information = 0
  rw [← hbridge]
  exact hzero

theorem stoppedFairJointLaw_empty_mass (z : Bool) :
    stoppedFairJointLaw.cell z [] = (1 : ℝ) / 2 := by
  cases z <;>
    norm_num [stoppedFairJointLaw, stoppedTranscriptJointLaw, transcriptMass,
      stoppedFairProtocol, neverStopFairProtocol, prefixMass_nil,
      binaryPriorLaw, binaryPrior]

end OperatorKO7.Meta.BoundaryObserver.TranscriptLaw
