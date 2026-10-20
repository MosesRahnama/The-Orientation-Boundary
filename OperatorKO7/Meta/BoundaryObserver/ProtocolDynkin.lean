import OperatorKO7.Meta.BoundaryObserver.TranscriptLaw

/-!
# The drift identity of a stopped protocol

Manuscript: the finite-horizon identity behind Example `ex:ruin-walk`, Corollary
`cor:sequential-reading-cost` and part (iv) of Theorem `thm:transcript-information`.

For a finite protocol, a target `z` and a function `V` on histories whose one-step mean exceeds it
by `d` at every unstopped history, the stopped mass of `V` at horizon `n` is the prior mass of `z`
times `V` at the empty history plus `d` times the active mass summed below the horizon. With unit
costs the expected cost at horizon `n` is that summed active mass.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped BigOperators
open OperatorKO7.Meta.BoundaryObserver.ProtocolResolution
open OperatorKO7.Meta.BoundaryObserver.TranscriptLaw

namespace OperatorKO7.Meta.BoundaryObserver.ProtocolDynkin

variable {Z A Y : Type} [Fintype Z] [Fintype A] [Fintype Y]

/-- The active mass of `z` summed over the horizons below `n`. -/
noncomputable def activeBelow (p : FiniteProtocol Z A Y) (z : Z) (n : ℕ) : ℝ :=
  ∑ h ∈ historySet (A × Y) n, activeValue p.stop n (prefixMass p z) h

/-- **The drift identity.** -/
theorem protocol_dynkin (p : FiniteProtocol Z A Y) (z : Z) (V : List (A × Y) → ℝ) (d : ℝ)
    (hdrift : ∀ h, p.stop h = false →
      ∑ a, ∑ y, (p.policy h).mass a * (p.observation h a z).mass y * V (h ++ [(a, y)]) =
        V h + d)
    (n : ℕ) :
    ∑ h ∈ historySet (A × Y) n, stoppedMass p n z h * V h =
      p.prior.mass z * V [] + d * activeBelow p z n := by
  have hb := historySet_boundary_balance p.stop n (fun h => prefixMass p z h * V h) (by
    intro h hs ay
    obtain ⟨a, y⟩ := ay
    simp [prefixMass_append, hs])
  have hbd : ∀ h, boundaryValue p.stop n (fun h => prefixMass p z h * V h) h =
      stoppedMass p n z h * V h := by
    intro h
    unfold boundaryValue stoppedMass
    split_ifs <;> simp
  have hact : ∀ h, activeValue p.stop n
      (fun h => prefixMass p z h * V h - ∑ ay : A × Y, prefixMass p z (h ++ [ay]) * V (h ++ [ay]))
        h = -d * activeValue p.stop n (prefixMass p z) h := by
    intro h
    unfold activeValue
    split_ifs with ha
    · have hc : ∑ ay : A × Y, prefixMass p z (h ++ [ay]) * V (h ++ [ay]) =
          prefixMass p z h * (V h + d) := by
        rw [Fintype.sum_prod_type, ← hdrift h ha.2, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [prefixMass_append, if_neg (by simp [ha.2])]
        ring
      show prefixMass p z h * V h -
        ∑ ay : A × Y, prefixMass p z (h ++ [ay]) * V (h ++ [ay]) = -d * prefixMass p z h
      rw [hc]
      ring
    · ring
  simp only [hbd, hact, prefixMass_nil] at hb
  rw [activeBelow]
  rw [Finset.mul_sum]
  have : ∑ h ∈ historySet (A × Y) n, -d * activeValue p.stop n (prefixMass p z) h =
      -(∑ h ∈ historySet (A × Y) n, d * activeValue p.stop n (prefixMass p z) h) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun h _ => by ring
  rw [this] at hb
  linarith

theorem activeBelow_zero (p : FiniteProtocol Z A Y) (z : Z) : activeBelow p z 0 = 0 := by
  unfold activeBelow
  refine Finset.sum_eq_zero fun h _ => ?_
  simp [activeValue]

/-- The summed active mass grows by the active mass at the horizon. -/
theorem activeBelow_succ (p : FiniteProtocol Z A Y) (z : Z) (n : ℕ) :
    activeBelow p z (n + 1) = activeBelow p z n + activeMass p n z := by
  unfold activeBelow activeMass
  have hsub : ∑ h ∈ historySet (A × Y) (n + 1), activeValue p.stop (n + 1) (prefixMass p z) h =
      ∑ h ∈ historySet (A × Y) n, activeValue p.stop (n + 1) (prefixMass p z) h := by
    symm
    apply Finset.sum_subset (historySet_mono (Nat.le_succ n))
    intro h hh hn
    have h1 := (mem_historySet (n + 1) h).1 hh
    have h2 : ¬ h.length ≤ n := fun hc => hn ((mem_historySet n h).2 hc)
    simp [activeValue, show ¬ h.length < n + 1 by omega]
  rw [hsub, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun h hh => ?_
  have hl := (mem_historySet n h).1 hh
  unfold activeValue
  by_cases hs : p.stop h = false
  · by_cases he : h.length = n
    · simp [hs, he]
    · simp [hs, he, show h.length < n by omega, show h.length < n + 1 by omega]
  · simp [hs]

/-- The summed active mass is the sum of the active masses at the horizons below `n`. -/
theorem activeBelow_eq_sum (p : FiniteProtocol Z A Y) (z : Z) (n : ℕ) :
    activeBelow p z n = ∑ t ∈ Finset.range n, activeMass p t z := by
  induction n with
  | zero => rw [activeBelow_zero, Finset.sum_range_zero]
  | succ n ih => rw [activeBelow_succ, ih, Finset.sum_range_succ]

/-- **Unit costs:** the expected cost at horizon `n` is the summed active mass. -/
theorem expectedCost_unit (p : FiniteProtocol Z A Y) (hcost : ∀ h a, p.cost h a = 1) (n : ℕ)
    (bank : List (List (A × Y))) (hb : HistoryBank n bank) :
    expectedCost p n bank = ∑ z, activeBelow p z n := by
  unfold expectedCost
  rw [hb.sum_eq]
  unfold activeBelow
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun h _ => ?_
  have hpol : ∑ a, (p.policy h).mass a * p.cost h a = 1 := by
    simp only [hcost, mul_one]
    exact (p.policy h).total
  unfold activeValue
  split_ifs with ha
  · rw [hpol, mul_one, historyMass]
  · rw [Finset.sum_const_zero]

theorem activeBelow_nonneg (p : FiniteProtocol Z A Y) (z : Z) (n : ℕ) :
    0 ≤ activeBelow p z n := by
  rw [activeBelow_eq_sum]
  exact Finset.sum_nonneg fun t _ => activeMass_nonneg p t z

/-- A bounded summed active mass forces the active mass to zero: the protocol stops with
probability one for that target. -/
theorem activeMass_tendsto_zero_of_bounded (p : FiniteProtocol Z A Y) (z : Z) (C : ℝ)
    (hC : ∀ n, activeBelow p z n ≤ C) :
    Filter.Tendsto (fun n => activeMass p n z) Filter.atTop (nhds 0) := by
  have hs : Summable (fun t => activeMass p t z) :=
    summable_of_sum_range_le (fun t => activeMass_nonneg p t z)
      (fun n => by rw [← activeBelow_eq_sum]; exact hC n)
  exact hs.tendsto_atTop_zero

end OperatorKO7.Meta.BoundaryObserver.ProtocolDynkin
