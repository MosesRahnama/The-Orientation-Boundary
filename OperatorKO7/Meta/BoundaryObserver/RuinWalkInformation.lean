import OperatorKO7.Meta.BoundaryObserver.ProtocolDynkin
import OperatorKO7.Meta.BoundaryObserver.ObservationPrincipleProtocols

/-!
# The symmetric ruin walk

Manuscript: Example `ex:ruin-walk`.

A protocol advances a counter by `±1` with equal chances at each reading of unit cost and stops at
`0` or at `N`, from a start `k` with `0 < k < N`, with one step law under both values of a fair
label. The pair is merged at every reading, so the walk acquires zero information about the label
at every horizon and in the limit. The potential `c (N - c)` drops by one at every unstopped
history, so the drift identity bounds the summed active mass by `k (N - k)`: the walk stops with
probability one, its expected cost at every horizon is at most `k (N - k)`, and the expected cost
tends to `k (N - k)`, which grows without bound as the barriers recede.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped BigOperators
open Filter Topology
open OperatorKO7.Meta.BoundaryObserver.ProtocolResolution
open OperatorKO7.Meta.BoundaryObserver.TranscriptLaw
open OperatorKO7.Meta.BoundaryObserver.ProtocolDynkin
open OperatorKO7.Meta.BoundaryObserver.BoundarySingularity
open OperatorKO7.Meta.BoundaryObserver.ObservationPrincipleProtocols

namespace OperatorKO7.Meta.BoundaryObserver.RuinWalkInformation

/-- The counter: the start `k` plus the net number of up steps. -/
def counter (k : ℕ) (h : List (Unit × Bool)) : ℤ :=
  k + (h.map (fun ay => if ay.2 then (1 : ℤ) else -1)).sum

theorem counter_nil (k : ℕ) : counter k [] = k := by simp [counter]

theorem counter_append (k : ℕ) (h : List (Unit × Bool)) (a : Unit) (y : Bool) :
    counter k (h ++ [(a, y)]) = counter k h + (if y then 1 else -1) := by
  simp only [counter, List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero]
  ring

/-- The walk stops at `0` or at `N`. -/
def ruinStop (N k : ℕ) (h : List (Unit × Bool)) : Bool :=
  decide (counter k h ≤ 0 ∨ (N : ℤ) ≤ counter k h)

theorem ruinStop_false_iff (N k : ℕ) (h : List (Unit × Bool)) :
    ruinStop N k h = false ↔ 0 < counter k h ∧ counter k h < N := by
  unfold ruinStop
  rw [decide_eq_false_iff_not]
  omega

theorem ruinStop_true_iff (N k : ℕ) (h : List (Unit × Bool)) :
    ruinStop N k h = true ↔ counter k h ≤ 0 ∨ (N : ℤ) ≤ counter k h := by
  unfold ruinStop
  rw [decide_eq_true_iff]

/-- The one-point law of the single reading. -/
noncomputable def unitLaw : FiniteLaw Unit where
  mass _ := 1
  nonnegative _ := zero_le_one
  total := by simp

/-- The fair step law. -/
noncomputable def coinLaw : FiniteLaw Bool where
  mass _ := 1 / 2
  nonnegative _ := by norm_num
  total := by rw [Fintype.sum_bool]; norm_num

/-- **The symmetric ruin walk**, with one step law under both values of a fair label. -/
noncomputable def ruinWalk (N k : ℕ) : FiniteProtocol Bool Unit Bool where
  prior := binaryPriorLaw (1 / 2) (by norm_num) (by norm_num)
  policy _ := unitLaw
  observation _ _ _ := coinLaw
  stop := ruinStop N k
  cost _ _ := 1
  cost_nonnegative _ _ := zero_le_one

/-- **Zero information at every horizon and in the limit:** the pair is merged at every reading. -/
theorem ruinWalk_zero_information (N k : ℕ) :
    (∀ n bank, HistoryBank n bank → terminalMI (ruinWalk N k) n bank = 0) ∧
      informationLimit (ruinWalk N k) = 0 :=
  zeroRows_zero_information (ruinWalk N k) fun _ _ =>
    (discrimination_eq_zero_iff _ _ (fun y => coinLaw.nonnegative y)
      (fun y => coinLaw.nonnegative y)).2 rfl

/-- The potential `c (N - c)`, zero at stopped histories. -/
noncomputable def pot (N k : ℕ) (h : List (Unit × Bool)) : ℝ :=
  if ruinStop N k h then 0 else (counter k h : ℝ) * ((N : ℝ) - counter k h)

theorem pot_nonneg (N k : ℕ) (h : List (Unit × Bool)) : 0 ≤ pot N k h := by
  unfold pot
  split_ifs with hs
  · exact le_rfl
  · have hc := (ruinStop_false_iff N k h).1 (by simpa using hs)
    have h1 : (0 : ℝ) < counter k h := by exact_mod_cast hc.1
    have h2 : (counter k h : ℝ) < N := by exact_mod_cast hc.2
    nlinarith

theorem pot_le (N k : ℕ) (h : List (Unit × Bool)) : pot N k h ≤ (N : ℝ) ^ 2 := by
  unfold pot
  split_ifs with hs
  · positivity
  · have hc := (ruinStop_false_iff N k h).1 (by simpa using hs)
    have h1 : (0 : ℝ) < counter k h := by exact_mod_cast hc.1
    have h2 : (counter k h : ℝ) < N := by exact_mod_cast hc.2
    nlinarith

/-- At a child of an unstopped history the potential is `c' (N - c')`, also when the child
stops at a barrier. -/
theorem pot_child (N k : ℕ) (h : List (Unit × Bool)) (hs : ruinStop N k h = false) (a : Unit)
    (y : Bool) :
    pot N k (h ++ [(a, y)]) = (counter k (h ++ [(a, y)]) : ℝ) *
      ((N : ℝ) - counter k (h ++ [(a, y)])) := by
  have hc := (ruinStop_false_iff N k h).1 hs
  unfold pot
  split_ifs with hs'
  · have hb := (ruinStop_true_iff N k _).1 hs'
    rw [counter_append] at hb ⊢
    have hcases : counter k h + (if y then 1 else -1) = 0 ∨
        counter k h + (if y then 1 else -1) = N := by
      cases y <;> simp at hb ⊢ <;> omega
    rcases hcases with h0 | hN
    · rw [h0]; simp
    · rw [hN]; simp
  · rfl

/-- **The potential drops by one at every unstopped history.** -/
theorem pot_drift (N k : ℕ) (z : Bool) (h : List (Unit × Bool)) (hs : (ruinWalk N k).stop h = false) :
    ∑ a, ∑ y, ((ruinWalk N k).policy h).mass a * ((ruinWalk N k).observation h a z).mass y *
      pot N k (h ++ [(a, y)]) = pot N k h + -1 := by
  have hs' : ruinStop N k h = false := hs
  have hpot : pot N k h = (counter k h : ℝ) * ((N : ℝ) - counter k h) := by simp [pot, hs']
  simp only [ruinWalk, unitLaw, coinLaw, Fintype.univ_unit, Finset.sum_singleton, Fintype.sum_bool,
    one_mul]
  rw [pot_child N k h hs' () true, pot_child N k h hs' () false, counter_append, counter_append,
    hpot]
  simp only [↓reduceIte, Bool.false_eq_true]
  push_cast
  ring

theorem pot_nil (N k : ℕ) (hk : 0 < k) (hkN : k < N) : pot N k [] = (k : ℝ) * ((N : ℝ) - k) := by
  have hs : ruinStop N k [] = false := by
    rw [ruinStop_false_iff, counter_nil]
    exact ⟨by exact_mod_cast hk, by exact_mod_cast hkN⟩
  simp [pot, hs, counter_nil]

/-- The drift identity for the ruin walk. -/
theorem ruin_dynkin (N k : ℕ) (hk : 0 < k) (hkN : k < N) (z : Bool) (n : ℕ) :
    ∑ h ∈ historySet (Unit × Bool) n, stoppedMass (ruinWalk N k) n z h * pot N k h =
      (ruinWalk N k).prior.mass z * ((k : ℝ) * ((N : ℝ) - k)) - activeBelow (ruinWalk N k) z n := by
  have h := protocol_dynkin (ruinWalk N k) z (pot N k) (-1) (fun h hs => pot_drift N k z h hs) n
  rw [pot_nil N k hk hkN] at h
  linarith

theorem stopped_pot_nonneg (N k : ℕ) (z : Bool) (n : ℕ) :
    0 ≤ ∑ h ∈ historySet (Unit × Bool) n, stoppedMass (ruinWalk N k) n z h * pot N k h :=
  Finset.sum_nonneg fun h _ => mul_nonneg (stoppedMass_nonnegative _ n z h) (pot_nonneg N k h)

theorem stopped_pot_le (N k : ℕ) (z : Bool) (n : ℕ) :
    ∑ h ∈ historySet (Unit × Bool) n, stoppedMass (ruinWalk N k) n z h * pot N k h ≤
      (N : ℝ) ^ 2 * activeMass (ruinWalk N k) n z := by
  unfold activeMass
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun h _ => ?_
  by_cases hs : ruinStop N k h = true
  · have : pot N k h = 0 := by simp [pot, hs]
    rw [this, mul_zero]
    apply mul_nonneg (by positivity)
    split_ifs
    · exact prefixMass_nonnegative _ z h
    · exact le_rfl
  · have hs' : (ruinWalk N k).stop h = false := by simpa [ruinWalk] using hs
    unfold stoppedMass
    by_cases hl : h.length = n
    · rw [if_pos ⟨hl.le, Or.inr hl⟩, if_pos ⟨hl, hs'⟩]
      have := mul_le_mul_of_nonneg_left (pot_le N k h) (prefixMass_nonnegative (ruinWalk N k) z h)
      linarith
    · rw [if_neg (by rintro ⟨-, h2 | h2⟩ <;> simp_all), if_neg (by rintro ⟨h1, -⟩; exact hl h1)]
      simp

/-- **The summed active mass is at most `k (N - k)`** at every horizon. -/
theorem activeBelow_le (N k : ℕ) (hk : 0 < k) (hkN : k < N) (z : Bool) (n : ℕ) :
    activeBelow (ruinWalk N k) z n ≤ (k : ℝ) * ((N : ℝ) - k) := by
  have h := ruin_dynkin N k hk hkN z n
  have h0 := stopped_pot_nonneg N k z n
  have hp : (ruinWalk N k).prior.mass z ≤ 1 := by
    cases z <;> simp [ruinWalk, binaryPriorLaw, binaryPrior] <;> norm_num
  have hkk : (0 : ℝ) ≤ (k : ℝ) * ((N : ℝ) - k) := by
    have : (k : ℝ) < N := by exact_mod_cast hkN
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith
  have := mul_le_mul_of_nonneg_right hp hkk
  linarith

/-- **The walk stops with probability one** under each value of the label. -/
theorem ruinWalk_stops (N k : ℕ) (hk : 0 < k) (hkN : k < N) (z : Bool) :
    Tendsto (fun n => activeMass (ruinWalk N k) n z) atTop (𝓝 0) :=
  activeMass_tendsto_zero_of_bounded _ z _ (activeBelow_le N k hk hkN z)

/-- **The expected cost at every horizon is at most `k (N - k)`.** -/
theorem expectedCost_le (N k : ℕ) (hk : 0 < k) (hkN : k < N) (n : ℕ) :
    expectedCost (ruinWalk N k) n (historyBank Unit Bool n) ≤ (k : ℝ) * ((N : ℝ) - k) := by
  rw [expectedCost_unit (ruinWalk N k) (fun _ _ => rfl) n _ (historyBank_complete Unit Bool n)]
  have h := fun z => ruin_dynkin N k hk hkN z n
  have h0 := fun z => stopped_pot_nonneg N k z n
  rw [Fintype.sum_bool]
  have ht := h true
  have hf := h false
  have h0t := h0 true
  have h0f := h0 false
  have hpt : (ruinWalk N k).prior.mass true + (ruinWalk N k).prior.mass false = 1 := by
    norm_num [ruinWalk, binaryPriorLaw, binaryPrior]
  have hK : (ruinWalk N k).prior.mass true * ((k : ℝ) * ((N : ℝ) - k)) +
      (ruinWalk N k).prior.mass false * ((k : ℝ) * ((N : ℝ) - k)) = (k : ℝ) * ((N : ℝ) - k) := by
    rw [← add_mul, hpt, one_mul]
  linarith

/-- **The expected cost tends to `k (N - k)`.** -/
theorem expectedCost_tendsto (N k : ℕ) (hk : 0 < k) (hkN : k < N) :
    Tendsto (fun n => expectedCost (ruinWalk N k) n (historyBank Unit Bool n)) atTop
      (𝓝 ((k : ℝ) * ((N : ℝ) - k))) := by
  have hform : ∀ n, expectedCost (ruinWalk N k) n (historyBank Unit Bool n) =
      (k : ℝ) * ((N : ℝ) - k) -
        (∑ h ∈ historySet (Unit × Bool) n, stoppedMass (ruinWalk N k) n true h * pot N k h +
          ∑ h ∈ historySet (Unit × Bool) n, stoppedMass (ruinWalk N k) n false h * pot N k h) := by
    intro n
    rw [expectedCost_unit (ruinWalk N k) (fun _ _ => rfl) n _ (historyBank_complete Unit Bool n),
      Fintype.sum_bool]
    have ht := ruin_dynkin N k hk hkN true n
    have hf := ruin_dynkin N k hk hkN false n
    have hpt : (ruinWalk N k).prior.mass true + (ruinWalk N k).prior.mass false = 1 := by
      norm_num [ruinWalk, binaryPriorLaw, binaryPrior]
    have hK : (ruinWalk N k).prior.mass true * ((k : ℝ) * ((N : ℝ) - k)) +
        (ruinWalk N k).prior.mass false * ((k : ℝ) * ((N : ℝ) - k)) = (k : ℝ) * ((N : ℝ) - k) := by
      rw [← add_mul, hpt, one_mul]
    linarith
  have hlim : ∀ z, Tendsto (fun n => ∑ h ∈ historySet (Unit × Bool) n,
      stoppedMass (ruinWalk N k) n z h * pot N k h) atTop (𝓝 0) := by
    intro z
    have hup : Tendsto (fun n => (N : ℝ) ^ 2 * activeMass (ruinWalk N k) n z) atTop (𝓝 0) := by
      simpa using (ruinWalk_stops N k hk hkN z).const_mul ((N : ℝ) ^ 2)
    exact squeeze_zero (fun n => stopped_pot_nonneg N k z n) (fun n => stopped_pot_le N k z n) hup
  have h := ((hlim true).add (hlim false)).const_sub ((k : ℝ) * ((N : ℝ) - k))
  rw [add_zero, sub_zero] at h
  exact h.congr fun n => (hform n).symm

/-- **The expected cost grows without bound as the barriers recede:** for every bound `M` there is
a distance beyond which every start pays more than `M`. -/
theorem expectedCost_unbounded (M : ℝ) :
    ∃ N₀ : ℕ, ∀ N k : ℕ, N₀ ≤ N → 0 < k → k < N → M ≤ (k : ℝ) * ((N : ℝ) - k) := by
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (M + 1)
  refine ⟨N₀, fun N k hN hk hkN => ?_⟩
  have h1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have h2 : (k : ℝ) + 1 ≤ N := by exact_mod_cast hkN
  have h3 : (N₀ : ℝ) ≤ N := by exact_mod_cast hN
  nlinarith

end OperatorKO7.Meta.BoundaryObserver.RuinWalkInformation
