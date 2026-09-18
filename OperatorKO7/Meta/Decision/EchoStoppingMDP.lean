import OperatorKO7.Meta.Decision.ZeroDeficitStopping
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Dynamic echo stopping with continuation value

The one-step interface compares a supplied forecast with stopping. The
finite-horizon recursion instead computes returns from actual transitions,
terminal rewards, gains and costs; its value is attained and bounds every legal
plan of the permitted length. The original static decision theorem is retained.

Relation: finite, nonempty successor sets preserving the declared observation.
Closure: every finite decision horizon on an arbitrary state type.
Strategy: the controller chooses a successor; stopping wins a tie.
The original interface uses deterministic successor choice. The stochastic
section uses normalized finite-support probabilities, finite legal action sets
(which may be empty), and history-dependent policies with attained expected
return. Its invariant criterion ignores zero-probability outcomes.
The old `futureValue` field has no effect on `horizonValue`. Constant stop rewards
within observer fibers and nonpositive net gains imply optimal stopping at every
finite horizon. A two-state example derives profitable continuation from the
next state's terminal reward despite zero immediate gain and positive cost.
Validation of additions requires the paired reach and axiom checks.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.Decision.EchoStopping

open OperatorKO7.Meta.Decision.ZeroDeficitStopping

universe u v

/-- A finite-branching sequential decision problem whose continue action stays
inside one observer fiber. -/
structure EchoStoppingMDP (S : Type u) (Q : Type v) [DecidableEq S] where
  observe : S → Q
  successors : S → Finset S
  successors_nonempty : ∀ s, (successors s).Nonempty
  echo_preserved : ∀ s t, t ∈ successors s → observe t = observe s
  stopValue : S → ℝ
  currentGain : S → ℝ
  futureValue : S → ℝ
  computeCost : S → ℝ

/-- The best supplied future value among states reachable by one continue
transition. -/
noncomputable def bestContinuation {S : Type u} {Q : Type v} [DecidableEq S]
    (M : EchoStoppingMDP S Q) (s : S) : ℝ :=
  (M.successors s).sup' (M.successors_nonempty s) M.futureValue

/-- Future value relative to stopping immediately. -/
noncomputable def continuationAdvantage {S : Type u} {Q : Type v} [DecidableEq S]
    (M : EchoStoppingMDP S Q) (s : S) : ℝ :=
  bestContinuation M s - M.stopValue s

/-- Net value of taking one more computational step. -/
noncomputable def netComputeAdvantage {S : Type u} {Q : Type v} [DecidableEq S]
    (M : EchoStoppingMDP S Q) (s : S) : ℝ :=
  M.currentGain s + continuationAdvantage M s - M.computeCost s

/-- Dynamic policy: continue exactly when the net value of one more computation
is strictly positive. -/
noncomputable def dynamicPolicy {S : Type u} {Q : Type v} [DecidableEq S]
    (M : EchoStoppingMDP S Q) (s : S) : MetaPolicy :=
  haveI := Classical.dec (0 < netComputeAdvantage M s)
  if 0 < netComputeAdvantage M s then MetaPolicy.compute else MetaPolicy.stop

/-- The finite successor envelope is bounded by `a` exactly when every reachable
future value is bounded by `a`. -/
theorem bestContinuation_le_iff
    {S : Type u} {Q : Type v} [DecidableEq S]
    (M : EchoStoppingMDP S Q) (s : S) (a : ℝ) :
    bestContinuation M s ≤ a ↔
      ∀ t ∈ M.successors s, M.futureValue t ≤ a := by
  exact Finset.sup'_le_iff (M.successors_nonempty s) M.futureValue

/-- Every successor is in the same observer fiber. This records the exact
"echo" premise consumed by the dynamic model. -/
theorem successor_observation_eq
    {S : Type u} {Q : Type v} [DecidableEq S]
    (M : EchoStoppingMDP S Q) {s t : S} (ht : t ∈ M.successors s) :
    M.observe t = M.observe s :=
  M.echo_preserved s t ht

/-- Correct dynamic stopping theorem. Zero current gain and positive cost force
stop when every reachable continuation has value no greater than stopping now. -/
theorem zero_current_gain_positive_cost_dominated_continuations_force_stop
    {S : Type u} {Q : Type v} [DecidableEq S]
    (M : EchoStoppingMDP S Q) (s : S)
    (hgain : M.currentGain s = 0)
    (hcost : 0 < M.computeCost s)
    (hfuture : ∀ t ∈ M.successors s, M.futureValue t ≤ M.stopValue s) :
    dynamicPolicy M s = MetaPolicy.stop := by
  have hbest : bestContinuation M s ≤ M.stopValue s :=
    (bestContinuation_le_iff M s (M.stopValue s)).2 hfuture
  have hnet : netComputeAdvantage M s < 0 := by
    unfold netComputeAdvantage continuationAdvantage
    rw [hgain]
    linarith
  unfold dynamicPolicy
  split_ifs with h
  · exact (lt_asymm h hnet).elim
  · rfl

/-- Stronger quantitative form: any nonpositive current gain is still dominated
when continuation value is no better than stopping and computation has positive
cost. -/
theorem nonpositive_current_gain_positive_cost_dominated_continuations_force_stop
    {S : Type u} {Q : Type v} [DecidableEq S]
    (M : EchoStoppingMDP S Q) (s : S)
    (hgain : M.currentGain s ≤ 0)
    (hcost : 0 < M.computeCost s)
    (hfuture : ∀ t ∈ M.successors s, M.futureValue t ≤ M.stopValue s) :
    dynamicPolicy M s = MetaPolicy.stop := by
  have hbest : bestContinuation M s ≤ M.stopValue s :=
    (bestContinuation_le_iff M s (M.stopValue s)).2 hfuture
  have hnet : netComputeAdvantage M s < 0 := by
    unfold netComputeAdvantage continuationAdvantage
    linarith
  unfold dynamicPolicy
  split_ifs with h
  · exact (lt_asymm h hnet).elim
  · rfl

/-- A positive continuation surplus that exceeds cost can make continued
computation optimal even when current gain is exactly zero. This is the formal
counterexample to the blanket zero-gain stopping slogan. -/
def futureGainFixture : EchoStoppingMDP Unit Unit where
  observe := fun _ => ()
  successors := fun _ => {()}
  successors_nonempty := fun _ => Finset.singleton_nonempty ()
  echo_preserved := by intro _ _ _; rfl
  stopValue := fun _ => 0
  currentGain := fun _ => 0
  futureValue := fun _ => 2
  computeCost := fun _ => 1

/-- The countermodel has zero immediate gain. -/
theorem futureGainFixture_currentGain_zero :
    futureGainFixture.currentGain () = 0 := rfl

/-- The countermodel has strictly positive computation cost. -/
theorem futureGainFixture_cost_pos :
    0 < futureGainFixture.computeCost () := by norm_num [futureGainFixture]

/-- Yet its future surplus dominates cost, so the optimal dynamic action is to
compute rather than stop. -/
theorem futureGainFixture_computes :
    dynamicPolicy futureGainFixture () = MetaPolicy.compute := by
  unfold dynamicPolicy netComputeAdvantage continuationAdvantage bestContinuation
  simp [futureGainFixture]

/-! ## Exact static specialization -/

/-- Embed the old one-step decision problem into the dynamic model by giving it
one self-successor whose future value equals the current stop value. Then the
continuation advantage is exactly zero, so the only gain is the static value of
computation. -/
noncomputable def staticEchoModel
    {A X W Cn : Type} [DecidableEq A] [Fintype X] [Fintype W] [Fintype Cn]
    (μ : W → ℝ) (ν : W → Cn → ℝ) (D : FiniteDecision A X)
    (r : W → Cn → X → ℝ) (cost : ℝ) : EchoStoppingMDP Unit Unit where
  observe := fun _ => ()
  successors := fun _ => {()}
  successors_nonempty := fun _ => Finset.singleton_nonempty ()
  echo_preserved := by intro _ _ _; rfl
  stopValue := fun _ => expectedStop μ ν D r
  currentGain := fun _ => valueOfComputation μ ν D r
  futureValue := fun _ => expectedStop μ ν D r
  computeCost := fun _ => cost

/-- The static embedding has zero continuation advantage by construction. -/
theorem staticEchoModel_continuationAdvantage_zero
    {A X W Cn : Type} [DecidableEq A] [Fintype X] [Fintype W] [Fintype Cn]
    (μ : W → ℝ) (ν : W → Cn → ℝ) (D : FiniteDecision A X)
    (r : W → Cn → X → ℝ) (cost : ℝ) :
    continuationAdvantage (staticEchoModel μ ν D r cost) () = 0 := by
  unfold continuationAdvantage bestContinuation staticEchoModel
  simp

/-- The dynamic policy exactly recovers the old `optimalMetaPolicy` on the
static embedding. Thus the dynamic theorem is a strict extension rather than a
replacement with changed semantics. -/
theorem static_optimalMetaPolicy_eq_dynamicPolicy
    {A X W Cn : Type} [DecidableEq A] [Fintype X] [Fintype W] [Fintype Cn]
    (μ : W → ℝ) (ν : W → Cn → ℝ) (D : FiniteDecision A X)
    (r : W → Cn → X → ℝ) (cost : ℝ) :
    optimalMetaPolicy μ ν D r cost =
      dynamicPolicy (staticEchoModel μ ν D r cost) () := by
  unfold optimalMetaPolicy dynamicPolicy netComputeAdvantage continuationAdvantage
    bestContinuation staticEchoModel expectedCompute valueOfComputation
  simp only [Finset.sup'_singleton, sub_self, add_zero]
  split_ifs with hstatic hdynamic
  · rfl
  · exfalso
    linarith
  · exfalso
    linarith
  · rfl

/-- The existing positive-cost zero-deficit theorem is recovered as the static
zero-continuation special case of the dynamic policy. -/
theorem static_zero_deficit_specialization_stops
    {A X W Cn : Type} [DecidableEq A] [Fintype X] [Fintype W] [Fintype Cn]
    (μ : W → ℝ) (ν : W → Cn → ℝ) (D : FiniteDecision A X)
    (r : W → Cn → X → ℝ) (cost : ℝ)
    (hν1 : ∀ w, ∑ c, ν w c = 1) (s : W → X → ℝ)
    (hconst : ∀ w c, r w c = s w) (hcost : 0 < cost) :
    dynamicPolicy (staticEchoModel μ ν D r cost) () = MetaPolicy.stop := by
  rw [← static_optimalMetaPolicy_eq_dynamicPolicy μ ν D r cost]
  exact positive_cost_zero_deficit_forces_stop μ ν D r cost hν1 s hconst hcost

/-! ## Finite-horizon returns and optimality -/

/-- The optimal return from at most `n` chosen successor transitions. This
recursion uses terminal rewards, immediate gains and costs, not `futureValue`. -/
noncomputable def horizonValue {S : Type u} {Q : Type v} [DecidableEq S]
    (M : EchoStoppingMDP S Q) : Nat → S → ℝ
  | 0, s => M.stopValue s
  | n + 1, s => max (M.stopValue s)
      (M.currentGain s + (M.successors s).sup' (M.successors_nonempty s)
        (horizonValue M n) - M.computeCost s)

/-- A realized return from a legal sequence of at most `n` transitions. -/
inductive HorizonReturn {S : Type u} {Q : Type v} [DecidableEq S]
    (M : EchoStoppingMDP S Q) : Nat → S → ℝ → Prop
  | stop (n : Nat) (s : S) : HorizonReturn M n s (M.stopValue s)
  | compute {n : Nat} {s t : S} {value : ℝ} :
      t ∈ M.successors s → HorizonReturn M n t value →
        HorizonReturn M (n + 1) s (M.currentGain s + value - M.computeCost s)

/-- Stopping remains available at every horizon. -/
theorem stopValue_le_horizonValue {S : Type u} {Q : Type v} [DecidableEq S]
    (M : EchoStoppingMDP S Q) (n : Nat) (s : S) :
    M.stopValue s ≤ horizonValue M n s := by
  cases n with
  | zero => exact le_rfl
  | succ n => exact le_max_left _ _

/-- Every realized return is bounded by the recursively computed value. -/
theorem HorizonReturn.le_horizonValue {S : Type u} {Q : Type v} [DecidableEq S]
    {M : EchoStoppingMDP S Q} {n : Nat} {s : S} {value : ℝ}
    (h : HorizonReturn M n s value) : value ≤ horizonValue M n s := by
  induction h with
  | stop n s => exact stopValue_le_horizonValue M n s
  | @compute n s t value ht h ih =>
      have hsup := Finset.le_sup' (horizonValue M n) ht
      have hcont : M.currentGain s + value - M.computeCost s ≤
          M.currentGain s + (M.successors s).sup' (M.successors_nonempty s)
            (horizonValue M n) - M.computeCost s := by linarith
      exact hcont.trans (le_max_right _ _)

/-- Some legal finite sequence attains the computed optimum. -/
theorem horizonValue_attained {S : Type u} {Q : Type v} [DecidableEq S]
    (M : EchoStoppingMDP S Q) (n : Nat) (s : S) :
    HorizonReturn M n s (horizonValue M n s) := by
  classical
  induction n generalizing s with
  | zero => exact HorizonReturn.stop 0 s
  | succ n ih =>
      obtain ⟨t, ht, hmax⟩ := Finset.exists_mem_eq_sup'
        (M.successors_nonempty s) (horizonValue M n)
      by_cases hstop : M.currentGain s + horizonValue M n t - M.computeCost s ≤ M.stopValue s
      · simpa only [horizonValue, hmax, max_eq_left hstop] using
          (HorizonReturn.stop (M := M) (n + 1) s)
      · simpa only [horizonValue, hmax, max_eq_right (le_of_not_ge hstop)] using
          (HorizonReturn.compute ht (ih t))

/-- The Bellman recursion computes the greatest legal finite-horizon return. -/
theorem horizonValue_isGreatest {S : Type u} {Q : Type v} [DecidableEq S]
    (M : EchoStoppingMDP S Q) (n : Nat) (s : S) :
    IsGreatest {value : ℝ | HorizonReturn M n s value} (horizonValue M n s) :=
  ⟨horizonValue_attained M n s, fun _ h => h.le_horizonValue⟩

/-- An additional permitted transition does not invalidate an existing plan. -/
theorem HorizonReturn.weaken {S : Type u} {Q : Type v} [DecidableEq S]
    {M : EchoStoppingMDP S Q} {n : Nat} {s : S} {value : ℝ}
    (h : HorizonReturn M n s value) : HorizonReturn M (n + 1) s value := by
  induction h with
  | stop n s => exact HorizonReturn.stop (n + 1) s
  | compute ht h ih => exact HorizonReturn.compute ht ih

/-- The computed optimum is nondecreasing with the permitted horizon. -/
theorem horizonValue_le_succ {S : Type u} {Q : Type v} [DecidableEq S]
    (M : EchoStoppingMDP S Q) (n : Nat) (s : S) :
    horizonValue M n s ≤ horizonValue M (n + 1) s :=
  (horizonValue_attained M n s).weaken.le_horizonValue

/-- The supplied one-step forecast has no effect on the finite-horizon recursion. -/
theorem horizonValue_independent_futureValue
    {S : Type u} {Q : Type v} [DecidableEq S]
    (M : EchoStoppingMDP S Q) (future : S → ℝ) (n : Nat) :
    horizonValue { M with futureValue := future } n = horizonValue M n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      funext s
      simp only [horizonValue, ih]

/-- The horizon policy compares stopping with the computed continuation optimum. -/
noncomputable def horizonPolicy {S : Type u} {Q : Type v} [DecidableEq S]
    (M : EchoStoppingMDP S Q) : Nat → S → MetaPolicy
  | 0, _ => .stop
  | n + 1, s => by
      classical
      exact if M.stopValue s < M.currentGain s +
        (M.successors s).sup' (M.successors_nonempty s) (horizonValue M n) -
          M.computeCost s then .compute else .stop

/-- Stopping is chosen exactly when no computed continuation improves its value. -/
theorem horizonPolicy_stop_iff {S : Type u} {Q : Type v} [DecidableEq S]
    (M : EchoStoppingMDP S Q) (n : Nat) (s : S) :
    horizonPolicy M (n + 1) s = .stop ↔
      M.currentGain s + (M.successors s).sup' (M.successors_nonempty s)
        (horizonValue M n) - M.computeCost s ≤ M.stopValue s := by
  classical
  simp [horizonPolicy, not_lt]

/-- Stopping is selected exactly when its reward equals the computed optimum. -/
theorem horizonPolicy_stop_iff_value_eq_stop
    {S : Type u} {Q : Type v} [DecidableEq S]
    (M : EchoStoppingMDP S Q) (n : Nat) (s : S) :
    horizonPolicy M n s = .stop ↔ horizonValue M n s = M.stopValue s := by
  cases n with
  | zero => simp [horizonPolicy, horizonValue]
  | succ n =>
      rw [horizonPolicy_stop_iff]
      exact max_eq_left_iff.symm

/-- The old forecast policy agrees with the horizon policy when its forecast
is the computed value at the preceding horizon. -/
theorem horizonPolicy_eq_dynamicPolicy
    {S : Type u} {Q : Type v} [DecidableEq S]
    (M : EchoStoppingMDP S Q) (n : Nat) (s : S) :
    horizonPolicy M (n + 1) s =
      dynamicPolicy { M with futureValue := horizonValue M n } s := by
  classical
  change (if M.stopValue s < M.currentGain s +
      (M.successors s).sup' (M.successors_nonempty s) (horizonValue M n) -
        M.computeCost s then MetaPolicy.compute else MetaPolicy.stop) =
    (if 0 < M.currentGain s +
      ((M.successors s).sup' (M.successors_nonempty s) (horizonValue M n) -
        M.stopValue s) - M.computeCost s then MetaPolicy.compute else MetaPolicy.stop)
  have hiff : (M.stopValue s < M.currentGain s +
      (M.successors s).sup' (M.successors_nonempty s) (horizonValue M n) -
        M.computeCost s) ↔
    (0 < M.currentGain s +
      ((M.successors s).sup' (M.successors_nonempty s) (horizonValue M n) -
        M.stopValue s) - M.computeCost s) := by
    constructor <;> intro h <;> linarith
  simp only [hiff]

/-- A compute decision has a legal, value-maximizing continuation with a strictly
greater return than stopping. -/
theorem horizonPolicy_compute_realized {S : Type u} {Q : Type v} [DecidableEq S]
    (M : EchoStoppingMDP S Q) (n : Nat) (s : S)
    (h : horizonPolicy M (n + 1) s = .compute) :
    ∃ t value, t ∈ M.successors s ∧ HorizonReturn M n t value ∧
      M.currentGain s + value - M.computeCost s = horizonValue M (n + 1) s ∧
      M.stopValue s < M.currentGain s + value - M.computeCost s := by
  classical
  have hpos : M.stopValue s < M.currentGain s +
      (M.successors s).sup' (M.successors_nonempty s) (horizonValue M n) -
        M.computeCost s := by
    have h' : M.stopValue s + M.computeCost s < M.currentGain s +
        (M.successors s).sup' (M.successors_nonempty s) (horizonValue M n) := by
      simpa [horizonPolicy] using h
    linarith
  obtain ⟨t, ht, hmax⟩ := Finset.exists_mem_eq_sup'
    (M.successors_nonempty s) (horizonValue M n)
  rw [hmax] at hpos
  refine ⟨t, horizonValue M n t, ht, horizonValue_attained M n t, ?_, hpos⟩
  simp only [horizonValue, hmax, max_eq_right hpos.le]

/-- If no legal edge improves the current stopping reward, stopping is optimal
at every finite horizon within a successor-closed set. -/
theorem horizonValue_eq_stop_on_invariant_of_edge_bound
    {S : Type u} {Q : Type v} [DecidableEq S]
    (M : EchoStoppingMDP S Q) (I : S → Prop)
    (hclosed : ∀ s t, I s → t ∈ M.successors s → I t)
    (hbound : ∀ s t, I s → t ∈ M.successors s →
      M.currentGain s + M.stopValue t - M.computeCost s ≤ M.stopValue s)
    (n : Nat) (s : S) (hs : I s) : horizonValue M n s = M.stopValue s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      have hsup : (M.successors s).sup' (M.successors_nonempty s)
          (horizonValue M n) ≤ M.stopValue s + M.computeCost s - M.currentGain s := by
        apply Finset.sup'_le
        intro t ht
        rw [ih t (hclosed s t hs ht)]
        have h := hbound s t hs ht
        linarith
      have hcont : M.currentGain s + (M.successors s).sup' (M.successors_nonempty s)
          (horizonValue M n) - M.computeCost s ≤ M.stopValue s := by
        linarith
      exact max_eq_left hcont

/-- The edge inequality is necessary and sufficient for immediate stopping to
be optimal at every horizon and every state of an invariant set. -/
theorem horizonValue_eq_stop_on_invariant_iff
    {S : Type u} {Q : Type v} [DecidableEq S]
    (M : EchoStoppingMDP S Q) (I : S → Prop)
    (hclosed : ∀ s t, I s → t ∈ M.successors s → I t) :
    (∀ n s, I s → horizonValue M n s = M.stopValue s) ↔
      ∀ s t, I s → t ∈ M.successors s →
        M.currentGain s + M.stopValue t - M.computeCost s ≤ M.stopValue s := by
  constructor
  · intro hall s t hs ht
    have h := (HorizonReturn.compute ht (HorizonReturn.stop 0 t)).le_horizonValue
    simpa only [hall 1 s hs] using h
  · intro hbound n s hs
    exact horizonValue_eq_stop_on_invariant_of_edge_bound M I hclosed hbound n s hs

/-- Every finite-horizon optimum equals immediate stopping exactly when every
legal edge satisfies the stopping inequality. -/
theorem horizonValue_eq_stop_iff_edge_bound
    {S : Type u} {Q : Type v} [DecidableEq S]
    (M : EchoStoppingMDP S Q) :
    (∀ n s, horizonValue M n s = M.stopValue s) ↔
      ∀ s t, t ∈ M.successors s →
        M.currentGain s + M.stopValue t - M.computeCost s ≤ M.stopValue s := by
  simpa only [true_implies] using
    horizonValue_eq_stop_on_invariant_iff M (fun _ => True) (fun _ _ _ _ => True.intro)

/-- The same edge inequality characterizes stopping decisions at every horizon. -/
theorem horizonPolicy_stops_iff_edge_bound
    {S : Type u} {Q : Type v} [DecidableEq S]
    (M : EchoStoppingMDP S Q) :
    (∀ n s, horizonPolicy M n s = .stop) ↔
      ∀ s t, t ∈ M.successors s →
        M.currentGain s + M.stopValue t - M.computeCost s ≤ M.stopValue s := by
  simp only [horizonPolicy_stop_iff_value_eq_stop]
  exact horizonValue_eq_stop_iff_edge_bound M

/-- Nonpositive net gains and nonincreasing stop rewards imply the exact edge
inequality. Neither separate condition is required by the exact criterion. -/
theorem horizonValue_eq_stop_on_invariant
    {S : Type u} {Q : Type v} [DecidableEq S]
    (M : EchoStoppingMDP S Q) (I : S → Prop)
    (hclosed : ∀ s t, I s → t ∈ M.successors s → I t)
    (hnet : ∀ s, I s → M.currentGain s ≤ M.computeCost s)
    (hstop : ∀ s t, I s → t ∈ M.successors s → M.stopValue t ≤ M.stopValue s)
    (n : Nat) (s : S) (hs : I s) : horizonValue M n s = M.stopValue s := by
  apply horizonValue_eq_stop_on_invariant_of_edge_bound M I hclosed (n := n) (s := s) (hs := hs)
  intro s t hs ht
  have h₁ := hnet s hs
  have h₂ := hstop s t hs ht
  linarith

/-- If stop rewards depend only on the unchanged observation and net gains are
nonpositive, every finite-horizon optimum equals immediate stopping. -/
theorem horizonValue_eq_stop_of_echo_license
    {S : Type u} {Q : Type v} [DecidableEq S]
    (M : EchoStoppingMDP S Q)
    (hnet : ∀ s, M.currentGain s ≤ M.computeCost s)
    (hreward : ∀ s t, M.observe s = M.observe t → M.stopValue s = M.stopValue t)
    (n : Nat) (s : S) : horizonValue M n s = M.stopValue s := by
  exact horizonValue_eq_stop_on_invariant M (fun _ => True)
    (fun _ _ _ _ => True.intro) (fun s _ => hnet s)
    (fun s t _ ht => le_of_eq (hreward t s (M.echo_preserved s t ht))) n s True.intro

/-- Echo-preserved terminal rewards and nonpositive net gains select stopping
at every finite horizon, including zero. -/
theorem horizonPolicy_stops_of_echo_license
    {S : Type u} {Q : Type v} [DecidableEq S]
    (M : EchoStoppingMDP S Q)
    (hnet : ∀ s, M.currentGain s ≤ M.computeCost s)
    (hreward : ∀ s t, M.observe s = M.observe t → M.stopValue s = M.stopValue t)
    (n : Nat) (s : S) : horizonPolicy M n s = .stop :=
  (horizonPolicy_stop_iff_value_eq_stop M n s).2
    (horizonValue_eq_stop_of_echo_license M hnet hreward n s)

/-- A two-state problem whose next state has a larger terminal reward. -/
def realizedFutureGainFixture : EchoStoppingMDP Bool Unit where
  observe := fun _ => ()
  successors := fun _ => {true}
  successors_nonempty := fun _ => Finset.singleton_nonempty true
  echo_preserved := by intro _ _ _; rfl
  stopValue := fun s => if s then 2 else 0
  currentGain := fun _ => 0
  futureValue := fun _ => 0
  computeCost := fun _ => 1

/-- The two-state continuation gains one unit after paying its actual cost. -/
theorem realizedFutureGainFixture_computes :
    realizedFutureGainFixture.currentGain false = 0 ∧
    realizedFutureGainFixture.computeCost false = 1 ∧
    horizonValue realizedFutureGainFixture 1 false = 1 ∧
    horizonPolicy realizedFutureGainFixture 1 false = .compute := by
  norm_num [realizedFutureGainFixture, horizonValue, horizonPolicy]

/-- The profitable plan takes an actual transition to a different state. -/
theorem realizedFutureGainFixture_transition :
    true ∈ realizedFutureGainFixture.successors false ∧
    (false : Bool) ≠ true ∧
    HorizonReturn realizedFutureGainFixture 1 false 1 := by
  refine ⟨by simp [realizedFutureGainFixture], by decide, ?_⟩
  convert
    (HorizonReturn.compute (M := realizedFutureGainFixture)
      (s := false) (t := true) (by simp [realizedFutureGainFixture])
      (HorizonReturn.stop 0 true)) using 1; norm_num [realizedFutureGainFixture]

/-- A positive immediate net gain is outweighed by the loss of terminal reward. -/
def compensatedGainFixture : EchoStoppingMDP Bool Unit where
  observe := fun _ => ()
  successors := fun _ => {true}
  successors_nonempty := fun _ => Finset.singleton_nonempty true
  echo_preserved := by intro _ _ _; rfl
  stopValue := fun s => if s then 0 else 2
  currentGain := fun s => if s then 0 else 2
  futureValue := fun _ => 0
  computeCost := fun _ => 1

/-- The exact criterion holds despite positive net gain at a state with a legal
transition to a different state. -/
theorem compensatedGainFixture_stops :
    compensatedGainFixture.computeCost false < compensatedGainFixture.currentGain false ∧
      true ∈ compensatedGainFixture.successors false ∧
      ∀ n s, horizonPolicy compensatedGainFixture n s = .stop := by
  refine ⟨by norm_num [compensatedGainFixture], by simp [compensatedGainFixture], ?_⟩
  apply (horizonPolicy_stops_iff_edge_bound compensatedGainFixture).2
  intro s t ht
  have ht' : t = true := by simpa [compensatedGainFixture] using ht
  subst t
  cases s <;> norm_num [compensatedGainFixture]

#check @bestContinuation_le_iff
#check @successor_observation_eq
#check @zero_current_gain_positive_cost_dominated_continuations_force_stop
#check @nonpositive_current_gain_positive_cost_dominated_continuations_force_stop
#check futureGainFixture_currentGain_zero
#check futureGainFixture_cost_pos
#check futureGainFixture_computes
#check @staticEchoModel_continuationAdvantage_zero
#check @static_optimalMetaPolicy_eq_dynamicPolicy
#check @static_zero_deficit_specialization_stops

#print axioms bestContinuation_le_iff
#print axioms successor_observation_eq
#print axioms zero_current_gain_positive_cost_dominated_continuations_force_stop
#print axioms nonpositive_current_gain_positive_cost_dominated_continuations_force_stop
#print axioms futureGainFixture_currentGain_zero
#print axioms futureGainFixture_cost_pos
#print axioms futureGainFixture_computes
#print axioms staticEchoModel_continuationAdvantage_zero
#print axioms static_optimalMetaPolicy_eq_dynamicPolicy
#print axioms static_zero_deficit_specialization_stops


/-! ## Finite-support stochastic stopping -/

namespace Stochastic

/-- Legal actions carry finite probability distributions and transition rewards. -/
structure Model (S : Type u) (A : Type v) [DecidableEq S] [DecidableEq A] where
  actions : S → Finset A
  support : S → A → Finset S
  probability : S → A → S → ℝ
  probability_nonneg : ∀ s a, a ∈ actions s →
    ∀ t ∈ support s a, 0 ≤ probability s a t
  probability_sum : ∀ s a, a ∈ actions s →
    ∑ t ∈ support s a, probability s a t = 1
  stopValue : S → ℝ
  reward : S → A → S → ℝ

variable {S : Type u} {A : Type v} [DecidableEq S] [DecidableEq A]

/-- Continuation value is the probability-weighted return from actual outcomes. -/
def expected (M : Model S A) (V : S → ℝ) (s : S) (a : A) : ℝ :=
  ∑ t ∈ M.support s a, M.probability s a t * (M.reward s a t + V t)

theorem expected_mono (M : Model S A) {V W : S → ℝ} {s : S} {a : A}
    (ha : a ∈ M.actions s) (h : ∀ t ∈ M.support s a, V t ≤ W t) :
    expected M V s a ≤ expected M W s a := by
  apply Finset.sum_le_sum
  intro t ht
  exact mul_le_mul_of_nonneg_left (add_le_add_left (h t ht) _)
    (M.probability_nonneg s a ha t ht)

theorem expected_congr (M : Model S A) {V W : S → ℝ} {s : S} {a : A}
    (h : ∀ t ∈ M.support s a, V t = W t) :
    expected M V s a = expected M W s a := by
  apply Finset.sum_congr rfl
  intro t ht
  rw [h t ht]

/-- Outcomes of probability zero impose no equality requirement. -/
theorem expected_congr_on_positive (M : Model S A) {V W : S → ℝ}
    {s : S} {a : A} (ha : a ∈ M.actions s)
    (h : ∀ t ∈ M.support s a, 0 < M.probability s a t → V t = W t) :
    expected M V s a = expected M W s a := by
  apply Finset.sum_congr rfl
  intro t ht
  by_cases hz : M.probability s a t = 0
  · simp only [hz, zero_mul]
  · rw [h t ht (lt_of_le_of_ne (M.probability_nonneg s a ha t ht) (Ne.symm hz))]

/-- A legal probability distribution has a positive-mass outcome. -/
theorem positive_outcome_exists (M : Model S A) {s : S} {a : A}
    (ha : a ∈ M.actions s) :
    ∃ t ∈ M.support s a, 0 < M.probability s a t := by
  classical
  by_contra h
  have hz : ∀ t ∈ M.support s a, M.probability s a t = 0 := by
    intro t ht
    exact le_antisymm (le_of_not_gt (fun hp => h ⟨t, ht, hp⟩))
      (M.probability_nonneg s a ha t ht)
  have hsum := M.probability_sum s a ha
  have hzero : (∑ t ∈ M.support s a, M.probability s a t) = 0 :=
    Finset.sum_eq_zero hz
  linarith

/-- Stopping is a choice even when there are no legal continuation actions. -/
def choices (M : Model S A) (s : S) : Finset (Option A) :=
  insert none ((M.actions s).image some)

theorem choices_nonempty (M : Model S A) (s : S) : (choices M s).Nonempty :=
  ⟨none, Finset.mem_insert_self _ _⟩

theorem mem_choices (M : Model S A) (s : S) (c : Option A) :
    c ∈ choices M s ↔ c = none ∨ ∃ a ∈ M.actions s, c = some a := by
  simp only [choices, Finset.mem_insert, Finset.mem_image]
  constructor
  · rintro (h | ⟨a, ha, h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨a, ha, h.symm⟩
  · rintro (h | ⟨a, ha, h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨a, ha, h.symm⟩

def choiceValue (M : Model S A) (V : S → ℝ) (s : S) : Option A → ℝ
  | none => M.stopValue s
  | some a => expected M V s a

noncomputable def bellman (M : Model S A) (V : S → ℝ) (s : S) : ℝ :=
  (choices M s).sup' (choices_nonempty M s) (choiceValue M V s)

noncomputable def value (M : Model S A) : Nat → S → ℝ
  | 0, s => M.stopValue s
  | n + 1, s => bellman M (value M n) s

theorem stop_le_bellman (M : Model S A) (V : S → ℝ) (s : S) :
    M.stopValue s ≤ bellman M V s := by
  change choiceValue M V s none ≤ bellman M V s
  exact Finset.le_sup' (choiceValue M V s)
    (show none ∈ choices M s from Finset.mem_insert_self _ _)

theorem expected_le_bellman (M : Model S A) (V : S → ℝ) {s : S} {a : A}
    (ha : a ∈ M.actions s) : expected M V s a ≤ bellman M V s :=
  Finset.le_sup' (choiceValue M V s)
    ((mem_choices M s (some a)).mpr (Or.inr ⟨a, ha, rfl⟩))

theorem stop_le_value (M : Model S A) (n : Nat) (s : S) :
    M.stopValue s ≤ value M n s := by
  cases n with
  | zero => exact le_rfl
  | succ n => exact stop_le_bellman M (value M n) s

/-- A policy chooses a legal action and a continuation for each observed state.
Continuations may differ at every node, so the policy can depend on history. -/
inductive Policy (M : Model S A) : Nat → S → Type (max u v)
  | stop (n : Nat) (s : S) : Policy M n s
  | compute {n : Nat} (s : S) (a : A) (ha : a ∈ M.actions s)
      (next : ∀ t : S, Policy M n t) : Policy M (n + 1) s

def Policy.value {M : Model S A} : {n : Nat} → {s : S} → Policy M n s → ℝ
  | _, _, .stop _ s => M.stopValue s
  | _, _, .compute s a _ next => expected M (fun t => Policy.value (next t)) s a

/-- Expected policy returns are bounded by the Bellman value. -/
theorem Policy.le_value {M : Model S A} {n : Nat} {s : S} (p : Policy M n s) :
    p.value ≤ Stochastic.value M n s := by
  induction p with
  | stop n s => exact stop_le_value M n s
  | @compute n s a ha next ih =>
      exact (expected_mono M ha (fun t _ => ih t)).trans
        (expected_le_bellman M (Stochastic.value M n) ha)

/-- A legal adaptive policy attains the Bellman value at every finite horizon. -/
theorem value_attained (M : Model S A) (n : Nat) (s : S) :
    ∃ p : Policy M n s, p.value = value M n s := by
  classical
  induction n generalizing s with
  | zero => exact ⟨Policy.stop 0 s, rfl⟩
  | succ n ih =>
      obtain ⟨c, hc, hmax⟩ := Finset.exists_mem_eq_sup'
        (choices_nonempty M s) (choiceValue M (value M n) s)
      rcases (mem_choices M s c).mp hc with hnone | ⟨a, ha, hsome⟩
      · subst c
        exact ⟨Policy.stop (n + 1) s, hmax.symm⟩
      · subst c
        let next : ∀ t : S, Policy M n t := fun t => Classical.choose (ih t)
        have hnext : ∀ t : S, (next t).value = value M n t :=
          fun t => Classical.choose_spec (ih t)
        refine ⟨Policy.compute s a ha next, ?_⟩
        change expected M (fun t => (next t).value) s a = value M (n + 1) s
        exact (expected_congr M (fun t _ => hnext t)).trans hmax.symm

theorem value_isGreatest (M : Model S A) (n : Nat) (s : S) :
    IsGreatest {r : ℝ | ∃ p : Policy M n s, p.value = r} (value M n s) := by
  refine ⟨value_attained M n s, ?_⟩
  rintro r ⟨p, rfl⟩
  exact p.le_value

theorem bellman_mono (M : Model S A) {V W : S → ℝ} (h : ∀ t, V t ≤ W t)
    (s : S) : bellman M V s ≤ bellman M W s := by
  apply Finset.sup'_le (choices_nonempty M s) (choiceValue M V s)
  intro c hc
  rcases (mem_choices M s c).mp hc with rfl | ⟨a, ha, rfl⟩
  · exact stop_le_bellman M W s
  · exact (expected_mono M ha (fun t _ => h t)).trans (expected_le_bellman M W ha)

theorem value_le_succ (M : Model S A) (n : Nat) (s : S) :
    value M n s ≤ value M (n + 1) s := by
  induction n generalizing s with
  | zero => exact stop_le_value M 1 s
  | succ n ih => exact bellman_mono M ih s

/-- Immediate stopping is optimal exactly when every legal action's expected return is bounded. -/
theorem bellman_eq_stop_iff (M : Model S A) (V : S → ℝ) (s : S) :
    bellman M V s = M.stopValue s ↔
      ∀ a ∈ M.actions s, expected M V s a ≤ M.stopValue s := by
  constructor
  · intro h a ha
    rw [← h]
    exact expected_le_bellman M V ha
  · intro h
    apply le_antisymm _ (stop_le_bellman M V s)
    apply Finset.sup'_le (choices_nonempty M s) (choiceValue M V s)
    intro c hc
    rcases (mem_choices M s c).mp hc with rfl | ⟨a, ha, rfl⟩
    · exact le_rfl
    · exact h a ha

theorem value_eq_stop_of_no_actions (M : Model S A) {s : S}
    (hs : M.actions s = ∅) (n : Nat) : value M n s = M.stopValue s := by
  cases n with
  | zero => rfl
  | succ n =>
      apply (bellman_eq_stop_iff M (value M n) s).mpr
      intro a ha
      simp only [hs, Finset.notMem_empty] at ha

/-- Closure is required only for positive-probability outcomes. -/
theorem value_eq_stop_on_invariant (M : Model S A) (I : S → Prop)
    (hclosed : ∀ s a t, I s → a ∈ M.actions s → t ∈ M.support s a →
      0 < M.probability s a t → I t)
    (hbound : ∀ s, I s → ∀ a ∈ M.actions s,
      expected M M.stopValue s a ≤ M.stopValue s)
    (n : Nat) (s : S) (hs : I s) : value M n s = M.stopValue s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      apply (bellman_eq_stop_iff M (value M n) s).mpr
      intro a ha
      rw [expected_congr_on_positive M ha (fun t ht hp =>
        ih t (hclosed s a t hs ha ht hp))]
      exact hbound s hs a ha

theorem value_eq_stop_on_invariant_iff (M : Model S A) (I : S → Prop)
    (hclosed : ∀ s a t, I s → a ∈ M.actions s → t ∈ M.support s a →
      0 < M.probability s a t → I t) :
    (∀ n s, I s → value M n s = M.stopValue s) ↔
      ∀ s, I s → ∀ a ∈ M.actions s, expected M M.stopValue s a ≤ M.stopValue s := by
  constructor
  · intro h s hs
    exact (bellman_eq_stop_iff M M.stopValue s).mp (h 1 s hs)
  · intro h n s hs
    exact value_eq_stop_on_invariant M I hclosed h n s hs

/-- One-step expected inequalities characterize stopping at all finite horizons. -/
theorem value_eq_stop_iff (M : Model S A) :
    (∀ n s, value M n s = M.stopValue s) ↔
      ∀ s a, a ∈ M.actions s → expected M M.stopValue s a ≤ M.stopValue s := by
  simpa only [true_implies] using
    value_eq_stop_on_invariant_iff M (fun _ => True) (fun _ _ _ _ _ _ _ => True.intro)

theorem expected_le_of_pointwise (M : Model S A) {V : S → ℝ} {s : S} {a : A}
    (ha : a ∈ M.actions s) (b : ℝ)
    (h : ∀ t ∈ M.support s a, 0 < M.probability s a t → M.reward s a t + V t ≤ b) :
    expected M V s a ≤ b := by
  calc
    expected M V s a ≤ ∑ t ∈ M.support s a, M.probability s a t * b := by
      apply Finset.sum_le_sum
      intro t ht
      by_cases hz : M.probability s a t = 0
      · simp only [hz, zero_mul, le_refl]
      · exact mul_le_mul_of_nonneg_left
          (h t ht (lt_of_le_of_ne (M.probability_nonneg s a ha t ht) (Ne.symm hz)))
          (M.probability_nonneg s a ha t ht)
    _ = b := by rw [← Finset.sum_mul, M.probability_sum s a ha, one_mul]

/-- An observation-preserving kernel and licensed stop rewards give stopping
when transition rewards are nonpositive on positive-mass outcomes. -/
theorem value_eq_stop_of_echo {Q : Type*} (M : Model S A) (q : S → Q)
    (hecho : ∀ s a t, a ∈ M.actions s → t ∈ M.support s a →
      0 < M.probability s a t → q t = q s)
    (hlicensed : ∀ s t, q s = q t → M.stopValue s = M.stopValue t)
    (hreward : ∀ s a t, a ∈ M.actions s → t ∈ M.support s a →
      0 < M.probability s a t → M.reward s a t ≤ 0)
    (n : Nat) (s : S) : value M n s = M.stopValue s := by
  apply (value_eq_stop_iff M).mpr _ n s
  intro s a ha
  apply expected_le_of_pointwise M ha (M.stopValue s)
  intro t ht hp
  rw [hlicensed t s (hecho s a t ha ht hp)]
  exact add_le_of_nonpos_left (hreward s a t ha ht hp)

/-- Two outcomes have mass one half; the third has mass zero and reward 100.
Only state zero has a continuation action. -/
noncomputable def averagingFixture : Model (Fin 3) Unit where
  actions := fun s => if s = 0 then {()} else ∅
  support := fun _ _ => Finset.univ
  probability := fun _ _ t => if t = 2 then 0 else 1 / 2
  probability_nonneg := by
    intro s a ha t ht
    split <;> norm_num
  probability_sum := by
    intro s a ha
    have h02 : (0 : Fin 3) ≠ 2 := by decide
    have h12 : (1 : Fin 3) ≠ 2 := by decide
    norm_num [Fin.sum_univ_succ, h02, h12]
  stopValue := fun _ => 0
  reward := fun _ _ t => if t = 0 then -1 else if t = 1 then 3 else 100

theorem averagingFixture_expected_formula (V : Fin 3 → ℝ) :
    expected averagingFixture V 0 () = ((-1 + V 0) + (3 + V 1)) / 2 := by
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  have h10 : (1 : Fin 3) ≠ 0 := by decide
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  norm_num [expected, averagingFixture, Fin.sum_univ_succ, h02, h12, h10, h20]
  ring

theorem averagingFixture_bellman_formula (V : Fin 3 → ℝ) :
    bellman averagingFixture V 0 = max 0 (((-1 + V 0) + (3 + V 1)) / 2) := by
  simp only [bellman, choices, averagingFixture, choiceValue]
  change max 0 (expected averagingFixture V 0 ()) = _
  rw [averagingFixture_expected_formula]

theorem averagingFixture_expected :
    expected averagingFixture averagingFixture.stopValue 0 () = 1 := by
  rw [averagingFixture_expected_formula]
  norm_num [averagingFixture]

theorem averagingFixture_one_step :
    value averagingFixture 1 0 = 1 := by
  change bellman averagingFixture averagingFixture.stopValue 0 = 1
  rw [averagingFixture_bellman_formula]
  norm_num [averagingFixture]

theorem averagingFixture_two_steps :
    value averagingFixture 2 0 = 3 / 2 := by
  change bellman averagingFixture (value averagingFixture 1) 0 = 3 / 2
  rw [averagingFixture_bellman_formula, averagingFixture_one_step]
  have hterminal : value averagingFixture 1 1 = 0 :=
    value_eq_stop_of_no_actions averagingFixture (by decide) 1
  rw [hterminal]
  norm_num

theorem averagingFixture_zero_mass_and_empty_actions :
    averagingFixture.probability 0 () 2 = 0 ∧
      averagingFixture.reward 0 () 2 = 100 ∧
      averagingFixture.actions 1 = ∅ ∧
      ∀ n, value averagingFixture n 1 = 0 := by
  refine ⟨rfl, rfl, by decide, ?_⟩
  intro n
  exact value_eq_stop_of_no_actions averagingFixture (by decide) n

/-- The actual branching process has a legal adaptive policy with expected return 3/2. -/
theorem averagingFixture_adaptive_policy :
    ∃ p : Policy averagingFixture 2 0, p.value = 3 / 2 := by
  obtain ⟨p, hp⟩ := value_attained averagingFixture 2 0
  exact ⟨p, hp.trans averagingFixture_two_steps⟩

end Stochastic

end OperatorKO7.Meta.Decision.EchoStopping
