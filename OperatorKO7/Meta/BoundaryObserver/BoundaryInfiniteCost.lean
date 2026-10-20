import OperatorKO7.Meta.BoundaryObserver.BoundaryPole
import OperatorKO7.Meta.BoundaryObserver.BoundaryThreeGeneral

set_option autoImplicit false

/-!
# The boundary as the set of infinite resolution cost


The paragraph after Theorem `thm:boundary-singularity` of the mathematics manuscript states the
boundary of an observer as one equivalence: two distinct states form a merged pair exactly if every
adaptive protocol of record-determined readings acquires zero information about their label at
every horizon and in the limit, and at a split pair one record-determined reading, the Boolean
indicator of the record, acquires the whole bit at cost one. The merged direction is
`BoundaryPole.recordProtocolPoleGoal`; the split direction reads the indicator of
`BoundaryThreeGeneral.indicatorReading` once, through `PairResolution.split_pair_one_reading`.
This module joins the two directions in one declaration, in the information form and in the cost
form. The record type `Q` carries no finiteness and no decidability hypothesis.

The target of the cost form lies in `(0, 1]`: the label is Boolean, so no protocol acquires more
than one bit, and a target above one bit is missed at every pair.

Relation: finite stopped laws of one named protocol. Trust: kernel-only. No `sorry`, `admit`,
`axiom`, `native_decide`.
-/

namespace OperatorKO7.Meta.BoundaryObserver.BoundaryInfiniteCost

open ProtocolResolution PairResolution MergedPair BoundaryPole BoundaryThreeGeneral

noncomputable section

/-- The merged direction for one observer and one pair: every adaptive protocol about the label of
a merged pair, with a record-determined reading at every retained history and action, acquires zero
information at every horizon and in the limit. -/
theorem recordProtocol_blind_of_merged {X Q : Type} (q : X → Q) {x₀ x₁ : X}
    (hm : IsMergedPair q x₀ x₁) :
    ∀ (A Y : Type) [Fintype A] [Fintype Y] (p : FiniteProtocol Bool A Y)
      (K : List (A × Y) → A → Reading X Y),
      (∀ h a, RecordDetermined q (K h a)) →
      (∀ h a b, p.observation h a b = K h a (pairState x₀ x₁ b)) →
      (∀ n bank, HistoryBank n bank → terminalMI p n bank = 0) ∧ informationLimit p = 0 := by
  intro A Y _ _ p K hdet hobs
  exact recordProtocolPoleGoal X Q A Y q x₀ x₁ p K hm hdet hobs

/-- The one-reading protocol of the Boolean indicator of the record of `x₀` at the pair
`(x₀, x₁)`: a fair label, the indicator law of the labelled state, one reading of cost one. -/
def indicatorProtocol {X Q : Type} (q : X → Q) (x₀ x₁ : X) : FiniteProtocol Bool Unit Bool :=
  repeatProtocol (indicatorReading q x₀ x₀) (indicatorReading q x₀ x₁) 1

/-- The reading of the indicator protocol at every retained history and action is the indicator
reading at the labelled state of the pair. -/
theorem indicatorProtocol_observation {X Q : Type} (q : X → Q) (x₀ x₁ : X)
    (h : List (Unit × Bool)) (a : Unit) (b : Bool) :
    (indicatorProtocol q x₀ x₁).observation h a b = indicatorReading q x₀ (pairState x₀ x₁ b) := by
  cases b <;> rfl

/-- At a split pair the indicator protocol is a protocol of one record-determined reading of
discrimination two and of cost one at every history, and it acquires the whole bit about the label
at expected cost one. -/
theorem indicator_protocol_split {X Q : Type} (q : X → Q) {x₀ x₁ : X} (hq : q x₀ ≠ q x₁) :
    RecordDetermined q (indicatorReading q x₀) ∧
      (∀ h a b, (indicatorProtocol q x₀ x₁).observation h a b =
        indicatorReading q x₀ (pairState x₀ x₁ b)) ∧
      (∀ h a, 1 ≤ (indicatorProtocol q x₀ x₁).cost h a) ∧
      readingDiscrimination (indicatorReading q x₀) x₀ x₁ = 2 ∧
      1 ≤ terminalMI (indicatorProtocol q x₀ x₁) 1 (historyBank Unit Bool 1) ∧
      expectedCost (indicatorProtocol q x₀ x₁) 1 (historyBank Unit Bool 1) = 1 := by
  classical
  have hsplit : decide (q x₀ = q x₀) ≠ decide (q x₁ = q x₀) := by
    simp [Ne.symm hq]
  have hone := split_pair_one_reading (fun z : X => decide (q z = q x₀)) x₀ x₁ hsplit
  refine ⟨indicatorReading_recordDetermined q x₀, indicatorProtocol_observation q x₀ x₁,
    fun _ _ => le_rfl, indicatorReading_discrimination_split q hq, ?_, ?_⟩
  · exact hone.2.1
  · exact hone.2.2

/-- The boundary is the set of pairs blind to every record-determined protocol: for distinct
states, the pair is merged exactly if every adaptive protocol about its label, with a
record-determined reading at every retained history and action, acquires zero information at every
horizon and in the limit. -/
theorem boundary_iff_blind {X Q : Type} (q : X → Q) {x₀ x₁ : X} (hne : x₀ ≠ x₁) :
    IsMergedPair q x₀ x₁ ↔
      ∀ (A Y : Type) [Fintype A] [Fintype Y] (p : FiniteProtocol Bool A Y)
        (K : List (A × Y) → A → Reading X Y),
        (∀ h a, RecordDetermined q (K h a)) →
        (∀ h a b, p.observation h a b = K h a (pairState x₀ x₁ b)) →
        (∀ n bank, HistoryBank n bank → terminalMI p n bank = 0) ∧ informationLimit p = 0 := by
  refine ⟨recordProtocol_blind_of_merged q, ?_⟩
  intro hall
  refine ⟨hne, ?_⟩
  by_contra hq
  obtain ⟨hdet, hobs, _, _, hinfo, _⟩ := indicator_protocol_split q hq
  have hzero := (hall Unit Bool (indicatorProtocol q x₀ x₁) (fun _ _ => indicatorReading q x₀)
    (fun _ _ => hdet) hobs).1 1 (historyBank Unit Bool 1) (historyBank_complete Unit Bool 1)
  rw [hzero] at hinfo
  norm_num at hinfo

/-- The cost form of the boundary: for distinct states and every target `c` in `(0, 1]` bits, the
pair is merged exactly if no adaptive protocol about its label, with a record-determined reading of
cost at least one at every retained history and action, acquires `c` bits at any horizon, so that
the resolution cost of the target by such protocols is infinite; and at a split pair the indicator
protocol acquires one bit at expected cost one. -/
theorem boundary_iff_infinite_cost {X Q : Type} (q : X → Q) {x₀ x₁ : X} (hne : x₀ ≠ x₁)
    (c : ℝ) (hc0 : 0 < c) (hc1 : c ≤ 1) :
    (IsMergedPair q x₀ x₁ ↔
      ∀ (A Y : Type) [Fintype A] [Fintype Y] (p : FiniteProtocol Bool A Y)
        (K : List (A × Y) → A → Reading X Y),
        (∀ h a, RecordDetermined q (K h a)) →
        (∀ h a b, p.observation h a b = K h a (pairState x₀ x₁ b)) →
        (∀ h a, 1 ≤ p.cost h a) →
        ∀ n bank, HistoryBank n bank → terminalMI p n bank < c) ∧
    (q x₀ ≠ q x₁ →
      1 ≤ terminalMI (indicatorProtocol q x₀ x₁) 1 (historyBank Unit Bool 1) ∧
        expectedCost (indicatorProtocol q x₀ x₁) 1 (historyBank Unit Bool 1) = 1) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro hm A Y _ _ p K hdet hobs _ n bank hb
    rw [(recordProtocol_blind_of_merged q hm A Y p K hdet hobs).1 n bank hb]
    exact hc0
  · intro hall
    refine ⟨hne, ?_⟩
    by_contra hq
    obtain ⟨hdet, hobs, hcost, _, hinfo, _⟩ := indicator_protocol_split q hq
    have hlt := hall Unit Bool (indicatorProtocol q x₀ x₁) (fun _ _ => indicatorReading q x₀)
      (fun _ _ => hdet) hobs hcost 1 (historyBank Unit Bool 1) (historyBank_complete Unit Bool 1)
    linarith
  · intro hq
    obtain ⟨_, _, _, _, hinfo, hcost⟩ := indicator_protocol_split q hq
    exact ⟨hinfo, hcost⟩

/-- The boundary of every observer, in the information form and in the cost form: for distinct
states the pair is merged exactly if every record-determined protocol is blind to its label, and,
for every target `c` in `(0, 1]` bits, exactly if no record-determined protocol of readings of cost
at least one acquires `c` bits at any horizon; at a split pair the indicator protocol acquires one
bit at expected cost one. -/
def BoundaryInfiniteCostGoal : Prop :=
  ∀ (X Q : Type) (q : X → Q) (x₀ x₁ : X), x₀ ≠ x₁ →
    (IsMergedPair q x₀ x₁ ↔
      ∀ (A Y : Type) [Fintype A] [Fintype Y] (p : FiniteProtocol Bool A Y)
        (K : List (A × Y) → A → Reading X Y),
        (∀ h a, RecordDetermined q (K h a)) →
        (∀ h a b, p.observation h a b = K h a (pairState x₀ x₁ b)) →
        (∀ n bank, HistoryBank n bank → terminalMI p n bank = 0) ∧ informationLimit p = 0) ∧
    ∀ c : ℝ, 0 < c → c ≤ 1 →
      (IsMergedPair q x₀ x₁ ↔
        ∀ (A Y : Type) [Fintype A] [Fintype Y] (p : FiniteProtocol Bool A Y)
          (K : List (A × Y) → A → Reading X Y),
          (∀ h a, RecordDetermined q (K h a)) →
          (∀ h a b, p.observation h a b = K h a (pairState x₀ x₁ b)) →
          (∀ h a, 1 ≤ p.cost h a) →
          ∀ n bank, HistoryBank n bank → terminalMI p n bank < c) ∧
      (q x₀ ≠ q x₁ →
        1 ≤ terminalMI (indicatorProtocol q x₀ x₁) 1 (historyBank Unit Bool 1) ∧
          expectedCost (indicatorProtocol q x₀ x₁) 1 (historyBank Unit Bool 1) = 1)

/-- The boundary of every observer is the set of pairs of infinite resolution cost for the
record-determined protocols. -/
theorem boundaryInfiniteCostGoal : BoundaryInfiniteCostGoal := by
  intro X Q q x₀ x₁ hne
  exact ⟨boundary_iff_blind q hne, fun c hc0 hc1 => boundary_iff_infinite_cost q hne c hc0 hc1⟩

end

end OperatorKO7.Meta.BoundaryObserver.BoundaryInfiniteCost
