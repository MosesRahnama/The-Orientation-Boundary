import OperatorKO7.Meta.BoundaryObserver.PairResolution
import OperatorKO7.Meta.BoundaryObserver.MergedPair
import OperatorKO7.Meta.DistinctionBoundary.GodelFixedPointSemantics
import OperatorKO7.Meta.BoundaryObserver.RecursorDecidability
import OperatorKO7.Meta.BoundaryObserver.DemandCompletion

set_option autoImplicit false

/-!
# Boundary pole: record-determined readings
Graph: notes/universal-roadmap/M6-EXECUTION.md, M6.0, source-reviewed.
The theorem statements below are copied exactly from BoundaryTheoremSpec.lean, with one
exception: `BoundaryZeroSetGoal` drops the hypotheses `[Fintype Q] [DecidableEq Q]` of the
specification, a strengthening, since the specification statement is its instance.
-/

namespace OperatorKO7.Meta.BoundaryObserver.BoundaryPole

universe u

open scoped BigOperators
open ProtocolResolution BoundarySingularity PairResolution MergedPair

noncomputable section

/-! ## M6.0: readings, the record and the pole (proposed module BoundaryPole) -/

/-- A reading of the states: one finite law on outcomes for each state. -/
abbrev Reading (X : Type*) (Y : Type) [Fintype Y] := X → FiniteLaw Y

/-- The reading factors through the record of `q`. -/
def RecordDetermined {X Q : Type*} {Y : Type} [Fintype Y] (q : X → Q) (K : Reading X Y) : Prop :=
  ∀ x x', q x = q x' → K x = K x'

/-- The discrimination of a reading at a pair of states. -/
def readingDiscrimination {X : Type*} {Y : Type} [Fintype Y] (K : Reading X Y) (x x' : X) : ℝ :=
  discrimination (K x).mass (K x').mass

/-- The two states of a pair as the two values of the label: `true` names `x₀`. -/
def pairState {X : Type*} (x₀ x₁ : X) (b : Bool) : X := if b then x₀ else x₁

/-- M6.0(i): every record-determined reading has discrimination zero at every merged pair. -/
def RecordPoleGoal : Prop :=
  ∀ (X Q Y : Type) [Fintype Y] (q : X → Q) (K : Reading X Y) (x₀ x₁ : X),
    RecordDetermined q K → IsMergedPair q x₀ x₁ → readingDiscrimination K x₀ x₁ = 0

/-- M6.0(ii): the boundary of `q` is the common zero set of the record-determined readings, for
every record type `Q`. The statement carries no finiteness and no decidability hypothesis on `Q`;
the one finite type in it is the output type `Y` of a reading. -/
def BoundaryZeroSetGoal : Prop :=
  ∀ (X Q : Type) (q : X → Q) (x₀ x₁ : X),
    IsMergedPair q x₀ x₁ ↔
      (x₀ ≠ x₁ ∧ ∀ (Y : Type) [Fintype Y] (K : Reading X Y),
        RecordDetermined q K → readingDiscrimination K x₀ x₁ = 0)

/-- M6.0(iii): an adaptive protocol about the label of a merged pair, with a record-determined
reading at every retained history and action, acquires nothing at every horizon and in the
limit, whatever its cost. -/
def RecordProtocolPoleGoal : Prop :=
  ∀ (X Q A Y : Type) [Fintype A] [Fintype Y] (q : X → Q) (x₀ x₁ : X)
    (p : FiniteProtocol Bool A Y) (K : List (A × Y) → A → Reading X Y),
    IsMergedPair q x₀ x₁ → (∀ h a, RecordDetermined q (K h a)) →
    (∀ h a b, p.observation h a b = K h a (pairState x₀ x₁ b)) →
      (∀ n bank, HistoryBank n bank → terminalMI p n bank = 0) ∧ informationLimit p = 0


/-- Equality of finite laws is fixed by equality of their mass functions. -/
private theorem finiteLaw_eq_of_mass_eq {Y : Type} [Fintype Y] (P Q : FiniteLaw Y)
    (h : P.mass = Q.mass) : P = Q := by
  cases P
  cases Q
  cases h
  rfl

/-- An observer-determined reading has zero discrimination on a merged pair. -/
theorem recordPoleGoal : RecordPoleGoal := by
  intro X Q Y _ q K x₀ x₁ hdet hmerged
  apply (discrimination_eq_zero_iff (K x₀).mass (K x₁).mass
    (K x₀).nonnegative (K x₁).nonnegative).mpr
  exact congrArg FiniteLaw.mass (hdet x₀ x₁ hmerged.2)

/-- The common zero set of all record-determined readings is the merged boundary, for every record
type. The converse reads the Boolean indicator of the record of `x₀`, a record-determined reading
on the two-point output type of discrimination 2 at a split pair. -/
theorem boundaryZeroSetGoal : BoundaryZeroSetGoal := by
  intro X Q q x₀ x₁
  constructor
  · intro hmerged
    refine ⟨hmerged.1, ?_⟩
    intro Y _ K hdet
    exact recordPoleGoal X Q Y q K x₀ x₁ hdet hmerged
  · rintro ⟨hne, hzero⟩
    refine ⟨hne, ?_⟩
    by_contra hq
    classical
    have hdet : RecordDetermined q
        (fun x => deterministicRow (fun z : X => decide (q z = q x₀)) x) := by
      intro x x' heq
      apply finiteLaw_eq_of_mass_eq
      funext b
      simp [deterministicRow_mass, heq]
    have hz := hzero Bool
      (fun x => deterministicRow (fun z : X => decide (q z = q x₀)) x) hdet
    have hd := discrimination_deterministic (fun z : X => decide (q z = q x₀)) x₀ x₁
    change readingDiscrimination
        (fun x => deterministicRow (fun z : X => decide (q z = q x₀)) x) x₀ x₁ =
      (if decide (q x₀ = q x₀) = decide (q x₁ = q x₀) then (0 : ℝ) else 2) at hd
    have hsplit :
        (if decide (q x₀ = q x₀) = decide (q x₁ = q x₀) then (0 : ℝ) else 2) = 2 := by
      simp [Ne.symm hq]
    have hcontr : (0 : ℝ) = 2 := hz.symm.trans (hd.trans hsplit)
    norm_num at hcontr

/-- Each identical-row adaptive reading has zero local gain, irrespective of its cost. -/
theorem recordProtocolPoleGoal : RecordProtocolPoleGoal := by
  intro X Q A Y _ _ q x₀ x₁ p K hmerged hdet hobs
  have hread : ∀ h a b, p.observation h a b = K h a x₀ := by
    intro h a b
    rw [hobs h a b]
    cases b with
    | false => exact hdet h a x₁ x₀ hmerged.2.symm
    | true => rfl
  have hcap : LocalCapacityBound p 0 := by
    intro h a hw _ _
    have hrow : (fun zy : Bool × Y =>
        posterior p h zy.1 * (p.observation h a zy.1).mass zy.2) =
        (fun zy : Bool × Y => posterior p h zy.1 * (K h a x₀).mass zy.2) := by
      funext zy
      rw [hread h a zy.1]
    have hz : localGain p h a = 0 := by
      unfold localGain
      rw [hrow]
      exact jointMI_product_zero (posterior p h) (K h a x₀).mass
        (posterior_total p h hw) (K h a x₀).total
    simpa only [hz, zero_mul] using (le_refl (0 : ℝ))
  refine ⟨?_, informationLimit_zero_capacity p hcap⟩
  intro n bank hb
  have hupper := terminalMI_le_expectedCost p 0 n bank hb hcap
  have hlower := terminalMI_nonnegative p n bank hb
  exact le_antisymm (by simpa only [zero_mul] using hupper) hlower


/-! ## M6.2: the pole of order one (proposed module BoundaryPole) -/

/-- The least horizon at which the repeated reading acquires a target, in readings. -/
def leastRepeatCost {Y : Type} [Fintype Y] (P Q : FiniteLaw Y) (c : ℝ) : ℕ :=
  sInf {N : ℕ | c ≤ terminalMI (repeatProtocol P Q N) N (historyBank Unit Y N)}

/-- M6.2(i): the two-sided cost written as the residue interval of the pole: the discrimination
times the cost lies between `c log 2` and `4 log (1 / (2 η)) + Δ`. -/
def PoleOrderOneGoal : Prop :=
  ∀ (Y : Type) [Fintype Y] (P Q : FiniteLaw Y), 0 < discrimination P.mass Q.mass →
    (∀ (A : Type) [Fintype A] (p : FiniteProtocol Bool A Y) (c : ℝ),
      PairMenu p (discrimination P.mass Q.mass) → ∀ n bank, HistoryBank n bank →
        c ≤ terminalMI p n bank →
          c * Real.log 2 ≤ discrimination P.mass Q.mass * expectedCost p n bank) ∧
    (∀ η : ℝ, 0 < η → η ≤ 1 / 2 → ∃ N : ℕ,
      1 - Real.binEntropy η / Real.log 2 ≤
          terminalMI (repeatProtocol P Q N) N (historyBank Unit Y N) ∧
        discrimination P.mass Q.mass * N ≤
          4 * Real.log (1 / (2 * η)) + discrimination P.mass Q.mass)

/-- Positive discrimination yields the lower and upper finite-horizon residue bounds. -/
theorem poleOrderOneGoal : PoleOrderOneGoal := by
  intro Y _ P Q hΔ
  constructor
  · intro A _ p c hmenu n bank hb hc
    have hcost :=
      pairMenu_cost_lower_bound p (discrimination P.mass Q.mass) c
        hmenu hΔ n bank hb hc
    have hcost' : c * Real.log 2 ≤
        expectedCost p n bank * discrimination P.mass Q.mass :=
      (div_le_iff₀ hΔ).mp hcost
    calc
      c * Real.log 2 ≤
          expectedCost p n bank * discrimination P.mass Q.mass := hcost'
      _ = discrimination P.mass Q.mass * expectedCost p n bank := mul_comm _ _
  · intro η hη0 hη1
    obtain ⟨hinfo, _, hupper⟩ := repeat_target P Q hΔ η hη0 hη1
    refine ⟨⌈4 * Real.log (1 / (2 * η)) / discrimination P.mass Q.mass⌉₊,
      hinfo, ?_⟩
    calc
      discrimination P.mass Q.mass *
          ((⌈4 * Real.log (1 / (2 * η)) / discrimination P.mass Q.mass⌉₊ : ℕ) : ℝ) ≤
          discrimination P.mass Q.mass *
            (4 * Real.log (1 / (2 * η)) / discrimination P.mass Q.mass + 1) :=
        mul_le_mul_of_nonneg_left hupper hΔ.le
      _ = 4 * Real.log (1 / (2 * η)) + discrimination P.mass Q.mass := by
        field_simp [ne_of_gt hΔ]


/-- M6.2(ii): the least cost of the repeated reading for the target `1 - h₂(η)` bits, times the
discrimination, lies in the residue interval. -/
def PoleResidueGoal : Prop :=
  ∀ (Y : Type) [Fintype Y] (P Q : FiniteLaw Y) (η : ℝ), 0 < discrimination P.mass Q.mass →
    0 < η → η ≤ 1 / 2 →
      (1 - Real.binEntropy η / Real.log 2) * Real.log 2 ≤
          discrimination P.mass Q.mass *
            leastRepeatCost P Q (1 - Real.binEntropy η / Real.log 2) ∧
        discrimination P.mass Q.mass *
            leastRepeatCost P Q (1 - Real.binEntropy η / Real.log 2) ≤
          4 * Real.log (1 / (2 * η)) + discrimination P.mass Q.mass

/-- The nonempty attainment set bounds its least qualifying repeat horizon on both sides. -/
theorem poleResidueGoal : PoleResidueGoal := by
  intro Y _ P Q η hΔ hη0 hη1
  let target : ℝ := 1 - Real.binEntropy η / Real.log 2
  let Δ : ℝ := discrimination P.mass Q.mass
  let N : ℕ := ⌈4 * Real.log (1 / (2 * η)) / Δ⌉₊
  have hrep := repeat_target P Q hΔ η hη0 hη1
  have hN : target ≤
      terminalMI (repeatProtocol P Q N) N (historyBank Unit Y N) := hrep.1
  have hnonempty :
      ({n : ℕ | target ≤ terminalMI (repeatProtocol P Q n) n
        (historyBank Unit Y n)} : Set ℕ).Nonempty := ⟨N, hN⟩
  let m : ℕ := leastRepeatCost P Q target
  have hm : target ≤
      terminalMI (repeatProtocol P Q m) m (historyBank Unit Y m) := by
    exact Nat.sInf_mem hnonempty
  have hmenu : PairMenu (repeatProtocol P Q m) Δ :=
    repeatProtocol_pairMenu P Q m
  have hcost := pairMenu_cost_lower_bound (repeatProtocol P Q m) Δ target
    hmenu hΔ m (historyBank Unit Y m) (historyBank_complete Unit Y m) hm
  have hlower : target * Real.log 2 ≤ Δ * (m : ℝ) := by
    have hmul : target * Real.log 2 ≤
        expectedCost (repeatProtocol P Q m) m (historyBank Unit Y m) * Δ :=
      (div_le_iff₀ hΔ).mp hcost
    rw [repeat_cost P Q m] at hmul
    calc
      target * Real.log 2 ≤ (m : ℝ) * Δ := hmul
      _ = Δ * (m : ℝ) := mul_comm _ _
  have hmin : m ≤ N := by
    exact Nat.sInf_le hN
  have hmin_real : (m : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast hmin
  have hupper : Δ * (m : ℝ) ≤
      4 * Real.log (1 / (2 * η)) + Δ := by
    calc
      Δ * (m : ℝ) ≤ Δ * (N : ℝ) :=
        mul_le_mul_of_nonneg_left hmin_real hΔ.le
      _ ≤ Δ * (4 * Real.log (1 / (2 * η)) / Δ + 1) :=
        mul_le_mul_of_nonneg_left hrep.2.2 hΔ.le
      _ = 4 * Real.log (1 / (2 * η)) + Δ := by
        field_simp [ne_of_gt hΔ]
  change target * Real.log 2 ≤ Δ * (m : ℝ) ∧
    Δ * (m : ℝ) ≤ 4 * Real.log (1 / (2 * η)) + Δ
  exact ⟨hlower, hupper⟩


/-! ## M6.3: logical and diagonal clauses -/

section Logic
open OperatorKO7.Meta.DistinctionBoundary.GodelArith

/-- A formula differs from its own negation. This mathematical fact does not
depend on the rewriting kernel. -/
private theorem formula_ne_not_local (φ : Formula) : φ ≠ Formula.not φ := by
  induction φ with
  | eq t u => exact fun h => Formula.noConfusion h
  | not ψ ih => exact fun h => ih (Formula.not.inj h)
  | imp a b _ _ => exact fun h => Formula.noConfusion h
  | all n ψ _ => exact fun h => Formula.noConfusion h

/-- The Gödel sentence and its negation have the same unprovable record.
This is the exact mathematical witness used by the former KernelCases import. -/
private theorem godel_merged_pair_core :
    IsMergedPair (fun φ : Formula => Provable φ) arithGodelSentence
      (Formula.not arithGodelSentence) :=
  ⟨formula_ne_not_local arithGodelSentence,
    propext ⟨fun h => absurd h godel_first_incompleteness_Q_unconditional.1,
      fun h => absurd h godel_first_incompleteness_Q_unconditional.2⟩⟩

/-- M6.3(i): every reading determined by provability has discrimination zero at the Godel sentence
and its negation, and its repetition acquires nothing about the pair at every horizon. -/
def GodelPoleGoal : Prop :=
  ∀ (Y : Type) [Fintype Y] (K : Reading Formula Y),
    RecordDetermined (fun φ : Formula => Provable φ) K →
      readingDiscrimination K arithGodelSentence (Formula.not arithGodelSentence) = 0 ∧
      ∀ N : ℕ, terminalMI (repeatProtocol (K arithGodelSentence)
        (K (Formula.not arithGodelSentence)) N) N (historyBank Unit Y N) = 0

/-- The unprovable merged pair yields zero discrimination and zero repeated information. -/
theorem godelPoleGoal : GodelPoleGoal := by
  intro Y _ K hdet
  have hmerge := godel_merged_pair_core
  have hzero : readingDiscrimination K arithGodelSentence
      (Formula.not arithGodelSentence) = 0 :=
    recordPoleGoal Formula Prop Y (fun φ : Formula => Provable φ) K
      arithGodelSentence (Formula.not arithGodelSentence) hdet hmerge
  refine ⟨hzero, ?_⟩
  intro N
  have hΔ : discrimination (K arithGodelSentence).mass
      (K (Formula.not arithGodelSentence)).mass = 0 := hzero
  have hmenu : PairMenu
      (repeatProtocol (K arithGodelSentence) (K (Formula.not arithGodelSentence)) N) 0 := by
    simpa only [hΔ] using
      (repeatProtocol_pairMenu (K arithGodelSentence)
        (K (Formula.not arithGodelSentence)) N)
  exact pairMenu_zero_discrimination
    (repeatProtocol (K arithGodelSentence) (K (Formula.not arithGodelSentence)) N)
    hmenu N (historyBank Unit Y N) (historyBank_complete Unit Y N)


/-- M6.3(ii): a side symbol with two values on the pair resolves it with one reading. -/
def GodelSideSymbolGoal : Prop :=
  ∀ (S : Type) [Fintype S] [DecidableEq S] (s : Formula → S),
    s arithGodelSentence ≠ s (Formula.not arithGodelSentence) →
      1 ≤ terminalMI (repeatProtocol (deterministicRow s arithGodelSentence)
        (deterministicRow s (Formula.not arithGodelSentence)) 1) 1 (historyBank Unit S 1)

/-- Distinct deterministic side-symbol rows acquire one bit in one reading. -/
theorem godelSideSymbolGoal : GodelSideSymbolGoal := by
  intro S _ _ s hs
  exact (split_pair_one_reading s arithGodelSentence
    (Formula.not arithGodelSentence) hs).2.1

end Logic


/-- M6.3(iii): the diagonal tower is a walk along the boundary. At every stage the transformed
diagonal is represented by no code of the stage, the added code of the next stage reads the
old diagonal, and every old evaluation is kept. -/
def DiagonalWalkGoal : Prop :=
  ∀ (C V : Type) (E : C → C → V) (j : V → V) (v0 : V), (∀ v, j v ≠ v) → ∀ n : ℕ,
    (¬ ∃ c, ∀ x, UniversalObservation.Completion.stageEval E j v0 n c x =
        j (UniversalObservation.Completion.stageEval E j v0 n x x)) ∧
    (∀ x : UniversalObservation.Completion.Stage C n,
      UniversalObservation.Completion.stageEval E j v0 (n + 1) none (some x) =
        j (UniversalObservation.Completion.stageEval E j v0 n x x)) ∧
    (∀ c x : UniversalObservation.Completion.Stage C n,
      UniversalObservation.Completion.stageEval E j v0 (n + 1) (some c) (some x) =
        UniversalObservation.Completion.stageEval E j v0 n c x)

/-- Each finite diagonal is absent, its old version is represented, and old rows persist. -/
theorem diagonalWalkGoal : DiagonalWalkGoal := by
  intro C V E j v0 hnofix n
  refine ⟨UniversalObservation.Completion.every_stage_diagonal_absent
      E j v0 hnofix n, ?_, ?_⟩
  · intro x
    exact UniversalObservation.Completion.stage_old_diagonal_represented E j v0 n x
  · intro c x
    exact UniversalObservation.Completion.stage_table_preserved E j v0 n 1 c x


/-- M6.3(iv): the union of the tower still misses its transformed diagonal. -/
def DiagonalUnionGoal : Prop :=
  ∀ (C V : Type) (E : C → C → V) (j : V → V) (v0 : V), (∀ v, j v ≠ v) →
    ¬ ∃ c, ∀ x, UniversalObservation.Completion.limitEval E j v0 c x =
      j (UniversalObservation.Completion.limitEval E j v0 x x)

/-- The union diagonal remains absent by the exact limit-evaluator theorem. -/
theorem diagonalUnionGoal : DiagonalUnionGoal := by
  intro C V E j v0 hnofix
  exact UniversalObservation.Completion.limit_diagonal_absent E j v0 hnofix


/-! ## M6.4: recursion -/

/-- M6.4(i): for every content type in every universe, a content-determined
reading has zero discrimination at any two passes of the same content. The
repeated-reading protocol acquires zero information at every finite horizon. -/
def OrientationPoleGoal : Prop :=
  ∀ (T : Type u) (Y : Type) [Fintype Y] (K : Reading (T × ℕ) Y),
    RecordDetermined (RecursorDecidability.content (T := T)) K →
      ∀ (R : T) (j k : ℕ),
        readingDiscrimination K (R, j) (R, k) = 0 ∧
        ∀ N : ℕ, terminalMI (repeatProtocol (K (R, j)) (K (R, k)) N) N
          (historyBank Unit Y N) = 0

theorem orientationPoleGoal : OrientationPoleGoal := by
  intro T Y _ K hdet R j k
  have hrow : K (R, j) = K (R, k) := hdet (R, j) (R, k) rfl
  have hdisc : readingDiscrimination K (R, j) (R, k) = 0 := by
    apply (discrimination_eq_zero_iff (K (R, j)).mass (K (R, k)).mass
      (K (R, j)).nonnegative (K (R, k)).nonnegative).mpr
    exact congrArg FiniteLaw.mass hrow
  refine ⟨hdisc, ?_⟩
  intro N
  have hΔ : discrimination (K (R, j)).mass (K (R, k)).mass = 0 := hdisc
  have hmenu : PairMenu (repeatProtocol (K (R, j)) (K (R, k)) N) 0 := by
    simpa only [hΔ] using (repeatProtocol_pairMenu (K (R, j)) (K (R, k)) N)
  exact pairMenu_zero_discrimination (repeatProtocol (K (R, j)) (K (R, k)) N)
    hmenu N (historyBank Unit Y N) (historyBank_complete Unit Y N)

/-- The deterministic Bool-valued row of a test on an arbitrary carrier.
The finite outcome type remains in Type, but the state type is universe-polymorphic. -/
noncomputable def booleanTestRow {X : Type u} (test : X → Bool) (x : X) :
    FiniteLaw Bool :=
  deterministicRow (id : Bool → Bool) (test x)

/-- M6.4(ii): a test of the counted place coordinate separates distinct
passes of the same content by a deterministic, one-reading protocol. -/
def CounterSideSymbolGoal : Prop :=
  ∀ (T : Type u) (R : T) (j k : ℕ), j ≠ k →
    1 ≤ terminalMI (repeatProtocol
      (booleanTestRow (fun p : T × ℕ => decide (p.2 = j)) (R, j))
      (booleanTestRow (fun p : T × ℕ => decide (p.2 = j)) (R, k)) 1) 1
      (historyBank Unit Bool 1)

theorem counterSideSymbolGoal : CounterSideSymbolGoal := by
  intro T R j k hjk
  have hk : k ≠ j := Ne.symm hjk
  have hsplit : decide (j = j) ≠ decide (k = j) := by
    simp [hk]
  exact (split_pair_one_reading (id : Bool → Bool)
    (decide (j = j)) (decide (k = j)) hsplit).2.1

/-- M6.4(iii): the complete recursion clause for arbitrary content carriers.
The inhabitance requirement is confined to claims that exhibit two distinct
counter values for a fixed content. Neither protocol result has that premise. -/
def RecursionClauseGoal : Prop :=
  OrientationPoleGoal.{u} ∧ CounterSideSymbolGoal.{u} ∧
    (∀ (T : Type u) [Nonempty T] (M : T × ℕ → ℕ),
      (∀ x y, RecursorDecidability.Pass x y → M y < M x) →
        ¬ Determines (RecursorDecidability.content (T := T)) M) ∧
    ∀ n : ℕ, RecursorDecidability.leftEntropy (fun _ : Fin (n + 1) => ()) =
      Real.log (n + 1)

theorem recursionClauseGoal : RecursionClauseGoal := by
  refine ⟨orientationPoleGoal, counterSideSymbolGoal, ?_, ?_⟩
  · intro T _ M hM
    exact RecursorDecidability.orienting_measure_not_content_determined M hM
  · intro n
    exact RecursorDecidability.content_leaves_log n


/-! ## M6.13: two-point information -/

/-- M6.13: every decoder of a protocol of readings of discrimination at most δ about the fair label
errs with mass e satisfying `h₂(e) ≥ log 2 - δ E[C]`: the two-point lower bound. -/
def TwoPointGoal : Prop :=
  ∀ (A Y : Type) [Fintype A] [Fintype Y] (p : FiniteProtocol Bool A Y) (δ : ℝ)
    (g : List (A × Y) → Bool) (n : ℕ),
    PairMenu p δ → 0 ≤ δ → (∀ b, p.prior.mass b = 1 / 2) →
      Real.log 2 - δ * expectedCost p n (historyBank A Y n) ≤
        Real.binEntropy (∑ h ∈ historySet (A × Y) n, stoppedMass p n (!g h) h)


theorem twoPointGoal : TwoPointGoal := by
  intro A Y _ _ p δ g n hmenu hδ hprior
  let err : ℝ := ∑ h ∈ historySet (A × Y) n, stoppedMass p n (!g h) h
  let uncertainty : ℝ := ∑ h ∈ historySet (A × Y) n,
    massUncertainty (fun b => stoppedMass p n b h)
  let info : ℝ := terminalMI p n (historyBank A Y n)
  let cost : ℝ := expectedCost p n (historyBank A Y n)
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hbank : HistoryBank n (historyBank A Y n) := historyBank_complete A Y n
  have htot : (∑ h ∈ historySet (A × Y) n,
      (stoppedMass p n true h + stoppedMass p n false h)) = 1 := by
    rw [Finset.sum_add_distrib, historySet_stoppedMass_target_marginal,
      historySet_stoppedMass_target_marginal, hprior true, hprior false]
    norm_num
  have hfano : uncertainty ≤ Real.binEntropy err / Real.log 2 :=
    ResolutionAttainment.sum_massUncertainty_le_binEntropy
      (historySet (A × Y) n) (fun h b => stoppedMass p n b h)
      (fun h b => stoppedMass_nonnegative p n b h) htot g
  have hfair : p.prior.mass = ResolutionAttainment.fairLaw.mass := by
    funext b
    exact hprior b
  have hent : entropy p.prior.mass = 1 := by
    rw [hfair]
    exact ResolutionAttainment.fairLaw_entropy
  have hinfo : info = 1 - uncertainty := by
    have h := terminalMI_eq_entropy_sub p n (historyBank A Y n) hbank
    rw [hent] at h
    exact h
  have hcap : info ≤ δ / Real.log 2 * cost :=
    (pairMenu_information_bound p δ hmenu hδ n (historyBank A Y n) hbank).2
  have hfa := mul_le_mul_of_nonneg_right hfano hlog.le
  have hca := mul_le_mul_of_nonneg_right hcap hlog.le
  have hcancelF : (Real.binEntropy err / Real.log 2) * Real.log 2 =
      Real.binEntropy err := by
    field_simp [ne_of_gt hlog]
  have hcancelC : (δ / Real.log 2 * cost) * Real.log 2 = δ * cost := by
    field_simp [ne_of_gt hlog]
  rw [hcancelF] at hfa
  rw [hcancelC] at hca
  have hunc : uncertainty = 1 - info := by
    linarith [hinfo]
  rw [hunc] at hfa
  change Real.log 2 - δ * cost ≤ Real.binEntropy err
  linarith [hfa, hca]

end
end OperatorKO7.Meta.BoundaryObserver.BoundaryPole
