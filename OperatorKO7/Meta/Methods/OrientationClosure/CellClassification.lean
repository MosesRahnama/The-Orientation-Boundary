import OperatorKO7.Meta.Methods.OrientationClosure.CouplingTheorem
import OperatorKO7.Meta.Methods.OrientationClosure.FreePolynomialTermination
import OperatorKO7.Meta.Methods.OrientationClosure.AblationComparisons
import OperatorKO7.Meta.Methods.OrientationClosure.AttainedPairs
import Mathlib.Tactic

/-!
# Wrapper-cost and counter-gain cell classification

The classification uses additive margins instead of truncated subtraction. For a
fixed base and counter term, wrapper margin is either bounded or unbounded over
the payload argument, and counter gain is either bounded or unbounded. The cell
with unbounded wrapper margin and bounded counter gain cannot orient the
step-duplicating rule. Each of the other three cells has an orienter and a
non-orienter on the free schema.
-/

set_option autoImplicit false

namespace OperatorKO7.Methods.OrientationClosure.CellClassification

open OperatorKO7.Methods.OrientationClosure.SchemaCore
open OperatorKO7.Methods.OrientationClosure.InterpretationLaws
open OperatorKO7.Methods.OrientationClosure.FreePolynomialTermination
open OperatorKO7.Methods.OrientationClosure.AblationComparisons
open OperatorKO7.Methods.OrientationClosure.AttainedPairs
open OperatorKO7.Methods.OrientationClosure.PolynomialRegion

universe u

/-- Wrapper margin is unbounded over the payload at fixed base and counter. -/
def WrapUnboundedAt {S : OperatorKO7.StepDuplicating.StepDuplicatingSchema}
    (M : S.T → Nat) (b n : S.T) : Prop :=
  ∀ K : Nat, ∃ s : S.T,
    M (S.recur b s n) + K < M (S.wrap s (S.recur b s n))

/-- Wrapper margin has a uniform payload-independent upper bound. -/
def WrapBoundedAt {S : OperatorKO7.StepDuplicating.StepDuplicatingSchema}
    (M : S.T → Nat) (b n : S.T) : Prop :=
  ∃ K : Nat, ∀ s : S.T,
    M (S.wrap s (S.recur b s n)) ≤ M (S.recur b s n) + K

/-- Counter gain is unbounded over the payload at fixed base and counter. -/
def GainUnboundedAt {S : OperatorKO7.StepDuplicating.StepDuplicatingSchema}
    (M : S.T → Nat) (b n : S.T) : Prop :=
  ∀ K : Nat, ∃ s : S.T,
    M (S.recur b s n) + K < M (S.recur b s (S.succ n))

/-- Counter gain has a uniform payload-independent upper bound. -/
def GainBoundedAt {S : OperatorKO7.StepDuplicating.StepDuplicatingSchema}
    (M : S.T → Nat) (b n : S.T) : Prop :=
  ∃ K : Nat, ∀ s : S.T,
    M (S.recur b s (S.succ n)) ≤ M (S.recur b s n) + K

/-- Every wrapper-margin function lies on one side of the bounded/unbounded split. -/
theorem wrap_growth_dichotomy
    {S : OperatorKO7.StepDuplicating.StepDuplicatingSchema}
    (M : S.T → Nat) (b n : S.T) :
    WrapUnboundedAt M b n ∨ WrapBoundedAt M b n := by
  classical
  by_cases h : WrapUnboundedAt M b n
  · exact Or.inl h
  · right
    simp only [WrapUnboundedAt] at h
    push_neg at h
    obtain ⟨K, hK⟩ := h
    refine ⟨K, ?_⟩
    intro s
    have hs := hK s
    omega

/-- Every counter-gain function lies on one side of the bounded/unbounded split. -/
theorem gain_growth_dichotomy
    {S : OperatorKO7.StepDuplicating.StepDuplicatingSchema}
    (M : S.T → Nat) (b n : S.T) :
    GainUnboundedAt M b n ∨ GainBoundedAt M b n := by
  classical
  by_cases h : GainUnboundedAt M b n
  · exact Or.inl h
  · right
    simp only [GainUnboundedAt] at h
    push_neg at h
    obtain ⟨K, hK⟩ := h
    refine ⟨K, ?_⟩
    intro s
    have hs := hK s
    omega

/-- The four cells cover every natural-valued interpretation at each fixed
base/counter pair. -/
theorem four_cell_coverage
    {S : OperatorKO7.StepDuplicating.StepDuplicatingSchema}
    (M : S.T → Nat) (b n : S.T) :
    (WrapUnboundedAt M b n ∧ GainBoundedAt M b n) ∨
    (WrapUnboundedAt M b n ∧ GainUnboundedAt M b n) ∨
    (WrapBoundedAt M b n ∧ GainBoundedAt M b n) ∨
    (WrapBoundedAt M b n ∧ GainUnboundedAt M b n) := by
  rcases wrap_growth_dichotomy M b n with hw | hw <;>
    rcases gain_growth_dichotomy M b n with hg | hg
  · exact Or.inr (Or.inl ⟨hw, hg⟩)
  · exact Or.inl ⟨hw, hg⟩
  · exact Or.inr (Or.inr (Or.inr ⟨hw, hg⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨hw, hg⟩))

/-- The unbounded-wrapper/bounded-gain cell excludes orientation at that fixed
base/counter pair. -/
theorem barrier_cell_excludes_orientation
    {S : OperatorKO7.StepDuplicating.StepDuplicatingSchema}
    (M : S.T → Nat) (b n : S.T)
    (hw : WrapUnboundedAt M b n) (hg : GainBoundedAt M b n) :
    ¬ ∀ s : S.T,
      M (S.wrap s (S.recur b s n)) < M (S.recur b s (S.succ n)) := by
  rintro horient
  obtain ⟨K, hK⟩ := hg
  obtain ⟨s, hs⟩ := hw K
  have hgain := hK s
  have ho := horient s
  omega

/-- Closed-term evaluation for a numeric free-syntax interpretation. -/
def closedEval (I : Interpretation Nat) : FreeTerm Empty → Nat :=
  I.eval Empty.elim

/-- Every interpretation with zero at `0` and unit successor maps the closed
successor tower `counterTerm k` to `k`. -/
theorem closedEval_counterTerm_of_unitSucc
    (I : Interpretation Nat)
    (hzero : I.zero = 0)
    (hsucc : ∀ x, I.succ x = x + 1) (k : Nat) :
    closedEval I (counterTerm k) = k := by
  induction k with
  | zero => simp [closedEval, counterTerm, hzero]
  | succ k ih =>
      change I.eval Empty.elim (counterTerm k) = k at ih
      simp [closedEval, counterTerm, hsucc, ih]

/-- Constant-zero non-orienter. -/
def zeroMeasure {ν : Type u} : FreeTerm ν → Nat := fun _ => 0

/-- The counter projection is in the bounded-wrapper/bounded-gain cell. -/
theorem counterRank_bounded_bounded :
    WrapBoundedAt (S := freeSchema Empty) counterRank .zero .zero ∧
      GainBoundedAt (S := freeSchema Empty) counterRank .zero .zero := by
  constructor
  · refine ⟨0, ?_⟩
    intro s
    simp [counterRank, freeSchema]
  · refine ⟨1, ?_⟩
    intro s
    simp [counterRank, freeSchema]

/-- The counter projection orients every successor instance. -/
theorem counterRank_is_orienter :
    ∀ b s n : FreeTerm Empty,
      counterRank (.wrap s (.recur b s n)) < counterRank (.recur b s (.succ n)) :=
  counterRank_orients_original_successor

/-- The zero measure occupies the same bounded/bounded cell and fails orientation. -/
theorem zeroMeasure_bounded_bounded_nonorienter :
    WrapBoundedAt (S := freeSchema Empty) (zeroMeasure (ν := Empty)) .zero .zero ∧
      GainBoundedAt (S := freeSchema Empty) (zeroMeasure (ν := Empty)) .zero .zero ∧
      ¬ (∀ b s n : FreeTerm Empty,
        zeroMeasure (.wrap s (.recur b s n)) < zeroMeasure (.recur b s (.succ n))) := by
  refine ⟨⟨0, ?_⟩, ⟨0, ?_⟩, ?_⟩
  · intro s
    simp [zeroMeasure]
  · intro s
    simp [zeroMeasure]
  · intro h
    have := h (.zero) (.zero) (.zero)
    simp [zeroMeasure] at this

/-- Coupled polynomial measure used by the unbounded/unbounded orienter. -/
def coupledClosedMeasure : FreeTerm Empty → Nat :=
  closedEval (coupledInterpretation 1 2)

@[simp] theorem coupledClosedMeasure_counterTerm (k : Nat) :
    coupledClosedMeasure (counterTerm k) = k := by
  exact closedEval_counterTerm_of_unitSucc (coupledInterpretation 1 2) rfl
    (fun x => by simp [coupledInterpretation, successorEval]) k

/-- The coupled polynomial witness lies in the unbounded/unbounded cell. -/
theorem coupledClosedMeasure_unbounded_unbounded :
    WrapUnboundedAt (S := freeSchema Empty) coupledClosedMeasure .zero .zero ∧
      GainUnboundedAt (S := freeSchema Empty) coupledClosedMeasure .zero .zero := by
  constructor
  · intro K
    refine ⟨counterTerm (K + 1), ?_⟩
    have hs :
        (coupledInterpretation 1 2).eval Empty.elim (counterTerm (K + 1)) = K + 1 := by
      simpa [coupledClosedMeasure, closedEval] using
        coupledClosedMeasure_counterTerm (K + 1)
    change
      (coupledInterpretation 1 2).recur
          (coupledInterpretation 1 2).zero
          ((coupledInterpretation 1 2).eval Empty.elim (counterTerm (K + 1)))
          (coupledInterpretation 1 2).zero + K <
        (coupledInterpretation 1 2).wrap
          ((coupledInterpretation 1 2).eval Empty.elim (counterTerm (K + 1)))
          ((coupledInterpretation 1 2).recur
            (coupledInterpretation 1 2).zero
            ((coupledInterpretation 1 2).eval Empty.elim (counterTerm (K + 1)))
            (coupledInterpretation 1 2).zero)
    rw [hs]
    simp only [coupledInterpretation, recursorEval, wrapperEval]
    omega
  · intro K
    refine ⟨counterTerm (K + 1), ?_⟩
    have hs :
        (coupledInterpretation 1 2).eval Empty.elim (counterTerm (K + 1)) = K + 1 := by
      simpa [coupledClosedMeasure, closedEval] using
        coupledClosedMeasure_counterTerm (K + 1)
    change
      (coupledInterpretation 1 2).recur
          (coupledInterpretation 1 2).zero
          ((coupledInterpretation 1 2).eval Empty.elim (counterTerm (K + 1)))
          (coupledInterpretation 1 2).zero + K <
        (coupledInterpretation 1 2).recur
          (coupledInterpretation 1 2).zero
          ((coupledInterpretation 1 2).eval Empty.elim (counterTerm (K + 1)))
          ((coupledInterpretation 1 2).succ (coupledInterpretation 1 2).zero)
    rw [hs]
    simp only [coupledInterpretation, recursorEval, successorEval]
    omega

/-- The coupled polynomial witness orients every successor instance. -/
theorem coupledClosedMeasure_is_orienter :
    ∀ b s n : FreeTerm Empty,
      coupledClosedMeasure (.wrap s (.recur b s n)) <
        coupledClosedMeasure (.recur b s (.succ n)) := by
  intro b s n
  exact (coupled_rootRuleOrients (α := 1) (β := 2) (by omega) (by omega)).recurSucc
    (closedEval (coupledInterpretation 1 2) b)
    (closedEval (coupledInterpretation 1 2) s)
    (closedEval (coupledInterpretation 1 2) n)

/-- Doubled-recursive-result wrapper with the same coupled recursor. -/
def doubledWrapperInterpretation : Interpretation Nat where
  zero := 0
  succ := fun x => x + 1
  wrap := fun s y => 2 * y + s + 1
  recur := recursorEval 1 2

/-- Closed measure for the doubled-wrapper non-orienter. -/
def doubledWrapperMeasure : FreeTerm Empty → Nat :=
  closedEval doubledWrapperInterpretation

@[simp] theorem doubledWrapperMeasure_counterTerm (k : Nat) :
    doubledWrapperMeasure (counterTerm k) = k := by
  exact closedEval_counterTerm_of_unitSucc doubledWrapperInterpretation rfl (fun _ => rfl) k

/-- The doubled-wrapper witness is unbounded in both margins but fails the
successor orientation already at zero payload and zero counter. -/
theorem doubledWrapper_unbounded_unbounded_nonorienter :
    WrapUnboundedAt (S := freeSchema Empty) doubledWrapperMeasure .zero .zero ∧
      GainUnboundedAt (S := freeSchema Empty) doubledWrapperMeasure .zero .zero ∧
      ¬ (∀ b s n : FreeTerm Empty,
        doubledWrapperMeasure (.wrap s (.recur b s n)) <
          doubledWrapperMeasure (.recur b s (.succ n))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro K
    refine ⟨counterTerm (K + 1), ?_⟩
    have hs :
        doubledWrapperInterpretation.eval Empty.elim (counterTerm (K + 1)) = K + 1 := by
      simpa [doubledWrapperMeasure, closedEval] using
        doubledWrapperMeasure_counterTerm (K + 1)
    change
      doubledWrapperInterpretation.recur doubledWrapperInterpretation.zero
          (doubledWrapperInterpretation.eval Empty.elim (counterTerm (K + 1)))
          doubledWrapperInterpretation.zero + K <
        doubledWrapperInterpretation.wrap
          (doubledWrapperInterpretation.eval Empty.elim (counterTerm (K + 1)))
          (doubledWrapperInterpretation.recur doubledWrapperInterpretation.zero
            (doubledWrapperInterpretation.eval Empty.elim (counterTerm (K + 1)))
            doubledWrapperInterpretation.zero)
    rw [hs]
    simp only [doubledWrapperInterpretation, recursorEval]
    omega
  · intro K
    refine ⟨counterTerm (K + 1), ?_⟩
    have hs :
        doubledWrapperInterpretation.eval Empty.elim (counterTerm (K + 1)) = K + 1 := by
      simpa [doubledWrapperMeasure, closedEval] using
        doubledWrapperMeasure_counterTerm (K + 1)
    change
      doubledWrapperInterpretation.recur doubledWrapperInterpretation.zero
          (doubledWrapperInterpretation.eval Empty.elim (counterTerm (K + 1)))
          doubledWrapperInterpretation.zero + K <
        doubledWrapperInterpretation.recur doubledWrapperInterpretation.zero
          (doubledWrapperInterpretation.eval Empty.elim (counterTerm (K + 1)))
          (doubledWrapperInterpretation.succ doubledWrapperInterpretation.zero)
    rw [hs]
    simp only [doubledWrapperInterpretation, recursorEval]
    omega
  · intro h
    have hz := h (.zero) (.zero) (.zero)
    norm_num [doubledWrapperMeasure, doubledWrapperInterpretation, closedEval,
      Interpretation.eval, recursorEval] at hz

/-- Wrapper that retains only the recursive-result coordinate at unit cost,
paired with the coupled recursor. -/
def boundedWrapperInterpretation : Interpretation Nat where
  zero := 0
  succ := fun x => x + 1
  wrap := fun _ y => y + 1
  recur := recursorEval 1 2

/-- Closed measure for the bounded-wrapper coupled orienter. -/
def boundedWrapperMeasure : FreeTerm Empty → Nat :=
  closedEval boundedWrapperInterpretation

@[simp] theorem boundedWrapperMeasure_counterTerm (k : Nat) :
    boundedWrapperMeasure (counterTerm k) = k := by
  exact closedEval_counterTerm_of_unitSucc boundedWrapperInterpretation rfl (fun _ => rfl) k

/-- The bounded-wrapper coupled measure has bounded wrapper margin and unbounded gain. -/
theorem boundedWrapperMeasure_bounded_unbounded :
    WrapBoundedAt (S := freeSchema Empty) boundedWrapperMeasure .zero .zero ∧
      GainUnboundedAt (S := freeSchema Empty) boundedWrapperMeasure .zero .zero := by
  constructor
  · refine ⟨1, ?_⟩
    intro s
    simp [boundedWrapperMeasure, boundedWrapperInterpretation, closedEval,
      Interpretation.eval, recursorEval, freeSchema]
  · intro K
    refine ⟨counterTerm (K + 1), ?_⟩
    have hs :
        boundedWrapperInterpretation.eval Empty.elim (counterTerm (K + 1)) = K + 1 := by
      simpa [boundedWrapperMeasure, closedEval] using
        boundedWrapperMeasure_counterTerm (K + 1)
    change
      boundedWrapperInterpretation.recur boundedWrapperInterpretation.zero
          (boundedWrapperInterpretation.eval Empty.elim (counterTerm (K + 1)))
          boundedWrapperInterpretation.zero + K <
        boundedWrapperInterpretation.recur boundedWrapperInterpretation.zero
          (boundedWrapperInterpretation.eval Empty.elim (counterTerm (K + 1)))
          (boundedWrapperInterpretation.succ boundedWrapperInterpretation.zero)
    rw [hs]
    simp only [boundedWrapperInterpretation, recursorEval]
    omega

/-- The bounded-wrapper coupled measure orients every successor instance. -/
theorem boundedWrapperMeasure_is_orienter :
    ∀ b s n : FreeTerm Empty,
      boundedWrapperMeasure (.wrap s (.recur b s n)) <
        boundedWrapperMeasure (.recur b s (.succ n)) := by
  intro b s n
  let bv := closedEval boundedWrapperInterpretation b
  let sv := closedEval boundedWrapperInterpretation s
  let nv := closedEval boundedWrapperInterpretation n
  have hfull :=
    orientsSuccessor_of_region (α := 1) (β := 2) (by omega) (by omega) bv sv nv
  change recursorEval 1 2 bv sv nv + 1 <
    recursorEval 1 2 bv sv (successorEval nv)
  simp only [wrapperEval] at hfull
  omega

/-- Recursor whose gain alternates between zero and a payload-dependent jump. -/
def alternatingGainInterpretation : Interpretation Nat where
  zero := 0
  succ := fun x => x + 1
  wrap := fun _ y => y + 1
  recur := fun b s n => b + (n / 2) * s

/-- Closed measure for the alternating-gain control. -/
def alternatingGainMeasure : FreeTerm Empty → Nat :=
  closedEval alternatingGainInterpretation

@[simp] theorem alternatingGainMeasure_counterTerm (k : Nat) :
    alternatingGainMeasure (counterTerm k) = k := by
  exact closedEval_counterTerm_of_unitSucc alternatingGainInterpretation rfl (fun _ => rfl) k

/-- At counter value one the alternating witness is in the bounded-wrapper,
unbounded-gain cell, while its zero-counter step fails orientation. -/
theorem alternatingGain_bounded_unbounded_nonorienter :
    WrapBoundedAt (S := freeSchema Empty) alternatingGainMeasure .zero (.succ .zero) ∧
      GainUnboundedAt (S := freeSchema Empty) alternatingGainMeasure .zero (.succ .zero) ∧
      ¬ (∀ b s n : FreeTerm Empty,
        alternatingGainMeasure (.wrap s (.recur b s n)) <
          alternatingGainMeasure (.recur b s (.succ n))) := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨1, ?_⟩
    intro s
    simp [alternatingGainMeasure, alternatingGainInterpretation, closedEval,
      Interpretation.eval, freeSchema]
  · intro K
    refine ⟨counterTerm (K + 2), ?_⟩
    have hs :
        alternatingGainInterpretation.eval Empty.elim (counterTerm (K + 2)) = K + 2 := by
      simpa [alternatingGainMeasure, closedEval] using
        alternatingGainMeasure_counterTerm (K + 2)
    change
      alternatingGainInterpretation.recur alternatingGainInterpretation.zero
          (alternatingGainInterpretation.eval Empty.elim (counterTerm (K + 2)))
          (alternatingGainInterpretation.succ alternatingGainInterpretation.zero) + K <
        alternatingGainInterpretation.recur alternatingGainInterpretation.zero
          (alternatingGainInterpretation.eval Empty.elim (counterTerm (K + 2)))
          (alternatingGainInterpretation.succ
            (alternatingGainInterpretation.succ alternatingGainInterpretation.zero))
    rw [hs]
    simp only [alternatingGainInterpretation, Nat.reduceAdd, Nat.reduceDiv, zero_mul,
      one_mul, zero_add]
    omega
  · intro h
    have hz := h (.zero) (.zero) (.zero)
    norm_num [alternatingGainMeasure, alternatingGainInterpretation, closedEval,
      Interpretation.eval] at hz

/-- Six non-barrier witnesses, grouped by growth cell and orientation verdict. -/
structure NonBarrierCellWitnessCatalog : Prop where
  boundedBoundedOrienter :
    WrapBoundedAt (S := freeSchema Empty) counterRank .zero .zero ∧
      GainBoundedAt (S := freeSchema Empty) counterRank .zero .zero ∧
      (∀ b s n : FreeTerm Empty,
        counterRank (.wrap s (.recur b s n)) < counterRank (.recur b s (.succ n)))
  boundedBoundedNonorienter :
    WrapBoundedAt (S := freeSchema Empty) (zeroMeasure (ν := Empty)) .zero .zero ∧
      GainBoundedAt (S := freeSchema Empty) (zeroMeasure (ν := Empty)) .zero .zero ∧
      ¬ (∀ b s n : FreeTerm Empty,
        zeroMeasure (.wrap s (.recur b s n)) < zeroMeasure (.recur b s (.succ n)))
  unboundedUnboundedOrienter :
    WrapUnboundedAt (S := freeSchema Empty) coupledClosedMeasure .zero .zero ∧
      GainUnboundedAt (S := freeSchema Empty) coupledClosedMeasure .zero .zero ∧
      (∀ b s n : FreeTerm Empty,
        coupledClosedMeasure (.wrap s (.recur b s n)) <
          coupledClosedMeasure (.recur b s (.succ n)))
  unboundedUnboundedNonorienter :
    WrapUnboundedAt (S := freeSchema Empty) doubledWrapperMeasure .zero .zero ∧
      GainUnboundedAt (S := freeSchema Empty) doubledWrapperMeasure .zero .zero ∧
      ¬ (∀ b s n : FreeTerm Empty,
        doubledWrapperMeasure (.wrap s (.recur b s n)) <
          doubledWrapperMeasure (.recur b s (.succ n)))
  boundedUnboundedOrienter :
    WrapBoundedAt (S := freeSchema Empty) boundedWrapperMeasure .zero .zero ∧
      GainUnboundedAt (S := freeSchema Empty) boundedWrapperMeasure .zero .zero ∧
      (∀ b s n : FreeTerm Empty,
        boundedWrapperMeasure (.wrap s (.recur b s n)) <
          boundedWrapperMeasure (.recur b s (.succ n)))
  boundedUnboundedNonorienter :
    WrapBoundedAt (S := freeSchema Empty) alternatingGainMeasure .zero (.succ .zero) ∧
      GainUnboundedAt (S := freeSchema Empty) alternatingGainMeasure .zero (.succ .zero) ∧
      ¬ (∀ b s n : FreeTerm Empty,
        alternatingGainMeasure (.wrap s (.recur b s n)) <
          alternatingGainMeasure (.recur b s (.succ n)))

/-- The six witnesses show that all three non-barrier cells contain an orienter
and a non-orienter. -/
theorem nonbarrier_cells_have_both_verdicts : NonBarrierCellWitnessCatalog where
  boundedBoundedOrienter :=
    ⟨counterRank_bounded_bounded.1, counterRank_bounded_bounded.2,
      counterRank_is_orienter⟩
  boundedBoundedNonorienter := zeroMeasure_bounded_bounded_nonorienter
  unboundedUnboundedOrienter :=
    ⟨coupledClosedMeasure_unbounded_unbounded.1,
      coupledClosedMeasure_unbounded_unbounded.2,
      coupledClosedMeasure_is_orienter⟩
  unboundedUnboundedNonorienter := doubledWrapper_unbounded_unbounded_nonorienter
  boundedUnboundedOrienter :=
    ⟨boundedWrapperMeasure_bounded_unbounded.1,
      boundedWrapperMeasure_bounded_unbounded.2,
      boundedWrapperMeasure_is_orienter⟩
  boundedUnboundedNonorienter := alternatingGain_bounded_unbounded_nonorienter

end OperatorKO7.Methods.OrientationClosure.CellClassification
