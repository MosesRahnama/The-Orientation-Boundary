import OperatorKO7.Meta.Methods.OrientationClosure.CellClassification
import OperatorKO7.Meta.BarrierPumpDischarge_Schema
import OperatorKO7.Meta.MatrixBarrierFunctional_Schema
import OperatorKO7.Meta.MatrixBarrierLexD_Schema
import OperatorKO7.Meta.QuadraticCrossTermBarrier_Schema
import OperatorKO7.Meta.MultilinearBarrier_Schema
import OperatorKO7.Meta.PolynomialBarrierGeneral_Schema
import OperatorKO7.Meta.MaxBarrier_Schema
import OperatorKO7.Meta.QuadraticBarrier_Schema
import Mathlib.Tactic

/-!
# Growth cells of the direct barrier families

`CellClassification.lean` splits every natural-valued measure, at a fixed base and
counter, by two growth questions over the payload argument: whether the wrapper margin
is bounded and whether the counter gain is bounded. The cell with unbounded wrapper
margin and bounded counter gain excludes orientation.

This module places each direct family of the Orientation Boundary in those cells at the
base pair `(base, base)`. No class lemma below uses the barrier theorem of its own
family; the growth facts come from the family equations and from the self-nested wrapper
chain of `BarrierPumpDischarge_Schema.lean`.

* Families whose wrapper keeps both arguments with coefficient at least one and whose
  recursor adds the payload value linearly (additive, affine, restricted quadratic, and
  the tracked scalar of each vector family) are identically zero or lie in the barrier
  cell.
* The max-plus family has zero counter gain against a wrapper cost of at least one once
  the payload value passes a threshold. The transparent compositional family has zero
  counter gain and a positive wrapper cost at every payload.
* The cross-term and multilinear families lie in the barrier cell when their payload
  coefficient does not grow from `base` to `succ base`. Under their dominance premise
  they fail at every payload past a computed threshold, as does the polynomial family
  under eventual dominance.

Each family barrier then follows from the cell theorem. The last section computes the
cells of the scalar direct-measure grammar on the free schema.
-/

set_option autoImplicit false

namespace OperatorKO7.Methods.OrientationClosure.CellClassificationFamilies

open OperatorKO7.StepDuplicating
open OperatorKO7.StepDuplicating.StepDuplicatingSchema
open OperatorKO7.Methods.OrientationClosure.CellClassification

/-! ## Generic cell facts -/

/-- Orientation fails at the instance `(b, s, n)`: the target is not strictly below the
source. -/
def FailsAt {S : StepDuplicatingSchema} (M : S.T → Nat) (b s n : S.T) : Prop :=
  M (S.recur b s (S.succ n)) ≤ M (S.wrap s (S.recur b s n))

/-- A measure lies in the barrier cell at some pair or fails at some instance. -/
def CellOrPointwiseFailure {S : StepDuplicatingSchema} (M : S.T → Nat) : Prop :=
  (∃ b n : S.T, WrapUnboundedAt M b n ∧ GainBoundedAt M b n) ∨
    ∃ b s n : S.T, FailsAt M b s n

/-- Either alternative excludes uniform orientation of the duplicating step. -/
theorem not_orients_of_cellOrPointwiseFailure {S : StepDuplicatingSchema} {M : S.T → Nat}
    (h : CellOrPointwiseFailure M) :
    ¬ ∀ b s n : S.T, M (S.wrap s (S.recur b s n)) < M (S.recur b s (S.succ n)) := by
  intro horient
  rcases h with ⟨b, n, hw, hg⟩ | ⟨b, s, n, hfail⟩
  · exact barrier_cell_excludes_orientation M b n hw hg (fun s => horient b s n)
  · have hlt := horient b s n
    unfold FailsAt at hfail
    omega

/-- The barrier cell also excludes nonincrease across every duplicating instance at that
pair. -/
theorem barrier_cell_excludes_nonstrict_orientation {S : StepDuplicatingSchema}
    (M : S.T → Nat) (b n : S.T)
    (hw : WrapUnboundedAt M b n) (hg : GainBoundedAt M b n) :
    ¬ ∀ s : S.T, M (S.wrap s (S.recur b s n)) ≤ M (S.recur b s (S.succ n)) := by
  intro h
  obtain ⟨K, hK⟩ := hg
  obtain ⟨s, hs⟩ := hw K
  have hgain := hK s
  have hle := h s
  omega

/-- A measure lies in the barrier cell at `(b, n)` when the wrapper keeps the payload value
on top of the recursive result, the payload values are unbounded, and the counter gain has
a payload-independent bound. -/
theorem barrierCell_of_retention {S : StepDuplicatingSchema} (M : S.T → Nat) (b n : S.T)
    (hretain : ∀ s : S.T, M (S.recur b s n) + M s ≤ M (S.wrap s (S.recur b s n)))
    (hunb : ∀ K : Nat, ∃ s : S.T, K ≤ M s)
    (hgain : ∃ g : Nat, ∀ s : S.T, M (S.recur b s (S.succ n)) ≤ M (S.recur b s n) + g) :
    WrapUnboundedAt M b n ∧ GainBoundedAt M b n := by
  refine ⟨?_, hgain⟩
  intro K
  obtain ⟨s, hs⟩ := hunb (K + 1)
  refine ⟨s, ?_⟩
  have hr := hretain s
  omega

/-- An identically zero measure fails at every instance. -/
theorem failsAt_of_zero {S : StepDuplicatingSchema} {M : S.T → Nat}
    (hzero : ∀ t : S.T, M t = 0) (b s n : S.T) : FailsAt M b s n := by
  unfold FailsAt
  have h1 := hzero (S.recur b s (S.succ n))
  omega

/-! ## Additive, affine and restricted quadratic families -/

/-- Additive measures lie in the barrier cell at every pair: the counter gain is the
successor weight and the wrapper keeps both arguments. -/
theorem additive_barrierCell {S : StepDuplicatingSchema} (M : AdditiveMeasure S)
    (b n : S.T) :
    WrapUnboundedAt M.eval b n ∧ GainBoundedAt M.eval b n := by
  apply barrierCell_of_retention M.eval b n
  · intro s
    rw [M.eval_wrap]
    omega
  · intro K
    exact ⟨wrapIter S K, eval_wrapIter_ge M K⟩
  · refine ⟨M.w_succ, ?_⟩
    intro s
    rw [M.eval_recur, M.eval_recur, M.eval_succ]
    omega

theorem additive_cellOrPointwiseFailure {S : StepDuplicatingSchema} (M : AdditiveMeasure S) :
    CellOrPointwiseFailure M.eval :=
  Or.inl ⟨S.base, S.base, additive_barrierCell M S.base S.base⟩

/-- The additive barrier as a corollary of the cell theorem. -/
theorem no_additive_orients_dup_step_via_cells {S : StepDuplicatingSchema}
    (M : AdditiveMeasure S) :
    ¬ ∀ b s n : S.T, M.eval (S.wrap s (S.recur b s n)) < M.eval (S.recur b s (S.succ n)) :=
  not_orients_of_cellOrPointwiseFailure (additive_cellOrPointwiseFailure M)

/-- Affine measures with positive wrapper coefficients are identically zero or lie in the
barrier cell at the base pair. -/
theorem affine_zero_or_barrierCell {S : StepDuplicatingSchema} (M : AffineMeasure S) :
    (∀ t : S.T, M.eval t = 0) ∨
      (WrapUnboundedAt M.eval S.base S.base ∧ GainBoundedAt M.eval S.base S.base) := by
  rcases affine_zero_or_hasUnboundedRange M with hzero | hunb
  · exact Or.inl hzero
  · right
    apply barrierCell_of_retention M.eval S.base S.base
    · intro s
      rw [M.eval_wrap]
      have hl := Nat.le_mul_of_pos_left (M.eval s) M.h_wrap_left_pos
      have hr := Nat.le_mul_of_pos_left (M.eval (S.recur S.base s S.base)) M.h_wrap_right_pos
      omega
    · exact hunb
    · refine ⟨M.recur_counter * (M.succ_bias + M.succ_scale * M.c_base), ?_⟩
      intro s
      rw [M.eval_recur, M.eval_recur, M.eval_succ, M.eval_base]
      omega

theorem affine_cellOrPointwiseFailure {S : StepDuplicatingSchema} (M : AffineMeasure S) :
    CellOrPointwiseFailure M.eval := by
  rcases affine_zero_or_barrierCell M with hzero | hcell
  · exact Or.inr ⟨S.base, S.base, S.base, failsAt_of_zero hzero S.base S.base S.base⟩
  · exact Or.inl ⟨S.base, S.base, hcell⟩

/-- The affine barrier as a corollary of the cell theorem. -/
theorem no_affine_orients_dup_step_via_cells {S : StepDuplicatingSchema}
    (M : AffineMeasure S) :
    ¬ ∀ b s n : S.T, M.eval (S.wrap s (S.recur b s n)) < M.eval (S.recur b s (S.succ n)) :=
  not_orients_of_cellOrPointwiseFailure (affine_cellOrPointwiseFailure M)

/-- Restricted quadratic measures are identically zero or lie in the barrier cell at the
base pair: the counter square is frozen at the base pair. -/
theorem quadratic_zero_or_barrierCell {S : StepDuplicatingSchema}
    (M : QuadraticCounterMeasure S) :
    (∀ t : S.T, M.eval t = 0) ∨
      (WrapUnboundedAt M.eval S.base S.base ∧ GainBoundedAt M.eval S.base S.base) := by
  by_cases hpos : ∃ t : S.T, 1 ≤ M.eval t
  · right
    apply barrierCell_of_retention M.eval S.base S.base
    · intro s
      rw [M.eval_wrap]
      have hl := Nat.le_mul_of_pos_left (M.eval s) M.h_wrap_left_pos
      have hr := Nat.le_mul_of_pos_left (M.eval (S.recur S.base s S.base)) M.h_wrap_right_pos
      omega
    · exact quadratic_hasUnboundedRange_of_exists_pos M hpos
    · refine ⟨M.recur_counter * (M.succ_bias + M.succ_scale * M.c_base) +
        M.recur_quad * (M.succ_bias + M.succ_scale * M.c_base) *
          (M.succ_bias + M.succ_scale * M.c_base), ?_⟩
      intro s
      rw [M.eval_recur, M.eval_recur, M.eval_succ, M.eval_base]
      omega
  · left
    intro t
    have hnot : ¬ 1 ≤ M.eval t := fun h1 => hpos ⟨t, h1⟩
    omega

theorem quadratic_cellOrPointwiseFailure {S : StepDuplicatingSchema}
    (M : QuadraticCounterMeasure S) :
    CellOrPointwiseFailure M.eval := by
  rcases quadratic_zero_or_barrierCell M with hzero | hcell
  · exact Or.inr ⟨S.base, S.base, S.base, failsAt_of_zero hzero S.base S.base S.base⟩
  · exact Or.inl ⟨S.base, S.base, hcell⟩

/-- The restricted quadratic barrier as a corollary of the cell theorem. -/
theorem no_quadratic_orients_dup_step_via_cells {S : StepDuplicatingSchema}
    (M : QuadraticCounterMeasure S) :
    ¬ ∀ b s n : S.T, M.eval (S.wrap s (S.recur b s n)) < M.eval (S.recur b s (S.succ n)) :=
  not_orients_of_cellOrPointwiseFailure (quadratic_cellOrPointwiseFailure M)

/-! ## Max-plus and transparent compositional families -/

/-- Max-plus measures: once the payload value passes a threshold, the counter gain at the
base pair is zero and the wrapper cost is at least one. -/
theorem max_gain_eventually_zero_wrap_cost_pos {S : StepDuplicatingSchema}
    (M : MaxMeasure S) :
    ∃ K : Nat, ∀ s : S.T, K ≤ M.eval s →
      M.eval (S.recur S.base s (S.succ S.base)) = M.eval (S.recur S.base s S.base) ∧
        M.eval (S.recur S.base s S.base) + 1 ≤
          M.eval (S.wrap s (S.recur S.base s S.base)) := by
  refine ⟨M.recur_base + M.c_base + (M.recur_counter + (M.succ_const + M.c_base)), ?_⟩
  intro s hs
  have h1 : M.recur_counter + (M.succ_const + M.c_base) ≤ M.recur_step + M.eval s := by
    omega
  have h2 : M.recur_counter + M.c_base ≤ M.recur_step + M.eval s := by omega
  have h3 : M.recur_base + M.c_base ≤ M.recur_step + M.eval s := by omega
  have hsrc : M.eval (S.recur S.base s (S.succ S.base)) =
      M.recur_const + (M.recur_step + M.eval s) := by
    rw [M.eval_recur, M.eval_succ, M.eval_base]
    have hinner :
        max (M.recur_step + M.eval s) (M.recur_counter + (M.succ_const + M.c_base)) =
          M.recur_step + M.eval s := max_eq_left h1
    rw [hinner]
    have houter : max (M.recur_base + M.c_base) (M.recur_step + M.eval s) =
        M.recur_step + M.eval s := max_eq_right h3
    rw [houter]
  have htgt : M.eval (S.recur S.base s S.base) =
      M.recur_const + (M.recur_step + M.eval s) := by
    rw [M.eval_recur, M.eval_base]
    have hinner : max (M.recur_step + M.eval s) (M.recur_counter + M.c_base) =
        M.recur_step + M.eval s := max_eq_left h2
    rw [hinner]
    have houter : max (M.recur_base + M.c_base) (M.recur_step + M.eval s) =
        M.recur_step + M.eval s := max_eq_right h3
    rw [houter]
  refine ⟨hsrc.trans htgt.symm, ?_⟩
  rw [M.eval_wrap, htgt]
  have hmax : M.wrap_right + (M.recur_const + (M.recur_step + M.eval s)) ≤
      max (M.wrap_left + M.eval s)
        (M.wrap_right + (M.recur_const + (M.recur_step + M.eval s))) :=
    le_max_right _ _
  have hpos := M.h_wrap_right_pos
  omega

theorem max_cellOrPointwiseFailure {S : StepDuplicatingSchema} (M : MaxMeasure S) :
    CellOrPointwiseFailure M.eval := by
  obtain ⟨K, hK⟩ := max_gain_eventually_zero_wrap_cost_pos M
  obtain ⟨s, hs⟩ := max_hasUnboundedRange M K
  obtain ⟨hgain, hwrap⟩ := hK s hs
  refine Or.inr ⟨S.base, s, S.base, ?_⟩
  unfold FailsAt
  omega

/-- The max-plus barrier as a corollary of the cell theorem. -/
theorem no_max_orients_dup_step_via_cells {S : StepDuplicatingSchema} (M : MaxMeasure S) :
    ¬ ∀ b s n : S.T, M.eval (S.wrap s (S.recur b s n)) < M.eval (S.recur b s (S.succ n)) :=
  not_orients_of_cellOrPointwiseFailure (max_cellOrPointwiseFailure M)

/-- Transparent compositional measures: at the base pair the counter gain is zero and the
wrapper cost is positive at every payload. -/
theorem compositional_transparent_gain_zero_wrap_cost_pos {S : StepDuplicatingSchema}
    (CM : CompositionalMeasure S) (h_transparent : CM.c_succ CM.c_base = CM.c_base)
    (s : S.T) :
    CM.eval (S.recur S.base s (S.succ S.base)) = CM.eval (S.recur S.base s S.base) ∧
      CM.eval (S.recur S.base s S.base) < CM.eval (S.wrap s (S.recur S.base s S.base)) := by
  constructor
  · rw [CM.eval_recur, CM.eval_recur, CM.eval_succ, CM.eval_base, h_transparent]
  · rw [CM.eval_wrap]
    exact CM.wrap_subterm2 _ _

theorem compositional_cellOrPointwiseFailure {S : StepDuplicatingSchema}
    (CM : CompositionalMeasure S) (h_transparent : CM.c_succ CM.c_base = CM.c_base) :
    CellOrPointwiseFailure CM.eval := by
  obtain ⟨hgain, hwrap⟩ :=
    compositional_transparent_gain_zero_wrap_cost_pos CM h_transparent S.base
  refine Or.inr ⟨S.base, S.base, S.base, ?_⟩
  unfold FailsAt
  omega

/-- The transparent compositional barrier as a corollary of the cell theorem. -/
theorem no_compositional_orients_dup_step_via_cells {S : StepDuplicatingSchema}
    (CM : CompositionalMeasure S) (h_transparent : CM.c_succ CM.c_base = CM.c_base) :
    ¬ ∀ b s n : S.T, CM.eval (S.wrap s (S.recur b s n)) < CM.eval (S.recur b s (S.succ n)) :=
  not_orients_of_cellOrPointwiseFailure (compositional_cellOrPointwiseFailure CM h_transparent)

/-! ## Dominance families -/

/-- Cross-term quadratic measures whose cross coefficient does not grow from `base` to
`succ base` are identically zero or lie in the barrier cell, with no coupling premise. -/
theorem crossTerm_zero_or_barrierCell_of_noCrossGrowth {S : StepDuplicatingSchema}
    (M : CrossTermQuadraticMeasure S)
    (hno : M.recur_cross * (M.succ_bias + M.succ_scale * M.c_base) ≤
      M.recur_cross * M.c_base) :
    (∀ t : S.T, M.eval t = 0) ∨
      (WrapUnboundedAt M.eval S.base S.base ∧ GainBoundedAt M.eval S.base S.base) := by
  by_cases hpos : ∃ t : S.T, 1 ≤ M.eval t
  · right
    apply barrierCell_of_retention M.eval S.base S.base
    · intro s
      rw [M.eval_wrap]
      have hl := Nat.le_mul_of_pos_left (M.eval s) M.h_wrap_left_pos
      have hr := Nat.le_mul_of_pos_left (M.eval (S.recur S.base s S.base)) M.h_wrap_right_pos
      omega
    · exact crossTerm_hasUnboundedRange_of_exists_pos M hpos
    · refine ⟨M.recur_counter * (M.succ_bias + M.succ_scale * M.c_base) +
        M.recur_quad * (M.succ_bias + M.succ_scale * M.c_base) *
          (M.succ_bias + M.succ_scale * M.c_base), ?_⟩
      intro s
      have hx : M.recur_cross * M.eval s * (M.succ_bias + M.succ_scale * M.c_base) ≤
          M.recur_cross * M.eval s * M.c_base := by
        have hm := Nat.mul_le_mul_right (M.eval s) hno
        calc M.recur_cross * M.eval s * (M.succ_bias + M.succ_scale * M.c_base)
            = M.recur_cross * (M.succ_bias + M.succ_scale * M.c_base) * M.eval s := by ring
          _ ≤ M.recur_cross * M.c_base * M.eval s := hm
          _ = M.recur_cross * M.eval s * M.c_base := by ring
      rw [M.eval_recur, M.eval_recur, M.eval_succ, M.eval_base]
      omega
  · left
    intro t
    have hnot : ¬ 1 ≤ M.eval t := fun h1 => hpos ⟨t, h1⟩
    omega

/-- Under the bounded coupling premise, a cross-term quadratic measure fails at the base
pair for every payload past a computed threshold. -/
theorem crossTerm_eventually_fails_of_bounded {S : StepDuplicatingSchema}
    (M : CrossTermQuadraticMeasure S) (hbounded : CrossTermBoundedAtBase M) :
    ∃ K : Nat, ∀ s : S.T, K ≤ M.eval s → FailsAt M.eval S.base s S.base := by
  let succBase := M.succ_bias + M.succ_scale * M.c_base
  let sourceCoeff := M.recur_step + M.recur_cross * succBase
  let targetCoeff := M.wrap_left + M.wrap_right * (M.recur_step + M.recur_cross * M.c_base)
  let sourceConst :=
    M.recur_const + M.recur_base * M.c_base +
      M.recur_counter * succBase + M.recur_quad * succBase * succBase
  let targetConst :=
    M.wrap_const +
      M.wrap_right *
        (M.recur_const + M.recur_base * M.c_base +
          M.recur_counter * M.c_base + M.recur_quad * M.c_base * M.c_base)
  refine ⟨sourceConst, ?_⟩
  intro s hs
  have hsrc : M.eval (S.recur S.base s (S.succ S.base)) =
      sourceConst + sourceCoeff * M.eval s := by
    rw [M.eval_recur, M.eval_succ, M.eval_base]
    simp only [sourceConst, sourceCoeff, succBase]
    ring
  have htgt : M.eval (S.wrap s (S.recur S.base s S.base)) =
      targetConst + targetCoeff * M.eval s := by
    rw [M.eval_wrap, M.eval_recur, M.eval_base]
    simp only [targetConst, targetCoeff]
    ring
  have hcoeff : sourceCoeff + 1 ≤ targetCoeff := by
    simpa [CrossTermBoundedAtBase, succBase, sourceCoeff, targetCoeff] using hbounded
  have hmul : (sourceCoeff + 1) * M.eval s ≤ targetCoeff * M.eval s :=
    Nat.mul_le_mul_right (M.eval s) hcoeff
  have hsource : sourceConst + sourceCoeff * M.eval s ≤ (sourceCoeff + 1) * M.eval s := by
    nlinarith
  unfold FailsAt
  rw [hsrc, htgt]
  calc sourceConst + sourceCoeff * M.eval s ≤ (sourceCoeff + 1) * M.eval s := hsource
    _ ≤ targetCoeff * M.eval s := hmul
    _ ≤ targetConst + targetCoeff * M.eval s := Nat.le_add_left _ _

theorem crossTerm_cellOrPointwiseFailure {S : StepDuplicatingSchema}
    (M : CrossTermQuadraticMeasure S) (hbounded : CrossTermBoundedAtBase M) :
    CellOrPointwiseFailure M.eval := by
  by_cases hpos : ∃ t : S.T, 1 ≤ M.eval t
  · obtain ⟨K, hK⟩ := crossTerm_eventually_fails_of_bounded M hbounded
    obtain ⟨s, hs⟩ := crossTerm_hasUnboundedRange_of_exists_pos M hpos K
    exact Or.inr ⟨S.base, s, S.base, hK s hs⟩
  · refine Or.inr ⟨S.base, S.base, S.base, ?_⟩
    have hnot : ¬ 1 ≤ M.eval (S.recur S.base S.base (S.succ S.base)) :=
      fun h1 => hpos ⟨_, h1⟩
    unfold FailsAt
    omega

/-- The bounded cross-term barrier as a corollary of the cell theorem. -/
theorem no_crossTerm_orients_dup_step_via_cells {S : StepDuplicatingSchema}
    (M : CrossTermQuadraticMeasure S) (hbounded : CrossTermBoundedAtBase M) :
    ¬ ∀ b s n : S.T, M.eval (S.wrap s (S.recur b s n)) < M.eval (S.recur b s (S.succ n)) :=
  not_orients_of_cellOrPointwiseFailure (crossTerm_cellOrPointwiseFailure M hbounded)

/-- Multilinear measures whose frozen payload coefficient does not grow from `base` to
`succ base` are identically zero or lie in the barrier cell, with no dominance premise. -/
theorem multilinear_zero_or_barrierCell_of_noStepGrowth {S : StepDuplicatingSchema}
    (M : BoundedMultilinearMeasure S)
    (hno : M.stepCoeffSum M.c_base (M.succ_bias + M.succ_scale * M.c_base) ≤
      M.stepCoeffSum M.c_base M.c_base) :
    (∀ t : S.T, M.eval t = 0) ∨
      (WrapUnboundedAt M.eval S.base S.base ∧ GainBoundedAt M.eval S.base S.base) := by
  by_cases hpos : ∃ t : S.T, 1 ≤ M.eval t
  · right
    apply barrierCell_of_retention M.eval S.base S.base
    · intro s
      rw [M.eval_wrap]
      have hl := Nat.le_mul_of_pos_left (M.eval s) M.h_wrap_left_pos
      have hr := Nat.le_mul_of_pos_left (M.eval (S.recur S.base s S.base)) M.h_wrap_right_pos
      omega
    · exact multilinear_hasUnboundedRange_of_exists_pos M hpos
    · refine ⟨M.recur_counter * (M.succ_bias + M.succ_scale * M.c_base) +
        M.constPartSum M.c_base (M.succ_bias + M.succ_scale * M.c_base), ?_⟩
      intro s
      have hsrc := M.monomialSum_eq_constPart_add_stepCoeff M.c_base (M.eval s)
        (M.succ_bias + M.succ_scale * M.c_base)
      have htgt := M.monomialSum_eq_constPart_add_stepCoeff M.c_base (M.eval s) M.c_base
      have hmul := Nat.mul_le_mul_right (M.eval s) hno
      rw [M.eval_recur, M.eval_recur, M.eval_succ, M.eval_base, hsrc, htgt]
      omega
  · left
    intro t
    have hnot : ¬ 1 ≤ M.eval t := fun h1 => hpos ⟨t, h1⟩
    omega

/-- Under base-point dominance, a multilinear measure fails at the base pair for every
payload past a computed threshold. -/
theorem multilinear_eventually_fails_of_dominated {S : StepDuplicatingSchema}
    (M : BoundedMultilinearMeasure S) (hdom : MultilinearDominatedAtBase M) :
    ∃ K : Nat, ∀ s : S.T, K ≤ M.eval s → FailsAt M.eval S.base s S.base := by
  let succBase := M.succ_bias + M.succ_scale * M.c_base
  let sourceCoeff := M.recur_step + M.stepCoeffSum M.c_base succBase
  let targetCoeff :=
    M.wrap_left + M.wrap_right * (M.recur_step + M.stepCoeffSum M.c_base M.c_base)
  let sourceConst :=
    M.recur_const + M.recur_base * M.c_base + M.recur_counter * succBase +
      M.constPartSum M.c_base succBase
  let targetConst :=
    M.wrap_const + M.wrap_right *
      (M.recur_const + M.recur_base * M.c_base + M.recur_counter * M.c_base +
        M.constPartSum M.c_base M.c_base)
  refine ⟨sourceConst, ?_⟩
  intro s hs
  have hsourceMono := M.monomialSum_eq_constPart_add_stepCoeff M.c_base (M.eval s)
    (M.succ_bias + M.succ_scale * M.c_base)
  have htargetMono := M.monomialSum_eq_constPart_add_stepCoeff M.c_base (M.eval s) M.c_base
  have hsrc : M.eval (S.recur S.base s (S.succ S.base)) =
      sourceConst + sourceCoeff * M.eval s := by
    rw [M.eval_recur, M.eval_succ, M.eval_base, hsourceMono]
    simp only [sourceConst, sourceCoeff, succBase]
    ring
  have htgt : M.eval (S.wrap s (S.recur S.base s S.base)) =
      targetConst + targetCoeff * M.eval s := by
    rw [M.eval_wrap, M.eval_recur, M.eval_base, htargetMono]
    simp only [targetConst, targetCoeff]
    ring
  have hcoeff : sourceCoeff + 1 ≤ targetCoeff := by
    simpa [MultilinearDominatedAtBase, succBase, sourceCoeff, targetCoeff] using hdom
  have hmul : (sourceCoeff + 1) * M.eval s ≤ targetCoeff * M.eval s :=
    Nat.mul_le_mul_right (M.eval s) hcoeff
  have hsource : sourceConst + sourceCoeff * M.eval s ≤ (sourceCoeff + 1) * M.eval s := by
    nlinarith
  unfold FailsAt
  rw [hsrc, htgt]
  calc sourceConst + sourceCoeff * M.eval s ≤ (sourceCoeff + 1) * M.eval s := hsource
    _ ≤ targetCoeff * M.eval s := hmul
    _ ≤ targetConst + targetCoeff * M.eval s := Nat.le_add_left _ _

theorem multilinear_cellOrPointwiseFailure {S : StepDuplicatingSchema}
    (M : BoundedMultilinearMeasure S) (hdom : MultilinearDominatedAtBase M) :
    CellOrPointwiseFailure M.eval := by
  by_cases hpos : ∃ t : S.T, 1 ≤ M.eval t
  · obtain ⟨K, hK⟩ := multilinear_eventually_fails_of_dominated M hdom
    obtain ⟨s, hs⟩ := multilinear_hasUnboundedRange_of_exists_pos M hpos K
    exact Or.inr ⟨S.base, s, S.base, hK s hs⟩
  · refine Or.inr ⟨S.base, S.base, S.base, ?_⟩
    have hnot : ¬ 1 ≤ M.eval (S.recur S.base S.base (S.succ S.base)) :=
      fun h1 => hpos ⟨_, h1⟩
    unfold FailsAt
    omega

/-- The bounded multilinear barrier as a corollary of the cell theorem. -/
theorem no_multilinear_orients_dup_step_via_cells {S : StepDuplicatingSchema}
    (M : BoundedMultilinearMeasure S) (hdom : MultilinearDominatedAtBase M) :
    ¬ ∀ b s n : S.T, M.eval (S.wrap s (S.recur b s n)) < M.eval (S.recur b s (S.succ n)) :=
  not_orients_of_cellOrPointwiseFailure (multilinear_cellOrPointwiseFailure M hdom)

/-- Under eventual frozen dominance, a polynomial-table measure fails at the base pair for
every payload past the dominance threshold. -/
theorem polynomial_eventually_fails_of_dominated {S : StepDuplicatingSchema}
    (M : BoundedPolynomialMeasure S) (hdom : EventuallyDominatedAtBase M) :
    ∃ K : Nat, ∀ s : S.T, K ≤ M.eval s → FailsAt M.eval S.base s S.base := by
  obtain ⟨K, hK⟩ := hdom
  refine ⟨K, ?_⟩
  intro s hs
  unfold FailsAt
  have hsrc :
      M.eval (S.recur S.base s (S.succ S.base)) = M.sourceFrozenAtBase (M.eval s) := by
    rw [M.eval_recur, M.eval_succ, M.eval_base]
    simp [BoundedPolynomialMeasure.sourceFrozenAtBase, Nat.add_assoc, Nat.add_left_comm,
      Nat.add_comm, Nat.mul_add]
  have htgt :
      M.eval (S.wrap s (S.recur S.base s S.base)) = M.targetFrozenAtBase (M.eval s) := by
    rw [M.eval_wrap, M.eval_recur, M.eval_base]
    simp [BoundedPolynomialMeasure.targetFrozenAtBase, Nat.add_assoc, Nat.add_left_comm,
      Nat.add_comm, Nat.mul_add]
  rw [hsrc, htgt]
  exact hK (M.eval s) hs

theorem polynomial_cellOrPointwiseFailure {S : StepDuplicatingSchema}
    (M : BoundedPolynomialMeasure S) (hdom : EventuallyDominatedAtBase M) :
    CellOrPointwiseFailure M.eval := by
  by_cases hpos : ∃ t : S.T, 1 ≤ M.eval t
  · obtain ⟨K, hK⟩ := polynomial_eventually_fails_of_dominated M hdom
    obtain ⟨s, hs⟩ := polynomial_hasUnboundedRange_of_exists_pos M hpos K
    exact Or.inr ⟨S.base, s, S.base, hK s hs⟩
  · refine Or.inr ⟨S.base, S.base, S.base, ?_⟩
    have hnot : ¬ 1 ≤ M.eval (S.recur S.base S.base (S.succ S.base)) :=
      fun h1 => hpos ⟨_, h1⟩
    unfold FailsAt
    omega

/-- The generalized polynomial barrier as a corollary of the cell theorem. -/
theorem no_polynomial_orients_dup_step_via_cells {S : StepDuplicatingSchema}
    (M : BoundedPolynomialMeasure S) (hdom : EventuallyDominatedAtBase M) :
    ¬ ∀ b s n : S.T, M.eval (S.wrap s (S.recur b s n)) < M.eval (S.recur b s (S.succ n)) :=
  not_orients_of_cellOrPointwiseFailure (polynomial_cellOrPointwiseFailure M hdom)

/-! ## Vector families through their tracked scalar -/

/-- Fixed-dimension componentwise barrier: the tracked coordinate is an affine measure,
and strict componentwise decrease forces its strict decrease. -/
theorem no_matrixD_orients_dup_step_via_cells {S : StepDuplicatingSchema} {d : Nat}
    {tracked : Fin d} (M : MatrixMeasureD S d tracked) :
    ¬ (∀ (b s n : S.T),
      VecLt (M.eval (S.wrap s (S.recur b s n))) (M.eval (S.recur b s (S.succ n)))) := by
  intro h
  exact no_affine_orients_dup_step_via_cells M.trackedAffine (fun b s n => h b s n tracked)

/-- Dimension-two componentwise barrier through the first coordinate. -/
theorem no_matrix2_orients_dup_step_via_cells {S : StepDuplicatingSchema}
    (M : MatrixMeasure2 S) :
    ¬ (∀ (b s n : S.T),
      PairLt (M.eval (S.wrap s (S.recur b s n))) (M.eval (S.recur b s (S.succ n)))) := by
  intro h
  exact no_affine_orients_dup_step_via_cells M.fstAffine (fun b s n => (h b s n).1)

/-- Balanced mixed-coordinate barrier through the coordinate sum. -/
theorem no_matrixMix2_orients_dup_step_via_cells {S : StepDuplicatingSchema}
    (M : MatrixMix2Measure S) :
    ¬ (∀ (b s n : S.T),
      PairLt (M.eval (S.wrap s (S.recur b s n))) (M.eval (S.recur b s (S.succ n)))) := by
  intro h
  exact no_affine_orients_dup_step_via_cells M.sumAffine
    (fun b s n => vecSum_lt_of_pairLt (h b s n))

/-- Weighted scalar-projection barrier through the weighted sum. -/
theorem no_matrixFunctional_orients_dup_step_via_cells {S : StepDuplicatingSchema} {d : Nat}
    (M : MatrixFunctionalMeasure S d) :
    ¬ (∀ (b s n : S.T),
      VecLt (M.eval (S.wrap s (S.recur b s n))) (M.eval (S.recur b s (S.succ n)))) := by
  intro h
  exact no_affine_orients_dup_step_via_cells M.projectedAffine
    (fun b s n => weightedSum_lt_of_vecLt M.h_weight_support (h b s n))

/-- Tracked-primary lexicographic barrier: lexicographic decrease forces nonincrease of the
primary coordinate, and the barrier cell excludes nonincrease. One positive primary value
rules out the zero case. -/
theorem no_matrixLexD_orients_dup_step_via_cells {S : StepDuplicatingSchema} {d : Nat}
    (M : MatrixLexMeasureD S d) (hpos : ∃ t : S.T, 1 ≤ M.eval t (primaryIdx d)) :
    ¬ (∀ (b s n : S.T),
      VecLexLt (M.eval (S.wrap s (S.recur b s n))) (M.eval (S.recur b s (S.succ n)))) := by
  intro h
  rcases affine_zero_or_barrierCell M.primaryAffine with hzero | ⟨hw, hg⟩
  · obtain ⟨t, ht⟩ := hpos
    have h0 : M.eval t (primaryIdx d) = 0 := hzero t
    omega
  · exact barrier_cell_excludes_nonstrict_orientation M.primaryAffine.eval S.base S.base hw hg
      (fun s => primary_le_of_vecLexLt (h S.base s S.base))

/-! ## The scalar grammar on the free schema -/

section GrammarShadow

open OperatorKO7.Meta.BoundaryGeneral.DirectMeasureGrammarClosure

/-- Profile of a free recursor term. -/
theorem profile_recur (m : Nat → Nat → Nat) (b s n : SchemaCore.FreeTerm Empty) :
    AttainedPairs.profileMeasure m ((SchemaCore.freeSchema Empty).recur b s n) =
      m (AttainedPairs.succPrefix n + AttainedPairs.counterObservation b)
        (AttainedPairs.payloadObservation b) := rfl

/-- Profile of a free recursor term one counter step higher. -/
theorem profile_recur_succ (m : Nat → Nat → Nat) (b s n : SchemaCore.FreeTerm Empty) :
    AttainedPairs.profileMeasure m
        ((SchemaCore.freeSchema Empty).recur b s ((SchemaCore.freeSchema Empty).succ n)) =
      m (AttainedPairs.succPrefix n + 1 + AttainedPairs.counterObservation b)
        (AttainedPairs.payloadObservation b) := rfl

/-- Profile of the wrapped recursive call. -/
theorem profile_wrap_recur (m : Nat → Nat → Nat) (b s n : SchemaCore.FreeTerm Empty) :
    AttainedPairs.profileMeasure m
        ((SchemaCore.freeSchema Empty).wrap s ((SchemaCore.freeSchema Empty).recur b s n)) =
      m (AttainedPairs.succPrefix n + AttainedPairs.counterObservation b)
        (AttainedPairs.payloadObservation s + AttainedPairs.payloadObservation b + 1) := rfl

/-- Every profile measure has bounded counter gain at every pair: the gain does not read
the payload argument. -/
theorem profile_gainBoundedAt (m : Nat → Nat → Nat) (b n : SchemaCore.FreeTerm Empty) :
    GainBoundedAt (S := SchemaCore.freeSchema Empty) (AttainedPairs.profileMeasure m) b n := by
  refine ⟨m (AttainedPairs.succPrefix n + 1 + AttainedPairs.counterObservation b)
    (AttainedPairs.payloadObservation b), ?_⟩
  intro s
  have h1 := profile_recur_succ m b s n
  have h2 := profile_recur m b s n
  omega

/-- On the free schema a grammar measure lies in the barrier cell at `(b, n)` exactly when
its payload section at the observed counter is not constant. -/
theorem grammar_profile_barrierCell_iff (e : MeasureExpr) (b n : SchemaCore.FreeTerm Empty) :
    (WrapUnboundedAt (S := SchemaCore.freeSchema Empty)
        (AttainedPairs.profileMeasure e.eval) b n ∧
      GainBoundedAt (S := SchemaCore.freeSchema Empty)
        (AttainedPairs.profileMeasure e.eval) b n) ↔
      ¬ ∀ p p' : Nat,
        e.eval (AttainedPairs.succPrefix n + AttainedPairs.counterObservation b) p =
          e.eval (AttainedPairs.succPrefix n + AttainedPairs.counterObservation b) p' := by
  constructor
  · rintro ⟨hw, -⟩ hconst
    obtain ⟨s, hs⟩ := hw 0
    have h1 := profile_wrap_recur e.eval b s n
    have h2 := profile_recur e.eval b s n
    have h3 := hconst
      (AttainedPairs.payloadObservation s + AttainedPairs.payloadObservation b + 1)
      (AttainedPairs.payloadObservation b)
    omega
  · intro hnon
    refine ⟨?_, profile_gainBoundedAt e.eval b n⟩
    rcases eval_section_const_or_unbounded e
        (AttainedPairs.succPrefix n + AttainedPairs.counterObservation b) with hconst | hunb
    · exact absurd hconst hnon
    · intro K
      obtain ⟨p, hp⟩ := hunb
        (e.eval (AttainedPairs.succPrefix n + AttainedPairs.counterObservation b)
          (AttainedPairs.payloadObservation b) + K + 1)
      refine ⟨AttainedPairs.payloadTerm p, ?_⟩
      have h1 := profile_wrap_recur e.eval b (AttainedPairs.payloadTerm p) n
      have h2 := profile_recur e.eval b (AttainedPairs.payloadTerm p) n
      have h3 := AttainedPairs.payloadObservation_payloadTerm p
      have hmono := eval_payloadMonotone e
        (AttainedPairs.succPrefix n + AttainedPairs.counterObservation b) p
        (AttainedPairs.payloadObservation (AttainedPairs.payloadTerm p) +
          AttainedPairs.payloadObservation b + 1) (by omega)
      omega

/-- A constant payload section puts the grammar measure in the bounded/bounded cell. -/
theorem grammar_profile_boundedBounded_of_const (e : MeasureExpr)
    (b n : SchemaCore.FreeTerm Empty)
    (hconst : ∀ p p' : Nat,
      e.eval (AttainedPairs.succPrefix n + AttainedPairs.counterObservation b) p =
        e.eval (AttainedPairs.succPrefix n + AttainedPairs.counterObservation b) p') :
    WrapBoundedAt (S := SchemaCore.freeSchema Empty) (AttainedPairs.profileMeasure e.eval) b n ∧
      GainBoundedAt (S := SchemaCore.freeSchema Empty)
        (AttainedPairs.profileMeasure e.eval) b n := by
  refine ⟨⟨0, ?_⟩, profile_gainBoundedAt e.eval b n⟩
  intro s
  have h1 := profile_wrap_recur e.eval b s n
  have h2 := profile_recur e.eval b s n
  have h3 := hconst
    (AttainedPairs.payloadObservation s + AttainedPairs.payloadObservation b + 1)
    (AttainedPairs.payloadObservation b)
  omega

/-- The grammar characterization read through the cells: a grammar expression orients every
free successor instance exactly when no pair is a barrier cell and its counter response is
strict. -/
theorem grammar_orients_iff_no_barrierCell_and_counterStrict (e : MeasureExpr) :
    (∀ b s n : SchemaCore.FreeTerm Empty,
        AttainedPairs.profileMeasure e.eval (.wrap s (.recur b s n)) <
          AttainedPairs.profileMeasure e.eval (.recur b s (.succ n))) ↔
      ((∀ b n : SchemaCore.FreeTerm Empty,
          ¬ (WrapUnboundedAt (S := SchemaCore.freeSchema Empty)
              (AttainedPairs.profileMeasure e.eval) b n ∧
            GainBoundedAt (S := SchemaCore.freeSchema Empty)
              (AttainedPairs.profileMeasure e.eval) b n)) ∧
        CounterStrict e.eval) := by
  constructor
  · intro h
    have horient : OrientsDupStep e.eval := by
      intro c p L hL
      have he := h (AttainedPairs.payloadTerm p) (AttainedPairs.payloadTerm (L - 1))
        (AttainedPairs.counterTerm c)
      have hL' : L - 1 + p + 1 = p + L := by omega
      simpa [AttainedPairs.profileMeasure, AttainedPairs.counterObservation,
        AttainedPairs.payloadObservation, AttainedPairs.succPrefix, hL'] using he
    obtain ⟨hblind, hcounter⟩ := (orients_iff_payloadBlind_and_counterStrict e).1 horient
    refine ⟨?_, hcounter⟩
    intro b n hcell
    exact (grammar_profile_barrierCell_iff e b n).1 hcell (fun p p' => hblind _ p p')
  · rintro ⟨hno, hcounter⟩
    have hblind : PayloadBlind e.eval := by
      intro c p p'
      by_contra hne
      apply hno SchemaCore.FreeTerm.zero (AttainedPairs.counterTerm c)
      refine (grammar_profile_barrierCell_iff e _ _).2 ?_
      intro hconst
      apply hne
      have hsec := hconst p p'
      simpa [AttainedPairs.counterObservation] using hsec
    have horient : OrientsDupStep e.eval :=
      payloadBlind_and_counterStrict_implies_orients hblind hcounter
    intro b s n
    exact (AttainedPairs.profile_orients_successors_iff e.eval).2 horient b s n

end GrammarShadow

end OperatorKO7.Methods.OrientationClosure.CellClassificationFamilies
