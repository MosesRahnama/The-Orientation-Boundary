import OperatorKO7.Meta.Methods.OrientationClosure.CellClassificationFamilies
import OperatorKO7.Meta.DominancePremiseSharpness
import OperatorKO7.Meta.NonlinearUnconstrainedExactLaw
import OperatorKO7.Meta.SchemaBarrier_OrderedCarrier
import OperatorKO7.Meta.MatrixBarrierOrderedField_Schema
import OperatorKO7.Meta.SymbolicComparatorBarrier_Weighted_Schema
import OperatorKO7.Meta.DepthBarrier_Schema
import Mathlib.Tactic

/-!
# Deleted-premise countermodels for the twelve direct barrier families

For every premise that a live direct barrier theorem consumes, this module either gives a
countermodel or proves that the premise is not load-bearing.

* A countermodel is a datum of the relaxed class (the live class with exactly the deleted premise
  removed, every other premise kept as a field), a proof that the deleted premise fails, and a
  strict orienter of the duplicating rule (or the exact negation of the barrier conclusion).
* `slot_barrier_restored` shows, by calling the live barrier theorem, that restoring the deleted
  premise gives the barrier back, so each relaxed class differs from the live class by exactly
  that premise.
* The premises proved not load-bearing are the additive and max-depth wrapper weights, the
  max-plus right wrapper offset, the first wrapper-subterm clause of the transparent
  compositional class, the two wrapper coefficients of the three dominance classes, and the
  succ/recursor positivity fields of the weighted variable condition.

The last section shows that both hypotheses of the barrier cell of
`CellClassification.barrier_cell_excludes_orientation` are individually necessary.

Relation: the schema duplicating step `recur b s (succ n) → wrap s (recur b s n)` at the root.
Property: premise necessity (countermodel) or premise redundancy (barrier without the premise).
External trust: none.
-/

set_option autoImplicit false

namespace OperatorKO7.Methods.OrientationClosure.HypothesisNecessity

open OperatorKO7.StepDuplicating
open OperatorKO7.StepDuplicating.StepDuplicatingSchema
open OperatorKO7.SymbolicComparatorBarrier (CoefficientAssignment SubtermCoefficients
  WeightedVariableConditionOrder weightedCount dupSrc dupTgt SchemaVar STerm
  not_orients_dup_rule_weighted wrapFirst_positivity_necessary wrapSecond_positivity_necessary
  wrapFirstDegenerate wrapSecondDegenerate weightedCount_dupSrc_s weightedCount_dupTgt_s)

/-! ## The twelve direct families -/

/-- The direct measure families of the Orientation Boundary. -/
inductive DirectBarrierFamily where
  | additiveCompositional
  | transparentCompositional
  | affine
  | restrictedQuadratic
  | boundedCrossTermQuadratic
  | boundedMultilinear
  | generalizedBoundedPolynomial
  | maxPlus
  | trackedPrimaryPair
  | trackedPrimaryLexicographic
  | maxDepth
  | headPrecedence
  deriving DecidableEq, Repr

/-- Every direct family, listed once. -/
def allDirectBarrierFamilies : List DirectBarrierFamily :=
  [.additiveCompositional, .transparentCompositional, .affine, .restrictedQuadratic,
    .boundedCrossTermQuadratic, .boundedMultilinear, .generalizedBoundedPolynomial, .maxPlus,
    .trackedPrimaryPair, .trackedPrimaryLexicographic, .maxDepth, .headPrecedence]

theorem allDirectBarrierFamilies_length : allDirectBarrierFamilies.length = 12 := rfl

theorem allDirectBarrierFamilies_nodup : allDirectBarrierFamilies.Nodup := by decide

theorem mem_allDirectBarrierFamilies (f : DirectBarrierFamily) :
    f ∈ allDirectBarrierFamilies := by
  cases f <;> decide

/-! ## Orientation of the duplicating rule -/

/-- Every instance of the duplicating rule is oriented by `R` under the valuation `e`. -/
def DupOrientsBy {S : StepDuplicatingSchema} {α : Type} (R : α → α → Prop) (e : S.T → α) :
    Prop :=
  ∀ b s n : S.T, R (e (S.wrap s (S.recur b s n))) (e (S.recur b s (S.succ n)))

/-! ## Two orienting weights of the free syntax -/

/-- Counter projection whose wrapper keeps only its right argument. -/
def counterWeight : FreeTerm → Nat
  | .base => 0
  | .succ t => 1 + counterWeight t
  | .wrap _ y => counterWeight y
  | .recur _ _ n => counterWeight n

theorem counterWeight_orients : DupOrientsBy (S := freeSchema) (· < ·) counterWeight := by
  intro b s n
  show counterWeight n < 1 + counterWeight n
  omega

/-- Step projection whose wrapper keeps only its left argument. -/
def stepWeight : FreeTerm → Nat
  | .base => 0
  | .succ t => stepWeight t
  | .wrap x _ => stepWeight x
  | .recur _ s _ => 1 + stepWeight s

theorem stepWeight_orients : DupOrientsBy (S := freeSchema) (· < ·) stepWeight := by
  intro b s n
  show stepWeight s < 1 + stepWeight s
  omega

/-! ## Generic pumping lemmas used by the redundancy proofs -/

/-- If the wrapper keeps its right argument, orientation makes the counter chain unbounded. -/
theorem unbounded_of_orients_rightRetaining {S : StepDuplicatingSchema} (e : S.T → Nat)
    (hwrap : ∀ x y : S.T, e y ≤ e (S.wrap x y)) (h : DupOrientsBy (· < ·) e) :
    ∀ K : Nat, ∃ t : S.T, K ≤ e t := by
  have hchain : ∀ k : Nat, k ≤ e (S.recur S.base S.base (succIter S k)) := by
    intro k
    induction k with
    | zero => exact Nat.zero_le _
    | succ k ih =>
        have h1 : e (S.wrap S.base (S.recur S.base S.base (succIter S k))) <
            e (S.recur S.base S.base (S.succ (succIter S k))) := h S.base S.base (succIter S k)
        have h2 := hwrap S.base (S.recur S.base S.base (succIter S k))
        show k + 1 ≤ e (S.recur S.base S.base (S.succ (succIter S k)))
        omega
  intro K
  exact ⟨_, hchain K⟩

/-- Nested recursor chain in the step argument. -/
def stepChain (S : StepDuplicatingSchema) : Nat → S.T
  | 0 => S.base
  | k + 1 => S.recur S.base (stepChain S k) (S.succ S.base)

/-- If the wrapper keeps its left argument, orientation makes the step chain unbounded. -/
theorem unbounded_of_orients_leftRetaining {S : StepDuplicatingSchema} (e : S.T → Nat)
    (hwrap : ∀ x y : S.T, e x ≤ e (S.wrap x y)) (h : DupOrientsBy (· < ·) e) :
    ∀ K : Nat, ∃ t : S.T, K ≤ e t := by
  have hchain : ∀ k : Nat, k ≤ e (stepChain S k) := by
    intro k
    induction k with
    | zero => exact Nat.zero_le _
    | succ k ih =>
        have h1 : e (S.wrap (stepChain S k) (S.recur S.base (stepChain S k) S.base)) <
            e (S.recur S.base (stepChain S k) (S.succ S.base)) := h S.base (stepChain S k) S.base
        have h2 := hwrap (stepChain S k) (S.recur S.base (stepChain S k) S.base)
        show k + 1 ≤ e (S.recur S.base (stepChain S k) (S.succ S.base))
        omega
  intro K
  exact ⟨_, hchain K⟩

/-- Unbounded values together with eventual failure at the base pair exclude orientation. -/
theorem not_orients_of_unbounded_of_eventualFailure {S : StepDuplicatingSchema} (e : S.T → Nat)
    (hunb : ∀ K : Nat, ∃ t : S.T, K ≤ e t)
    (hfail : ∃ K : Nat, ∀ s : S.T, K ≤ e s →
      e (S.recur S.base s (S.succ S.base)) ≤ e (S.wrap s (S.recur S.base s S.base))) :
    ¬ DupOrientsBy (· < ·) e := by
  intro h
  obtain ⟨K, hK⟩ := hfail
  obtain ⟨s, hs⟩ := hunb K
  have h1 := hK s hs
  have h2 : e (S.wrap s (S.recur S.base s S.base)) < e (S.recur S.base s (S.succ S.base)) :=
    h S.base s S.base
  omega

/-! ## Additive compositional family

Live theorems: `no_ordered_additive_orients_dup_step` (premise `hatt`, field `eval_wrap_ge`),
`no_unconstrainedDirect_orients_dup_step` (clauses `wrap_keeps_arguments`, `counter_gain`), and
`CellClassificationFamilies.no_additive_orients_dup_step_via_cells` (field `h_wrap_pos`, shown
not load-bearing below). -/

section Additive

/-- Strictly negative valuation of the free syntax. -/
def negativeWeight : FreeTerm → Int
  | .base => -1
  | .succ t => negativeWeight t
  | .wrap x y => negativeWeight x + negativeWeight y
  | .recur b s n => negativeWeight b + negativeWeight s + negativeWeight n

theorem negativeWeight_neg (t : FreeTerm) : negativeWeight t < 0 := by
  induction t with
  | base => simp [negativeWeight]
  | succ t ih => simpa [negativeWeight] using ih
  | wrap x y ihx ihy => simp only [negativeWeight]; omega
  | recur b s n ihb ihs ihn => simp only [negativeWeight]; omega

/-- The negative valuation as an ordered additive measure over `Int` on the free schema. -/
def negativeOrderedAdditive : OrderedAdditiveMeasure freeSchema Int where
  eval := negativeWeight
  w_base := -1
  w_succ := 0
  w_recur := 0
  eval_base := rfl
  eval_succ := fun t => by simp [freeSchema, negativeWeight]
  eval_wrap_ge := fun x y => by simp [freeSchema, negativeWeight]
  eval_recur := fun b s n => by simp [freeSchema, negativeWeight]

theorem negativeOrderedAdditive_not_attained :
    ¬ ∃ t : freeSchema.T, negativeOrderedAdditive.w_succ ≤ negativeOrderedAdditive.eval t := by
  rintro ⟨t, ht⟩
  have hneg := negativeWeight_neg t
  change (0 : Int) ≤ negativeWeight t at ht
  omega

theorem negativeOrderedAdditive_orients :
    DupOrientsBy (S := freeSchema) (· < ·) negativeOrderedAdditive.eval := by
  intro b s n
  have hneg := negativeWeight_neg s
  change negativeWeight s + (negativeWeight b + negativeWeight s + negativeWeight n) <
    negativeWeight b + negativeWeight s + negativeWeight n
  omega

theorem additiveAttainment_restored (M : OrderedAdditiveMeasure freeSchema Int)
    (hd : ∃ t : freeSchema.T, M.w_succ ≤ M.eval t) :
    ¬ DupOrientsBy (S := freeSchema) (· < ·) M.eval :=
  no_ordered_additive_orients_dup_step M hd

/-- **Attainment is necessary.** On the free schema and on the negative-integer schema of
`ordered_additive_attainment_hypothesis_necessary`, the ordered additive barrier without `hatt`
is false. -/
theorem additiveAttainment_deleted_barrier_false :
    (¬ ∀ M : OrderedAdditiveMeasure freeSchema Int,
      ¬ DupOrientsBy (S := freeSchema) (· < ·) M.eval) ∧
    (¬ ∃ t : negativeIntSchema.T,
      negativeIntOrderedAdditiveMeasure.w_succ ≤ negativeIntOrderedAdditiveMeasure.eval t) ∧
    (¬ ∀ M : OrderedAdditiveMeasure negativeIntSchema Int,
      ¬ DupOrientsBy (S := negativeIntSchema) (· < ·) M.eval) :=
  ⟨fun hall => hall negativeOrderedAdditive negativeOrderedAdditive_orients,
    ordered_additive_attainment_hypothesis_necessary.2,
    fun hall => hall negativeIntOrderedAdditiveMeasure
      ordered_additive_attainment_hypothesis_necessary.1⟩

/-- The ordered additive class with the wrapper-retention field removed; attainment is kept. -/
structure OrderedAdditiveNoRetention where
  eval : freeSchema.T → Int
  w_base : Int
  w_succ : Int
  w_recur : Int
  eval_base : eval freeSchema.base = w_base
  eval_succ : ∀ t, eval (freeSchema.succ t) = eval t + w_succ
  eval_recur : ∀ b s n, eval (freeSchema.recur b s n) = w_recur + eval b + eval s + eval n
  attained : ∃ t : freeSchema.T, w_succ ≤ eval t

/-- The deleted field `eval_wrap_ge`. -/
def OrderedAdditiveNoRetention.WrapRetention (M : OrderedAdditiveNoRetention) : Prop :=
  ∀ x y : freeSchema.T, M.eval x + M.eval y ≤ M.eval (freeSchema.wrap x y)

/-- Restoring the deleted field gives a live ordered additive measure. -/
def OrderedAdditiveNoRetention.restore (M : OrderedAdditiveNoRetention)
    (h : M.WrapRetention) : OrderedAdditiveMeasure freeSchema Int where
  eval := M.eval
  w_base := M.w_base
  w_succ := M.w_succ
  w_recur := M.w_recur
  eval_base := M.eval_base
  eval_succ := M.eval_succ
  eval_wrap_ge := h
  eval_recur := M.eval_recur

theorem additiveWrapRetention_restored (M : OrderedAdditiveNoRetention)
    (hd : M.WrapRetention) : ¬ DupOrientsBy (S := freeSchema) (· < ·) M.eval :=
  no_ordered_additive_orients_dup_step (M.restore hd) M.attained

/-- Valuation whose wrapper is worth zero. -/
def retentionFailWeight : FreeTerm → Int
  | .base => 0
  | .succ t => retentionFailWeight t + 1
  | .wrap _ _ => 0
  | .recur b s n => retentionFailWeight b + retentionFailWeight s + retentionFailWeight n

theorem retentionFailWeight_nonneg (t : FreeTerm) : 0 ≤ retentionFailWeight t := by
  induction t with
  | base => simp [retentionFailWeight]
  | succ t ih => simp only [retentionFailWeight]; omega
  | wrap x y _ _ => simp [retentionFailWeight]
  | recur b s n ihb ihs ihn => simp only [retentionFailWeight]; omega

def retentionFailAdditive : OrderedAdditiveNoRetention where
  eval := retentionFailWeight
  w_base := 0
  w_succ := 1
  w_recur := 0
  eval_base := rfl
  eval_succ := fun t => by simp [freeSchema, retentionFailWeight]
  eval_recur := fun b s n => by simp [freeSchema, retentionFailWeight]
  attained := ⟨FreeTerm.succ FreeTerm.base, by simp [retentionFailWeight]⟩

theorem retentionFailAdditive_not_retention : ¬ retentionFailAdditive.WrapRetention := by
  intro h
  have h1 := h (FreeTerm.succ FreeTerm.base) (FreeTerm.succ FreeTerm.base)
  change retentionFailWeight (FreeTerm.succ FreeTerm.base) +
      retentionFailWeight (FreeTerm.succ FreeTerm.base) ≤
    retentionFailWeight (FreeTerm.wrap (FreeTerm.succ FreeTerm.base)
      (FreeTerm.succ FreeTerm.base)) at h1
  simp only [retentionFailWeight] at h1
  omega

theorem retentionFailAdditive_orients :
    DupOrientsBy (S := freeSchema) (· < ·) retentionFailAdditive.eval := by
  intro b s n
  have hb := retentionFailWeight_nonneg b
  have hs := retentionFailWeight_nonneg s
  have hn := retentionFailWeight_nonneg n
  change (0 : Int) < retentionFailWeight b + retentionFailWeight s + (retentionFailWeight n + 1)
  omega

/-- **Wrapper retention of the ordered additive class is necessary.** -/
theorem additiveWrapRetention_deleted_barrier_false :
    ¬ ∀ M : OrderedAdditiveNoRetention, ¬ DupOrientsBy (S := freeSchema) (· < ·) M.eval :=
  fun hall => hall retentionFailAdditive retentionFailAdditive_orients

/-- The exact direct law with the wrapper clause removed. -/
structure DirectLawNoRetention where
  eval : freeSchema.T → Nat
  succGain : Nat
  counter_gain : ∀ b s n : freeSchema.T,
    eval (freeSchema.recur b s (freeSchema.succ n)) ≤ succGain + eval (freeSchema.recur b s n)

/-- The deleted clause: a fixed wrapper cost with both arguments kept. -/
def DirectLawNoRetention.WrapperRetention (M : DirectLawNoRetention) : Prop :=
  ∃ wrapCost : Nat, ∀ x y : freeSchema.T,
    wrapCost + M.eval x + M.eval y ≤ M.eval (freeSchema.wrap x y)

theorem directLawWrapperRetention_restored (M : DirectLawNoRetention)
    (hd : M.WrapperRetention) : ¬ DupOrientsBy (S := freeSchema) (· < ·) M.eval := by
  obtain ⟨c, hc⟩ := hd
  exact no_unconstrainedDirect_orients_dup_step (S := freeSchema)
    { eval := M.eval, wrapCost := c, wrap_keeps_arguments := hc, succGain := M.succGain,
      counter_gain := M.counter_gain }

/-- `botRightWeight` with counter gain one. -/
def botRightDirectLaw : DirectLawNoRetention where
  eval := botRightWeight
  succGain := 1
  counter_gain := fun b s n => by
    simp only [freeSchema, botRightWeight]
    omega

theorem botRightDirectLaw_not_retention : ¬ botRightDirectLaw.WrapperRetention := by
  rintro ⟨c, hc⟩
  exact Eq.mp unconstrainedDirectLaw_wrap_clause_necessary (fun x y => by
    have h := hc x y
    change c + botRightWeight x + botRightWeight y ≤ botRightWeight (freeSchema.wrap x y) at h
    omega)

/-- **The wrapper clause of the exact direct law is necessary.** -/
theorem directLawWrapperRetention_deleted_barrier_false :
    ¬ ∀ M : DirectLawNoRetention, ¬ DupOrientsBy (S := freeSchema) (· < ·) M.eval :=
  fun hall => hall botRightDirectLaw unconstrainedDirectLaw_wrap_clause_escape

/-- The exact direct law with the counter-gain clause removed. -/
structure DirectLawNoGain where
  eval : freeSchema.T → Nat
  wrapCost : Nat
  wrap_keeps_arguments : ∀ x y : freeSchema.T,
    wrapCost + eval x + eval y ≤ eval (freeSchema.wrap x y)

/-- The deleted clause: a fixed bound on the counter gain. -/
def DirectLawNoGain.BoundedCounterGain (M : DirectLawNoGain) : Prop :=
  ∃ succGain : Nat, ∀ b s n : freeSchema.T,
    M.eval (freeSchema.recur b s (freeSchema.succ n)) ≤ succGain + M.eval (freeSchema.recur b s n)

theorem directLawBoundedCounterGain_restored (M : DirectLawNoGain)
    (hd : M.BoundedCounterGain) : ¬ DupOrientsBy (S := freeSchema) (· < ·) M.eval := by
  obtain ⟨g, hg⟩ := hd
  exact no_unconstrainedDirect_orients_dup_step (S := freeSchema)
    { eval := M.eval, wrapCost := M.wrapCost, wrap_keeps_arguments := M.wrap_keeps_arguments,
      succGain := g, counter_gain := hg }

/-- `crossCoupledWeight` with wrapper cost zero. -/
def crossCoupledDirectLaw : DirectLawNoGain where
  eval := crossCoupledWeight
  wrapCost := 0
  wrap_keeps_arguments := crossCoupledWeight_keeps_wrapper_arguments

theorem crossCoupledDirectLaw_not_boundedGain : ¬ crossCoupledDirectLaw.BoundedCounterGain := by
  rintro ⟨g, hg⟩
  exact unconstrainedDirectLaw_counter_clause_escape.2.2 g hg

/-- **The counter-gain clause of the exact direct law is necessary.** The countermodel is
independent of the wrapper-clause countermodel. -/
theorem directLawBoundedCounterGain_deleted_barrier_false :
    ¬ ∀ M : DirectLawNoGain, ¬ DupOrientsBy (S := freeSchema) (· < ·) M.eval :=
  fun hall => hall crossCoupledDirectLaw unconstrainedDirectLaw_counter_clause_escape.2.1

/-- The natural additive class with the wrapper-weight positivity field removed. -/
structure AdditiveNoWrapPos (S : StepDuplicatingSchema) where
  eval : S.T → Nat
  w_base : Nat
  w_succ : Nat
  w_wrap : Nat
  w_recur : Nat
  eval_base : eval S.base = w_base
  eval_succ : ∀ t, eval (S.succ t) = w_succ + eval t
  eval_wrap : ∀ x y, eval (S.wrap x y) = w_wrap + eval x + eval y
  eval_recur : ∀ b s n, eval (S.recur b s n) = w_recur + eval b + eval s + eval n

/-- **`h_wrap_pos` of the additive class is not load-bearing.** The instance
`(base, succ base, base)` already fails. -/
theorem additive_wrapPos_nonLoadBearing {S : StepDuplicatingSchema} (M : AdditiveNoWrapPos S) :
    ¬ DupOrientsBy (· < ·) M.eval := by
  intro h
  have hs : M.eval (S.wrap (S.succ S.base) (S.recur S.base (S.succ S.base) S.base)) <
      M.eval (S.recur S.base (S.succ S.base) (S.succ S.base)) := h S.base (S.succ S.base) S.base
  simp only [M.eval_wrap, M.eval_recur, M.eval_succ, M.eval_base] at hs
  omega

end Additive

/-! ## Transparent compositional family

Live theorem: `CellClassificationFamilies.no_compositional_orients_dup_step_via_cells`
(premise `h_transparent`, field `wrap_subterm2`; field `wrap_subterm1` is not load-bearing). -/

section Compositional

/-- Coupled compositional valuation: `recur b s n = 2 n + s n`. -/
def compCoupledWeight : FreeTerm → Nat
  | .base => 1
  | .succ t => compCoupledWeight t + 1
  | .wrap x y => compCoupledWeight x + compCoupledWeight y + 1
  | .recur _ s n => 2 * compCoupledWeight n + compCoupledWeight s * compCoupledWeight n

def compCoupledMeasure : CompositionalMeasure freeSchema where
  eval := compCoupledWeight
  c_base := 1
  c_succ := fun x => x + 1
  c_wrap := fun x y => x + y + 1
  c_recur := fun _ s n => 2 * n + s * n
  eval_base := rfl
  eval_succ := fun t => by simp [freeSchema, compCoupledWeight]
  eval_wrap := fun x y => by simp [freeSchema, compCoupledWeight]
  eval_recur := fun b s n => by simp [freeSchema, compCoupledWeight]
  wrap_subterm1 := fun x y => by show x < x + y + 1; omega
  wrap_subterm2 := fun x y => by show y < x + y + 1; omega

theorem compCoupledMeasure_not_transparent :
    ¬ compCoupledMeasure.c_succ compCoupledMeasure.c_base = compCoupledMeasure.c_base := by
  show ¬ ((1 : Nat) + 1 = 1)
  omega

theorem compCoupledMeasure_orients :
    DupOrientsBy (S := freeSchema) (· < ·) compCoupledMeasure.eval := by
  intro b s n
  change compCoupledWeight s + (2 * compCoupledWeight n + compCoupledWeight s * compCoupledWeight n)
      + 1 <
    2 * (compCoupledWeight n + 1) + compCoupledWeight s * (compCoupledWeight n + 1)
  have hmul : compCoupledWeight s * (compCoupledWeight n + 1) =
      compCoupledWeight s * compCoupledWeight n + compCoupledWeight s := by ring
  omega

theorem transparentSuccessor_restored (M : CompositionalMeasure freeSchema)
    (hd : M.c_succ M.c_base = M.c_base) : ¬ DupOrientsBy (S := freeSchema) (· < ·) M.eval :=
  CellClassificationFamilies.no_compositional_orients_dup_step_via_cells M hd

/-- **Successor transparency is necessary.** -/
theorem transparentSuccessor_deleted_barrier_false :
    ¬ ∀ M : CompositionalMeasure freeSchema, ¬ DupOrientsBy (S := freeSchema) (· < ·) M.eval :=
  fun hall => hall compCoupledMeasure compCoupledMeasure_orients

/-- The compositional class with `wrap_subterm2` removed; transparency is kept. -/
structure CompositionalNoSubterm2 where
  eval : freeSchema.T → Nat
  c_base : Nat
  c_succ : Nat → Nat
  c_wrap : Nat → Nat → Nat
  c_recur : Nat → Nat → Nat → Nat
  eval_base : eval freeSchema.base = c_base
  eval_succ : ∀ t, eval (freeSchema.succ t) = c_succ (eval t)
  eval_wrap : ∀ x y, eval (freeSchema.wrap x y) = c_wrap (eval x) (eval y)
  eval_recur : ∀ b s n, eval (freeSchema.recur b s n) = c_recur (eval b) (eval s) (eval n)
  wrap_subterm1 : ∀ x y, c_wrap x y > x
  transparent : c_succ c_base = c_base

/-- The deleted field `wrap_subterm2`. -/
def CompositionalNoSubterm2.WrapSubterm2 (M : CompositionalNoSubterm2) : Prop :=
  ∀ x y, M.c_wrap x y > y

def CompositionalNoSubterm2.restore (M : CompositionalNoSubterm2) (h : M.WrapSubterm2) :
    CompositionalMeasure freeSchema where
  eval := M.eval
  c_base := M.c_base
  c_succ := M.c_succ
  c_wrap := M.c_wrap
  c_recur := M.c_recur
  eval_base := M.eval_base
  eval_succ := M.eval_succ
  eval_wrap := M.eval_wrap
  eval_recur := M.eval_recur
  wrap_subterm1 := M.wrap_subterm1
  wrap_subterm2 := h

theorem compositionalWrapSubterm2_restored (M : CompositionalNoSubterm2)
    (hd : M.WrapSubterm2) : ¬ DupOrientsBy (S := freeSchema) (· < ·) M.eval :=
  CellClassificationFamilies.no_compositional_orients_dup_step_via_cells (M.restore hd)
    M.transparent

/-- Valuation whose wrapper reads only its left argument. -/
def leftWrapWeight : FreeTerm → Nat
  | .base => 0
  | .succ t => leftWrapWeight t
  | .wrap x _ => leftWrapWeight x + 1
  | .recur _ s _ => leftWrapWeight s + 2

def leftWrapCompositional : CompositionalNoSubterm2 where
  eval := leftWrapWeight
  c_base := 0
  c_succ := fun x => x
  c_wrap := fun x _ => x + 1
  c_recur := fun _ s _ => s + 2
  eval_base := rfl
  eval_succ := fun t => by simp [freeSchema, leftWrapWeight]
  eval_wrap := fun x y => by simp [freeSchema, leftWrapWeight]
  eval_recur := fun b s n => by simp [freeSchema, leftWrapWeight]
  wrap_subterm1 := fun x y => by show x < x + 1; omega
  transparent := rfl

theorem leftWrapCompositional_not_subterm2 : ¬ leftWrapCompositional.WrapSubterm2 := by
  intro h
  have h1 : (0 : Nat) + 1 > 1 := h 0 1
  omega

theorem leftWrapCompositional_orients :
    DupOrientsBy (S := freeSchema) (· < ·) leftWrapCompositional.eval := by
  intro b s n
  show leftWrapWeight s + 1 < leftWrapWeight s + 2
  omega

/-- **The second wrapper-subterm clause is necessary.** -/
theorem compositionalWrapSubterm2_deleted_barrier_false :
    ¬ ∀ M : CompositionalNoSubterm2, ¬ DupOrientsBy (S := freeSchema) (· < ·) M.eval :=
  fun hall => hall leftWrapCompositional leftWrapCompositional_orients

/-- The compositional class with `wrap_subterm1` removed. -/
structure CompositionalNoSubterm1 (S : StepDuplicatingSchema) where
  eval : S.T → Nat
  c_base : Nat
  c_succ : Nat → Nat
  c_wrap : Nat → Nat → Nat
  c_recur : Nat → Nat → Nat → Nat
  eval_base : eval S.base = c_base
  eval_succ : ∀ t, eval (S.succ t) = c_succ (eval t)
  eval_wrap : ∀ x y, eval (S.wrap x y) = c_wrap (eval x) (eval y)
  eval_recur : ∀ b s n, eval (S.recur b s n) = c_recur (eval b) (eval s) (eval n)
  wrap_subterm2 : ∀ x y, c_wrap x y > y

/-- **`wrap_subterm1` is not load-bearing.** -/
theorem compositional_wrapSubterm1_nonLoadBearing {S : StepDuplicatingSchema}
    (CM : CompositionalNoSubterm1 S) (h_transparent : CM.c_succ CM.c_base = CM.c_base) :
    ¬ DupOrientsBy (· < ·) CM.eval := by
  intro h
  have hspec : CM.eval (S.wrap S.base (S.recur S.base S.base S.base)) <
      CM.eval (S.recur S.base S.base (S.succ S.base)) := h S.base S.base S.base
  simp only [CM.eval_base, CM.eval_succ, CM.eval_wrap, CM.eval_recur, h_transparent] at hspec
  have hsub := CM.wrap_subterm2 CM.c_base (CM.c_recur CM.c_base CM.c_base CM.c_base)
  omega

end Compositional

/-! ## Affine family

Live theorems: `CellClassificationFamilies.no_affine_orients_dup_step_via_cells` (fields
`h_wrap_left_pos`, `h_wrap_right_pos`) and
`no_affine_primary_nonstrict_orients_dup_step_of_exists_pos` (the same fields and `hpos`).
The weighted variable-condition barrier `not_orients_dup_rule_weighted` (fields `wrap₁_pos`,
`wrap₂_pos`) is the coefficient form of the two wrapper positivity premises. -/

section Affine

/-- The affine class with `h_wrap_left_pos` removed. -/
structure AffineNoWrapLeftPos where
  eval : freeSchema.T → Nat
  c_base : Nat
  succ_bias : Nat
  succ_scale : Nat
  wrap_const : Nat
  wrap_left : Nat
  wrap_right : Nat
  recur_const : Nat
  recur_base : Nat
  recur_step : Nat
  recur_counter : Nat
  eval_base : eval freeSchema.base = c_base
  eval_succ : ∀ t, eval (freeSchema.succ t) = succ_bias + succ_scale * eval t
  eval_wrap : ∀ x y,
    eval (freeSchema.wrap x y) = wrap_const + wrap_left * eval x + wrap_right * eval y
  eval_recur : ∀ b s n, eval (freeSchema.recur b s n) =
    recur_const + recur_base * eval b + recur_step * eval s + recur_counter * eval n
  h_wrap_right_pos : 1 ≤ wrap_right

def AffineNoWrapLeftPos.restore (M : AffineNoWrapLeftPos) (h : 1 ≤ M.wrap_left) :
    AffineMeasure freeSchema where
  eval := M.eval
  c_base := M.c_base
  succ_bias := M.succ_bias
  succ_scale := M.succ_scale
  wrap_const := M.wrap_const
  wrap_left := M.wrap_left
  wrap_right := M.wrap_right
  recur_const := M.recur_const
  recur_base := M.recur_base
  recur_step := M.recur_step
  recur_counter := M.recur_counter
  eval_base := M.eval_base
  eval_succ := M.eval_succ
  eval_wrap := M.eval_wrap
  eval_recur := M.eval_recur
  h_wrap_left_pos := h
  h_wrap_right_pos := M.h_wrap_right_pos

/-- The affine class with `h_wrap_right_pos` removed. -/
structure AffineNoWrapRightPos where
  eval : freeSchema.T → Nat
  c_base : Nat
  succ_bias : Nat
  succ_scale : Nat
  wrap_const : Nat
  wrap_left : Nat
  wrap_right : Nat
  recur_const : Nat
  recur_base : Nat
  recur_step : Nat
  recur_counter : Nat
  eval_base : eval freeSchema.base = c_base
  eval_succ : ∀ t, eval (freeSchema.succ t) = succ_bias + succ_scale * eval t
  eval_wrap : ∀ x y,
    eval (freeSchema.wrap x y) = wrap_const + wrap_left * eval x + wrap_right * eval y
  eval_recur : ∀ b s n, eval (freeSchema.recur b s n) =
    recur_const + recur_base * eval b + recur_step * eval s + recur_counter * eval n
  h_wrap_left_pos : 1 ≤ wrap_left

def AffineNoWrapRightPos.restore (M : AffineNoWrapRightPos) (h : 1 ≤ M.wrap_right) :
    AffineMeasure freeSchema where
  eval := M.eval
  c_base := M.c_base
  succ_bias := M.succ_bias
  succ_scale := M.succ_scale
  wrap_const := M.wrap_const
  wrap_left := M.wrap_left
  wrap_right := M.wrap_right
  recur_const := M.recur_const
  recur_base := M.recur_base
  recur_step := M.recur_step
  recur_counter := M.recur_counter
  eval_base := M.eval_base
  eval_succ := M.eval_succ
  eval_wrap := M.eval_wrap
  eval_recur := M.eval_recur
  h_wrap_left_pos := M.h_wrap_left_pos
  h_wrap_right_pos := h

def counterAffine : AffineNoWrapLeftPos where
  eval := counterWeight
  c_base := 0
  succ_bias := 1
  succ_scale := 1
  wrap_const := 0
  wrap_left := 0
  wrap_right := 1
  recur_const := 0
  recur_base := 0
  recur_step := 0
  recur_counter := 1
  eval_base := rfl
  eval_succ := fun t => by simp [freeSchema, counterWeight]
  eval_wrap := fun x y => by simp [freeSchema, counterWeight]
  eval_recur := fun b s n => by simp [freeSchema, counterWeight]
  h_wrap_right_pos := le_refl 1

def stepAffine : AffineNoWrapRightPos where
  eval := stepWeight
  c_base := 0
  succ_bias := 0
  succ_scale := 1
  wrap_const := 0
  wrap_left := 1
  wrap_right := 0
  recur_const := 1
  recur_base := 0
  recur_step := 1
  recur_counter := 0
  eval_base := rfl
  eval_succ := fun t => by simp [freeSchema, stepWeight]
  eval_wrap := fun x y => by simp [freeSchema, stepWeight]
  eval_recur := fun b s n => by simp [freeSchema, stepWeight]
  h_wrap_left_pos := le_refl 1

theorem affineWrapLeftPositive_restored (M : AffineNoWrapLeftPos) (hd : 1 ≤ M.wrap_left) :
    ¬ DupOrientsBy (S := freeSchema) (· < ·) M.eval :=
  CellClassificationFamilies.no_affine_orients_dup_step_via_cells (M.restore hd)

theorem affineWrapRightPositive_restored (M : AffineNoWrapRightPos) (hd : 1 ≤ M.wrap_right) :
    ¬ DupOrientsBy (S := freeSchema) (· < ·) M.eval :=
  CellClassificationFamilies.no_affine_orients_dup_step_via_cells (M.restore hd)

/-- The weighted coefficient class with `wrap₁_pos` removed. -/
structure WrapFirstFreeCoefficients extends CoefficientAssignment where
  succ_pos : 1 ≤ succ
  wrap₂_pos : 1 ≤ wrap₂
  recur₁_pos : 1 ≤ recur₁
  recur₂_pos : 1 ≤ recur₂
  recur₃_pos : 1 ≤ recur₃

/-- The weighted coefficient class with `wrap₂_pos` removed. -/
structure WrapSecondFreeCoefficients extends CoefficientAssignment where
  succ_pos : 1 ≤ succ
  wrap₁_pos : 1 ≤ wrap₁
  recur₁_pos : 1 ≤ recur₁
  recur₂_pos : 1 ≤ recur₂
  recur₃_pos : 1 ≤ recur₃

/-- A comparator with the weighted variable condition for an arbitrary coefficient assignment. -/
structure CoefficientConditionOrder (A : CoefficientAssignment) where
  gt : STerm → STerm → Prop
  variable_condition :
    ∀ {x y : STerm} {v : SchemaVar}, gt x y → weightedCount A v y ≤ weightedCount A v x

/-- **Only the two wrapper coefficients are load-bearing in the weighted barrier.** The succ and
recursor positivity fields of `SubtermCoefficients` are not used. -/
theorem weighted_barrier_of_wrapPositivity (A : CoefficientAssignment) (h₁ : 1 ≤ A.wrap₁)
    (h₂ : 1 ≤ A.wrap₂) (O : CoefficientConditionOrder A) : ¬ O.gt dupSrc dupTgt := by
  intro h
  have hle := O.variable_condition (v := SchemaVar.s) h
  rw [weightedCount_dupSrc_s, weightedCount_dupTgt_s] at hle
  have hmul : A.recur₂ ≤ A.wrap₂ * A.recur₂ := Nat.le_mul_of_pos_left _ h₂
  omega

theorem wrapFirst_restored (C : WrapFirstFreeCoefficients) (h : 1 ≤ C.wrap₁)
    (O : CoefficientConditionOrder C.toCoefficientAssignment) : ¬ O.gt dupSrc dupTgt :=
  not_orients_dup_rule_weighted
    (C := (⟨C.toCoefficientAssignment, C.succ_pos, h, C.wrap₂_pos, C.recur₁_pos, C.recur₂_pos,
      C.recur₃_pos⟩ : SubtermCoefficients))
    { gt := O.gt, variable_condition := O.variable_condition }

theorem wrapSecond_restored (C : WrapSecondFreeCoefficients) (h : 1 ≤ C.wrap₂)
    (O : CoefficientConditionOrder C.toCoefficientAssignment) : ¬ O.gt dupSrc dupTgt :=
  not_orients_dup_rule_weighted
    (C := (⟨C.toCoefficientAssignment, C.succ_pos, C.wrap₁_pos, h, C.recur₁_pos, C.recur₂_pos,
      C.recur₃_pos⟩ : SubtermCoefficients))
    { gt := O.gt, variable_condition := O.variable_condition }

def wrapFirstFreeWitness : WrapFirstFreeCoefficients where
  toCoefficientAssignment := wrapFirstDegenerate
  succ_pos := by decide
  wrap₂_pos := by decide
  recur₁_pos := by decide
  recur₂_pos := by decide
  recur₃_pos := by decide

def wrapSecondFreeWitness : WrapSecondFreeCoefficients where
  toCoefficientAssignment := wrapSecondDegenerate
  succ_pos := by decide
  wrap₁_pos := by decide
  recur₁_pos := by decide
  recur₂_pos := by decide
  recur₃_pos := by decide

/-- The variable-condition comparator of a coefficient assignment. -/
def weightedConditionOrder (A : CoefficientAssignment) : CoefficientConditionOrder A where
  gt x y := ∀ v : SchemaVar, weightedCount A v y ≤ weightedCount A v x
  variable_condition := fun h => h _

/-- **Left wrapper positivity is necessary**, for the strict affine barrier, for the nonstrict
affine barrier, and, through `wrapFirst_positivity_necessary`, for the weighted barrier. -/
theorem affineWrapLeftPositive_deleted_barrier_false :
    (¬ ∀ M : AffineNoWrapLeftPos, ¬ DupOrientsBy (S := freeSchema) (· < ·) M.eval) ∧
    (¬ ∀ M : AffineNoWrapLeftPos, (∃ t : freeSchema.T, 1 ≤ M.eval t) →
      ¬ DupOrientsBy (S := freeSchema) (· ≤ ·) M.eval) ∧
    (¬ 1 ≤ wrapFirstFreeWitness.wrap₁) ∧
    (¬ ∀ (C : WrapFirstFreeCoefficients) (O : CoefficientConditionOrder C.toCoefficientAssignment),
      ¬ O.gt dupSrc dupTgt) := by
  refine ⟨fun hall => hall counterAffine counterWeight_orients, fun hall => ?_, ?_, fun hall => ?_⟩
  · exact hall counterAffine ⟨FreeTerm.succ FreeTerm.base, by decide⟩
      (fun b s n => Nat.le_of_lt (counterWeight_orients b s n))
  · have h0 := wrapFirst_positivity_necessary.1
    change ¬ 1 ≤ wrapFirstDegenerate.wrap₁
    omega
  · exact hall wrapFirstFreeWitness (weightedConditionOrder wrapFirstDegenerate)
      (fun v => wrapFirst_positivity_necessary.2 v)

/-- **Right wrapper positivity is necessary**, for the strict affine barrier, for the nonstrict
affine barrier, and, through `wrapSecond_positivity_necessary`, for the weighted barrier. -/
theorem affineWrapRightPositive_deleted_barrier_false :
    (¬ ∀ M : AffineNoWrapRightPos, ¬ DupOrientsBy (S := freeSchema) (· < ·) M.eval) ∧
    (¬ ∀ M : AffineNoWrapRightPos, (∃ t : freeSchema.T, 1 ≤ M.eval t) →
      ¬ DupOrientsBy (S := freeSchema) (· ≤ ·) M.eval) ∧
    (¬ 1 ≤ wrapSecondFreeWitness.wrap₂) ∧
    (¬ ∀ (C : WrapSecondFreeCoefficients) (O : CoefficientConditionOrder C.toCoefficientAssignment),
      ¬ O.gt dupSrc dupTgt) := by
  refine ⟨fun hall => hall stepAffine stepWeight_orients, fun hall => ?_, ?_, fun hall => ?_⟩
  · exact hall stepAffine ⟨FreeTerm.recur FreeTerm.base FreeTerm.base FreeTerm.base, by decide⟩
      (fun b s n => Nat.le_of_lt (stepWeight_orients b s n))
  · have h0 := wrapSecond_positivity_necessary.1
    change ¬ 1 ≤ wrapSecondDegenerate.wrap₂
    omega
  · exact hall wrapSecondFreeWitness (weightedConditionOrder wrapSecondDegenerate)
      (fun v => wrapSecond_positivity_necessary.2 v)

theorem affineNonstrictPositivity_restored (M : AffineMeasure freeSchema)
    (hd : ∃ t : freeSchema.T, 1 ≤ M.eval t) :
    ¬ DupOrientsBy (S := freeSchema) (· ≤ ·) M.eval :=
  no_affine_primary_nonstrict_orients_dup_step_of_exists_pos M hd

theorem zeroAffine_not_positive : ¬ ∃ t : freeSchema.T, 1 ≤ (zeroAffineMeasure freeSchema).eval t := by
  rintro ⟨t, ht⟩
  change 1 ≤ 0 at ht
  omega

/-- **The positivity premise of the nonstrict affine barrier is necessary**
(`nonstrict_affine_barrier_positivity_premise_necessary` at the free schema). -/
theorem affineNonstrictPositivity_deleted_barrier_false :
    ¬ ∀ M : AffineMeasure freeSchema, ¬ DupOrientsBy (S := freeSchema) (· ≤ ·) M.eval :=
  nonstrict_affine_barrier_positivity_premise_necessary freeSchema

end Affine

/-! ## Restricted quadratic family

Live theorem: `CellClassificationFamilies.no_quadratic_orients_dup_step_via_cells` (fields
`h_wrap_left_pos`, `h_wrap_right_pos`). -/

section Quadratic

structure QuadraticNoWrapLeftPos where
  eval : freeSchema.T → Nat
  c_base : Nat
  succ_bias : Nat
  succ_scale : Nat
  wrap_const : Nat
  wrap_left : Nat
  wrap_right : Nat
  recur_const : Nat
  recur_base : Nat
  recur_step : Nat
  recur_counter : Nat
  recur_quad : Nat
  eval_base : eval freeSchema.base = c_base
  eval_succ : ∀ t, eval (freeSchema.succ t) = succ_bias + succ_scale * eval t
  eval_wrap : ∀ x y,
    eval (freeSchema.wrap x y) = wrap_const + wrap_left * eval x + wrap_right * eval y
  eval_recur : ∀ b s n, eval (freeSchema.recur b s n) =
    recur_const + recur_base * eval b + recur_step * eval s + recur_counter * eval n +
      recur_quad * eval n * eval n
  h_wrap_right_pos : 1 ≤ wrap_right

def QuadraticNoWrapLeftPos.restore (M : QuadraticNoWrapLeftPos) (h : 1 ≤ M.wrap_left) :
    QuadraticCounterMeasure freeSchema where
  eval := M.eval
  c_base := M.c_base
  succ_bias := M.succ_bias
  succ_scale := M.succ_scale
  wrap_const := M.wrap_const
  wrap_left := M.wrap_left
  wrap_right := M.wrap_right
  recur_const := M.recur_const
  recur_base := M.recur_base
  recur_step := M.recur_step
  recur_counter := M.recur_counter
  recur_quad := M.recur_quad
  eval_base := M.eval_base
  eval_succ := M.eval_succ
  eval_wrap := M.eval_wrap
  eval_recur := M.eval_recur
  h_wrap_left_pos := h
  h_wrap_right_pos := M.h_wrap_right_pos

structure QuadraticNoWrapRightPos where
  eval : freeSchema.T → Nat
  c_base : Nat
  succ_bias : Nat
  succ_scale : Nat
  wrap_const : Nat
  wrap_left : Nat
  wrap_right : Nat
  recur_const : Nat
  recur_base : Nat
  recur_step : Nat
  recur_counter : Nat
  recur_quad : Nat
  eval_base : eval freeSchema.base = c_base
  eval_succ : ∀ t, eval (freeSchema.succ t) = succ_bias + succ_scale * eval t
  eval_wrap : ∀ x y,
    eval (freeSchema.wrap x y) = wrap_const + wrap_left * eval x + wrap_right * eval y
  eval_recur : ∀ b s n, eval (freeSchema.recur b s n) =
    recur_const + recur_base * eval b + recur_step * eval s + recur_counter * eval n +
      recur_quad * eval n * eval n
  h_wrap_left_pos : 1 ≤ wrap_left

def QuadraticNoWrapRightPos.restore (M : QuadraticNoWrapRightPos) (h : 1 ≤ M.wrap_right) :
    QuadraticCounterMeasure freeSchema where
  eval := M.eval
  c_base := M.c_base
  succ_bias := M.succ_bias
  succ_scale := M.succ_scale
  wrap_const := M.wrap_const
  wrap_left := M.wrap_left
  wrap_right := M.wrap_right
  recur_const := M.recur_const
  recur_base := M.recur_base
  recur_step := M.recur_step
  recur_counter := M.recur_counter
  recur_quad := M.recur_quad
  eval_base := M.eval_base
  eval_succ := M.eval_succ
  eval_wrap := M.eval_wrap
  eval_recur := M.eval_recur
  h_wrap_left_pos := M.h_wrap_left_pos
  h_wrap_right_pos := h

def counterQuadratic : QuadraticNoWrapLeftPos where
  eval := counterWeight
  c_base := 0
  succ_bias := 1
  succ_scale := 1
  wrap_const := 0
  wrap_left := 0
  wrap_right := 1
  recur_const := 0
  recur_base := 0
  recur_step := 0
  recur_counter := 1
  recur_quad := 0
  eval_base := rfl
  eval_succ := fun t => by simp [freeSchema, counterWeight]
  eval_wrap := fun x y => by simp [freeSchema, counterWeight]
  eval_recur := fun b s n => by simp [freeSchema, counterWeight]
  h_wrap_right_pos := le_refl 1

def stepQuadratic : QuadraticNoWrapRightPos where
  eval := stepWeight
  c_base := 0
  succ_bias := 0
  succ_scale := 1
  wrap_const := 0
  wrap_left := 1
  wrap_right := 0
  recur_const := 1
  recur_base := 0
  recur_step := 1
  recur_counter := 0
  recur_quad := 0
  eval_base := rfl
  eval_succ := fun t => by simp [freeSchema, stepWeight]
  eval_wrap := fun x y => by simp [freeSchema, stepWeight]
  eval_recur := fun b s n => by simp [freeSchema, stepWeight]
  h_wrap_left_pos := le_refl 1

theorem quadraticWrapLeftPositive_restored (M : QuadraticNoWrapLeftPos) (hd : 1 ≤ M.wrap_left) :
    ¬ DupOrientsBy (S := freeSchema) (· < ·) M.eval :=
  CellClassificationFamilies.no_quadratic_orients_dup_step_via_cells (M.restore hd)

theorem quadraticWrapRightPositive_restored (M : QuadraticNoWrapRightPos)
    (hd : 1 ≤ M.wrap_right) : ¬ DupOrientsBy (S := freeSchema) (· < ·) M.eval :=
  CellClassificationFamilies.no_quadratic_orients_dup_step_via_cells (M.restore hd)

theorem quadraticWrapLeftPositive_deleted_barrier_false :
    ¬ ∀ M : QuadraticNoWrapLeftPos, ¬ DupOrientsBy (S := freeSchema) (· < ·) M.eval :=
  fun hall => hall counterQuadratic counterWeight_orients

theorem quadraticWrapRightPositive_deleted_barrier_false :
    ¬ ∀ M : QuadraticNoWrapRightPos, ¬ DupOrientsBy (S := freeSchema) (· < ·) M.eval :=
  fun hall => hall stepQuadratic stepWeight_orients

end Quadratic

/-! ## Dominance families

Live theorems: `CellClassificationFamilies.no_crossTerm_orients_dup_step_via_cells`,
`..._multilinear_...`, `..._polynomial_...`. Each dominance premise is necessary through
`DominancePremiseSharpness`. Each wrapper positivity field is not load-bearing: the remaining
positivity field and orientation give unbounded values, and the dominance premise then fails
orientation at the base pair. -/

section Dominance

/-- Cross-term quadratic data without the two wrapper positivity fields. -/
structure CrossTermCore (S : StepDuplicatingSchema) where
  eval : S.T → Nat
  c_base : Nat
  succ_bias : Nat
  succ_scale : Nat
  wrap_const : Nat
  wrap_left : Nat
  wrap_right : Nat
  recur_const : Nat
  recur_base : Nat
  recur_step : Nat
  recur_counter : Nat
  recur_quad : Nat
  recur_cross : Nat
  eval_base : eval S.base = c_base
  eval_succ : ∀ t, eval (S.succ t) = succ_bias + succ_scale * eval t
  eval_wrap : ∀ x y, eval (S.wrap x y) = wrap_const + wrap_left * eval x + wrap_right * eval y
  eval_recur : ∀ b s n, eval (S.recur b s n) =
    recur_const + recur_base * eval b + recur_step * eval s + recur_counter * eval n +
      recur_quad * eval n * eval n + recur_cross * eval s * eval n

/-- `CrossTermBoundedAtBase` on the core data. -/
def CrossTermCore.BoundedAtBase {S : StepDuplicatingSchema} (M : CrossTermCore S) : Prop :=
  let succBase := M.succ_bias + M.succ_scale * M.c_base
  M.recur_step + M.recur_cross * succBase + 1 ≤
    M.wrap_left + M.wrap_right * (M.recur_step + M.recur_cross * M.c_base)

theorem CrossTermCore.eventually_fails {S : StepDuplicatingSchema} (M : CrossTermCore S)
    (hbounded : M.BoundedAtBase) :
    ∃ K : Nat, ∀ s : S.T, K ≤ M.eval s →
      M.eval (S.recur S.base s (S.succ S.base)) ≤ M.eval (S.wrap s (S.recur S.base s S.base)) := by
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
    simpa [CrossTermCore.BoundedAtBase, succBase, sourceCoeff, targetCoeff] using hbounded
  have hmul : (sourceCoeff + 1) * M.eval s ≤ targetCoeff * M.eval s :=
    Nat.mul_le_mul_right (M.eval s) hcoeff
  have hsource : sourceConst + sourceCoeff * M.eval s ≤ (sourceCoeff + 1) * M.eval s := by
    nlinarith
  rw [hsrc, htgt]
  calc sourceConst + sourceCoeff * M.eval s ≤ (sourceCoeff + 1) * M.eval s := hsource
    _ ≤ targetCoeff * M.eval s := hmul
    _ ≤ targetConst + targetCoeff * M.eval s := Nat.le_add_left _ _

structure CrossTermNoWrapLeftPos (S : StepDuplicatingSchema) extends CrossTermCore S where
  h_wrap_right_pos : 1 ≤ wrap_right

structure CrossTermNoWrapRightPos (S : StepDuplicatingSchema) extends CrossTermCore S where
  h_wrap_left_pos : 1 ≤ wrap_left

/-- **`h_wrap_left_pos` of the bounded cross-term class is not load-bearing.** -/
theorem crossTerm_wrapLeftPos_nonLoadBearing {S : StepDuplicatingSchema}
    (M : CrossTermNoWrapLeftPos S) (hbounded : M.BoundedAtBase) :
    ¬ DupOrientsBy (· < ·) M.eval := by
  intro h
  have hunb := unbounded_of_orients_rightRetaining M.eval (fun x y => by
    rw [M.eval_wrap]
    have := Nat.le_mul_of_pos_left (M.eval y) M.h_wrap_right_pos
    omega) h
  exact not_orients_of_unbounded_of_eventualFailure M.eval hunb
    (M.toCrossTermCore.eventually_fails hbounded) h

/-- **`h_wrap_right_pos` of the bounded cross-term class is not load-bearing.** -/
theorem crossTerm_wrapRightPos_nonLoadBearing {S : StepDuplicatingSchema}
    (M : CrossTermNoWrapRightPos S) (hbounded : M.BoundedAtBase) :
    ¬ DupOrientsBy (· < ·) M.eval := by
  intro h
  have hunb := unbounded_of_orients_leftRetaining M.eval (fun x y => by
    rw [M.eval_wrap]
    have := Nat.le_mul_of_pos_left (M.eval x) M.h_wrap_left_pos
    omega) h
  exact not_orients_of_unbounded_of_eventualFailure M.eval hunb
    (M.toCrossTermCore.eventually_fails hbounded) h

theorem crossTermBaseDominance_restored (M : CrossTermQuadraticMeasure freeSchema)
    (hd : CrossTermBoundedAtBase M) : ¬ DupOrientsBy (S := freeSchema) (· < ·) M.eval :=
  CellClassificationFamilies.no_crossTerm_orients_dup_step_via_cells M hd

/-- **Base dominance of the cross-term class is necessary.** -/
theorem crossTermBaseDominance_deleted_barrier_false :
    ¬ ∀ M : CrossTermQuadraticMeasure freeSchema,
      ¬ DupOrientsBy (S := freeSchema) (· < ·) M.eval :=
  fun hall => hall crossCoupledQuadratic three_dominance_premises_are_sharp.1.2

/-- Bounded multilinear data without the two wrapper positivity fields. -/
structure MultilinearCore (S : StepDuplicatingSchema) where
  eval : S.T → Nat
  c_base : Nat
  succ_bias : Nat
  succ_scale : Nat
  wrap_const : Nat
  wrap_left : Nat
  wrap_right : Nat
  recur_const : Nat
  recur_base : Nat
  recur_step : Nat
  recur_counter : Nat
  monomials : List MultilinearMonomial
  eval_base : eval S.base = c_base
  eval_succ : ∀ t, eval (S.succ t) = succ_bias + succ_scale * eval t
  eval_wrap : ∀ x y, eval (S.wrap x y) = wrap_const + wrap_left * eval x + wrap_right * eval y
  eval_recur : ∀ b s n, eval (S.recur b s n) =
    recur_const + recur_base * eval b + recur_step * eval s + recur_counter * eval n +
      monomialEvalSum monomials (eval b) (eval s) (eval n)

/-- `MultilinearDominatedAtBase` on the core data. -/
def MultilinearCore.DominatedAtBase {S : StepDuplicatingSchema} (M : MultilinearCore S) : Prop :=
  let succBase := M.succ_bias + M.succ_scale * M.c_base
  let sourceCoeff := M.recur_step + monomialStepCoeffSum M.monomials M.c_base succBase
  let targetCoeff :=
    M.wrap_left + M.wrap_right * (M.recur_step + monomialStepCoeffSum M.monomials M.c_base M.c_base)
  sourceCoeff + 1 ≤ targetCoeff

theorem MultilinearCore.eventually_fails {S : StepDuplicatingSchema} (M : MultilinearCore S)
    (hdom : M.DominatedAtBase) :
    ∃ K : Nat, ∀ s : S.T, K ≤ M.eval s →
      M.eval (S.recur S.base s (S.succ S.base)) ≤ M.eval (S.wrap s (S.recur S.base s S.base)) := by
  let succBase := M.succ_bias + M.succ_scale * M.c_base
  let sourceCoeff := M.recur_step + monomialStepCoeffSum M.monomials M.c_base succBase
  let targetCoeff :=
    M.wrap_left + M.wrap_right * (M.recur_step + monomialStepCoeffSum M.monomials M.c_base M.c_base)
  let sourceConst :=
    M.recur_const + M.recur_base * M.c_base + M.recur_counter * succBase +
      monomialConstSum M.monomials M.c_base succBase
  let targetConst :=
    M.wrap_const + M.wrap_right *
      (M.recur_const + M.recur_base * M.c_base + M.recur_counter * M.c_base +
        monomialConstSum M.monomials M.c_base M.c_base)
  refine ⟨sourceConst, ?_⟩
  intro s hs
  have hsourceMono := monomialSum_eq_constPart_add_stepCoeff M.monomials M.c_base (M.eval s)
    (M.succ_bias + M.succ_scale * M.c_base)
  have htargetMono := monomialSum_eq_constPart_add_stepCoeff M.monomials M.c_base (M.eval s)
    M.c_base
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
    simpa [MultilinearCore.DominatedAtBase, succBase, sourceCoeff, targetCoeff] using hdom
  have hmul : (sourceCoeff + 1) * M.eval s ≤ targetCoeff * M.eval s :=
    Nat.mul_le_mul_right (M.eval s) hcoeff
  have hsource : sourceConst + sourceCoeff * M.eval s ≤ (sourceCoeff + 1) * M.eval s := by
    nlinarith
  rw [hsrc, htgt]
  calc sourceConst + sourceCoeff * M.eval s ≤ (sourceCoeff + 1) * M.eval s := hsource
    _ ≤ targetCoeff * M.eval s := hmul
    _ ≤ targetConst + targetCoeff * M.eval s := Nat.le_add_left _ _

structure MultilinearNoWrapLeftPos (S : StepDuplicatingSchema) extends MultilinearCore S where
  h_wrap_right_pos : 1 ≤ wrap_right

structure MultilinearNoWrapRightPos (S : StepDuplicatingSchema) extends MultilinearCore S where
  h_wrap_left_pos : 1 ≤ wrap_left

/-- **`h_wrap_left_pos` of the bounded multilinear class is not load-bearing.** -/
theorem multilinear_wrapLeftPos_nonLoadBearing {S : StepDuplicatingSchema}
    (M : MultilinearNoWrapLeftPos S) (hdom : M.DominatedAtBase) :
    ¬ DupOrientsBy (· < ·) M.eval := by
  intro h
  have hunb := unbounded_of_orients_rightRetaining M.eval (fun x y => by
    rw [M.eval_wrap]
    have := Nat.le_mul_of_pos_left (M.eval y) M.h_wrap_right_pos
    omega) h
  exact not_orients_of_unbounded_of_eventualFailure M.eval hunb
    (M.toMultilinearCore.eventually_fails hdom) h

/-- **`h_wrap_right_pos` of the bounded multilinear class is not load-bearing.** -/
theorem multilinear_wrapRightPos_nonLoadBearing {S : StepDuplicatingSchema}
    (M : MultilinearNoWrapRightPos S) (hdom : M.DominatedAtBase) :
    ¬ DupOrientsBy (· < ·) M.eval := by
  intro h
  have hunb := unbounded_of_orients_leftRetaining M.eval (fun x y => by
    rw [M.eval_wrap]
    have := Nat.le_mul_of_pos_left (M.eval x) M.h_wrap_left_pos
    omega) h
  exact not_orients_of_unbounded_of_eventualFailure M.eval hunb
    (M.toMultilinearCore.eventually_fails hdom) h

theorem multilinearBaseDominance_restored (M : BoundedMultilinearMeasure freeSchema)
    (hd : MultilinearDominatedAtBase M) : ¬ DupOrientsBy (S := freeSchema) (· < ·) M.eval :=
  CellClassificationFamilies.no_multilinear_orients_dup_step_via_cells M hd

/-- **Base dominance of the multilinear class is necessary.** -/
theorem multilinearBaseDominance_deleted_barrier_false :
    ¬ ∀ M : BoundedMultilinearMeasure freeSchema,
      ¬ DupOrientsBy (S := freeSchema) (· < ·) M.eval :=
  fun hall => hall crossCoupledMultilinear three_dominance_premises_are_sharp.2.1.2

/-- Bounded polynomial data without the two wrapper positivity fields. -/
structure PolynomialCore (S : StepDuplicatingSchema) where
  eval : S.T → Nat
  c_base : Nat
  succ_bias : Nat
  succ_scale : Nat
  wrap_const : Nat
  wrap_left : Nat
  wrap_right : Nat
  recur_const : Nat
  recur_base : Nat
  recur_step : Nat
  recur_counter : Nat
  monomials : List PolynomialMonomial
  eval_base : eval S.base = c_base
  eval_succ : ∀ t, eval (S.succ t) = succ_bias + succ_scale * eval t
  eval_wrap : ∀ x y, eval (S.wrap x y) = wrap_const + wrap_left * eval x + wrap_right * eval y
  eval_recur : ∀ b s n, eval (S.recur b s n) =
    recur_const + recur_base * eval b + recur_step * eval s + recur_counter * eval n +
      (monomials.map (fun m => m.eval (eval b) (eval s) (eval n))).sum

def PolynomialCore.sourceFrozenAtBase {S : StepDuplicatingSchema} (M : PolynomialCore S)
    (Sval : Nat) : Nat :=
  let succBase := M.succ_bias + M.succ_scale * M.c_base
  M.recur_const + M.recur_base * M.c_base + M.recur_step * Sval + M.recur_counter * succBase +
    (M.monomials.map (fun m => m.eval M.c_base Sval succBase)).sum

def PolynomialCore.targetFrozenAtBase {S : StepDuplicatingSchema} (M : PolynomialCore S)
    (Sval : Nat) : Nat :=
  let inner :=
    M.recur_const + M.recur_base * M.c_base + M.recur_step * Sval + M.recur_counter * M.c_base +
      (M.monomials.map (fun m => m.eval M.c_base Sval M.c_base)).sum
  M.wrap_const + M.wrap_left * Sval + M.wrap_right * inner

/-- `EventuallyDominatedAtBase` on the core data. -/
def PolynomialCore.EventuallyDominatedAtBase {S : StepDuplicatingSchema} (M : PolynomialCore S) :
    Prop :=
  ∃ K : Nat, ∀ Sval : Nat, K ≤ Sval → M.sourceFrozenAtBase Sval ≤ M.targetFrozenAtBase Sval

theorem PolynomialCore.eventually_fails {S : StepDuplicatingSchema} (M : PolynomialCore S)
    (hdom : M.EventuallyDominatedAtBase) :
    ∃ K : Nat, ∀ s : S.T, K ≤ M.eval s →
      M.eval (S.recur S.base s (S.succ S.base)) ≤ M.eval (S.wrap s (S.recur S.base s S.base)) := by
  obtain ⟨K, hK⟩ := hdom
  refine ⟨K, ?_⟩
  intro s hs
  have hsrc :
      M.eval (S.recur S.base s (S.succ S.base)) = M.sourceFrozenAtBase (M.eval s) := by
    rw [M.eval_recur, M.eval_succ, M.eval_base]
    simp [PolynomialCore.sourceFrozenAtBase, Nat.add_assoc, Nat.add_left_comm,
      Nat.add_comm, Nat.mul_add]
  have htgt :
      M.eval (S.wrap s (S.recur S.base s S.base)) = M.targetFrozenAtBase (M.eval s) := by
    rw [M.eval_wrap, M.eval_recur, M.eval_base]
    simp [PolynomialCore.targetFrozenAtBase, Nat.add_assoc, Nat.add_left_comm,
      Nat.add_comm, Nat.mul_add]
  rw [hsrc, htgt]
  exact hK (M.eval s) hs

structure PolynomialNoWrapLeftPos (S : StepDuplicatingSchema) extends PolynomialCore S where
  h_wrap_right_pos : 1 ≤ wrap_right

structure PolynomialNoWrapRightPos (S : StepDuplicatingSchema) extends PolynomialCore S where
  h_wrap_left_pos : 1 ≤ wrap_left

/-- **`h_wrap_left_pos` of the bounded polynomial class is not load-bearing.** -/
theorem polynomial_wrapLeftPos_nonLoadBearing {S : StepDuplicatingSchema}
    (M : PolynomialNoWrapLeftPos S) (hdom : M.EventuallyDominatedAtBase) :
    ¬ DupOrientsBy (· < ·) M.eval := by
  intro h
  have hunb := unbounded_of_orients_rightRetaining M.eval (fun x y => by
    rw [M.eval_wrap]
    have := Nat.le_mul_of_pos_left (M.eval y) M.h_wrap_right_pos
    omega) h
  exact not_orients_of_unbounded_of_eventualFailure M.eval hunb
    (M.toPolynomialCore.eventually_fails hdom) h

/-- **`h_wrap_right_pos` of the bounded polynomial class is not load-bearing.** -/
theorem polynomial_wrapRightPos_nonLoadBearing {S : StepDuplicatingSchema}
    (M : PolynomialNoWrapRightPos S) (hdom : M.EventuallyDominatedAtBase) :
    ¬ DupOrientsBy (· < ·) M.eval := by
  intro h
  have hunb := unbounded_of_orients_leftRetaining M.eval (fun x y => by
    rw [M.eval_wrap]
    have := Nat.le_mul_of_pos_left (M.eval x) M.h_wrap_left_pos
    omega) h
  exact not_orients_of_unbounded_of_eventualFailure M.eval hunb
    (M.toPolynomialCore.eventually_fails hdom) h

theorem polynomialEventualDominance_restored (M : BoundedPolynomialMeasure freeSchema)
    (hd : EventuallyDominatedAtBase M) : ¬ DupOrientsBy (S := freeSchema) (· < ·) M.eval :=
  CellClassificationFamilies.no_polynomial_orients_dup_step_via_cells M hd

/-- **Eventual base dominance of the polynomial class is necessary.** -/
theorem polynomialEventualDominance_deleted_barrier_false :
    ¬ ∀ M : BoundedPolynomialMeasure freeSchema,
      ¬ DupOrientsBy (S := freeSchema) (· < ·) M.eval :=
  fun hall => hall crossCoupledPolynomial three_dominance_premises_are_sharp.2.2.2

end Dominance

/-! ## Max-plus and max-depth families

Live theorems: `CellClassificationFamilies.no_max_orients_dup_step_via_cells` (field
`h_wrap_right_pos`) and `no_maxDepth_orients_dup_step` (field `h_wrap_pos`). Neither field is
load-bearing, so these two families have no hypothesis slot. -/

section MaxFamilies

structure MaxNoWrapRightPos (S : StepDuplicatingSchema) where
  eval : S.T → Nat
  c_base : Nat
  succ_const : Nat
  wrap_const : Nat
  wrap_left : Nat
  wrap_right : Nat
  recur_const : Nat
  recur_base : Nat
  recur_step : Nat
  recur_counter : Nat
  eval_base : eval S.base = c_base
  eval_succ : ∀ t, eval (S.succ t) = succ_const + eval t
  eval_wrap : ∀ x y,
    eval (S.wrap x y) = wrap_const + max (wrap_left + eval x) (wrap_right + eval y)
  eval_recur : ∀ b s n, eval (S.recur b s n) =
    recur_const + max (recur_base + eval b) (max (recur_step + eval s) (recur_counter + eval n))

theorem MaxNoWrapRightPos.eval_succIter {S : StepDuplicatingSchema} (M : MaxNoWrapRightPos S)
    (k : Nat) : M.eval (succIter S k) = M.c_base + k * M.succ_const := by
  induction k with
  | zero => simp [succIter, M.eval_base]
  | succ k ih =>
      rw [succIter, M.eval_succ, ih, Nat.succ_mul]
      omega

/-- **`h_wrap_right_pos` of the max-plus class is not load-bearing.** The wrapper already keeps
the recursive call at offset zero, and a long enough successor chain makes the counter branch
invisible. -/
theorem max_wrapRightPos_nonLoadBearing {S : StepDuplicatingSchema} (M : MaxNoWrapRightPos S) :
    ¬ DupOrientsBy (· < ·) M.eval := by
  intro h
  by_cases hsc : M.succ_const = 0
  · have hs : M.eval (S.wrap S.base (S.recur S.base S.base S.base)) <
        M.eval (S.recur S.base S.base (S.succ S.base)) := h S.base S.base S.base
    simp only [M.eval_wrap, M.eval_recur, M.eval_succ, M.eval_base, hsc] at hs
    omega
  · have hval := M.eval_succIter (M.recur_counter + 1)
    have h1 : M.recur_counter ≤ M.recur_counter * M.succ_const :=
      Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hsc)
    have h2 : (M.recur_counter + 1) * M.succ_const =
        M.recur_counter * M.succ_const + M.succ_const := by ring
    have hs : M.eval (S.wrap (succIter S (M.recur_counter + 1))
          (S.recur S.base (succIter S (M.recur_counter + 1)) S.base)) <
        M.eval (S.recur S.base (succIter S (M.recur_counter + 1)) (S.succ S.base)) :=
      h S.base (succIter S (M.recur_counter + 1)) S.base
    simp only [M.eval_wrap, M.eval_recur, M.eval_succ, M.eval_base, hval] at hs
    omega

structure MaxDepthNoWrapPos (S : StepDuplicatingSchema) where
  eval : S.T → Nat
  c_base : Nat
  c_succ : Nat
  c_wrap : Nat
  c_recur : Nat
  eval_base : eval S.base = c_base
  eval_succ : ∀ t, eval (S.succ t) = c_succ + eval t
  eval_wrap : ∀ x y, eval (S.wrap x y) = c_wrap + max (eval x) (eval y)
  eval_recur : ∀ b s n, eval (S.recur b s n) = c_recur + max (max (eval b) (eval s)) (eval n)

/-- **`h_wrap_pos` of the max-depth class is not load-bearing.** The instance
`(base, succ base, base)` already fails. -/
theorem maxDepth_wrapPos_nonLoadBearing {S : StepDuplicatingSchema} (M : MaxDepthNoWrapPos S) :
    ¬ DupOrientsBy (· < ·) M.eval := by
  intro h
  have hs : M.eval (S.wrap (S.succ S.base) (S.recur S.base (S.succ S.base) S.base)) <
      M.eval (S.recur S.base (S.succ S.base) (S.succ S.base)) := h S.base (S.succ S.base) S.base
  simp only [M.eval_wrap, M.eval_recur, M.eval_succ, M.eval_base] at hs
  omega

end MaxFamilies

/-! ## Tracked-primary pair family

Live theorems: `CellClassificationFamilies.no_matrix2_orients_dup_step_via_cells` (fields
`h_wrap_left1_pos`, `h_wrap_right1_pos`) and `no_matrix2_lex_orients_dup_step_of_fst_pos` (the
same fields and `hpos`). -/

section Pair

structure PairNoWrapLeftPos where
  eval : freeSchema.T → Vec2
  c_base1 : Nat
  c_base2 : Nat
  succ_bias1 : Nat
  succ_scale1 : Nat
  succ_bias2 : Nat
  succ_scale2 : Nat
  wrap_const1 : Nat
  wrap_left1 : Nat
  wrap_right1 : Nat
  wrap_const2 : Nat
  wrap_left2 : Nat
  wrap_right2 : Nat
  recur_const1 : Nat
  recur_base1 : Nat
  recur_step1 : Nat
  recur_counter1 : Nat
  recur_const2 : Nat
  recur_base2 : Nat
  recur_step2 : Nat
  recur_counter2 : Nat
  eval_base : eval freeSchema.base = (c_base1, c_base2)
  eval_succ1 : ∀ t, (eval (freeSchema.succ t)).1 = succ_bias1 + succ_scale1 * (eval t).1
  eval_succ2 : ∀ t, (eval (freeSchema.succ t)).2 = succ_bias2 + succ_scale2 * (eval t).2
  eval_wrap1 : ∀ x y, (eval (freeSchema.wrap x y)).1 =
    wrap_const1 + wrap_left1 * (eval x).1 + wrap_right1 * (eval y).1
  eval_wrap2 : ∀ x y, (eval (freeSchema.wrap x y)).2 =
    wrap_const2 + wrap_left2 * (eval x).2 + wrap_right2 * (eval y).2
  eval_recur1 : ∀ b s n, (eval (freeSchema.recur b s n)).1 =
    recur_const1 + recur_base1 * (eval b).1 + recur_step1 * (eval s).1 +
      recur_counter1 * (eval n).1
  eval_recur2 : ∀ b s n, (eval (freeSchema.recur b s n)).2 =
    recur_const2 + recur_base2 * (eval b).2 + recur_step2 * (eval s).2 +
      recur_counter2 * (eval n).2
  h_wrap_right1_pos : 1 ≤ wrap_right1

structure PairNoWrapRightPos where
  eval : freeSchema.T → Vec2
  c_base1 : Nat
  c_base2 : Nat
  succ_bias1 : Nat
  succ_scale1 : Nat
  succ_bias2 : Nat
  succ_scale2 : Nat
  wrap_const1 : Nat
  wrap_left1 : Nat
  wrap_right1 : Nat
  wrap_const2 : Nat
  wrap_left2 : Nat
  wrap_right2 : Nat
  recur_const1 : Nat
  recur_base1 : Nat
  recur_step1 : Nat
  recur_counter1 : Nat
  recur_const2 : Nat
  recur_base2 : Nat
  recur_step2 : Nat
  recur_counter2 : Nat
  eval_base : eval freeSchema.base = (c_base1, c_base2)
  eval_succ1 : ∀ t, (eval (freeSchema.succ t)).1 = succ_bias1 + succ_scale1 * (eval t).1
  eval_succ2 : ∀ t, (eval (freeSchema.succ t)).2 = succ_bias2 + succ_scale2 * (eval t).2
  eval_wrap1 : ∀ x y, (eval (freeSchema.wrap x y)).1 =
    wrap_const1 + wrap_left1 * (eval x).1 + wrap_right1 * (eval y).1
  eval_wrap2 : ∀ x y, (eval (freeSchema.wrap x y)).2 =
    wrap_const2 + wrap_left2 * (eval x).2 + wrap_right2 * (eval y).2
  eval_recur1 : ∀ b s n, (eval (freeSchema.recur b s n)).1 =
    recur_const1 + recur_base1 * (eval b).1 + recur_step1 * (eval s).1 +
      recur_counter1 * (eval n).1
  eval_recur2 : ∀ b s n, (eval (freeSchema.recur b s n)).2 =
    recur_const2 + recur_base2 * (eval b).2 + recur_step2 * (eval s).2 +
      recur_counter2 * (eval n).2
  h_wrap_left1_pos : 1 ≤ wrap_left1

def PairNoWrapLeftPos.restore (M : PairNoWrapLeftPos) (h : 1 ≤ M.wrap_left1) :
    MatrixMeasure2 freeSchema where
  eval := M.eval
  c_base1 := M.c_base1
  c_base2 := M.c_base2
  succ_bias1 := M.succ_bias1
  succ_scale1 := M.succ_scale1
  succ_bias2 := M.succ_bias2
  succ_scale2 := M.succ_scale2
  wrap_const1 := M.wrap_const1
  wrap_left1 := M.wrap_left1
  wrap_right1 := M.wrap_right1
  wrap_const2 := M.wrap_const2
  wrap_left2 := M.wrap_left2
  wrap_right2 := M.wrap_right2
  recur_const1 := M.recur_const1
  recur_base1 := M.recur_base1
  recur_step1 := M.recur_step1
  recur_counter1 := M.recur_counter1
  recur_const2 := M.recur_const2
  recur_base2 := M.recur_base2
  recur_step2 := M.recur_step2
  recur_counter2 := M.recur_counter2
  eval_base := M.eval_base
  eval_succ1 := M.eval_succ1
  eval_succ2 := M.eval_succ2
  eval_wrap1 := M.eval_wrap1
  eval_wrap2 := M.eval_wrap2
  eval_recur1 := M.eval_recur1
  eval_recur2 := M.eval_recur2
  h_wrap_left1_pos := h
  h_wrap_right1_pos := M.h_wrap_right1_pos

def PairNoWrapRightPos.restore (M : PairNoWrapRightPos) (h : 1 ≤ M.wrap_right1) :
    MatrixMeasure2 freeSchema where
  eval := M.eval
  c_base1 := M.c_base1
  c_base2 := M.c_base2
  succ_bias1 := M.succ_bias1
  succ_scale1 := M.succ_scale1
  succ_bias2 := M.succ_bias2
  succ_scale2 := M.succ_scale2
  wrap_const1 := M.wrap_const1
  wrap_left1 := M.wrap_left1
  wrap_right1 := M.wrap_right1
  wrap_const2 := M.wrap_const2
  wrap_left2 := M.wrap_left2
  wrap_right2 := M.wrap_right2
  recur_const1 := M.recur_const1
  recur_base1 := M.recur_base1
  recur_step1 := M.recur_step1
  recur_counter1 := M.recur_counter1
  recur_const2 := M.recur_const2
  recur_base2 := M.recur_base2
  recur_step2 := M.recur_step2
  recur_counter2 := M.recur_counter2
  eval_base := M.eval_base
  eval_succ1 := M.eval_succ1
  eval_succ2 := M.eval_succ2
  eval_wrap1 := M.eval_wrap1
  eval_wrap2 := M.eval_wrap2
  eval_recur1 := M.eval_recur1
  eval_recur2 := M.eval_recur2
  h_wrap_left1_pos := M.h_wrap_left1_pos
  h_wrap_right1_pos := h

def counterPair : PairNoWrapLeftPos where
  eval := fun t => (counterWeight t, counterWeight t)
  c_base1 := 0
  c_base2 := 0
  succ_bias1 := 1
  succ_scale1 := 1
  succ_bias2 := 1
  succ_scale2 := 1
  wrap_const1 := 0
  wrap_left1 := 0
  wrap_right1 := 1
  wrap_const2 := 0
  wrap_left2 := 0
  wrap_right2 := 1
  recur_const1 := 0
  recur_base1 := 0
  recur_step1 := 0
  recur_counter1 := 1
  recur_const2 := 0
  recur_base2 := 0
  recur_step2 := 0
  recur_counter2 := 1
  eval_base := rfl
  eval_succ1 := fun t => by simp [freeSchema, counterWeight]
  eval_succ2 := fun t => by simp [freeSchema, counterWeight]
  eval_wrap1 := fun x y => by simp [freeSchema, counterWeight]
  eval_wrap2 := fun x y => by simp [freeSchema, counterWeight]
  eval_recur1 := fun b s n => by simp [freeSchema, counterWeight]
  eval_recur2 := fun b s n => by simp [freeSchema, counterWeight]
  h_wrap_right1_pos := le_refl 1

def stepCounterPair : PairNoWrapRightPos where
  eval := fun t => (stepWeight t, counterWeight t)
  c_base1 := 0
  c_base2 := 0
  succ_bias1 := 0
  succ_scale1 := 1
  succ_bias2 := 1
  succ_scale2 := 1
  wrap_const1 := 0
  wrap_left1 := 1
  wrap_right1 := 0
  wrap_const2 := 0
  wrap_left2 := 0
  wrap_right2 := 1
  recur_const1 := 1
  recur_base1 := 0
  recur_step1 := 1
  recur_counter1 := 0
  recur_const2 := 0
  recur_base2 := 0
  recur_step2 := 0
  recur_counter2 := 1
  eval_base := rfl
  eval_succ1 := fun t => by simp [freeSchema, stepWeight]
  eval_succ2 := fun t => by simp [freeSchema, counterWeight]
  eval_wrap1 := fun x y => by simp [freeSchema, stepWeight]
  eval_wrap2 := fun x y => by simp [freeSchema, counterWeight]
  eval_recur1 := fun b s n => by simp [freeSchema, stepWeight]
  eval_recur2 := fun b s n => by simp [freeSchema, counterWeight]
  h_wrap_left1_pos := le_refl 1

theorem counterPair_orients : DupOrientsBy (S := freeSchema) PairLt counterPair.eval :=
  fun b s n => ⟨counterWeight_orients b s n, counterWeight_orients b s n⟩

theorem stepCounterPair_orients : DupOrientsBy (S := freeSchema) PairLt stepCounterPair.eval :=
  fun b s n => ⟨stepWeight_orients b s n, counterWeight_orients b s n⟩

theorem pairWrapLeftPositive_restored (M : PairNoWrapLeftPos) (hd : 1 ≤ M.wrap_left1) :
    ¬ DupOrientsBy (S := freeSchema) PairLt M.eval :=
  CellClassificationFamilies.no_matrix2_orients_dup_step_via_cells (M.restore hd)

theorem pairWrapRightPositive_restored (M : PairNoWrapRightPos) (hd : 1 ≤ M.wrap_right1) :
    ¬ DupOrientsBy (S := freeSchema) PairLt M.eval :=
  CellClassificationFamilies.no_matrix2_orients_dup_step_via_cells (M.restore hd)

/-- **`h_wrap_left1_pos` is necessary** for the componentwise pair barrier and for the
lexicographic pair barrier. -/
theorem pairWrapLeftPositive_deleted_barrier_false :
    (¬ ∀ M : PairNoWrapLeftPos, ¬ DupOrientsBy (S := freeSchema) PairLt M.eval) ∧
    (∀ M : PairNoWrapLeftPos, 1 ≤ M.wrap_left1 → (∃ t : freeSchema.T, 1 ≤ (M.eval t).1) →
      ¬ DupOrientsBy (S := freeSchema) PairLexLt M.eval) ∧
    (¬ ∀ M : PairNoWrapLeftPos, (∃ t : freeSchema.T, 1 ≤ (M.eval t).1) →
      ¬ DupOrientsBy (S := freeSchema) PairLexLt M.eval) :=
  ⟨fun hall => hall counterPair counterPair_orients,
    fun M hd hpos => no_matrix2_lex_orients_dup_step_of_fst_pos (M.restore hd) hpos,
    fun hall => hall counterPair ⟨FreeTerm.succ FreeTerm.base, by decide⟩
      (fun b s n => Or.inl (counterPair_orients b s n).1)⟩

/-- **`h_wrap_right1_pos` is necessary** for the componentwise pair barrier and for the
lexicographic pair barrier. -/
theorem pairWrapRightPositive_deleted_barrier_false :
    (¬ ∀ M : PairNoWrapRightPos, ¬ DupOrientsBy (S := freeSchema) PairLt M.eval) ∧
    (∀ M : PairNoWrapRightPos, 1 ≤ M.wrap_right1 → (∃ t : freeSchema.T, 1 ≤ (M.eval t).1) →
      ¬ DupOrientsBy (S := freeSchema) PairLexLt M.eval) ∧
    (¬ ∀ M : PairNoWrapRightPos, (∃ t : freeSchema.T, 1 ≤ (M.eval t).1) →
      ¬ DupOrientsBy (S := freeSchema) PairLexLt M.eval) :=
  ⟨fun hall => hall stepCounterPair stepCounterPair_orients,
    fun M hd hpos => no_matrix2_lex_orients_dup_step_of_fst_pos (M.restore hd) hpos,
    fun hall => hall stepCounterPair
      ⟨FreeTerm.recur FreeTerm.base FreeTerm.base FreeTerm.base, by decide⟩
      (fun b s n => Or.inl (stepCounterPair_orients b s n).1)⟩

/-- Pair whose first coordinate is zero and whose second coordinate is the counter. -/
def zeroFirstPair : MatrixMeasure2 freeSchema where
  eval := fun t => (0, counterWeight t)
  c_base1 := 0
  c_base2 := 0
  succ_bias1 := 0
  succ_scale1 := 0
  succ_bias2 := 1
  succ_scale2 := 1
  wrap_const1 := 0
  wrap_left1 := 1
  wrap_right1 := 1
  wrap_const2 := 0
  wrap_left2 := 0
  wrap_right2 := 1
  recur_const1 := 0
  recur_base1 := 0
  recur_step1 := 0
  recur_counter1 := 0
  recur_const2 := 0
  recur_base2 := 0
  recur_step2 := 0
  recur_counter2 := 1
  eval_base := rfl
  eval_succ1 := fun t => by simp
  eval_succ2 := fun t => by simp [freeSchema, counterWeight]
  eval_wrap1 := fun x y => by simp
  eval_wrap2 := fun x y => by simp [freeSchema, counterWeight]
  eval_recur1 := fun b s n => by simp
  eval_recur2 := fun b s n => by simp [freeSchema, counterWeight]
  h_wrap_left1_pos := le_refl 1
  h_wrap_right1_pos := le_refl 1

theorem zeroFirstPair_not_positive : ¬ ∃ t : freeSchema.T, 1 ≤ (zeroFirstPair.eval t).1 := by
  rintro ⟨t, ht⟩
  change 1 ≤ 0 at ht
  omega

theorem zeroFirstPair_orients : DupOrientsBy (S := freeSchema) PairLexLt zeroFirstPair.eval :=
  fun b s n => Or.inr ⟨rfl, counterWeight_orients b s n⟩

theorem pairLexFirstPositive_restored (M : MatrixMeasure2 freeSchema)
    (hd : ∃ t : freeSchema.T, 1 ≤ (M.eval t).1) :
    ¬ DupOrientsBy (S := freeSchema) PairLexLt M.eval :=
  no_matrix2_lex_orients_dup_step_of_fst_pos M hd

/-- **First-coordinate positivity of the lexicographic pair barrier is necessary.** -/
theorem pairLexFirstPositive_deleted_barrier_false :
    ¬ ∀ M : MatrixMeasure2 freeSchema, ¬ DupOrientsBy (S := freeSchema) PairLexLt M.eval :=
  fun hall => hall zeroFirstPair zeroFirstPair_orients

end Pair

/-! ## Tracked-primary lexicographic family

Live theorem: `CellClassificationFamilies.no_matrixLexD_orients_dup_step_via_cells` (fields
`h_wrap_left_pos`, `h_wrap_right_pos`, premise `hpos`), used at dimension `1 + 1`. The
field-matrix companion is `tracked_nonincreasing_positivity_hypothesis_necessary`. -/

section Lex

/-- A two-coordinate vector with a given primary and second coordinate. -/
def primaryEmbed (u v : Nat) : Fin (1 + 1) → Nat := fun i => if i.val = 0 then u else v

theorem primaryEmbed_primary (u v : Nat) : primaryEmbed u v (primaryIdx 1) = u := if_pos rfl

theorem primaryEmbed_zero (u v : Nat) : primaryEmbed u v 0 = u := if_pos rfl

theorem primaryEmbed_vecLexLt_primary {u v w z : Nat} (h : u < w) :
    VecLexLt (primaryEmbed u v) (primaryEmbed w z) := by
  refine ⟨primaryIdx 1, ?_, ?_⟩
  · intro j hj
    simp [primaryIdx] at hj
  · simpa [primaryEmbed, primaryIdx] using h

theorem primaryEmbed_vecLexLt_second {u v w z : Nat} (hprim : u = w) (hsec : v < z) :
    VecLexLt (primaryEmbed u v) (primaryEmbed w z) := by
  refine ⟨⟨1, by omega⟩, ?_, ?_⟩
  · intro j hj
    rw [Fin.val_mk] at hj
    have hj0 : j.val = 0 := by omega
    simp [primaryEmbed, hj0, hprim]
  · simpa [primaryEmbed] using hsec

structure LexNoWrapLeftPos where
  eval : freeSchema.T → Fin (1 + 1) → Nat
  c_base : Nat
  succ_bias : Nat
  succ_scale : Nat
  wrap_const : Nat
  wrap_left : Nat
  wrap_right : Nat
  recur_const : Nat
  recur_base : Nat
  recur_step : Nat
  recur_counter : Nat
  eval_base : eval freeSchema.base (primaryIdx 1) = c_base
  eval_succ : ∀ t, eval (freeSchema.succ t) (primaryIdx 1) =
    succ_bias + succ_scale * eval t (primaryIdx 1)
  eval_wrap : ∀ x y, eval (freeSchema.wrap x y) (primaryIdx 1) =
    wrap_const + wrap_left * eval x (primaryIdx 1) + wrap_right * eval y (primaryIdx 1)
  eval_recur : ∀ b s n, eval (freeSchema.recur b s n) (primaryIdx 1) =
    recur_const + recur_base * eval b (primaryIdx 1) + recur_step * eval s (primaryIdx 1) +
      recur_counter * eval n (primaryIdx 1)
  h_wrap_right_pos : 1 ≤ wrap_right
  primary_pos : ∃ t : freeSchema.T, 1 ≤ eval t (primaryIdx 1)

structure LexNoWrapRightPos where
  eval : freeSchema.T → Fin (1 + 1) → Nat
  c_base : Nat
  succ_bias : Nat
  succ_scale : Nat
  wrap_const : Nat
  wrap_left : Nat
  wrap_right : Nat
  recur_const : Nat
  recur_base : Nat
  recur_step : Nat
  recur_counter : Nat
  eval_base : eval freeSchema.base (primaryIdx 1) = c_base
  eval_succ : ∀ t, eval (freeSchema.succ t) (primaryIdx 1) =
    succ_bias + succ_scale * eval t (primaryIdx 1)
  eval_wrap : ∀ x y, eval (freeSchema.wrap x y) (primaryIdx 1) =
    wrap_const + wrap_left * eval x (primaryIdx 1) + wrap_right * eval y (primaryIdx 1)
  eval_recur : ∀ b s n, eval (freeSchema.recur b s n) (primaryIdx 1) =
    recur_const + recur_base * eval b (primaryIdx 1) + recur_step * eval s (primaryIdx 1) +
      recur_counter * eval n (primaryIdx 1)
  h_wrap_left_pos : 1 ≤ wrap_left
  primary_pos : ∃ t : freeSchema.T, 1 ≤ eval t (primaryIdx 1)

def LexNoWrapLeftPos.restore (M : LexNoWrapLeftPos) (h : 1 ≤ M.wrap_left) :
    MatrixLexMeasureD freeSchema 1 where
  eval := M.eval
  c_base := M.c_base
  succ_bias := M.succ_bias
  succ_scale := M.succ_scale
  wrap_const := M.wrap_const
  wrap_left := M.wrap_left
  wrap_right := M.wrap_right
  recur_const := M.recur_const
  recur_base := M.recur_base
  recur_step := M.recur_step
  recur_counter := M.recur_counter
  eval_base := M.eval_base
  eval_succ := M.eval_succ
  eval_wrap := M.eval_wrap
  eval_recur := M.eval_recur
  h_wrap_left_pos := h
  h_wrap_right_pos := M.h_wrap_right_pos

def LexNoWrapRightPos.restore (M : LexNoWrapRightPos) (h : 1 ≤ M.wrap_right) :
    MatrixLexMeasureD freeSchema 1 where
  eval := M.eval
  c_base := M.c_base
  succ_bias := M.succ_bias
  succ_scale := M.succ_scale
  wrap_const := M.wrap_const
  wrap_left := M.wrap_left
  wrap_right := M.wrap_right
  recur_const := M.recur_const
  recur_base := M.recur_base
  recur_step := M.recur_step
  recur_counter := M.recur_counter
  eval_base := M.eval_base
  eval_succ := M.eval_succ
  eval_wrap := M.eval_wrap
  eval_recur := M.eval_recur
  h_wrap_left_pos := M.h_wrap_left_pos
  h_wrap_right_pos := h

def counterLex : LexNoWrapLeftPos where
  eval := fun t => primaryEmbed (counterWeight t) 0
  c_base := 0
  succ_bias := 1
  succ_scale := 1
  wrap_const := 0
  wrap_left := 0
  wrap_right := 1
  recur_const := 0
  recur_base := 0
  recur_step := 0
  recur_counter := 1
  eval_base := primaryEmbed_primary _ _
  eval_succ := fun t => by simp [primaryEmbed_zero, freeSchema, counterWeight]
  eval_wrap := fun x y => by simp [primaryEmbed_zero, freeSchema, counterWeight]
  eval_recur := fun b s n => by simp [primaryEmbed_zero, freeSchema, counterWeight]
  h_wrap_right_pos := le_refl 1
  primary_pos := ⟨FreeTerm.succ FreeTerm.base, by
    simp [primaryEmbed_zero, counterWeight]⟩

def stepLex : LexNoWrapRightPos where
  eval := fun t => primaryEmbed (stepWeight t) 0
  c_base := 0
  succ_bias := 0
  succ_scale := 1
  wrap_const := 0
  wrap_left := 1
  wrap_right := 0
  recur_const := 1
  recur_base := 0
  recur_step := 1
  recur_counter := 0
  eval_base := primaryEmbed_primary _ _
  eval_succ := fun t => by simp [primaryEmbed_zero, freeSchema, stepWeight]
  eval_wrap := fun x y => by simp [primaryEmbed_zero, freeSchema, stepWeight]
  eval_recur := fun b s n => by simp [primaryEmbed_zero, freeSchema, stepWeight]
  h_wrap_left_pos := le_refl 1
  primary_pos := ⟨FreeTerm.recur FreeTerm.base FreeTerm.base FreeTerm.base, by
    simp [primaryEmbed_zero, stepWeight]⟩

theorem counterLex_orients : DupOrientsBy (S := freeSchema) VecLexLt counterLex.eval :=
  fun b s n => primaryEmbed_vecLexLt_primary (counterWeight_orients b s n)

theorem stepLex_orients : DupOrientsBy (S := freeSchema) VecLexLt stepLex.eval :=
  fun b s n => primaryEmbed_vecLexLt_primary (stepWeight_orients b s n)

/-- Lexicographic measure with zero primary coordinate and the counter in second position. -/
def zeroPrimaryLex : MatrixLexMeasureD freeSchema 1 where
  eval := fun t => primaryEmbed 0 (counterWeight t)
  c_base := 0
  succ_bias := 0
  succ_scale := 0
  wrap_const := 0
  wrap_left := 1
  wrap_right := 1
  recur_const := 0
  recur_base := 0
  recur_step := 0
  recur_counter := 0
  eval_base := primaryEmbed_primary _ _
  eval_succ := fun t => by simp [primaryEmbed_zero]
  eval_wrap := fun x y => by simp [primaryEmbed_zero]
  eval_recur := fun b s n => by simp [primaryEmbed_zero]
  h_wrap_left_pos := le_refl 1
  h_wrap_right_pos := le_refl 1

theorem zeroPrimaryLex_not_positive :
    ¬ ∃ t : freeSchema.T, 1 ≤ zeroPrimaryLex.eval t (primaryIdx 1) := by
  rintro ⟨t, ht⟩
  have h0 : zeroPrimaryLex.eval t (primaryIdx 1) = 0 := primaryEmbed_primary 0 (counterWeight t)
  omega

theorem zeroPrimaryLex_orients : DupOrientsBy (S := freeSchema) VecLexLt zeroPrimaryLex.eval :=
  fun b s n => primaryEmbed_vecLexLt_second rfl (counterWeight_orients b s n)

theorem lexWrapLeftPositive_restored (M : LexNoWrapLeftPos) (hd : 1 ≤ M.wrap_left) :
    ¬ DupOrientsBy (S := freeSchema) VecLexLt M.eval :=
  CellClassificationFamilies.no_matrixLexD_orients_dup_step_via_cells (M.restore hd) M.primary_pos

theorem lexWrapRightPositive_restored (M : LexNoWrapRightPos) (hd : 1 ≤ M.wrap_right) :
    ¬ DupOrientsBy (S := freeSchema) VecLexLt M.eval :=
  CellClassificationFamilies.no_matrixLexD_orients_dup_step_via_cells (M.restore hd) M.primary_pos

theorem lexPrimaryPositive_restored (M : MatrixLexMeasureD freeSchema 1)
    (hd : ∃ t : freeSchema.T, 1 ≤ M.eval t (primaryIdx 1)) :
    ¬ DupOrientsBy (S := freeSchema) VecLexLt M.eval :=
  CellClassificationFamilies.no_matrixLexD_orients_dup_step_via_cells M hd

theorem lexWrapLeftPositive_deleted_barrier_false :
    ¬ ∀ M : LexNoWrapLeftPos, ¬ DupOrientsBy (S := freeSchema) VecLexLt M.eval :=
  fun hall => hall counterLex counterLex_orients

theorem lexWrapRightPositive_deleted_barrier_false :
    ¬ ∀ M : LexNoWrapRightPos, ¬ DupOrientsBy (S := freeSchema) VecLexLt M.eval :=
  fun hall => hall stepLex stepLex_orients

/-- **Primary positivity of the lexicographic barrier is necessary**, and, through
`tracked_nonincreasing_positivity_hypothesis_necessary` at `K = ℕ`, so is positivity of the
nonincreasing field-matrix barrier. -/
theorem lexPrimaryPositive_deleted_barrier_false :
    (¬ ∀ M : MatrixLexMeasureD freeSchema 1, ¬ DupOrientsBy (S := freeSchema) VecLexLt M.eval) ∧
    (¬ ∃ t : freeSchema.T, 0 < (zeroFieldNatMatrixMeasure (K := ℕ) freeSchema).eval t 0) ∧
    (¬ ∀ (M : FieldNatMatrixMeasure freeSchema 1 ℕ) (i : Fin 1), FieldWrapDiagPositive M i →
      ∀ {R : FieldMatrixVec 1 ℕ → FieldMatrixVec 1 ℕ → Prop},
        (∀ {u v : FieldMatrixVec 1 ℕ}, R u v → u i ≤ v i) →
          ¬ ∀ b s n : freeSchema.T,
            R (M.eval (freeSchema.wrap s (freeSchema.recur b s n)))
              (M.eval (freeSchema.recur b s (freeSchema.succ n)))) := by
  obtain ⟨hi, horient, hnot⟩ :=
    tracked_nonincreasing_positivity_hypothesis_necessary (K := ℕ) (S := freeSchema)
  refine ⟨fun hall => hall zeroPrimaryLex zeroPrimaryLex_orients, hnot, fun hall => ?_⟩
  exact @hall (zeroFieldNatMatrixMeasure freeSchema) 0 hi (fun u v => u 0 ≤ v 0)
    (fun h => h) horient

end Lex

/-! ## Hypothesis slots and evidence -/

/-- The load-bearing premises of the live barrier theorems, indexed by family. The max-plus,
max-depth and head-precedence families have none. -/
inductive HypothesisSlot : DirectBarrierFamily → Type where
  | additiveAttainment : HypothesisSlot .additiveCompositional
  | additiveWrapRetention : HypothesisSlot .additiveCompositional
  | directLawWrapperRetention : HypothesisSlot .additiveCompositional
  | directLawBoundedCounterGain : HypothesisSlot .additiveCompositional
  | transparentSuccessor : HypothesisSlot .transparentCompositional
  | compositionalWrapSubterm2 : HypothesisSlot .transparentCompositional
  | affineWrapLeftPositive : HypothesisSlot .affine
  | affineWrapRightPositive : HypothesisSlot .affine
  | affineNonstrictPositivity : HypothesisSlot .affine
  | quadraticWrapLeftPositive : HypothesisSlot .restrictedQuadratic
  | quadraticWrapRightPositive : HypothesisSlot .restrictedQuadratic
  | crossTermBaseDominance : HypothesisSlot .boundedCrossTermQuadratic
  | multilinearBaseDominance : HypothesisSlot .boundedMultilinear
  | polynomialEventualDominance : HypothesisSlot .generalizedBoundedPolynomial
  | pairWrapLeftPositive : HypothesisSlot .trackedPrimaryPair
  | pairWrapRightPositive : HypothesisSlot .trackedPrimaryPair
  | pairLexFirstPositive : HypothesisSlot .trackedPrimaryPair
  | lexPrimaryPositive : HypothesisSlot .trackedPrimaryLexicographic
  | lexWrapLeftPositive : HypothesisSlot .trackedPrimaryLexicographic
  | lexWrapRightPositive : HypothesisSlot .trackedPrimaryLexicographic

theorem maxPlus_has_no_slot : IsEmpty (HypothesisSlot .maxPlus) := ⟨fun h => nomatch h⟩

theorem maxDepth_has_no_slot : IsEmpty (HypothesisSlot .maxDepth) := ⟨fun h => nomatch h⟩

theorem headPrecedence_has_no_slot : IsEmpty (HypothesisSlot .headPrecedence) :=
  ⟨fun h => nomatch h⟩

/-- The slots of each family, listed once. -/
def familySlots : (f : DirectBarrierFamily) → List (HypothesisSlot f)
  | .additiveCompositional =>
      [.additiveAttainment, .additiveWrapRetention, .directLawWrapperRetention,
        .directLawBoundedCounterGain]
  | .transparentCompositional => [.transparentSuccessor, .compositionalWrapSubterm2]
  | .affine => [.affineWrapLeftPositive, .affineWrapRightPositive, .affineNonstrictPositivity]
  | .restrictedQuadratic => [.quadraticWrapLeftPositive, .quadraticWrapRightPositive]
  | .boundedCrossTermQuadratic => [.crossTermBaseDominance]
  | .boundedMultilinear => [.multilinearBaseDominance]
  | .generalizedBoundedPolynomial => [.polynomialEventualDominance]
  | .maxPlus => []
  | .trackedPrimaryPair => [.pairWrapLeftPositive, .pairWrapRightPositive, .pairLexFirstPositive]
  | .trackedPrimaryLexicographic =>
      [.lexPrimaryPositive, .lexWrapLeftPositive, .lexWrapRightPositive]
  | .maxDepth => []
  | .headPrecedence => []

theorem mem_familySlots : ∀ {f : DirectBarrierFamily} (h : HypothesisSlot f), h ∈ familySlots f
  | _, h => by cases h <;> simp [familySlots]

theorem familySlots_nodup : ∀ f : DirectBarrierFamily, (familySlots f).Nodup := by
  intro f
  cases f <;> simp [familySlots]

theorem familySlots_total :
    (allDirectBarrierFamilies.map (fun f => (familySlots f).length)).sum = 20 := rfl

/-- The carrier of a slot (the live class with the slot's premise removed), the deleted premise,
and the orientation that the barrier excludes. -/
structure SlotSpec where
  Carrier : Type
  Deleted : Carrier → Prop
  Orients : Carrier → Prop

def slotSpec : {f : DirectBarrierFamily} → HypothesisSlot f → SlotSpec
  | _, .additiveAttainment =>
      { Carrier := OrderedAdditiveMeasure freeSchema Int
        Deleted := fun M => ∃ t : freeSchema.T, M.w_succ ≤ M.eval t
        Orients := fun M => DupOrientsBy (S := freeSchema) (· < ·) M.eval }
  | _, .additiveWrapRetention =>
      { Carrier := OrderedAdditiveNoRetention
        Deleted := fun M => M.WrapRetention
        Orients := fun M => DupOrientsBy (S := freeSchema) (· < ·) M.eval }
  | _, .directLawWrapperRetention =>
      { Carrier := DirectLawNoRetention
        Deleted := fun M => M.WrapperRetention
        Orients := fun M => DupOrientsBy (S := freeSchema) (· < ·) M.eval }
  | _, .directLawBoundedCounterGain =>
      { Carrier := DirectLawNoGain
        Deleted := fun M => M.BoundedCounterGain
        Orients := fun M => DupOrientsBy (S := freeSchema) (· < ·) M.eval }
  | _, .transparentSuccessor =>
      { Carrier := CompositionalMeasure freeSchema
        Deleted := fun M => M.c_succ M.c_base = M.c_base
        Orients := fun M => DupOrientsBy (S := freeSchema) (· < ·) M.eval }
  | _, .compositionalWrapSubterm2 =>
      { Carrier := CompositionalNoSubterm2
        Deleted := fun M => M.WrapSubterm2
        Orients := fun M => DupOrientsBy (S := freeSchema) (· < ·) M.eval }
  | _, .affineWrapLeftPositive =>
      { Carrier := AffineNoWrapLeftPos
        Deleted := fun M => 1 ≤ M.wrap_left
        Orients := fun M => DupOrientsBy (S := freeSchema) (· < ·) M.eval }
  | _, .affineWrapRightPositive =>
      { Carrier := AffineNoWrapRightPos
        Deleted := fun M => 1 ≤ M.wrap_right
        Orients := fun M => DupOrientsBy (S := freeSchema) (· < ·) M.eval }
  | _, .affineNonstrictPositivity =>
      { Carrier := AffineMeasure freeSchema
        Deleted := fun M => ∃ t : freeSchema.T, 1 ≤ M.eval t
        Orients := fun M => DupOrientsBy (S := freeSchema) (· ≤ ·) M.eval }
  | _, .quadraticWrapLeftPositive =>
      { Carrier := QuadraticNoWrapLeftPos
        Deleted := fun M => 1 ≤ M.wrap_left
        Orients := fun M => DupOrientsBy (S := freeSchema) (· < ·) M.eval }
  | _, .quadraticWrapRightPositive =>
      { Carrier := QuadraticNoWrapRightPos
        Deleted := fun M => 1 ≤ M.wrap_right
        Orients := fun M => DupOrientsBy (S := freeSchema) (· < ·) M.eval }
  | _, .crossTermBaseDominance =>
      { Carrier := CrossTermQuadraticMeasure freeSchema
        Deleted := fun M => CrossTermBoundedAtBase M
        Orients := fun M => DupOrientsBy (S := freeSchema) (· < ·) M.eval }
  | _, .multilinearBaseDominance =>
      { Carrier := BoundedMultilinearMeasure freeSchema
        Deleted := fun M => MultilinearDominatedAtBase M
        Orients := fun M => DupOrientsBy (S := freeSchema) (· < ·) M.eval }
  | _, .polynomialEventualDominance =>
      { Carrier := BoundedPolynomialMeasure freeSchema
        Deleted := fun M => EventuallyDominatedAtBase M
        Orients := fun M => DupOrientsBy (S := freeSchema) (· < ·) M.eval }
  | _, .pairWrapLeftPositive =>
      { Carrier := PairNoWrapLeftPos
        Deleted := fun M => 1 ≤ M.wrap_left1
        Orients := fun M => DupOrientsBy (S := freeSchema) PairLt M.eval }
  | _, .pairWrapRightPositive =>
      { Carrier := PairNoWrapRightPos
        Deleted := fun M => 1 ≤ M.wrap_right1
        Orients := fun M => DupOrientsBy (S := freeSchema) PairLt M.eval }
  | _, .pairLexFirstPositive =>
      { Carrier := MatrixMeasure2 freeSchema
        Deleted := fun M => ∃ t : freeSchema.T, 1 ≤ (M.eval t).1
        Orients := fun M => DupOrientsBy (S := freeSchema) PairLexLt M.eval }
  | _, .lexPrimaryPositive =>
      { Carrier := MatrixLexMeasureD freeSchema 1
        Deleted := fun M => ∃ t : freeSchema.T, 1 ≤ M.eval t (primaryIdx 1)
        Orients := fun M => DupOrientsBy (S := freeSchema) VecLexLt M.eval }
  | _, .lexWrapLeftPositive =>
      { Carrier := LexNoWrapLeftPos
        Deleted := fun M => 1 ≤ M.wrap_left
        Orients := fun M => DupOrientsBy (S := freeSchema) VecLexLt M.eval }
  | _, .lexWrapRightPositive =>
      { Carrier := LexNoWrapRightPos
        Deleted := fun M => 1 ≤ M.wrap_right
        Orients := fun M => DupOrientsBy (S := freeSchema) VecLexLt M.eval }

/-- A deleted-premise countermodel: a datum of the relaxed class, the failure of the deleted
premise, and the orientation excluded by the live barrier. Every other premise is a field of
the datum. -/
structure DeletedHypothesisCountermodel (P : SlotSpec) where
  datum : P.Carrier
  deletedFails : ¬ P.Deleted datum
  orients : P.Orients datum

/-- A countermodel refutes the barrier stated without the deleted premise. -/
theorem DeletedHypothesisCountermodel.refutes_deleted_barrier {P : SlotSpec}
    (C : DeletedHypothesisCountermodel P) : ¬ ∀ M : P.Carrier, ¬ P.Orients M :=
  fun hall => hall C.datum C.orients

abbrev NecessityEvidence (f : DirectBarrierFamily) (h : HypothesisSlot f) : Type :=
  DeletedHypothesisCountermodel (slotSpec h)

/-- Restoring the deleted premise gives back the live barrier theorem. -/
theorem slot_barrier_restored :
    ∀ {f : DirectBarrierFamily} (h : HypothesisSlot f) (M : (slotSpec h).Carrier),
      (slotSpec h).Deleted M → ¬ (slotSpec h).Orients M
  | _, .additiveAttainment, M, hd => additiveAttainment_restored M hd
  | _, .additiveWrapRetention, M, hd => additiveWrapRetention_restored M hd
  | _, .directLawWrapperRetention, M, hd => directLawWrapperRetention_restored M hd
  | _, .directLawBoundedCounterGain, M, hd => directLawBoundedCounterGain_restored M hd
  | _, .transparentSuccessor, M, hd => transparentSuccessor_restored M hd
  | _, .compositionalWrapSubterm2, M, hd => compositionalWrapSubterm2_restored M hd
  | _, .affineWrapLeftPositive, M, hd => affineWrapLeftPositive_restored M hd
  | _, .affineWrapRightPositive, M, hd => affineWrapRightPositive_restored M hd
  | _, .affineNonstrictPositivity, M, hd => affineNonstrictPositivity_restored M hd
  | _, .quadraticWrapLeftPositive, M, hd => quadraticWrapLeftPositive_restored M hd
  | _, .quadraticWrapRightPositive, M, hd => quadraticWrapRightPositive_restored M hd
  | _, .crossTermBaseDominance, M, hd => crossTermBaseDominance_restored M hd
  | _, .multilinearBaseDominance, M, hd => multilinearBaseDominance_restored M hd
  | _, .polynomialEventualDominance, M, hd => polynomialEventualDominance_restored M hd
  | _, .pairWrapLeftPositive, M, hd => pairWrapLeftPositive_restored M hd
  | _, .pairWrapRightPositive, M, hd => pairWrapRightPositive_restored M hd
  | _, .pairLexFirstPositive, M, hd => pairLexFirstPositive_restored M hd
  | _, .lexPrimaryPositive, M, hd => lexPrimaryPositive_restored M hd
  | _, .lexWrapLeftPositive, M, hd => lexWrapLeftPositive_restored M hd
  | _, .lexWrapRightPositive, M, hd => lexWrapRightPositive_restored M hd

def additiveAttainmentEvidence : NecessityEvidence .additiveCompositional .additiveAttainment where
  datum := negativeOrderedAdditive
  deletedFails := negativeOrderedAdditive_not_attained
  orients := negativeOrderedAdditive_orients

def additiveWrapRetentionEvidence :
    NecessityEvidence .additiveCompositional .additiveWrapRetention where
  datum := retentionFailAdditive
  deletedFails := retentionFailAdditive_not_retention
  orients := retentionFailAdditive_orients

def directLawWrapperRetentionEvidence :
    NecessityEvidence .additiveCompositional .directLawWrapperRetention where
  datum := botRightDirectLaw
  deletedFails := botRightDirectLaw_not_retention
  orients := unconstrainedDirectLaw_wrap_clause_escape

def directLawBoundedCounterGainEvidence :
    NecessityEvidence .additiveCompositional .directLawBoundedCounterGain where
  datum := crossCoupledDirectLaw
  deletedFails := crossCoupledDirectLaw_not_boundedGain
  orients := unconstrainedDirectLaw_counter_clause_escape.2.1

def transparentSuccessorEvidence :
    NecessityEvidence .transparentCompositional .transparentSuccessor where
  datum := compCoupledMeasure
  deletedFails := compCoupledMeasure_not_transparent
  orients := compCoupledMeasure_orients

def compositionalWrapSubterm2Evidence :
    NecessityEvidence .transparentCompositional .compositionalWrapSubterm2 where
  datum := leftWrapCompositional
  deletedFails := leftWrapCompositional_not_subterm2
  orients := leftWrapCompositional_orients

def affineWrapLeftPositiveEvidence : NecessityEvidence .affine .affineWrapLeftPositive where
  datum := counterAffine
  deletedFails := fun h => absurd (show (1 : Nat) ≤ 0 from h) (by decide)
  orients := counterWeight_orients

def affineWrapRightPositiveEvidence : NecessityEvidence .affine .affineWrapRightPositive where
  datum := stepAffine
  deletedFails := fun h => absurd (show (1 : Nat) ≤ 0 from h) (by decide)
  orients := stepWeight_orients

def affineNonstrictPositivityEvidence : NecessityEvidence .affine .affineNonstrictPositivity where
  datum := zeroAffineMeasure freeSchema
  deletedFails := zeroAffine_not_positive
  orients := zeroAffineMeasure_nonstrict_orients freeSchema

def quadraticWrapLeftPositiveEvidence :
    NecessityEvidence .restrictedQuadratic .quadraticWrapLeftPositive where
  datum := counterQuadratic
  deletedFails := fun h => absurd (show (1 : Nat) ≤ 0 from h) (by decide)
  orients := counterWeight_orients

def quadraticWrapRightPositiveEvidence :
    NecessityEvidence .restrictedQuadratic .quadraticWrapRightPositive where
  datum := stepQuadratic
  deletedFails := fun h => absurd (show (1 : Nat) ≤ 0 from h) (by decide)
  orients := stepWeight_orients

def crossTermBaseDominanceEvidence :
    NecessityEvidence .boundedCrossTermQuadratic .crossTermBaseDominance where
  datum := crossCoupledQuadratic
  deletedFails := crossCoupledQuadratic_not_boundedAtBase
  orients := three_dominance_premises_are_sharp.1.2

def multilinearBaseDominanceEvidence :
    NecessityEvidence .boundedMultilinear .multilinearBaseDominance where
  datum := crossCoupledMultilinear
  deletedFails := crossCoupledMultilinear_not_dominatedAtBase
  orients := three_dominance_premises_are_sharp.2.1.2

def polynomialEventualDominanceEvidence :
    NecessityEvidence .generalizedBoundedPolynomial .polynomialEventualDominance where
  datum := crossCoupledPolynomial
  deletedFails := crossCoupledPolynomial_not_eventuallyDominated
  orients := three_dominance_premises_are_sharp.2.2.2

def pairWrapLeftPositiveEvidence : NecessityEvidence .trackedPrimaryPair .pairWrapLeftPositive where
  datum := counterPair
  deletedFails := fun h => absurd (show (1 : Nat) ≤ 0 from h) (by decide)
  orients := counterPair_orients

def pairWrapRightPositiveEvidence :
    NecessityEvidence .trackedPrimaryPair .pairWrapRightPositive where
  datum := stepCounterPair
  deletedFails := fun h => absurd (show (1 : Nat) ≤ 0 from h) (by decide)
  orients := stepCounterPair_orients

def pairLexFirstPositiveEvidence : NecessityEvidence .trackedPrimaryPair .pairLexFirstPositive where
  datum := zeroFirstPair
  deletedFails := zeroFirstPair_not_positive
  orients := zeroFirstPair_orients

def lexPrimaryPositiveEvidence :
    NecessityEvidence .trackedPrimaryLexicographic .lexPrimaryPositive where
  datum := zeroPrimaryLex
  deletedFails := zeroPrimaryLex_not_positive
  orients := zeroPrimaryLex_orients

def lexWrapLeftPositiveEvidence :
    NecessityEvidence .trackedPrimaryLexicographic .lexWrapLeftPositive where
  datum := counterLex
  deletedFails := fun h => absurd (show (1 : Nat) ≤ 0 from h) (by decide)
  orients := counterLex_orients

def lexWrapRightPositiveEvidence :
    NecessityEvidence .trackedPrimaryLexicographic .lexWrapRightPositive where
  datum := stepLex
  deletedFails := fun h => absurd (show (1 : Nat) ≤ 0 from h) (by decide)
  orients := stepLex_orients

/-- **Every load-bearing premise of every direct family has a deleted-premise countermodel.** -/
theorem used_hypothesis_has_countermodel :
    ∀ (f : DirectBarrierFamily) (h : HypothesisSlot f), Nonempty (NecessityEvidence f h)
  | _, .additiveAttainment => ⟨additiveAttainmentEvidence⟩
  | _, .additiveWrapRetention => ⟨additiveWrapRetentionEvidence⟩
  | _, .directLawWrapperRetention => ⟨directLawWrapperRetentionEvidence⟩
  | _, .directLawBoundedCounterGain => ⟨directLawBoundedCounterGainEvidence⟩
  | _, .transparentSuccessor => ⟨transparentSuccessorEvidence⟩
  | _, .compositionalWrapSubterm2 => ⟨compositionalWrapSubterm2Evidence⟩
  | _, .affineWrapLeftPositive => ⟨affineWrapLeftPositiveEvidence⟩
  | _, .affineWrapRightPositive => ⟨affineWrapRightPositiveEvidence⟩
  | _, .affineNonstrictPositivity => ⟨affineNonstrictPositivityEvidence⟩
  | _, .quadraticWrapLeftPositive => ⟨quadraticWrapLeftPositiveEvidence⟩
  | _, .quadraticWrapRightPositive => ⟨quadraticWrapRightPositiveEvidence⟩
  | _, .crossTermBaseDominance => ⟨crossTermBaseDominanceEvidence⟩
  | _, .multilinearBaseDominance => ⟨multilinearBaseDominanceEvidence⟩
  | _, .polynomialEventualDominance => ⟨polynomialEventualDominanceEvidence⟩
  | _, .pairWrapLeftPositive => ⟨pairWrapLeftPositiveEvidence⟩
  | _, .pairWrapRightPositive => ⟨pairWrapRightPositiveEvidence⟩
  | _, .pairLexFirstPositive => ⟨pairLexFirstPositiveEvidence⟩
  | _, .lexPrimaryPositive => ⟨lexPrimaryPositiveEvidence⟩
  | _, .lexWrapLeftPositive => ⟨lexWrapLeftPositiveEvidence⟩
  | _, .lexWrapRightPositive => ⟨lexWrapRightPositiveEvidence⟩

/-- Each slot premise is exactly necessary: with it the live barrier holds, without it the
barrier is false. -/
theorem slot_premise_exactly_necessary {f : DirectBarrierFamily} (h : HypothesisSlot f) :
    (∀ M : (slotSpec h).Carrier, (slotSpec h).Deleted M → ¬ (slotSpec h).Orients M) ∧
      ¬ ∀ M : (slotSpec h).Carrier, ¬ (slotSpec h).Orients M := by
  obtain ⟨C⟩ := used_hypothesis_has_countermodel f h
  exact ⟨slot_barrier_restored h, C.refutes_deleted_barrier⟩

/-! ## Both hypotheses of the barrier cell -/

section BarrierCell

open CellClassification

/-- The counter projection keeps bounded counter gain, fails unbounded wrapper margin, and
orients at the pair `(zero, zero)`. -/
theorem counterRank_cell_countermodel :
    GainBoundedAt (S := SchemaCore.freeSchema Empty) AblationComparisons.counterRank .zero .zero ∧
    ¬ WrapUnboundedAt (S := SchemaCore.freeSchema Empty) AblationComparisons.counterRank
      .zero .zero ∧
    ∀ s : (SchemaCore.freeSchema Empty).T,
      AblationComparisons.counterRank ((SchemaCore.freeSchema Empty).wrap s
          ((SchemaCore.freeSchema Empty).recur .zero s .zero)) <
        AblationComparisons.counterRank ((SchemaCore.freeSchema Empty).recur .zero s
          ((SchemaCore.freeSchema Empty).succ .zero)) := by
  refine ⟨counterRank_bounded_bounded.2, ?_, fun s => counterRank_is_orienter .zero s .zero⟩
  intro hw
  obtain ⟨K, hK⟩ := counterRank_bounded_bounded.1
  obtain ⟨s, hs⟩ := hw K
  have h1 := hK s
  omega

/-- The coupled polynomial measure keeps unbounded wrapper margin, fails bounded counter gain,
and orients at the pair `(zero, zero)`. -/
theorem coupledClosedMeasure_cell_countermodel :
    WrapUnboundedAt (S := SchemaCore.freeSchema Empty) coupledClosedMeasure .zero .zero ∧
    ¬ GainBoundedAt (S := SchemaCore.freeSchema Empty) coupledClosedMeasure .zero .zero ∧
    ∀ s : (SchemaCore.freeSchema Empty).T,
      coupledClosedMeasure ((SchemaCore.freeSchema Empty).wrap s
          ((SchemaCore.freeSchema Empty).recur .zero s .zero)) <
        coupledClosedMeasure ((SchemaCore.freeSchema Empty).recur .zero s
          ((SchemaCore.freeSchema Empty).succ .zero)) := by
  refine ⟨coupledClosedMeasure_unbounded_unbounded.1, ?_,
    fun s => coupledClosedMeasure_is_orienter .zero s .zero⟩
  rintro ⟨K, hK⟩
  obtain ⟨s, hs⟩ := coupledClosedMeasure_unbounded_unbounded.2 K
  have h1 := hK s
  omega

/-- **Unbounded wrapper margin is necessary for the barrier cell.** -/
theorem barrier_cell_wrap_unbounded_hypothesis_necessary :
    ¬ ∀ (M : (SchemaCore.freeSchema Empty).T → Nat) (b n : (SchemaCore.freeSchema Empty).T),
      GainBoundedAt M b n →
        ¬ ∀ s : (SchemaCore.freeSchema Empty).T,
          M ((SchemaCore.freeSchema Empty).wrap s ((SchemaCore.freeSchema Empty).recur b s n)) <
            M ((SchemaCore.freeSchema Empty).recur b s ((SchemaCore.freeSchema Empty).succ n)) :=
  fun hall => hall AblationComparisons.counterRank .zero .zero
    counterRank_cell_countermodel.1 counterRank_cell_countermodel.2.2

/-- **Bounded counter gain is necessary for the barrier cell.** -/
theorem barrier_cell_gain_bounded_hypothesis_necessary :
    ¬ ∀ (M : (SchemaCore.freeSchema Empty).T → Nat) (b n : (SchemaCore.freeSchema Empty).T),
      WrapUnboundedAt M b n →
        ¬ ∀ s : (SchemaCore.freeSchema Empty).T,
          M ((SchemaCore.freeSchema Empty).wrap s ((SchemaCore.freeSchema Empty).recur b s n)) <
            M ((SchemaCore.freeSchema Empty).recur b s ((SchemaCore.freeSchema Empty).succ n)) :=
  fun hall => hall coupledClosedMeasure .zero .zero
    coupledClosedMeasure_cell_countermodel.1 coupledClosedMeasure_cell_countermodel.2.2

/-- **Both barrier-cell hypotheses are individually necessary**, by independent countermodels;
`barrier_cell_excludes_orientation` is the barrier with both. -/
theorem barrier_cell_hypotheses_individually_necessary :
    (¬ ∀ (M : (SchemaCore.freeSchema Empty).T → Nat) (b n : (SchemaCore.freeSchema Empty).T),
      GainBoundedAt M b n →
        ¬ ∀ s : (SchemaCore.freeSchema Empty).T,
          M ((SchemaCore.freeSchema Empty).wrap s ((SchemaCore.freeSchema Empty).recur b s n)) <
            M ((SchemaCore.freeSchema Empty).recur b s ((SchemaCore.freeSchema Empty).succ n))) ∧
    (¬ ∀ (M : (SchemaCore.freeSchema Empty).T → Nat) (b n : (SchemaCore.freeSchema Empty).T),
      WrapUnboundedAt M b n →
        ¬ ∀ s : (SchemaCore.freeSchema Empty).T,
          M ((SchemaCore.freeSchema Empty).wrap s ((SchemaCore.freeSchema Empty).recur b s n)) <
            M ((SchemaCore.freeSchema Empty).recur b s ((SchemaCore.freeSchema Empty).succ n))) :=
  ⟨barrier_cell_wrap_unbounded_hypothesis_necessary,
    barrier_cell_gain_bounded_hypothesis_necessary⟩

end BarrierCell

end OperatorKO7.Methods.OrientationClosure.HypothesisNecessity
