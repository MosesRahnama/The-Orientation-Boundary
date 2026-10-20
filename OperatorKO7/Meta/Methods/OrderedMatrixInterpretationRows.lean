import OperatorKO7.Meta.Methods.NaturalMatrixInterpretationRows
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Real.Archimedean

/-!
# Ordered-field matrix interpretations

Coefficients are field elements, not casts of natural matrices. The strict
comparison uses a fixed positive margin on one coordinate and weak comparison
on every coordinate. Matrix monotonicity is equivalent to a diagonal entry at
least one. Natural floor supplies a decreasing rank on nonnegative vectors.
The schema obstruction applies to every interpretation in this class.
-/

set_option autoImplicit false
open scoped BigOperators

namespace OperatorKO7.Methods.OrderedMatrixInterpretationRows

open OperatorKO7.StepDuplicating
open OperatorKO7.StepDuplicating.StepDuplicatingSchema
open OperatorKO7.Methods.AlgebraicInterpretationRows
open OperatorKO7.Methods.NaturalMatrixInterpretationRows (MatrixArgument)

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def MatrixDelta {d : Nat} (δ : K) (i : Fin d)
    (u v : FieldMatrixVec d K) : Prop :=
  (∀ j, u j ≤ v j) ∧ u i + δ ≤ v i

theorem matrixDelta_strict {d : Nat} {δ : K} (hδ : 0 < δ) {i : Fin d}
    {u v : FieldMatrixVec d K} (h : MatrixDelta δ i u v) : u i < v i :=
  (lt_add_of_pos_right _ hδ).trans_le h.2

theorem fieldMatrixAct_mono {d : Nat} (A : FieldMixedMatrix d K)
    {u v : FieldMatrixVec d K} (h : ∀ j, u j ≤ v j) :
    ∀ i, A.act u i ≤ A.act v i := by
  intro i
  exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (h j) (A.h_nonneg i j))

theorem fieldMatrixAct_sub {d : Nat} (A : FieldMixedMatrix d K)
    (u v : FieldMatrixVec d K) (i : Fin d) :
    A.act (fun j => v j - u j) i = A.act v i - A.act u i := by
  simp [FieldMixedMatrix.act, mul_sub, Finset.sum_sub_distrib]

theorem fieldMatrixAct_margin {d : Nat} (A : FieldMixedMatrix d K)
    (i : Fin d) (hA : 1 ≤ A.coeff i i) {δ : K}
    {u v : FieldMatrixVec d K} (h : MatrixDelta δ i u v) :
    MatrixDelta δ i (A.act u) (A.act v) := by
  refine ⟨fieldMatrixAct_mono A h.1, ?_⟩
  have hd : ∀ j, 0 ≤ v j - u j := fun j => sub_nonneg.mpr (h.1 j)
  have hb := FieldMixedMatrix.coord_le_act_of_diag_pos A
    (fun j => v j - u j) hd i hA
  rw [fieldMatrixAct_sub] at hb
  have hm := h.2
  linarith

theorem fieldMatrixAct_margin_iff {d : Nat} (A : FieldMixedMatrix d K)
    (i : Fin d) {δ : K} (hδ : 0 < δ) :
    (∀ {u v : FieldMatrixVec d K},
      MatrixDelta δ i u v → MatrixDelta δ i (A.act u) (A.act v)) ↔
      1 ≤ A.coeff i i := by
  constructor
  · intro h
    have ht : MatrixDelta δ i (fun _ => 0) (fun j => if j = i then δ else 0) := by
      refine ⟨?_, ?_⟩
      · intro j
        change 0 ≤ if j = i then δ else 0
        split <;> simp_all [le_of_lt hδ]
      · simp
    have hi := (h ht).2
    have hmul : 1 * δ ≤ A.coeff i i * δ := by
      simpa [FieldMixedMatrix.act] using hi
    exact (mul_le_mul_right hδ).mp hmul
  · intro hA
    exact fieldMatrixAct_margin A i hA

theorem matrixDelta_compatibility {d : Nat} (δ : K) (i : Fin d) :
    (∀ {u v w : FieldMatrixVec d K}, MatrixDelta δ i u v →
      (∀ j, v j ≤ w j) → MatrixDelta δ i u w) ∧
    (∀ {u v w : FieldMatrixVec d K}, (∀ j, u j ≤ v j) →
      MatrixDelta δ i v w → MatrixDelta δ i u w) := by
  constructor
  · intro u v w huv hvw
    exact ⟨fun j => (huv.1 j).trans (hvw j), huv.2.trans (hvw i)⟩
  · intro u v w huv hvw
    exact ⟨fun j => (huv j).trans (hvw.1 j),
      (add_le_add_right (huv i) δ).trans hvw.2⟩

def NonnegativeVector (d : Nat) (K : Type*) [Zero K] [LE K] :=
  {v : Fin d → K // ∀ i, 0 ≤ v i}

theorem matrixDelta_wellFounded [FloorSemiring K] {d : Nat}
    {δ : K} (hδ : 0 < δ) (i : Fin d) :
    WellFounded (fun u v : NonnegativeVector d K => MatrixDelta δ i u.val v.val) := by
  apply Subrelation.wf (r := fun u v : NonnegativeVector d K =>
    Nat.floor (u.val i / δ) < Nat.floor (v.val i / δ))
  · intro u v h
    have hdiv : u.val i / δ + 1 ≤ v.val i / δ := by
      have h' := div_le_div_of_nonneg_right h.2 hδ.le
      simpa [add_div, ne_of_gt hδ] using h'
    have hfloor := Nat.floor_mono hdiv
    rw [Nat.floor_add_one (div_nonneg (u.property i) hδ.le)] at hfloor
    omega
  · exact (measure (fun v : NonnegativeVector d K => Nat.floor (v.val i / δ))).wf

structure FieldMatrixOperation (d n : Nat) (K : Type*)
    [Field K] [LinearOrder K] [IsStrictOrderedRing K] where
  bias : FieldMatrixVec d K
  argument : Fin n → FieldMixedMatrix d K

def FieldMatrixOperation.eval {d n : Nat} (F : FieldMatrixOperation d n K)
    (v : Fin n → FieldMatrixVec d K) : FieldMatrixVec d K :=
  fun i => F.bias i + ∑ a, (F.argument a).act (v a) i

theorem FieldMatrixOperation.margin_mono {d n : Nat}
    (F : FieldMatrixOperation d n K) (δ : K) (i : Fin d) (k : Fin n)
    (hF : 1 ≤ (F.argument k).coeff i i)
    {u v : Fin n → FieldMatrixVec d K} (hk : MatrixDelta δ i (u k) (v k))
    (hother : ∀ a, a ≠ k → ∀ j, u a j ≤ v a j) :
    MatrixDelta δ i (F.eval u) (F.eval v) := by
  have hw : ∀ a j, u a j ≤ v a j := by
    intro a j
    by_cases ha : a = k
    · subst a; exact hk.1 j
    · exact hother a ha j
  refine ⟨?_, ?_⟩
  · intro j
    exact add_le_add_left (Finset.sum_le_sum
      (fun a _ => fieldMatrixAct_mono (F.argument a) (hw a) j)) _
  · have ht := (fieldMatrixAct_margin (F.argument k) i hF hk).2
    have hrem :
        ∑ a ∈ Finset.univ.erase k, (F.argument a).act (u a) i ≤
          ∑ a ∈ Finset.univ.erase k, (F.argument a).act (v a) i := by
      exact Finset.sum_le_sum (fun a _ => fieldMatrixAct_mono (F.argument a) (hw a) i)
    have hu := Finset.sum_erase_add (s := Finset.univ)
      (f := fun a => (F.argument a).act (u a) i) (Finset.mem_univ k)
    have hv := Finset.sum_erase_add (s := Finset.univ)
      (f := fun a => (F.argument a).act (v a) i) (Finset.mem_univ k)
    dsimp [FieldMatrixOperation.eval]
    linarith

def fieldArgumentMatrix {S : StepDuplicatingSchema} {d : Nat}
    (M : FieldNatMatrixMeasure S d K) : MatrixArgument → FieldMixedMatrix d K
  | .succ => M.succ_mat
  | .wrapLeft => M.wrap_left
  | .wrapRight => M.wrap_right
  | .recurBase => M.recur_base
  | .recurStep => M.recur_step
  | .recurCounter => M.recur_counter

structure OrderedMatrixMethod (S : StepDuplicatingSchema) (d : Nat) (K : Type*)
    [Field K] [LinearOrder K] [IsStrictOrderedRing K] [NeZero d] where
  interpretation : FieldNatMatrixMeasure S d K
  delta : K
  delta_pos : 0 < delta
  diagonal : ∀ a, 1 ≤ (fieldArgumentMatrix interpretation a).coeff 0 0
  succ_bias_nonneg : ∀ i, 0 ≤ interpretation.succ_bias i

def OrderedMatrixMethod.eval {S : StepDuplicatingSchema} {d : Nat} [NeZero d]
    (M : OrderedMatrixMethod S d K) (t : S.T) : NonnegativeVector d K :=
  ⟨M.interpretation.eval t, M.interpretation.h_eval_nonneg t⟩

theorem OrderedMatrixMethod.order_wellFounded [FloorSemiring K]
    {S : StepDuplicatingSchema} {d : Nat} [NeZero d] (M : OrderedMatrixMethod S d K) :
    WellFounded (fun u v : NonnegativeVector d K => MatrixDelta M.delta 0 u.val v.val) :=
  matrixDelta_wellFounded M.delta_pos 0

theorem OrderedMatrixMethod.not_orients {S : StepDuplicatingSchema}
    {d : Nat} [NeZero d] (M : OrderedMatrixMethod S d K) :
    ¬ ∀ b s n : S.T, MatrixDelta M.delta 0
      (M.interpretation.eval (S.wrap s (S.recur b s n)))
      (M.interpretation.eval (S.recur b s (S.succ n))) :=
  no_matrix_orients_dup_step_field_of_tracked_strict M.interpretation
    ⟨M.diagonal .wrapLeft, M.diagonal .wrapRight⟩
    (fun h => matrixDelta_strict M.delta_pos h)

def fieldIdentityMatrix (d : Nat) : FieldMixedMatrix d K where
  coeff i j := if i = j then 1 else 0
  h_nonneg := by intro i j; split <;> norm_num

@[simp] theorem fieldIdentityMatrix_act {d : Nat} (v : FieldMatrixVec d K) :
    (fieldIdentityMatrix d).act v = v := by
  funext i
  simp [fieldIdentityMatrix, FieldMixedMatrix.act]

def scaledSizeMatrixMeasure (d : Nat) (c : K) (hc : 0 ≤ c) :
    FieldNatMatrixMeasure freeSchema d K where
  eval := fun t _ => c * (unitAffineNatEval t : K)
  base_vec := fun _ => c
  succ_bias := fun _ => c
  succ_mat := fieldIdentityMatrix d
  wrap_bias := fun _ => c
  wrap_left := fieldIdentityMatrix d
  wrap_right := fieldIdentityMatrix d
  recur_bias := fun _ => c
  recur_base := fieldIdentityMatrix d
  recur_step := fieldIdentityMatrix d
  recur_counter := fieldIdentityMatrix d
  eval_base := by funext i; simp [freeSchema, unitAffineNatEval]
  eval_succ := by
    intro t; funext i
    simp [freeSchema, unitAffineNatEval, fieldVecAdd, mul_add]
  eval_wrap := by
    intro x y; funext i
    simp [freeSchema, unitAffineNatEval, fieldVecAdd, mul_add, add_assoc]
  eval_recur := by
    intro b s n; funext i
    simp [freeSchema, unitAffineNatEval, fieldVecAdd, mul_add, add_assoc]
  h_eval_nonneg := by intro t i; exact mul_nonneg hc (Nat.cast_nonneg _)
  h_wrap_bias_nonneg := fun _ => hc
  h_recur_bias_nonneg := fun _ => hc

def scaledSizeMatrixMethod (d : Nat) [NeZero d] (c : K) (hc : 0 < c) :
    OrderedMatrixMethod freeSchema d K where
  interpretation := scaledSizeMatrixMeasure d c hc.le
  delta := c
  delta_pos := hc
  diagonal := by
    intro a; cases a <;> simp [fieldArgumentMatrix, scaledSizeMatrixMeasure, fieldIdentityMatrix]
  succ_bias_nonneg := fun _ => hc.le

theorem scaledSizeMatrixMethod_strict_witness (d : Nat) [NeZero d]
    (c : K) (hc : 0 < c) :
    MatrixDelta c 0
      ((scaledSizeMatrixMethod d c hc).interpretation.eval .base)
      ((scaledSizeMatrixMethod d c hc).interpretation.eval (.succ .base)) := by
  constructor
  · intro i
    change c * (unitAffineNatEval .base : K) ≤ c * (unitAffineNatEval (.succ .base) : K)
    norm_num [unitAffineNatEval]
    linarith
  · change c * (unitAffineNatEval .base : K) + c ≤
      c * (unitAffineNatEval (.succ .base) : K)
    norm_num [unitAffineNatEval]
    linarith

theorem ordered_matrix_method_inhabited (d : Nat) [NeZero d] :
    Nonempty (OrderedMatrixMethod freeSchema d K) ∧
      ∃ M : OrderedMatrixMethod freeSchema d K,
        M.interpretation.eval .base ≠ M.interpretation.eval (.succ .base) := by
  let M := scaledSizeMatrixMethod d (1 : K) zero_lt_one
  refine ⟨⟨M⟩, M, ?_⟩
  intro heq
  have hstrict := matrixDelta_strict (K := K) zero_lt_one
    (scaledSizeMatrixMethod_strict_witness d (1 : K) zero_lt_one)
  exact (ne_of_lt hstrict) (congrFun heq 0)

def diagonalFieldMatrix (d : Nat) (a : K) (ha : 0 ≤ a) : FieldMixedMatrix d K where
  coeff i j := if i = j then a else 0
  h_nonneg := by intro i j; split <;> simp_all

@[simp] theorem diagonalFieldMatrix_act {d : Nat} (a : K) (ha : 0 ≤ a)
    (v : FieldMatrixVec d K) (i : Fin d) :
    (diagonalFieldMatrix d a ha).act v i = a * v i := by
  simp [diagonalFieldMatrix, FieldMixedMatrix.act]

def fieldAffineSize (c a : K) : FreeTerm → K
  | .base => c
  | .succ t => c + a * fieldAffineSize c a t
  | .wrap x y => c + fieldAffineSize c a x + fieldAffineSize c a y
  | .recur b s n => c + fieldAffineSize c a b + fieldAffineSize c a s + fieldAffineSize c a n

theorem fieldAffineSize_nonneg (c a : K) (hc : 0 ≤ c) (ha : 0 ≤ a) (t : FreeTerm) :
    0 ≤ fieldAffineSize c a t := by
  induction t <;> simp only [fieldAffineSize] <;> positivity

def affineSizeMatrixMethod (d : Nat) [NeZero d] (c a : K)
    (hc : 0 < c) (ha : 1 ≤ a) : OrderedMatrixMethod freeSchema d K where
  interpretation :=
    { eval := fun t _ => fieldAffineSize c a t
      base_vec := fun _ => c
      succ_bias := fun _ => c
      succ_mat := diagonalFieldMatrix d a (zero_le_one.trans ha)
      wrap_bias := fun _ => c
      wrap_left := fieldIdentityMatrix d
      wrap_right := fieldIdentityMatrix d
      recur_bias := fun _ => c
      recur_base := fieldIdentityMatrix d
      recur_step := fieldIdentityMatrix d
      recur_counter := fieldIdentityMatrix d
      eval_base := rfl
      eval_succ := by
        intro t; funext i
        simp [freeSchema, fieldAffineSize, fieldVecAdd]
      eval_wrap := by
        intro x y; funext i
        simp [freeSchema, fieldAffineSize, fieldVecAdd, add_assoc]
      eval_recur := by
        intro b s n; funext i
        simp [freeSchema, fieldAffineSize, fieldVecAdd, add_assoc]
      h_eval_nonneg := fun t _ => fieldAffineSize_nonneg c a hc.le (zero_le_one.trans ha) t
      h_wrap_bias_nonneg := fun _ => hc.le
      h_recur_bias_nonneg := fun _ => hc.le }
  delta := c
  delta_pos := hc
  diagonal := by
    intro arg; cases arg <;> simp [fieldArgumentMatrix, diagonalFieldMatrix, fieldIdentityMatrix, ha]
  succ_bias_nonneg := fun _ => hc.le

def fractionalMatrixMethod (d : Nat) [NeZero d] : OrderedMatrixMethod freeSchema d K :=
  affineSizeMatrixMethod d (2 / 3 : K) (3 / 2 : K) (by norm_num) (by norm_num)

theorem fractionalMatrixMethod_entry (d : Nat) [NeZero d] :
    (fractionalMatrixMethod (K := K) d).interpretation.succ_mat.coeff 0 0 = 3 / 2 := by
  simp [fractionalMatrixMethod, affineSizeMatrixMethod, diagonalFieldMatrix]

theorem fractionalMatrixMethod_entry_not_nat (d : Nat) [NeZero d] :
    ¬ ∃ n : Nat,
      (fractionalMatrixMethod (K := K) d).interpretation.succ_mat.coeff 0 0 = (n : K) := by
  rw [fractionalMatrixMethod_entry]
  rintro ⟨n, hn⟩
  have hlow : (1 : K) < (n : K) := by rw [← hn]; norm_num
  have hhigh : (n : K) < (2 : K) := by rw [← hn]; norm_num
  have hnlow : 1 < n := by exact_mod_cast hlow
  have hnhigh : n < 2 := by exact_mod_cast hhigh
  omega

theorem fractionalMatrixMethod_nonconstant (d : Nat) [NeZero d] :
    (fractionalMatrixMethod (K := K) d).interpretation.eval .base ≠
      (fractionalMatrixMethod (K := K) d).interpretation.eval (.succ .base) := by
  intro h
  have hi := congrFun h (0 : Fin d)
  norm_num [fractionalMatrixMethod, affineSizeMatrixMethod, fieldAffineSize] at hi

abbrev OrderedMatrixExactRowClaim (K : Type*)
    [Field K] [LinearOrder K] [IsStrictOrderedRing K] : Prop :=
  ∀ (S : StepDuplicatingSchema) (d : Nat) [NeZero d] (M : OrderedMatrixMethod S d K),
    ¬ ∀ b s n : S.T, MatrixDelta M.delta 0
      (M.interpretation.eval (S.wrap s (S.recur b s n)))
      (M.interpretation.eval (S.recur b s (S.succ n)))

theorem orderedMatrix_exact_row : OrderedMatrixExactRowClaim K :=
  fun _ _ _ M => M.not_orients

theorem rationalMatrix_exact_row : OrderedMatrixExactRowClaim ℚ := orderedMatrix_exact_row

theorem realMatrix_exact_row : OrderedMatrixExactRowClaim ℝ := orderedMatrix_exact_row

theorem rational_real_matrix_exact_row :
    OrderedMatrixExactRowClaim ℚ ∧ OrderedMatrixExactRowClaim ℝ :=
  ⟨rationalMatrix_exact_row, realMatrix_exact_row⟩

end OperatorKO7.Methods.OrderedMatrixInterpretationRows
