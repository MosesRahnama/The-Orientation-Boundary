import OperatorKO7.Meta.ProjectedPrimaryBarrier

/-!
# Arbitrary Mixed-Matrix Scalarization Barrier

This module packages a first-class finite-dimensional mixed-matrix interface with an
explicit scalarization witness. The scalarization is theorem-backed: each constructor's
full matrix action must respect the chosen weight vector, so the scalarized measure is an
ordinary affine direct measure.

The resulting barrier does not privilege a distinguished primary coordinate. Any explicit
weight vector is allowed, provided the ambient order is proved to make the induced scalar
projection non-increasing.
-/

open scoped BigOperators

namespace OperatorKO7.StepDuplicating

namespace StepDuplicatingSchema

open Finset

/-- Finite-dimensional natural vectors used by the mixed-matrix interface. -/
abbrev MatrixVec (d : Nat) := Fin d → Nat

/-- Pointwise vector addition. -/
@[simp] def vecAdd {d : Nat} (u v : MatrixVec d) : MatrixVec d :=
  fun i => u i + v i

/-- Explicit scalarization of a vector by a natural weight profile. -/
@[simp] def matrixScalarize {d : Nat} (weight : MatrixVec d) (v : MatrixVec d) : Nat :=
  ∑ i, weight i * v i

@[simp] lemma matrixScalarize_vecAdd
    {d : Nat} (weight u v : MatrixVec d) :
    matrixScalarize weight (vecAdd u v) =
      matrixScalarize weight u + matrixScalarize weight v := by
  unfold matrixScalarize vecAdd
  calc
    ∑ i, weight i * (u i + v i)
        = ∑ i, (weight i * u i + weight i * v i) := by
            refine sum_congr rfl ?_
            intro i _
            rw [Nat.left_distrib]
    _ = (∑ i, weight i * u i) + ∑ i, weight i * v i := by
          rw [sum_add_distrib]

/-- A full `d × d` natural matrix. -/
structure MixedMatrix (d : Nat) where
  coeff : Fin d → Fin d → Nat

namespace MixedMatrix

/-- Matrix action on vectors. -/
@[simp] def act {d : Nat} (A : MixedMatrix d) (v : MatrixVec d) : MatrixVec d :=
  fun i => ∑ j, A.coeff i j * v j

/-- Weighted contribution of one source coordinate to the scalarization. -/
@[simp] def weightedColumn {d : Nat}
    (weight : MatrixVec d) (A : MixedMatrix d) (j : Fin d) : Nat :=
  ∑ i, weight i * A.coeff i j

/-- The matrix acts by a single scalar on the chosen scalarization. -/
def RespectsWeight {d : Nat}
    (A : MixedMatrix d) (weight : MatrixVec d) (scale : Nat) : Prop :=
  ∀ j : Fin d, weightedColumn weight A j = scale * weight j

/-- Scalarizing after matrix action is equivalent to scalarizing with the induced weighted
columns. -/
lemma scalarize_act_eq_reweighted
    {d : Nat} (weight : MatrixVec d) (A : MixedMatrix d) (v : MatrixVec d) :
    matrixScalarize weight (A.act v) =
      matrixScalarize (fun j => weightedColumn weight A j) v := by
  unfold matrixScalarize act weightedColumn
  calc
    ∑ i, weight i * ∑ j, A.coeff i j * v j
        = ∑ i, ∑ j, weight i * (A.coeff i j * v j) := by
            refine sum_congr rfl ?_
            intro i _
            simpa using
              (Finset.mul_sum (s := univ) (a := weight i) (f := fun j => A.coeff i j * v j))
    _ = ∑ j, ∑ i, weight i * (A.coeff i j * v j) := by
          rw [sum_comm]
    _ = ∑ j, (∑ i, weight i * A.coeff i j) * v j := by
          refine sum_congr rfl ?_
          intro j _
          calc
            ∑ i, weight i * (A.coeff i j * v j)
                = ∑ i, (weight i * A.coeff i j) * v j := by
                    refine sum_congr rfl ?_
                    intro i _
                    rw [Nat.mul_assoc]
            _ = (∑ i, weight i * A.coeff i j) * v j := by
                  simpa using
                    (Finset.sum_mul (s := univ) (f := fun i => weight i * A.coeff i j)
                      (a := v j)).symm
    _ = matrixScalarize (fun j => weightedColumn weight A j) v := by
          rfl

/-- If the matrix respects the chosen weight profile, scalarization commutes with its action
up to one natural scaling coefficient. -/
lemma scalarize_act_eq_of_respectsWeight
    {d : Nat} {A : MixedMatrix d} {weight v : MatrixVec d} {scale : Nat}
    (hA : RespectsWeight A weight scale) :
    matrixScalarize weight (A.act v) = scale * matrixScalarize weight v := by
  calc
    matrixScalarize weight (A.act v)
        = ∑ j, weightedColumn weight A j * v j := by
            simpa [matrixScalarize] using scalarize_act_eq_reweighted weight A v
    _ = ∑ j, (scale * weight j) * v j := by
          refine sum_congr rfl ?_
          intro j _
          rw [hA j]
    _ = ∑ j, scale * (weight j * v j) := by
          refine sum_congr rfl ?_
          intro j _
          rw [Nat.mul_assoc]
    _ = scale * ∑ j, weight j * v j := by
          simpa using
        (Finset.mul_sum (s := univ) (a := scale) (f := fun j => weight j * v j)).symm
    _ = scale * matrixScalarize weight v := by
          rfl

end MixedMatrix

/-- A first-class arbitrary finite-dimensional mixed-matrix measure equipped with an explicit
theorem-backed scalarization profile. -/
structure MatrixArbitraryMeasure (S : StepDuplicatingSchema) (d : Nat) where
  eval : S.T → MatrixVec d
  weight : MatrixVec d
  base_vec : MatrixVec d
  succ_bias : MatrixVec d
  succ_mat : MixedMatrix d
  wrap_bias : MatrixVec d
  wrap_left : MixedMatrix d
  wrap_right : MixedMatrix d
  recur_bias : MatrixVec d
  recur_base : MixedMatrix d
  recur_step : MixedMatrix d
  recur_counter : MixedMatrix d
  succ_scale : Nat
  wrap_left_scale : Nat
  wrap_right_scale : Nat
  recur_base_scale : Nat
  recur_step_scale : Nat
  recur_counter_scale : Nat
  eval_base : eval S.base = base_vec
  eval_succ :
    ∀ t, eval (S.succ t) = vecAdd succ_bias (succ_mat.act (eval t))
  eval_wrap :
    ∀ x y,
      eval (S.wrap x y) =
        vecAdd wrap_bias (vecAdd (wrap_left.act (eval x)) (wrap_right.act (eval y)))
  eval_recur :
    ∀ b s n,
      eval (S.recur b s n) =
        vecAdd recur_bias
          (vecAdd (recur_base.act (eval b))
            (vecAdd (recur_step.act (eval s)) (recur_counter.act (eval n))))
  h_succ_respects : succ_mat.RespectsWeight weight succ_scale
  h_wrap_left_respects : wrap_left.RespectsWeight weight wrap_left_scale
  h_wrap_right_respects : wrap_right.RespectsWeight weight wrap_right_scale
  h_recur_base_respects : recur_base.RespectsWeight weight recur_base_scale
  h_recur_step_respects : recur_step.RespectsWeight weight recur_step_scale
  h_recur_counter_respects : recur_counter.RespectsWeight weight recur_counter_scale
  h_wrap_left_pos : 1 ≤ wrap_left_scale
  h_wrap_right_pos : 1 ≤ wrap_right_scale

/-- Scalar affine measure induced by the explicit mixed-matrix scalarization interface. -/
def MatrixArbitraryMeasure.scalarAffine
    {S : StepDuplicatingSchema} {d : Nat}
    (M : MatrixArbitraryMeasure S d) : AffineMeasure S where
  eval := fun t => matrixScalarize M.weight (M.eval t)
  c_base := matrixScalarize M.weight M.base_vec
  succ_bias := matrixScalarize M.weight M.succ_bias
  succ_scale := M.succ_scale
  wrap_const := matrixScalarize M.weight M.wrap_bias
  wrap_left := M.wrap_left_scale
  wrap_right := M.wrap_right_scale
  recur_const := matrixScalarize M.weight M.recur_bias
  recur_base := M.recur_base_scale
  recur_step := M.recur_step_scale
  recur_counter := M.recur_counter_scale
  eval_base := by
    rw [M.eval_base]
  eval_succ := by
    intro t
    rw [M.eval_succ, matrixScalarize_vecAdd]
    simpa using
      (MixedMatrix.scalarize_act_eq_of_respectsWeight
        (A := M.succ_mat) (weight := M.weight) (v := M.eval t) M.h_succ_respects)
  eval_wrap := by
    intro x y
    rw [M.eval_wrap, matrixScalarize_vecAdd, matrixScalarize_vecAdd]
    rw [MixedMatrix.scalarize_act_eq_of_respectsWeight
        (A := M.wrap_left) (weight := M.weight) (v := M.eval x) M.h_wrap_left_respects]
    rw [MixedMatrix.scalarize_act_eq_of_respectsWeight
        (A := M.wrap_right) (weight := M.weight) (v := M.eval y) M.h_wrap_right_respects]
    simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  eval_recur := by
    intro b s n
    rw [M.eval_recur, matrixScalarize_vecAdd, matrixScalarize_vecAdd, matrixScalarize_vecAdd]
    rw [MixedMatrix.scalarize_act_eq_of_respectsWeight
        (A := M.recur_base) (weight := M.weight) (v := M.eval b) M.h_recur_base_respects]
    rw [MixedMatrix.scalarize_act_eq_of_respectsWeight
        (A := M.recur_step) (weight := M.weight) (v := M.eval s) M.h_recur_step_respects]
    rw [MixedMatrix.scalarize_act_eq_of_respectsWeight
        (A := M.recur_counter) (weight := M.weight) (v := M.eval n) M.h_recur_counter_respects]
    simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  h_wrap_left_pos := M.h_wrap_left_pos
  h_wrap_right_pos := M.h_wrap_right_pos

/-- Unbounded pump in the explicit scalarization attached to a mixed-matrix measure. -/
def HasUnboundedScalarizedRange
    {S : StepDuplicatingSchema} {d : Nat}
    (M : MatrixArbitraryMeasure S d) : Prop :=
  ∀ k : Nat, ∃ t : S.T, k ≤ matrixScalarize M.weight (M.eval t)

/-- Explicit theorem-backed interface connecting an ambient matrix order to the chosen
scalarization. -/
structure MatrixScalarDominance {d : Nat}
    (weight : MatrixVec d) (R : MatrixVec d → MatrixVec d → Prop) : Prop where
  nonstrict : ∀ {u v : MatrixVec d}, R u v → matrixScalarize weight u ≤ matrixScalarize weight v

/-- Pointwise weak comparison plus one explicit strict coordinate. -/
def VecLeLt {d : Nat} (tracked : Fin d) (u v : MatrixVec d) : Prop :=
  (∀ i : Fin d, u i ≤ v i) ∧ u tracked < v tracked

lemma matrixScalarize_le_of_pointwise_le
    {d : Nat} (weight u v : MatrixVec d)
    (h : ∀ i : Fin d, u i ≤ v i) :
    matrixScalarize weight u ≤ matrixScalarize weight v := by
  unfold matrixScalarize
  exact sum_le_sum (fun i _ => Nat.mul_le_mul_left _ (h i))

namespace MatrixScalarDominance

/-- Strict componentwise decrease is enough to make any natural scalarization non-increasing. -/
def of_pointwise_lt {d : Nat} (weight : MatrixVec d) :
    MatrixScalarDominance weight VecLt where
  nonstrict := by
    intro u v h
    exact matrixScalarize_le_of_pointwise_le weight u v (fun i => Nat.le_of_lt (h i))

/-- Pointwise weak decrease together with one designated strict coordinate still makes any
natural scalarization non-increasing. -/
def of_pointwise_le_lt {d : Nat} (weight : MatrixVec d) (tracked : Fin d) :
    MatrixScalarDominance weight (VecLeLt tracked) where
  nonstrict := by
    intro u v h
    exact matrixScalarize_le_of_pointwise_le weight u v h.1

end MatrixScalarDominance

/-- Arbitrary mixed finite-dimensional matrix orientations are impossible whenever an
explicit scalarization is affine, unbounded, and non-increasing along the ambient order. -/
theorem no_matrixArbitrary_orients_dup_step_of_scalar_dominance_pump
    {S : StepDuplicatingSchema} {d : Nat}
    (M : MatrixArbitraryMeasure S d)
    {R : MatrixVec d → MatrixVec d → Prop}
    (D : MatrixScalarDominance M.weight R)
    (hunbounded : HasUnboundedScalarizedRange M) :
    ¬ (∀ (b s n : S.T),
      R (M.eval (S.wrap s (S.recur b s n))) (M.eval (S.recur b s (S.succ n)))) := by
  intro h
  have hscalar :
      ∀ (b s n : S.T),
        M.scalarAffine.eval (S.wrap s (S.recur b s n)) ≤
          M.scalarAffine.eval (S.recur b s (S.succ n)) := by
    intro b s n
    simpa [MatrixArbitraryMeasure.scalarAffine] using D.nonstrict (h b s n)
  have hunbounded' : HasUnboundedRange M.scalarAffine := by
    intro k
    rcases hunbounded k with ⟨t, ht⟩
    exact ⟨t, by simpa [MatrixArbitraryMeasure.scalarAffine] using ht⟩
  exact
    no_affine_primary_nonstrict_orients_dup_step_of_unbounded
      (S := S) M.scalarAffine hunbounded' hscalar

/-- Global root orientation is impossible under the same arbitrary mixed-matrix
scalar-dominance hypotheses. -/
theorem no_global_orients_matrixArbitrary_of_scalar_dominance_pump
    {Sys : StepDuplicatingSystem} {d : Nat}
    (M : MatrixArbitraryMeasure Sys.toStepDuplicatingSchema d)
    {R : MatrixVec d → MatrixVec d → Prop}
    (D : MatrixScalarDominance M.weight R)
    (hunbounded : HasUnboundedScalarizedRange M) :
    ¬ GlobalOrients Sys M.eval R := by
  intro h
  exact
    no_matrixArbitrary_orients_dup_step_of_scalar_dominance_pump
      (S := Sys.toStepDuplicatingSchema) M D hunbounded
      (fun b s n => h (Sys.dup_step b s n))

end StepDuplicatingSchema

end OperatorKO7.StepDuplicating
