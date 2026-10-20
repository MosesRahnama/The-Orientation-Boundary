import OperatorKO7.Meta.MatrixBarrierNatural_Schema
import OperatorKO7.Meta.MatrixBarrierArbitrary_Instances
import OperatorKO7.Meta.CompositionalMeasure_Impossibility

set_option autoImplicit false

/-!
# KO7 natural-matrix barrier: certificate-free, pump-free, dimension-uniform

`Meta/MatrixBarrierNatural_Schema.lean` proves that a natural matrix interpretation whose two
wrapper matrices carry a positive `(i, i)` entry cannot orient the duplicating step under any
order that forces coordinate `i` to decrease, and cannot orient it under any order that only
forces nonincrease once coordinate `i` is positive somewhere. Neither statement uses a weight
vector, a `RespectsWeight` certificate, a `MatrixScalarDominance` witness, or a pump.

This module instantiates that layer at the KO7 kernel and supplies the two non-vacuity
witnesses required by Gate R5.

The second witness is the point of the module. `mixedNatMatrixMeasure` is a two-dimensional
natural matrix interpretation of KO7 whose wrapper matrices are `onesMatrix` and
`upperMatrix`. `mixedNatMatrixMeasure_not_ewz_orients` shows the barrier applies to it, and
`mixedNatMatrixMeasure_no_common_weight` shows that no nonzero weight vector is respected by
both wrapper matrices at once. Every certificate-backed matrix theorem of the stack requires
such a weight vector, so this interpretation sits outside all of them and inside the
certificate-free barrier.

Relation: full kernel `Step` through `ko7System`; root closure.
Strategy: not applicable.
Trust: kernel-only. Mathlib, the schema layer, and the KO7 kernel definitions.
Named method: natural matrix interpretations (Endrullis, Waldmann, Zantema) presented as
`NatMatrixMeasure`: six constructor matrices, six bias vectors, and the four evaluation
equations of the step-duplicating schema. The comparison order is a parameter.
Scope: the KO7 duplicating rule. Nothing here claims termination or non-termination of KO7.
-/

open scoped BigOperators

namespace OperatorKO7.StepDuplicating

namespace StepDuplicatingSchema

open Finset

/-- Weighted column of a matrix under a unit weight concentrated on one row: the column
contributes exactly that row's entry. -/
theorem weightedColumn_unitWeight {d : Nat} (A : MixedMatrix d) (tracked j : Fin d) :
    MixedMatrix.weightedColumn (unitWeight tracked) A j = A.coeff tracked j := by
  unfold MixedMatrix.weightedColumn unitWeight
  rw [sum_eq_single tracked]
  · simp
  · intro i _ hi
    simp [hi]
  · simp

/--
Proves: a mixed-matrix measure whose scalarization certificate uses the unit weight on
`tracked` has strictly monotone wrapper matrices at `tracked`, so the certificate-free
natural-matrix barrier applies to it.
Does not prove: that every certificate weight is a unit weight.
Trust: kernel-only.
Scope: the two wrapper matrices only; the other four certificates are not consumed.
-/
theorem MatrixArbitraryMeasure.wrapDiagPositive_of_unitWeight
    {S : StepDuplicatingSchema} {d : Nat}
    (M : MatrixArbitraryMeasure S d) (tracked : Fin d)
    (hweight : M.weight = unitWeight tracked) :
    WrapDiagPositive M.toNatMatrixMeasure tracked := by
  have hl := M.h_wrap_left_respects tracked
  have hr := M.h_wrap_right_respects tracked
  rw [hweight, weightedColumn_unitWeight] at hl hr
  have hu : unitWeight tracked tracked = 1 := by simp [unitWeight]
  rw [hu, Nat.mul_one] at hl hr
  refine ⟨?_, ?_⟩
  · show 1 ≤ M.wrap_left.coeff tracked tracked
    rw [hl]; exact M.h_wrap_left_pos
  · show 1 ≤ M.wrap_right.coeff tracked tracked
    rw [hr]; exact M.h_wrap_right_pos

end StepDuplicatingSchema

end OperatorKO7.StepDuplicating

namespace OperatorKO7.MatrixBarrierNatural

open OperatorKO7
open OperatorKO7.Trace
open OperatorKO7.StepDuplicating
open OperatorKO7.StepDuplicating.StepDuplicatingSchema
open OperatorKO7.CompositionalImpossibility
open Finset

/-! ## KO7 specializations -/

/-- KO7 natural-matrix barrier for every order whose strict comparison forces strict decrease
of the tracked coordinate. No certificate, no pump, no positivity premise. -/
theorem no_global_step_orientation_naturalMatrix_of_tracked_strict
    {d : Nat} (M : NatMatrixMeasure ko7Schema d) {i : Fin d} (hi : WrapDiagPositive M i)
    {R : MatrixVec d → MatrixVec d → Prop}
    (hR : ∀ {u v : MatrixVec d}, R u v → u i < v i) :
    ¬ GlobalOrients ko7System M.eval R :=
  no_global_orients_natMatrix_of_tracked_strict (Sys := ko7System) M hi hR

/-- KO7 natural-matrix barrier for every order that only forces nonincrease of the tracked
coordinate, with one positive value of that coordinate. -/
theorem no_global_step_orientation_naturalMatrix_of_tracked_nonincreasing
    {d : Nat} (M : NatMatrixMeasure ko7Schema d) {i : Fin d} (hi : WrapDiagPositive M i)
    {R : MatrixVec d → MatrixVec d → Prop}
    (hR : ∀ {u v : MatrixVec d}, R u v → u i ≤ v i)
    (hpos : ∃ t : Trace, 1 ≤ M.eval t i) :
    ¬ GlobalOrients ko7System M.eval R :=
  no_global_orients_natMatrix_of_tracked_nonincreasing (Sys := ko7System) M hi hR hpos

/-- KO7 natural-matrix barrier for the strict componentwise order. -/
theorem no_global_step_orientation_naturalMatrix_componentwise
    {d : Nat} (M : NatMatrixMeasure ko7Schema d) {i : Fin d} (hi : WrapDiagPositive M i) :
    ¬ GlobalOrients ko7System M.eval VecLt :=
  no_global_orients_natMatrix_componentwise (Sys := ko7System) M hi

/-- KO7 natural-matrix barrier for the Endrullis-Waldmann-Zantema order. -/
theorem no_global_step_orientation_naturalMatrix_ewz
    {d : Nat} (M : NatMatrixMeasure ko7Schema d) {tracked : Fin d}
    (hi : WrapDiagPositive M tracked) :
    ¬ GlobalOrients ko7System M.eval (VecLeLt tracked) :=
  no_global_orients_natMatrix_ewz (Sys := ko7System) M hi

/-- KO7 natural-matrix barrier for the finite lexicographic order. -/
theorem no_global_step_orientation_naturalMatrix_lexD_of_primary_pos
    {d : Nat} (M : NatMatrixMeasure ko7Schema (d + 1))
    (hi : WrapDiagPositive M (primaryIdx d))
    (hpos : ∃ t : Trace, 1 ≤ M.eval t (primaryIdx d)) :
    ¬ GlobalOrients ko7System M.eval VecLexLt :=
  no_global_orients_natMatrix_lexD_of_primary_pos (Sys := ko7System) M hi hpos

/-- KO7 natural-matrix barrier for the permutation-priority lexicographic order. -/
theorem no_global_step_orientation_naturalMatrix_lexPermD_of_primary_pos
    {d : Nat} (σ : Equiv.Perm (Fin (d + 1))) (M : NatMatrixMeasure ko7Schema (d + 1))
    (hi : WrapDiagPositive M (permPrimaryIdx σ))
    (hpos : ∃ t : Trace, 1 ≤ M.eval t (permPrimaryIdx σ)) :
    ¬ GlobalOrients ko7System M.eval (VecPermLexLt σ) :=
  no_global_orients_natMatrix_lexPermD_of_primary_pos (Sys := ko7System) σ M hi hpos

/-- Certificate-free reading of the unit-weight mixed-matrix row: the scalarization
certificate is discarded and the barrier still applies, with no pump. -/
theorem no_global_step_orientation_matrixArbitrary_unit_certificateFree
    {d : Nat} (M : MatrixArbitraryMeasure ko7Schema d) (tracked : Fin d)
    (hweight : M.weight = unitWeight tracked) :
    ¬ GlobalOrients ko7System M.eval (VecLeLt tracked) :=
  no_global_orients_natMatrix_ewz (Sys := ko7System) M.toNatMatrixMeasure
    (MatrixArbitraryMeasure.wrapDiagPositive_of_unitWeight M tracked hweight)

/-! ## Witness 1: the one-dimensional size interpretation -/

/-- The all-ones matrix in any finite dimension. -/
@[simp] def onesMatrix {d : Nat} : MixedMatrix d where
  coeff _ _ := 1

/-- A one-dimensional natural matrix interpretation of KO7 realizing `simpleSize`. -/
def simpleSizeNatMatrixMeasure : NatMatrixMeasure ko7Schema 1 where
  eval := fun t _ => simpleSize_ACM.eval t
  base_vec := fun _ => 0
  succ_bias := fun _ => 1
  succ_mat := onesMatrix
  wrap_bias := fun _ => 1
  wrap_left := onesMatrix
  wrap_right := onesMatrix
  recur_bias := fun _ => 1
  recur_base := onesMatrix
  recur_step := onesMatrix
  recur_counter := onesMatrix
  eval_base := by
    funext i; fin_cases i; simp [ko7Schema, simpleSize_ACM]
  eval_succ := by
    intro t; funext i; fin_cases i
    simp [ko7Schema, simpleSize_ACM, vecAdd, MixedMatrix.act]
  eval_wrap := by
    intro x y; funext i; fin_cases i
    simp [ko7Schema, simpleSize_ACM, vecAdd, MixedMatrix.act, Nat.add_assoc]
  eval_recur := by
    intro b s n; funext i; fin_cases i
    simp [ko7Schema, simpleSize_ACM, vecAdd, MixedMatrix.act, Nat.add_assoc]

/-- Both wrapper matrices of the size interpretation are strictly monotone at coordinate 0. -/
theorem simpleSizeNatMatrixMeasure_wrapDiagPositive :
    WrapDiagPositive simpleSizeNatMatrixMeasure (0 : Fin 1) :=
  ⟨le_refl 1, le_refl 1⟩

/-! ## Witness 2: a two-dimensional interpretation outside every certificate

The wrapper matrices of `mixedNatMatrixMeasure` are `onesMatrix` and `upperMatrix`. They
share no nonzero weight vector, so no scalarization certificate exists for this
interpretation and no certificate-backed theorem of the stack covers it.
-/

/-- Upper-triangular two-dimensional matrix: every entry is one except the lower-left. -/
@[simp] def upperMatrix : MixedMatrix 2 where
  coeff i j := if i = 1 ∧ j = 0 then 0 else 1

/-- The recursive pair interpretation behind `mixedNatMatrixMeasure`. The `app` clause is the
one that forces the two wrapper matrices apart: the second coordinate drops the left
argument's first coordinate. -/
def mixedPair : Trace → Nat × Nat
  | void => (0, 0)
  | delta t => (1 + (mixedPair t).1 + (mixedPair t).2, 1 + (mixedPair t).1 + (mixedPair t).2)
  | integrate t =>
      (1 + (mixedPair t).1 + (mixedPair t).2, 1 + (mixedPair t).1 + (mixedPair t).2)
  | merge a b =>
      (1 + (mixedPair a).1 + (mixedPair a).2 + (mixedPair b).1 + (mixedPair b).2,
       1 + (mixedPair a).1 + (mixedPair a).2 + (mixedPair b).1 + (mixedPair b).2)
  | app a b =>
      (1 + (mixedPair a).1 + (mixedPair a).2 + (mixedPair b).1 + (mixedPair b).2,
       1 + (mixedPair a).1 + (mixedPair a).2 + (mixedPair b).2)
  | recΔ b s n =>
      (1 + (mixedPair b).1 + (mixedPair b).2 + (mixedPair s).1 + (mixedPair s).2
         + (mixedPair n).1 + (mixedPair n).2,
       1 + (mixedPair b).1 + (mixedPair b).2 + (mixedPair s).1 + (mixedPair s).2
         + (mixedPair n).1 + (mixedPair n).2)
  | eqW a b =>
      (1 + (mixedPair a).1 + (mixedPair a).2 + (mixedPair b).1 + (mixedPair b).2,
       1 + (mixedPair a).1 + (mixedPair a).2 + (mixedPair b).1 + (mixedPair b).2)

/-- Read a pair as a two-dimensional vector. -/
@[simp] def pairVec (p : Nat × Nat) : MatrixVec 2 :=
  fun i => if i = 0 then p.1 else p.2

/-- A two-dimensional natural matrix interpretation of KO7 whose two wrapper matrices admit
no common nonzero weight vector. -/
def mixedNatMatrixMeasure : NatMatrixMeasure ko7Schema 2 where
  eval := fun t => pairVec (mixedPair t)
  base_vec := fun _ => 0
  succ_bias := fun _ => 1
  succ_mat := onesMatrix
  wrap_bias := fun _ => 1
  wrap_left := onesMatrix
  wrap_right := upperMatrix
  recur_bias := fun _ => 1
  recur_base := onesMatrix
  recur_step := onesMatrix
  recur_counter := onesMatrix
  eval_base := by
    funext i; fin_cases i <;> simp [ko7Schema, mixedPair]
  eval_succ := by
    intro t; funext i; fin_cases i <;>
      simp [ko7Schema, mixedPair, vecAdd, MixedMatrix.act, Fin.sum_univ_two, Nat.add_assoc]
  eval_wrap := by
    intro x y; funext i; fin_cases i <;>
      simp [ko7Schema, mixedPair, vecAdd, MixedMatrix.act, Fin.sum_univ_two, Nat.add_assoc]
  eval_recur := by
    intro b s n; funext i; fin_cases i <;>
      simp [ko7Schema, mixedPair, vecAdd, MixedMatrix.act, Fin.sum_univ_two, Nat.add_assoc]

/-- Both wrapper matrices of the mixed interpretation are strictly monotone at coordinate 0. -/
theorem mixedNatMatrixMeasure_wrapDiagPositive :
    WrapDiagPositive mixedNatMatrixMeasure (0 : Fin 2) := by
  refine ⟨?_, ?_⟩ <;> simp [mixedNatMatrixMeasure, onesMatrix, upperMatrix]

/-- The mixed interpretation fails the Endrullis-Waldmann-Zantema order on full KO7 `Step`,
with no certificate and no pump. -/
theorem mixedNatMatrixMeasure_not_ewz_orients :
    ¬ GlobalOrients ko7System mixedNatMatrixMeasure.eval (VecLeLt (0 : Fin 2)) :=
  no_global_orients_natMatrix_ewz (Sys := ko7System) mixedNatMatrixMeasure
    mixedNatMatrixMeasure_wrapDiagPositive

/-- **Separation.** No nonzero weight vector is respected by both wrapper matrices of
`mixedNatMatrixMeasure`. Every certificate-backed matrix barrier of the stack needs such a
vector, so this interpretation lies outside all of them. -/
theorem mixedNatMatrixMeasure_no_common_weight
    (w : MatrixVec 2) (c₁ c₂ : Nat)
    (h₁ : MixedMatrix.RespectsWeight onesMatrix w c₁)
    (h₂ : MixedMatrix.RespectsWeight upperMatrix w c₂) :
    w = fun _ => 0 := by
  have o0 := h₁ 0
  have o1 := h₁ 1
  have u0 := h₂ 0
  have u1 := h₂ 1
  simp only [MixedMatrix.weightedColumn, onesMatrix, upperMatrix, Fin.sum_univ_two] at o0 o1 u0 u1
  norm_num at o0 o1 u0 u1
  have hw0 : w 0 = 0 := by
    rcases Nat.eq_zero_or_pos (w 0) with h | h
    · exact h
    · have hc2 : c₂ = 1 := by
        rcases Nat.lt_or_ge c₂ 1 with hlt | hge
        · interval_cases c₂
          omega
        · rcases Nat.lt_or_ge 1 c₂ with hgt | hle
          · nlinarith [u0]
          · omega
      rw [hc2, Nat.one_mul] at u1
      omega
  have hw1 : w 1 = 0 := by
    rw [hw0] at o0
    omega
  funext i
  fin_cases i
  · exact hw0
  · exact hw1

end OperatorKO7.MatrixBarrierNatural
