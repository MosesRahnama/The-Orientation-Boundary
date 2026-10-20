import OperatorKO7.Meta.AffineBarrierOrderedField_Schema
import OperatorKO7.Meta.MatrixBarrierNatural_Schema
import Mathlib.Data.NNRat.Lemmas
import Mathlib.Data.NNReal.Defs

set_option autoImplicit false

/-!
# Natural-matrix barrier over ordered semirings

Entries live in a partially ordered commutative semiring `K` and are nonnegative.
The `(i,i)` wrapper entries are at least `1`, so coordinate `i` of a wrapper
value dominates the sum of the argument coordinates. The self-nested wrapper
chain doubles that coordinate. `Archimedean` makes one positive coordinate
unbounded, so no order that keeps coordinate `i` merely nonincreasing can
orient the duplicating step.  For a strict tracked coordinate, however, the
recurrence term at `succ base` already attains the required bound, and the
barrier is unconditional over the stated ordered-semiring class.

`NNRat` and `NNReal` instances coerce the Nat matrix measure.  The affine
companion gives a lexicographic witness showing why the stronger unbounded-
range route cannot be inferred in every non-Archimedean order.

Trust: kernel-only. No `sorry`/`admit`/`axiom`/`native_decide`.
-/

open scoped BigOperators

open OperatorKO7.StepDuplicating.StepDuplicatingSchema
open Finset

namespace OperatorKO7.StepDuplicating.StepDuplicatingSchema

variable {K : Type*} [CommSemiring K] [PartialOrder K] [IsStrictOrderedRing K]

abbrev FieldMatrixVec (d : Nat) (K : Type*) := Fin d → K

def fieldVecAdd {d : Nat} (u v : FieldMatrixVec d K) : FieldMatrixVec d K :=
  fun i => u i + v i

structure FieldMixedMatrix (d : Nat) (K : Type*)
    [CommSemiring K] [PartialOrder K] [IsStrictOrderedRing K] where
  coeff : Fin d → Fin d → K
  h_nonneg : ∀ i j, 0 ≤ coeff i j

namespace FieldMixedMatrix

def act {d : Nat} (A : FieldMixedMatrix d K) (v : FieldMatrixVec d K) :
    FieldMatrixVec d K :=
  fun i => ∑ j, A.coeff i j * v j

theorem act_nonneg {d : Nat} (A : FieldMixedMatrix d K) (v : FieldMatrixVec d K)
    (hv : ∀ j, 0 ≤ v j) (i : Fin d) : 0 ≤ A.act v i :=
  Finset.sum_nonneg fun j _ => mul_nonneg (A.h_nonneg i j) (hv j)

theorem diag_mul_le_act {d : Nat} (A : FieldMixedMatrix d K) (v : FieldMatrixVec d K)
    (hv : ∀ j, 0 ≤ v j) (i : Fin d) :
    A.coeff i i * v i ≤ A.act v i :=
  Finset.single_le_sum (f := fun j => A.coeff i j * v j)
    (fun j _ => mul_nonneg (A.h_nonneg i j) (hv j)) (Finset.mem_univ i)

theorem coord_le_act_of_diag_pos {d : Nat} (A : FieldMixedMatrix d K)
    (v : FieldMatrixVec d K) (hv : ∀ j, 0 ≤ v j) (i : Fin d)
    (hA : (1 : K) ≤ A.coeff i i) :
    v i ≤ A.act v i :=
  le_trans (le_mul_of_one_le_left (hv i) hA) (diag_mul_le_act A v hv i)

end FieldMixedMatrix

structure FieldNatMatrixMeasure (S : StepDuplicatingSchema) (d : Nat) (K : Type*)
    [CommSemiring K] [PartialOrder K] [IsStrictOrderedRing K] where
  eval : S.T → FieldMatrixVec d K
  base_vec : FieldMatrixVec d K
  succ_bias : FieldMatrixVec d K
  succ_mat : FieldMixedMatrix d K
  wrap_bias : FieldMatrixVec d K
  wrap_left : FieldMixedMatrix d K
  wrap_right : FieldMixedMatrix d K
  recur_bias : FieldMatrixVec d K
  recur_base : FieldMixedMatrix d K
  recur_step : FieldMixedMatrix d K
  recur_counter : FieldMixedMatrix d K
  eval_base : eval S.base = base_vec
  eval_succ :
    ∀ t, eval (S.succ t) = fieldVecAdd succ_bias (succ_mat.act (eval t))
  eval_wrap :
    ∀ x y,
      eval (S.wrap x y) =
        fieldVecAdd wrap_bias
          (fieldVecAdd (wrap_left.act (eval x)) (wrap_right.act (eval y)))
  eval_recur :
    ∀ b s n,
      eval (S.recur b s n) =
        fieldVecAdd recur_bias
          (fieldVecAdd (recur_base.act (eval b))
            (fieldVecAdd (recur_step.act (eval s)) (recur_counter.act (eval n))))
  h_eval_nonneg : ∀ t i, 0 ≤ eval t i
  h_wrap_bias_nonneg : ∀ i, 0 ≤ wrap_bias i
  h_recur_bias_nonneg : ∀ i, 0 ≤ recur_bias i

variable {S : StepDuplicatingSchema} {d : Nat}

def FieldWrapDiagPositive (M : FieldNatMatrixMeasure S d K) (i : Fin d) : Prop :=
  (1 : K) ≤ M.wrap_left.coeff i i ∧ (1 : K) ≤ M.wrap_right.coeff i i

theorem field_wrap_coord_lower_bound (M : FieldNatMatrixMeasure S d K) {i : Fin d}
    (hi : FieldWrapDiagPositive M i) (x y : S.T) :
    M.eval x i + M.eval y i ≤ M.eval (S.wrap x y) i := by
  have hx : ∀ j, 0 ≤ M.eval x j := fun j => M.h_eval_nonneg x j
  have hy : ∀ j, 0 ≤ M.eval y j := fun j => M.h_eval_nonneg y j
  have h1 := FieldMixedMatrix.coord_le_act_of_diag_pos M.wrap_left (M.eval x) hx i hi.1
  have h2 := FieldMixedMatrix.coord_le_act_of_diag_pos M.wrap_right (M.eval y) hy i hi.2
  rw [M.eval_wrap]
  simp only [fieldVecAdd]
  calc
    M.eval x i + M.eval y i
        ≤ M.wrap_left.act (M.eval x) i + M.wrap_right.act (M.eval y) i :=
      add_le_add h1 h2
    _ ≤ M.wrap_bias i +
          (M.wrap_left.act (M.eval x) i + M.wrap_right.act (M.eval y) i) :=
      le_add_of_nonneg_left (M.h_wrap_bias_nonneg i)

theorem field_recur_coord_eq (M : FieldNatMatrixMeasure S d K) (b s n : S.T) (i : Fin d) :
    M.eval (S.recur b s n) i =
      M.recur_bias i + M.recur_base.act (M.eval b) i +
        M.recur_step.act (M.eval s) i + M.recur_counter.act (M.eval n) i := by
  rw [M.eval_recur]
  simp [fieldVecAdd, add_assoc]

theorem field_coord_bounded_of_nonincreasing (M : FieldNatMatrixMeasure S d K) {i : Fin d}
    (hi : FieldWrapDiagPositive M i)
    (h : ∀ b s n : S.T,
      M.eval (S.wrap s (S.recur b s n)) i ≤ M.eval (S.recur b s (S.succ n)) i)
    (s : S.T) :
    M.eval s i ≤ M.recur_counter.act (M.eval (S.succ S.base)) i := by
  have hs := h S.base s S.base
  have hw := field_wrap_coord_lower_bound M hi s (S.recur S.base s S.base)
  have hge : M.eval s i + M.eval (S.recur S.base s S.base) i ≤
      M.eval (S.recur S.base s (S.succ S.base)) i :=
    le_trans hw hs
  have e1 := field_recur_coord_eq M S.base s S.base i
  have e2 := field_recur_coord_eq M S.base s (S.succ S.base) i
  set A :=
    M.recur_bias i + M.recur_base.act (M.eval S.base) i +
      M.recur_step.act (M.eval s) i with hA
  set B := M.recur_counter.act (M.eval S.base) i with hB
  set T := M.recur_counter.act (M.eval (S.succ S.base)) i with hT
  have inner : M.eval (S.recur S.base s S.base) i = A + B := by
    simp [A, B, e1, add_left_comm, add_comm]
  have source : M.eval (S.recur S.base s (S.succ S.base)) i = A + T := by
    simp [A, T, e2, add_left_comm, add_comm]
  have hsum : M.eval s i + (A + B) ≤ A + T := by
    simpa [inner, source] using hge
  have hBnn : 0 ≤ B :=
    FieldMixedMatrix.act_nonneg M.recur_counter (M.eval S.base)
      (fun j => M.h_eval_nonneg S.base j) i
  have : M.eval s i + B ≤ T := by
    have h' : M.eval s i + A + B ≤ A + T := by
      simpa [add_assoc] using hsum
    have h'' : A + M.eval s i + B ≤ A + T := by
      simpa [add_left_comm, add_comm] using h'
    have h''' : A + (M.eval s i + B) ≤ A + T := by
      simpa [add_assoc] using h''
    exact (add_le_add_iff_left A).1 h'''
  exact le_trans (le_add_of_nonneg_right hBnn) this

/-- A strict tracked coordinate is strictly bounded by the counter contribution
at `succ base`; this is the cancellation core of the universal strict barrier. -/
theorem field_coord_strictly_bounded_of_strict
    (M : FieldNatMatrixMeasure S d K) {i : Fin d}
    (hi : FieldWrapDiagPositive M i)
    (h : ∀ b s n : S.T,
      M.eval (S.wrap s (S.recur b s n)) i < M.eval (S.recur b s (S.succ n)) i)
    (s : S.T) :
    M.eval s i < M.recur_counter.act (M.eval (S.succ S.base)) i := by
  have hs := h S.base s S.base
  have hw := field_wrap_coord_lower_bound M hi s (S.recur S.base s S.base)
  have hge : M.eval s i + M.eval (S.recur S.base s S.base) i <
      M.eval (S.recur S.base s (S.succ S.base)) i :=
    lt_of_le_of_lt hw hs
  have e1 := field_recur_coord_eq M S.base s S.base i
  have e2 := field_recur_coord_eq M S.base s (S.succ S.base) i
  set A :=
    M.recur_bias i + M.recur_base.act (M.eval S.base) i +
      M.recur_step.act (M.eval s) i with hA
  set B := M.recur_counter.act (M.eval S.base) i with hB
  set T := M.recur_counter.act (M.eval (S.succ S.base)) i with hT
  have inner : M.eval (S.recur S.base s S.base) i = A + B := by
    simp [A, B, e1, add_left_comm, add_comm]
  have source : M.eval (S.recur S.base s (S.succ S.base)) i = A + T := by
    simp [A, T, e2, add_left_comm, add_comm]
  have hsum : M.eval s i + (A + B) < A + T := by
    simpa [inner, source] using hge
  have hBnn : 0 ≤ B :=
    FieldMixedMatrix.act_nonneg M.recur_counter (M.eval S.base)
      (fun j => M.h_eval_nonneg S.base j) i
  have hcancel : M.eval s i + B < T := by
    have h' : A + (M.eval s i + B) < A + T := by
      simpa [add_assoc, add_left_comm, add_comm] using hsum
    exact (add_lt_add_iff_left A).1 h'
  exact lt_of_le_of_lt (le_add_of_nonneg_right hBnn) hcancel

/-- The recurrence term at `succ base` attains the counter-coordinate threshold. -/
theorem field_recur_counter_coord_threshold_attained
    (M : FieldNatMatrixMeasure S d K) (i : Fin d) :
    ∃ s : S.T,
      M.recur_counter.act (M.eval (S.succ S.base)) i ≤ M.eval s i := by
  refine ⟨S.recur S.base S.base (S.succ S.base), ?_⟩
  have hbase := FieldMixedMatrix.act_nonneg M.recur_base (M.eval S.base)
    (fun j => M.h_eval_nonneg S.base j) i
  have hstep := FieldMixedMatrix.act_nonneg M.recur_step (M.eval S.base)
    (fun j => M.h_eval_nonneg S.base j) i
  have hprefix :
      0 ≤ M.recur_bias i + M.recur_base.act (M.eval S.base) i +
        M.recur_step.act (M.eval S.base) i :=
    add_nonneg (add_nonneg (M.h_recur_bias_nonneg i) hbase) hstep
  rw [field_recur_coord_eq]
  exact le_add_of_nonneg_left hprefix

private theorem two_pow_ge_self (n : Nat) : n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ']
      have : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by decide)
      omega

theorem field_eval_wrapDouble_coord_ge (M : FieldNatMatrixMeasure S d K) {i : Fin d}
    (hi : FieldWrapDiagPositive M i) (t : S.T) (k : Nat) :
    (2 ^ k : ℕ) • M.eval t i ≤ M.eval (wrapDouble S t k) i := by
  induction k with
  | zero =>
      simp [wrapDouble]
  | succ k ih =>
      have hsum := field_wrap_coord_lower_bound M hi (wrapDouble S t k) (wrapDouble S t k)
      rw [wrapDouble_succ]
      have hscale := nsmul_le_nsmul_right ih 2
      have h2e := two_nsmul (M.eval (wrapDouble S t k) i)
      have hpow :
          (2 : ℕ) • ((2 ^ k : ℕ) • M.eval t i) = (2 ^ (k + 1) : ℕ) • M.eval t i := by
        rw [← mul_nsmul', pow_succ']
      calc
        (2 ^ (k + 1) : ℕ) • M.eval t i
            = (2 : ℕ) • ((2 ^ k : ℕ) • M.eval t i) := by rw [hpow]
        _ ≤ (2 : ℕ) • M.eval (wrapDouble S t k) i := hscale
        _ = M.eval (wrapDouble S t k) i + M.eval (wrapDouble S t k) i := h2e
        _ ≤ M.eval (S.wrap (wrapDouble S t k) (wrapDouble S t k)) i := hsum

def FieldCoordHasUnboundedRange (M : FieldNatMatrixMeasure S d K) (i : Fin d) : Prop :=
  ∀ y : K, ∃ t : S.T, y ≤ M.eval t i

theorem field_coord_unbounded_of_pos [Archimedean K] (M : FieldNatMatrixMeasure S d K)
    {i : Fin d} (hi : FieldWrapDiagPositive M i)
    (hpos : ∃ t : S.T, 0 < M.eval t i) :
    FieldCoordHasUnboundedRange M i := by
  rcases hpos with ⟨t, ht⟩
  intro y
  obtain ⟨n, hn⟩ := Archimedean.arch y ht
  refine ⟨wrapDouble S t n, ?_⟩
  have hge := field_eval_wrapDouble_coord_ge M hi t n
  have hv := M.h_eval_nonneg t i
  have hpow : n • M.eval t i ≤ (2 ^ n : ℕ) • M.eval t i :=
    nsmul_le_nsmul_left hv (two_pow_ge_self n)
  exact le_trans hn (le_trans hpow hge)

theorem no_matrix_orients_dup_step_field_of_tracked_nonincreasing_of_unbounded
    (M : FieldNatMatrixMeasure S d K) {i : Fin d} (hi : FieldWrapDiagPositive M i)
    {R : FieldMatrixVec d K → FieldMatrixVec d K → Prop}
    (hR : ∀ {u v : FieldMatrixVec d K}, R u v → u i ≤ v i)
    (hunb : FieldCoordHasUnboundedRange M i) :
    ¬ (∀ (b s n : S.T),
      R (M.eval (S.wrap s (S.recur b s n))) (M.eval (S.recur b s (S.succ n)))) := by
  intro h
  have hbound :=
    field_coord_bounded_of_nonincreasing M hi (fun b s n => hR (h b s n))
  let B := M.recur_counter.act (M.eval (S.succ S.base)) i
  rcases hunb (B + 1) with ⟨s, hs⟩
  have hle : B + 1 ≤ B := le_trans hs (hbound s)
  have : (1 : K) ≤ 0 := (add_le_add_iff_left B).1 (by simpa [add_zero] using hle)
  exact (not_le_of_gt (zero_lt_one : (0 : K) < 1)) this

theorem no_matrix_orients_dup_step_field_of_tracked_nonincreasing [Archimedean K]
    (M : FieldNatMatrixMeasure S d K) {i : Fin d} (hi : FieldWrapDiagPositive M i)
    {R : FieldMatrixVec d K → FieldMatrixVec d K → Prop}
    (hR : ∀ {u v : FieldMatrixVec d K}, R u v → u i ≤ v i)
    (hpos : ∃ t : S.T, 0 < M.eval t i) :
    ¬ (∀ (b s n : S.T),
      R (M.eval (S.wrap s (S.recur b s n))) (M.eval (S.recur b s (S.succ n)))) :=
  no_matrix_orients_dup_step_field_of_tracked_nonincreasing_of_unbounded M hi hR
    (field_coord_unbounded_of_pos M hi hpos)

/-- Universal strict tracked-coordinate matrix barrier. -/
theorem no_matrix_orients_dup_step_field_of_tracked_strict
    (M : FieldNatMatrixMeasure S d K) {i : Fin d} (hi : FieldWrapDiagPositive M i)
    {R : FieldMatrixVec d K → FieldMatrixVec d K → Prop}
    (hR : ∀ {u v : FieldMatrixVec d K}, R u v → u i < v i) :
    ¬ (∀ (b s n : S.T),
      R (M.eval (S.wrap s (S.recur b s n))) (M.eval (S.recur b s (S.succ n)))) := by
  intro h
  have hbound :=
    field_coord_strictly_bounded_of_strict M hi (fun b s n => hR (h b s n))
  rcases field_recur_counter_coord_threshold_attained M i with ⟨s, hs⟩
  exact (not_lt_of_ge hs) (hbound s)

/-! ## Sharpness of the nonincreasing-coordinate premise -/

def fieldZeroMatrix (d : Nat) : FieldMixedMatrix d K where
  coeff := fun _ _ => 0
  h_nonneg := fun _ _ => le_rfl

def fieldUnitMatrixOne : FieldMixedMatrix 1 K where
  coeff := fun _ _ => 1
  h_nonneg := fun _ _ => zero_le_one

/-- The zero evaluation with unit wrapper diagonals is a live matrix model on
every duplicating schema. -/
def zeroFieldNatMatrixMeasure (S : StepDuplicatingSchema) :
    FieldNatMatrixMeasure S 1 K where
  eval := fun _ _ => 0
  base_vec := fun _ => 0
  succ_bias := fun _ => 0
  succ_mat := fieldZeroMatrix 1
  wrap_bias := fun _ => 0
  wrap_left := fieldUnitMatrixOne
  wrap_right := fieldUnitMatrixOne
  recur_bias := fun _ => 0
  recur_base := fieldZeroMatrix 1
  recur_step := fieldZeroMatrix 1
  recur_counter := fieldZeroMatrix 1
  eval_base := rfl
  eval_succ := fun _ => by
    funext i
    simp [fieldVecAdd, FieldMixedMatrix.act, fieldZeroMatrix]
  eval_wrap := fun _ _ => by
    funext i
    simp [fieldVecAdd, FieldMixedMatrix.act, fieldUnitMatrixOne]
  eval_recur := fun _ _ _ => by
    funext i
    simp [fieldVecAdd, FieldMixedMatrix.act, fieldZeroMatrix]
  h_eval_nonneg := fun _ _ => le_rfl
  h_wrap_bias_nonneg := fun _ => le_rfl
  h_recur_bias_nonneg := fun _ => le_rfl

theorem zeroFieldNatMatrixMeasure_wrapDiagPositive :
    FieldWrapDiagPositive (zeroFieldNatMatrixMeasure (K := K) S) (0 : Fin 1) := by
  constructor <;> simp [zeroFieldNatMatrixMeasure, fieldUnitMatrixOne]

theorem zeroFieldNatMatrixMeasure_orients_nonincreasing :
    ∀ b s n : S.T,
      (zeroFieldNatMatrixMeasure (K := K) S).eval (S.wrap s (S.recur b s n)) 0 ≤
        (zeroFieldNatMatrixMeasure (K := K) S).eval (S.recur b s (S.succ n)) 0 := by
  intro b s n
  rfl

theorem zeroFieldNatMatrixMeasure_has_no_positive_coordinate :
    ¬ ∃ t : S.T, 0 < (zeroFieldNatMatrixMeasure (K := K) S).eval t 0 := by
  simp [zeroFieldNatMatrixMeasure]

/-- Positivity or an equivalent unboundedness premise is necessary for the
merely nonincreasing matrix theorem.  Without it, a nontrivial wrapper matrix
can carry the constant-zero evaluation and orient every instance weakly. -/
theorem tracked_nonincreasing_positivity_hypothesis_necessary :
    FieldWrapDiagPositive (zeroFieldNatMatrixMeasure (K := K) S) (0 : Fin 1) ∧
    (∀ b s n : S.T,
      (zeroFieldNatMatrixMeasure (K := K) S).eval (S.wrap s (S.recur b s n)) 0 ≤
        (zeroFieldNatMatrixMeasure (K := K) S).eval (S.recur b s (S.succ n)) 0) ∧
    ¬ ∃ t : S.T, 0 < (zeroFieldNatMatrixMeasure (K := K) S).eval t 0 :=
  ⟨zeroFieldNatMatrixMeasure_wrapDiagPositive,
    zeroFieldNatMatrixMeasure_orients_nonincreasing,
    zeroFieldNatMatrixMeasure_has_no_positive_coordinate⟩

def fieldMixedMatrixOfNat {d : Nat} (A : MixedMatrix d) : FieldMixedMatrix d K where
  coeff i j := (A.coeff i j : K)
  h_nonneg i j := by exact_mod_cast (Nat.zero_le (A.coeff i j))

def fieldNatMatrixMeasureOfNat (M : NatMatrixMeasure S d) :
    FieldNatMatrixMeasure S d K where
  eval := fun t i => (M.eval t i : K)
  base_vec := fun i => (M.base_vec i : K)
  succ_bias := fun i => (M.succ_bias i : K)
  succ_mat := fieldMixedMatrixOfNat M.succ_mat
  wrap_bias := fun i => (M.wrap_bias i : K)
  wrap_left := fieldMixedMatrixOfNat M.wrap_left
  wrap_right := fieldMixedMatrixOfNat M.wrap_right
  recur_bias := fun i => (M.recur_bias i : K)
  recur_base := fieldMixedMatrixOfNat M.recur_base
  recur_step := fieldMixedMatrixOfNat M.recur_step
  recur_counter := fieldMixedMatrixOfNat M.recur_counter
  eval_base := by
    funext i
    simp [M.eval_base]
  eval_succ := fun t => by
    funext i
    simp [M.eval_succ, fieldVecAdd, FieldMixedMatrix.act, fieldMixedMatrixOfNat, vecAdd,
      MixedMatrix.act, Nat.cast_add, Nat.cast_mul, Nat.cast_sum]
  eval_wrap := fun x y => by
    funext i
    simp [M.eval_wrap, fieldVecAdd, FieldMixedMatrix.act, fieldMixedMatrixOfNat, vecAdd,
      MixedMatrix.act, Nat.cast_add, Nat.cast_mul, Nat.cast_sum]
  eval_recur := fun b s n => by
    funext i
    simp [M.eval_recur, fieldVecAdd, FieldMixedMatrix.act, fieldMixedMatrixOfNat, vecAdd,
      MixedMatrix.act, Nat.cast_add, Nat.cast_mul, Nat.cast_sum]
  h_eval_nonneg := fun t i => by exact_mod_cast (Nat.zero_le (M.eval t i))
  h_wrap_bias_nonneg := fun i => by exact_mod_cast (Nat.zero_le (M.wrap_bias i))
  h_recur_bias_nonneg := fun i => by exact_mod_cast (Nat.zero_le (M.recur_bias i))

theorem fieldWrapDiagPositive_ofNat (M : NatMatrixMeasure S d) {i : Fin d}
    (hi : WrapDiagPositive M i) :
    FieldWrapDiagPositive (fieldNatMatrixMeasureOfNat (K := K) M) i := by
  constructor
  · change (1 : K) ≤ (M.wrap_left.coeff i i : K)
    exact_mod_cast hi.1
  · change (1 : K) ≤ (M.wrap_right.coeff i i : K)
    exact_mod_cast hi.2

theorem no_matrix_orients_dup_step_nnrat (M : NatMatrixMeasure S d) {i : Fin d}
    (hi : WrapDiagPositive M i)
    {R : FieldMatrixVec d NNRat → FieldMatrixVec d NNRat → Prop}
    (hR : ∀ {u v : FieldMatrixVec d NNRat}, R u v → u i < v i) :
    ¬ (∀ (b s n : S.T),
      R ((fieldNatMatrixMeasureOfNat (K := NNRat) M).eval (S.wrap s (S.recur b s n)))
        ((fieldNatMatrixMeasureOfNat (K := NNRat) M).eval (S.recur b s (S.succ n)))) :=
  no_matrix_orients_dup_step_field_of_tracked_strict
    (fieldNatMatrixMeasureOfNat (K := NNRat) M)
    (fieldWrapDiagPositive_ofNat (K := NNRat) M hi) hR

theorem no_matrix_orients_dup_step_nnreal (M : NatMatrixMeasure S d) {i : Fin d}
    (hi : WrapDiagPositive M i)
    {R : FieldMatrixVec d NNReal → FieldMatrixVec d NNReal → Prop}
    (hR : ∀ {u v : FieldMatrixVec d NNReal}, R u v → u i < v i) :
    ¬ (∀ (b s n : S.T),
      R ((fieldNatMatrixMeasureOfNat (K := NNReal) M).eval (S.wrap s (S.recur b s n)))
        ((fieldNatMatrixMeasureOfNat (K := NNReal) M).eval (S.recur b s (S.succ n)))) :=
  no_matrix_orients_dup_step_field_of_tracked_strict
    (fieldNatMatrixMeasureOfNat (K := NNReal) M)
    (fieldWrapDiagPositive_ofNat (K := NNReal) M hi) hR

end OperatorKO7.StepDuplicating.StepDuplicatingSchema
