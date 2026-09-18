import OperatorKO7.Meta.BarrierPumpDischarge_Schema
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.NNRat.Lemmas
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Prod.Lex

set_option autoImplicit false

/-!
# Affine barrier over ordered semirings

Coefficients live in a partially ordered commutative semiring `K`. Wrapper
coefficients are at least `1` and values are nonnegative. Strict orientation
is Lucas `δ`-order: `eval (reduct) + δ ≤ eval (source)` with `0 < δ`.

The duplicating step cannot `δ`-orient over any carrier satisfying the stated
ordered-semiring laws.  The recurrence term at `succ base` already attains the
single threshold needed by the contradiction.  An Archimedean hypothesis is
therefore needed only for the stronger, independent conclusion that one
positive value generates an unbounded wrapper range.

`NNRat` and `NNReal` are the nonnegative `ℚ` and `ℝ` instances. The Nat
affine barrier embeds by coercion.  A lexicographic example records why the
unbounded-range corollary does not follow in arbitrary non-Archimedean orders.

Trust: kernel-only. No `sorry`/`admit`/`axiom`/`native_decide`.
-/

open OperatorKO7.StepDuplicating.StepDuplicatingSchema

namespace OperatorKO7.StepDuplicating.StepDuplicatingSchema

/-- Affine measure with coefficients in `K`. -/
structure FieldAffineMeasure (S : StepDuplicatingSchema) (K : Type*)
    [CommSemiring K] [PartialOrder K] [IsStrictOrderedRing K] where
  eval : S.T → K
  c_base : K
  succ_bias : K
  succ_scale : K
  wrap_const : K
  wrap_left : K
  wrap_right : K
  recur_const : K
  recur_base : K
  recur_step : K
  recur_counter : K
  eval_base : eval S.base = c_base
  eval_succ : ∀ t, eval (S.succ t) = succ_bias + succ_scale * eval t
  eval_wrap : ∀ x y, eval (S.wrap x y) = wrap_const + wrap_left * eval x + wrap_right * eval y
  eval_recur :
    ∀ b s n,
      eval (S.recur b s n) =
        recur_const + recur_base * eval b + recur_step * eval s + recur_counter * eval n
  h_wrap_left_pos : (1 : K) ≤ wrap_left
  h_wrap_right_pos : (1 : K) ≤ wrap_right
  h_wrap_const_nonneg : 0 ≤ wrap_const
  h_eval_nonneg : ∀ t, 0 ≤ eval t
  h_succ_bias_nonneg : 0 ≤ succ_bias
  h_succ_scale_nonneg : 0 ≤ succ_scale
  h_recur_const_nonneg : 0 ≤ recur_const
  h_recur_base_nonneg : 0 ≤ recur_base
  h_recur_step_nonneg : 0 ≤ recur_step
  h_recur_counter_nonneg : 0 ≤ recur_counter

variable {S : StepDuplicatingSchema} {K : Type*}
  [CommSemiring K] [PartialOrder K] [IsStrictOrderedRing K]

/-- Lucas `δ`-orientation of the duplicating step. -/
def FieldAffineOrients (M : FieldAffineMeasure S K) (δ : K) : Prop :=
  ∀ b s n : S.T,
    M.eval (S.wrap s (S.recur b s n)) + δ ≤ M.eval (S.recur b s (S.succ n))

/-- Unbounded range in `K`. -/
def FieldHasUnboundedRange (M : FieldAffineMeasure S K) : Prop :=
  ∀ y : K, ∃ t : S.T, y ≤ M.eval t

theorem eval_wrap_ge_sum (M : FieldAffineMeasure S K) (x y : S.T) :
    M.eval x + M.eval y ≤ M.eval (S.wrap x y) := by
  have hx := M.h_eval_nonneg x
  have hy := M.h_eval_nonneg y
  have hL := le_mul_of_one_le_left hx M.h_wrap_left_pos
  have hR := le_mul_of_one_le_left hy M.h_wrap_right_pos
  rw [M.eval_wrap]
  calc
    M.eval x + M.eval y
        ≤ M.wrap_left * M.eval x + M.wrap_right * M.eval y := add_le_add hL hR
    _ ≤ M.wrap_const + (M.wrap_left * M.eval x + M.wrap_right * M.eval y) :=
      le_add_of_nonneg_left M.h_wrap_const_nonneg
    _ = M.wrap_const + M.wrap_left * M.eval x + M.wrap_right * M.eval y := by
      simp [add_assoc]

private theorem two_pow_ge_self (n : Nat) : n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ']
      have : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by decide)
      omega

theorem eval_wrapDouble_ge_two_pow (M : FieldAffineMeasure S K) {t : S.T}
    (k : Nat) :
    (2 ^ k : ℕ) • M.eval t ≤ M.eval (wrapDouble S t k) := by
  induction k with
  | zero =>
      simp [wrapDouble]
  | succ k ih =>
      have hsum := eval_wrap_ge_sum M (wrapDouble S t k) (wrapDouble S t k)
      rw [wrapDouble_succ]
      have hscale :
          (2 : ℕ) • ((2 ^ k : ℕ) • M.eval t)
            ≤ (2 : ℕ) • M.eval (wrapDouble S t k) :=
        nsmul_le_nsmul_right ih 2
      have h2e :
          (2 : ℕ) • M.eval (wrapDouble S t k)
            = M.eval (wrapDouble S t k) + M.eval (wrapDouble S t k) :=
        two_nsmul _
      have hpow :
          (2 : ℕ) • ((2 ^ k : ℕ) • M.eval t) = (2 ^ (k + 1) : ℕ) • M.eval t := by
        rw [← mul_nsmul', pow_succ']
      calc
        (2 ^ (k + 1) : ℕ) • M.eval t
            = (2 : ℕ) • ((2 ^ k : ℕ) • M.eval t) := by rw [hpow]
        _ ≤ (2 : ℕ) • M.eval (wrapDouble S t k) := hscale
        _ = M.eval (wrapDouble S t k) + M.eval (wrapDouble S t k) := h2e
        _ ≤ M.eval (S.wrap (wrapDouble S t k) (wrapDouble S t k)) := hsum

theorem field_unbounded_of_pos [Archimedean K] (M : FieldAffineMeasure S K)
    (hpos : ∃ t : S.T, 0 < M.eval t) :
    FieldHasUnboundedRange M := by
  rcases hpos with ⟨t, ht⟩
  intro y
  obtain ⟨n, hn⟩ := Archimedean.arch y ht
  refine ⟨wrapDouble S t n, ?_⟩
  have hge := eval_wrapDouble_ge_two_pow (t := t) M n
  have hv := M.h_eval_nonneg t
  have hpow : n • M.eval t ≤ (2 ^ n : ℕ) • M.eval t :=
    nsmul_le_nsmul_left hv (two_pow_ge_self n)
  exact le_trans hn (le_trans hpow hge)

theorem no_affine_orients_dup_step_field_of_threshold
    (M : FieldAffineMeasure S K) (δ : K) (hδ : 0 < δ) (s : S.T)
    (hs : M.recur_counter * (M.succ_bias + M.succ_scale * M.c_base) ≤ M.eval s) :
    ¬ FieldAffineOrients M δ := by
  intro h
  let T := M.recur_counter * (M.succ_bias + M.succ_scale * M.c_base)
  let Sval := M.eval s
  let A := M.recur_const + M.recur_base * M.c_base + M.recur_step * Sval
  let B := M.recur_counter * M.c_base
  have hspec := h S.base s S.base
  have hinnerAB :
      M.eval (S.recur S.base s S.base) = A + B := by
    simp [A, B, Sval, M.eval_recur, M.eval_base, add_assoc, add_left_comm, add_comm]
  have hrhs :
      M.eval (S.recur S.base s (S.succ S.base)) = A + T := by
    simp [A, T, Sval, M.eval_recur, M.eval_base, M.eval_succ, mul_add,
      add_left_comm, add_comm]
  have hsum : Sval + (A + B) ≤ M.eval (S.wrap s (S.recur S.base s S.base)) := by
    simpa [Sval, hinnerAB] using eval_wrap_ge_sum M s (S.recur S.base s S.base)
  have hB : 0 ≤ B :=
    mul_nonneg M.h_recur_counter_nonneg (by simpa [M.eval_base] using M.h_eval_nonneg S.base)
  have hAT : A + T ≤ Sval + (A + B) := by
    have hTS : T ≤ Sval := hs
    calc
      A + T ≤ A + Sval := add_le_add_left hTS A
      _ ≤ A + Sval + B := le_add_of_nonneg_right hB
      _ = Sval + (A + B) := by
        simp [add_left_comm, add_comm]
  have hge : A + T ≤ M.eval (S.wrap s (S.recur S.base s S.base)) :=
    le_trans hAT hsum
  have hbnd : M.eval (S.wrap s (S.recur S.base s S.base)) + δ ≤ A + T := by
    simpa [hrhs] using hspec
  have hfinal : A + T + δ ≤ A + T :=
    le_trans (add_le_add_right hge δ) hbnd
  have hδle : δ ≤ 0 :=
    (add_le_add_iff_left (A + T)).1 (by simpa [add_zero] using hfinal)
  exact (not_le_of_gt hδ) hδle

theorem no_affine_orients_dup_step_field_of_unbounded
    (M : FieldAffineMeasure S K) (δ : K) (hδ : 0 < δ)
    (hunb : FieldHasUnboundedRange M) :
    ¬ FieldAffineOrients M δ := by
  let T := M.recur_counter * (M.succ_bias + M.succ_scale * M.c_base)
  rcases hunb T with ⟨s, hs⟩
  exact no_affine_orients_dup_step_field_of_threshold M δ hδ s hs

/-- The recurrence term at `succ base` attains the exact threshold needed by
the affine contradiction; no Archimedean or global unboundedness assumption is
required. -/
theorem field_recur_counter_threshold_attained (M : FieldAffineMeasure S K) :
    ∃ s : S.T,
      M.recur_counter * (M.succ_bias + M.succ_scale * M.c_base) ≤ M.eval s := by
  refine ⟨S.recur S.base S.base (S.succ S.base), ?_⟩
  have hc : 0 ≤ M.c_base := by
    simpa [M.eval_base] using M.h_eval_nonneg S.base
  have hprefix :
      0 ≤ M.recur_const + M.recur_base * M.c_base + M.recur_step * M.c_base :=
    add_nonneg
      (add_nonneg M.h_recur_const_nonneg (mul_nonneg M.h_recur_base_nonneg hc))
      (mul_nonneg M.h_recur_step_nonneg hc)
  rw [M.eval_recur, M.eval_succ, M.eval_base]
  exact le_add_of_nonneg_left hprefix

/-- Universal affine barrier over the stated ordered-semiring class. -/
theorem no_affine_orients_dup_step_field (M : FieldAffineMeasure S K) (δ : K)
    (hδ : 0 < δ) :
    ¬ FieldAffineOrients M δ := by
  rcases field_recur_counter_threshold_attained M with ⟨s, hs⟩
  exact no_affine_orients_dup_step_field_of_threshold M δ hδ s hs

/-- Coerce a Nat affine measure into `NNRat`. -/
def fieldAffineMeasureNNRat (M : AffineMeasure S) : FieldAffineMeasure S NNRat where
  eval := fun t => (M.eval t : NNRat)
  c_base := (M.c_base : NNRat)
  succ_bias := (M.succ_bias : NNRat)
  succ_scale := (M.succ_scale : NNRat)
  wrap_const := (M.wrap_const : NNRat)
  wrap_left := (M.wrap_left : NNRat)
  wrap_right := (M.wrap_right : NNRat)
  recur_const := (M.recur_const : NNRat)
  recur_base := (M.recur_base : NNRat)
  recur_step := (M.recur_step : NNRat)
  recur_counter := (M.recur_counter : NNRat)
  eval_base := by simp [M.eval_base]
  eval_succ := fun t => by simp [M.eval_succ]
  eval_wrap := fun x y => by simp [M.eval_wrap]
  eval_recur := fun b s n => by simp [M.eval_recur]
  h_wrap_left_pos := by exact_mod_cast M.h_wrap_left_pos
  h_wrap_right_pos := by exact_mod_cast M.h_wrap_right_pos
  h_wrap_const_nonneg := by exact_mod_cast (Nat.zero_le M.wrap_const)
  h_eval_nonneg := fun t => by exact_mod_cast (Nat.zero_le (M.eval t))
  h_succ_bias_nonneg := by exact_mod_cast (Nat.zero_le M.succ_bias)
  h_succ_scale_nonneg := by exact_mod_cast (Nat.zero_le M.succ_scale)
  h_recur_const_nonneg := by exact_mod_cast (Nat.zero_le M.recur_const)
  h_recur_base_nonneg := by exact_mod_cast (Nat.zero_le M.recur_base)
  h_recur_step_nonneg := by exact_mod_cast (Nat.zero_le M.recur_step)
  h_recur_counter_nonneg := by exact_mod_cast (Nat.zero_le M.recur_counter)

/-- Coerce a Nat affine measure into `NNReal`. -/
def fieldAffineMeasureNNReal (M : AffineMeasure S) : FieldAffineMeasure S NNReal where
  eval := fun t => (M.eval t : NNReal)
  c_base := (M.c_base : NNReal)
  succ_bias := (M.succ_bias : NNReal)
  succ_scale := (M.succ_scale : NNReal)
  wrap_const := (M.wrap_const : NNReal)
  wrap_left := (M.wrap_left : NNReal)
  wrap_right := (M.wrap_right : NNReal)
  recur_const := (M.recur_const : NNReal)
  recur_base := (M.recur_base : NNReal)
  recur_step := (M.recur_step : NNReal)
  recur_counter := (M.recur_counter : NNReal)
  eval_base := by simp [M.eval_base]
  eval_succ := fun t => by simp [M.eval_succ]
  eval_wrap := fun x y => by simp [M.eval_wrap]
  eval_recur := fun b s n => by simp [M.eval_recur]
  h_wrap_left_pos := by exact_mod_cast M.h_wrap_left_pos
  h_wrap_right_pos := by exact_mod_cast M.h_wrap_right_pos
  h_wrap_const_nonneg := by exact_mod_cast (Nat.zero_le M.wrap_const)
  h_eval_nonneg := fun t => by exact_mod_cast (Nat.zero_le (M.eval t))
  h_succ_bias_nonneg := by exact_mod_cast (Nat.zero_le M.succ_bias)
  h_succ_scale_nonneg := by exact_mod_cast (Nat.zero_le M.succ_scale)
  h_recur_const_nonneg := by exact_mod_cast (Nat.zero_le M.recur_const)
  h_recur_base_nonneg := by exact_mod_cast (Nat.zero_le M.recur_base)
  h_recur_step_nonneg := by exact_mod_cast (Nat.zero_le M.recur_step)
  h_recur_counter_nonneg := by exact_mod_cast (Nat.zero_le M.recur_counter)

theorem no_affine_orients_dup_step_nnrat (M : AffineMeasure S) :
    ¬ FieldAffineOrients (fieldAffineMeasureNNRat M) (1 : NNRat) :=
  no_affine_orients_dup_step_field (fieldAffineMeasureNNRat M) (1 : NNRat) (by decide)

theorem no_affine_orients_dup_step_nnreal (M : AffineMeasure S) :
    ¬ FieldAffineOrients (fieldAffineMeasureNNReal M) (1 : NNReal) :=
  no_affine_orients_dup_step_field (fieldAffineMeasureNNReal M) (1 : NNReal)
    zero_lt_one

/-! The unbounded-range route is genuinely Archimedean: doubling `(0,1)` in
lex `ℕ × ℕ` stays below `(1,0)`.  This does not limit the universal barrier,
whose proof above uses an attained recurrence threshold instead. -/

def lexDouble : Nat → Lex (Nat × Nat)
  | 0 => toLex (0, 1)
  | k + 1 =>
      let p := ofLex (lexDouble k)
      toLex (p.1 + p.1, p.2 + p.2)

theorem lexDouble_fst_zero (k : Nat) : (ofLex (lexDouble k)).1 = 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp [lexDouble, ih]

theorem lex_double_lt_one_zero (k : Nat) : lexDouble k < toLex (1, 0) := by
  have h0 := lexDouble_fst_zero k
  have hlt : (ofLex (lexDouble k)).1 < 1 := by
    rw [h0]
    exact Nat.zero_lt_one
  exact Prod.Lex.left (ofLex (lexDouble k)).2 0 hlt

theorem archimedean_unbounded_route_separated_by_lex :
    ∀ k : Nat, ¬ toLex (1, 0) ≤ lexDouble k := by
  intro k h
  exact not_le_of_gt (lex_double_lt_one_zero k) h

/-- Backwards-compatible name for the lexicographic separation theorem. -/
theorem archimedean_load_bearing_lex :
    ∀ k : Nat, ¬ toLex (1, 0) ≤ lexDouble k :=
  archimedean_unbounded_route_separated_by_lex

end OperatorKO7.StepDuplicating.StepDuplicatingSchema
