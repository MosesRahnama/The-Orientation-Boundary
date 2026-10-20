import OperatorKO7.Meta.Methods.AlgebraicInterpretationRows

/-!
# Natural matrix method semantics

The direct method uses natural matrices, componentwise weak comparison, and
strict comparison at one coordinate. Strict matrix monotonicity is proved equivalent
to positivity of the corresponding diagonal entry. The order is well founded.
The schema obstruction is then applied to each interpretation's own matrices.

The triangular subclass restricts every argument matrix, including successor
and all three recursor arguments, to zero below the diagonal and diagonal
entries at most one. These are the restrictions in Moser, Schnabl, Waldmann,
FSTTCS 2008, Definition 3; the direct order is that of Endrullis, Waldmann,
Zantema, JAR 2008, Section 4. No complexity bound is asserted here.
-/

set_option autoImplicit false
open scoped BigOperators

namespace OperatorKO7.Methods.NaturalMatrixInterpretationRows

open OperatorKO7.StepDuplicating
open OperatorKO7.StepDuplicating.StepDuplicatingSchema
open OperatorKO7.Methods.AlgebraicInterpretationRows

/-- Natural matrix action preserves coordinatewise comparison. -/
theorem matrixAct_mono {d : Nat} (A : MixedMatrix d) {u v : MatrixVec d}
    (h : ∀ i, u i ≤ v i) : ∀ i, A.act u i ≤ A.act v i := by
  intro i
  exact Finset.sum_le_sum (fun j _ => Nat.mul_le_mul_left _ (h j))

/-- A positive tracked diagonal preserves the actual weak-strict vector order. -/
theorem matrixAct_strict {d : Nat} (A : MixedMatrix d) (i : Fin d)
    (hA : 1 ≤ A.coeff i i) {u v : MatrixVec d} (h : VecLeLt i u v) :
    VecLeLt i (A.act u) (A.act v) := by
  refine ⟨matrixAct_mono A h.1, ?_⟩
  apply Finset.sum_lt_sum
  · intro j _
    exact Nat.mul_le_mul_left _ (h.1 j)
  · exact ⟨i, Finset.mem_univ i, Nat.mul_lt_mul_of_pos_left h.2 hA⟩

/-- The positive diagonal condition is necessary as well as sufficient. -/
theorem matrixAct_strict_iff {d : Nat} (A : MixedMatrix d) (i : Fin d) :
    (∀ {u v : MatrixVec d}, VecLeLt i u v → VecLeLt i (A.act u) (A.act v)) ↔
      1 ≤ A.coeff i i := by
  constructor
  · intro h
    have hv : VecLeLt i (fun _ => 0) (fun j => if j = i then 1 else 0) := by
      constructor
      · intro j; exact Nat.zero_le _
      · simp
    have hi := (h hv).2
    simpa [MixedMatrix.act] using hi
  · exact matrixAct_strict A i

/-- Adding a fixed bias preserves the weak-strict order. -/
theorem vecAdd_strict {d : Nat} (c : MatrixVec d) (i : Fin d)
    {u v : MatrixVec d} (h : VecLeLt i u v) :
    VecLeLt i (vecAdd c u) (vecAdd c v) := by
  exact ⟨fun j => Nat.add_le_add_left (h.1 j) _, Nat.add_lt_add_left h.2 _⟩

/-- The vector order is well founded in every dimension with a tracked coordinate. -/
theorem vectorOrder_wellFounded {d : Nat} (i : Fin d) :
    WellFounded (VecLeLt i) :=
  Subrelation.wf (fun {_ _} h => h.2) (measure (fun v : MatrixVec d => v i)).wf

/-- The strict and weak comparisons satisfy reduction-pair compatibility. -/
theorem vectorOrder_compatible {d : Nat} (i : Fin d) {u v w : MatrixVec d}
    (huv : VecLeLt i u v) (hvw : ∀ j, v j ≤ w j) : VecLeLt i u w :=
  ⟨fun j => (huv.1 j).trans (hvw j), huv.2.trans_le (hvw i)⟩

theorem vectorOrder_weak_strict {d : Nat} (i : Fin d) {u v w : MatrixVec d}
    (huv : ∀ j, u j ≤ v j) (hvw : VecLeLt i v w) : VecLeLt i u w :=
  ⟨fun j => (huv j).trans (hvw.1 j), (huv i).trans_lt hvw.2⟩

theorem vectorOrder_compatibility {d : Nat} (i : Fin d) :
    (∀ {u v w : MatrixVec d}, VecLeLt i u v →
      (∀ j, v j ≤ w j) → VecLeLt i u w) ∧
    (∀ {u v w : MatrixVec d}, (∀ j, u j ≤ v j) →
      VecLeLt i v w → VecLeLt i u w) :=
  ⟨vectorOrder_compatible i, vectorOrder_weak_strict i⟩

/-- A constructor of arbitrary finite arity interpreted by matrices and a bias. -/
structure MatrixOperation (d n : Nat) where
  bias : MatrixVec d
  argument : Fin n → MixedMatrix d

def MatrixOperation.eval {d n : Nat} (F : MatrixOperation d n)
    (v : Fin n → MatrixVec d) : MatrixVec d :=
  fun i => F.bias i + ∑ a, (F.argument a).act (v a) i

theorem MatrixOperation.weak_mono {d n : Nat} (F : MatrixOperation d n)
    {u v : Fin n → MatrixVec d} (h : ∀ a i, u a i ≤ v a i) :
    ∀ i, F.eval u i ≤ F.eval v i := by
  intro i
  exact Nat.add_le_add_left (Finset.sum_le_sum
    (fun a _ => matrixAct_mono (F.argument a) (h a) i)) _

/-- A strict argument comparison and weak comparisons elsewhere imply strict output. -/
theorem MatrixOperation.strict_mono_of_weak {d n : Nat} (F : MatrixOperation d n)
    (i : Fin d) (k : Fin n) (hF : 1 ≤ (F.argument k).coeff i i)
    {u v : Fin n → MatrixVec d} (h : VecLeLt i (u k) (v k))
    (hother : ∀ a, a ≠ k → ∀ j, u a j ≤ v a j) :
    VecLeLt i (F.eval u) (F.eval v) := by
  have hweak : ∀ a j, u a j ≤ v a j := by
    intro a j
    by_cases ha : a = k
    · subst a; exact h.1 j
    · exact hother a ha j
  refine ⟨F.weak_mono hweak, Nat.add_lt_add_left ?_ _⟩
  apply Finset.sum_lt_sum
  · intro a _
    exact matrixAct_mono (F.argument a) (hweak a) i
  · exact ⟨k, Finset.mem_univ k, (matrixAct_strict (F.argument k) i hF h).2⟩

/-- The usual single-argument monotonicity law is a special case. -/
theorem MatrixOperation.strict_mono {d n : Nat} (F : MatrixOperation d n)
    (i : Fin d) (k : Fin n) (hF : 1 ≤ (F.argument k).coeff i i)
    {u v : Fin n → MatrixVec d} (h : VecLeLt i (u k) (v k))
    (heq : ∀ a, a ≠ k → u a = v a) : VecLeLt i (F.eval u) (F.eval v) :=
  F.strict_mono_of_weak i k hF h (fun a ha j => le_of_eq (congrFun (heq a ha) j))

/-- The six argument matrices of the duplicating schema signature. -/
inductive MatrixArgument where
  | succ | wrapLeft | wrapRight | recurBase | recurStep | recurCounter
  deriving DecidableEq, Repr

def argumentMatrix {S : StepDuplicatingSchema} {d : Nat}
    (M : NatMatrixMeasure S d) : MatrixArgument → MixedMatrix d
  | .succ => M.succ_mat
  | .wrapLeft => M.wrap_left
  | .wrapRight => M.wrap_right
  | .recurBase => M.recur_base
  | .recurStep => M.recur_step
  | .recurCounter => M.recur_counter

/-- A natural matrix interpretation with the published direct-method laws. -/
structure NaturalMatrixMethod (S : StepDuplicatingSchema) (d : Nat) [NeZero d] where
  interpretation : NatMatrixMeasure S d
  monotone : EWZMonotoneInterpretation interpretation

theorem NaturalMatrixMethod.argument_strict {S : StepDuplicatingSchema}
    {d : Nat} [NeZero d] (M : NaturalMatrixMethod S d) (a : MatrixArgument)
    {u v : MatrixVec d} (h : VecLeLt 0 u v) :
    VecLeLt 0 ((argumentMatrix M.interpretation a).act u)
      ((argumentMatrix M.interpretation a).act v) := by
  apply matrixAct_strict _ _ _ h
  cases a
  · exact M.monotone.succ_mat
  · exact M.monotone.wrap_left
  · exact M.monotone.wrap_right
  · exact M.monotone.recur_base
  · exact M.monotone.recur_step
  · exact M.monotone.recur_counter

theorem NaturalMatrixMethod.not_orients {S : StepDuplicatingSchema}
    {d : Nat} [NeZero d] (M : NaturalMatrixMethod S d) :
    ¬ ∀ b s n : S.T, VecLeLt 0
      (M.interpretation.eval (S.wrap s (S.recur b s n)))
      (M.interpretation.eval (S.recur b s (S.succ n))) :=
  no_ewz_monotone_orients_dup_step M.interpretation M.monotone

/-- Every argument matrix satisfies the triangular complexity restrictions. -/
structure TriangularMatrixMethod (S : StepDuplicatingSchema) (d : Nat) [NeZero d]
    extends NaturalMatrixMethod S d where
  upper : ∀ a, UpperTriangular (argumentMatrix interpretation a)
  diagonal_le_one : ∀ a i, (argumentMatrix interpretation a).coeff i i ≤ 1

theorem TriangularMatrixMethod.not_orients {S : StepDuplicatingSchema}
    {d : Nat} [NeZero d] (M : TriangularMatrixMethod S d) :
    ¬ ∀ b s n : S.T, VecLeLt 0
      (M.interpretation.eval (S.wrap s (S.recur b s n)))
      (M.interpretation.eval (S.recur b s (S.succ n))) :=
  M.toNaturalMatrixMethod.not_orients

/-- The identity matrix provides an interpretation in every positive dimension. -/
def identityMatrix (d : Nat) : MixedMatrix d where
  coeff i j := if i = j then 1 else 0

@[simp] theorem identityMatrix_act {d : Nat} (v : MatrixVec d) :
    (identityMatrix d).act v = v := by
  funext i
  simp [identityMatrix, MixedMatrix.act]

def sizeMatrixMeasure (d : Nat) : NatMatrixMeasure freeSchema d where
  eval := fun t _ => unitAffineNatEval t
  base_vec := fun _ => 1
  succ_bias := fun _ => 1
  succ_mat := identityMatrix d
  wrap_bias := fun _ => 1
  wrap_left := identityMatrix d
  wrap_right := identityMatrix d
  recur_bias := fun _ => 1
  recur_base := identityMatrix d
  recur_step := identityMatrix d
  recur_counter := identityMatrix d
  eval_base := rfl
  eval_succ := by intro t; funext i; simp [freeSchema, unitAffineNatEval, vecAdd, identityMatrix]
  eval_wrap := by
    intro x y; funext i; simp [freeSchema, unitAffineNatEval, vecAdd, identityMatrix, Nat.add_assoc]
  eval_recur := by
    intro b s n; funext i
    simp [freeSchema, unitAffineNatEval, vecAdd, identityMatrix, Nat.add_assoc]

def sizeNaturalMatrixMethod (d : Nat) [NeZero d] : NaturalMatrixMethod freeSchema d where
  interpretation := sizeMatrixMeasure d
  monotone := by constructor <;> simp [EWZMonotone, sizeMatrixMeasure, identityMatrix]

def sizeTriangularMatrixMethod (d : Nat) [NeZero d] : TriangularMatrixMethod freeSchema d where
  toNaturalMatrixMethod := sizeNaturalMatrixMethod d
  upper := by
    intro a
    refine ⟨?_, ?_⟩
    · intro i j hij
      have hne : i ≠ j := by intro h; subst j; exact Nat.lt_irrefl _ hij
      cases a <;> simp [argumentMatrix, sizeNaturalMatrixMethod, sizeMatrixMeasure,
        identityMatrix, hne]
    · intro i
      cases a <;> simp [argumentMatrix, sizeNaturalMatrixMethod, sizeMatrixMeasure, identityMatrix]
  diagonal_le_one := by
    intro a i
    cases a <;> simp [argumentMatrix, sizeNaturalMatrixMethod, sizeMatrixMeasure, identityMatrix]

theorem sizeNaturalMatrixMethod_strict_witness (d : Nat) [NeZero d] :
    VecLeLt 0 ((sizeNaturalMatrixMethod d).interpretation.eval .base)
      ((sizeNaturalMatrixMethod d).interpretation.eval (.succ .base)) := by
  constructor
  · intro i; change (1 : Nat) ≤ 2; decide
  · change (1 : Nat) < 2; decide

/-- Both named-method classes have a nonconstant instance in every positive dimension. -/
theorem natural_matrix_classes_inhabited (d : Nat) [NeZero d] :
    Nonempty (NaturalMatrixMethod freeSchema d) ∧
      Nonempty (TriangularMatrixMethod freeSchema d) ∧
      (sizeMatrixMeasure d).eval .base ≠ (sizeMatrixMeasure d).eval (.succ .base) := by
  refine ⟨⟨sizeNaturalMatrixMethod d⟩, ⟨sizeTriangularMatrixMethod d⟩, ?_⟩
  intro h
  have hi := congrFun h (0 : Fin d)
  change (1 : Nat) = 1 + 1 at hi
  omega

abbrev NaturalMatrixExactRowClaim : Prop :=
  ∀ (S : StepDuplicatingSchema) (d : Nat) [NeZero d] (M : NaturalMatrixMethod S d),
    ¬ ∀ b s n : S.T, VecLeLt 0
      (M.interpretation.eval (S.wrap s (S.recur b s n)))
      (M.interpretation.eval (S.recur b s (S.succ n)))

theorem naturalMatrix_exact_row : NaturalMatrixExactRowClaim :=
  fun _ _ _ M => M.not_orients

abbrev TriangularMatrixExactRowClaim : Prop :=
  ∀ (S : StepDuplicatingSchema) (d : Nat) [NeZero d] (M : TriangularMatrixMethod S d),
    ¬ ∀ b s n : S.T, VecLeLt 0
      (M.interpretation.eval (S.wrap s (S.recur b s n)))
      (M.interpretation.eval (S.recur b s (S.succ n)))

theorem triangularMatrix_exact_row : TriangularMatrixExactRowClaim :=
  fun _ _ _ M => M.not_orients

end OperatorKO7.Methods.NaturalMatrixInterpretationRows
