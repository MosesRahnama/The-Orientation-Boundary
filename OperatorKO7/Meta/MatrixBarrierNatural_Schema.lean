import OperatorKO7.Meta.BarrierPumpDischarge_Schema
import OperatorKO7.Meta.MatrixOrderInterfaces
import OperatorKO7.Meta.MatrixUnrestrictedSplitCore

set_option autoImplicit false

/-!
# Natural-Matrix Barrier: certificate-free, dimension-uniform

Matrix interpretations over the natural numbers (Endrullis, Waldmann, Zantema) interpret
every constructor by an affine map `v ↦ Σ Aᵢ vᵢ + c` with natural `d × d` matrices `Aᵢ`,
and compare vectors by an order that forces the first coordinate to descend (strictly, or at
least weakly) whenever the vectors are ordered. Strict monotonicity of the interpretation in
each argument is the condition `(Aᵢ)₀₀ ≥ 1`.

The existing matrix barriers of the stack (`MatrixBarrierArbitrary_Schema`,
`MatrixBarrierArcticTropical_Schema`, `OrderedSemiringMatrixLiftBarrier`) all require a
scalarization certificate: a weight vector respected by every constructor matrix, plus a
dominance witness and a pump. This module removes the certificate. Over `Nat`, every entry
is nonnegative, so the `i`-th coordinate of `A v` is at least `Aᵢᵢ · vᵢ`; with `Aᵢᵢ ≥ 1` the
coordinate is at least `vᵢ`. Applied to the two wrapper matrices at the duplicating step
`recur base s (succ base) → wrap s (recur base s base)` this gives

  `eval s i + eval (recur base s base) i ≤ eval (wrap s (recur base s base)) i`,

while the source differs from the inner recursor value only by the constant
`(recur_counter · eval (succ base)) i`. Any order that forces nonincrease of coordinate `i`
therefore bounds `eval s i` by that constant for every `s`; the self-nested wrapper chain
`wrapDouble` is unbounded in coordinate `i` as soon as one value is positive; and strict
orders supply that positive value at `(base, base, base)`.

Main theorems:

* `no_natMatrix_orients_dup_step_of_tracked_strict`: unconditional for every order whose
  strict comparison forces strict decrease of coordinate `i`, given `WrapDiagPositive M i`.
* `no_natMatrix_orients_dup_step_of_tracked_nonincreasing`: the same for orders that only
  force nonincrease (lexicographic, priority, Pareto, cone, norm), with one extra premise,
  a positive value of coordinate `i` somewhere.
* Named instances: strict componentwise (`VecLt`), the Endrullis-Waldmann-Zantema order
  (`VecLeLt`), finite and permutation-priority lexicographic (`VecLexLt`, `VecPermLexLt`),
  and every order interface of `MatrixOrderInterfaces` and `MatrixUnrestrictedSplitCore`.

No weight vector, no `RespectsWeight` field, no `MatrixScalarDominance` witness, no pump.
The result is uniform in the dimension `d`.

Relation: the schema duplicating step at the root; `GlobalOrients` for systems.
Closure: root; global versions quantify over every step.
External trust: none. Mathlib only.
Named method: natural matrix interpretations, `NatMatrixMeasure` (the six constructor
matrices and biases with their evaluation equations); the order is a parameter.
-/

open scoped BigOperators

namespace OperatorKO7.StepDuplicating

namespace StepDuplicatingSchema

open Finset

namespace MixedMatrix

/-- Nonnegativity: the diagonal term is a lower bound for the `i`-th coordinate of `A v`. -/
theorem diag_mul_le_act {d : Nat} (A : MixedMatrix d) (v : MatrixVec d) (i : Fin d) :
    A.coeff i i * v i ≤ A.act v i := by
  unfold act
  exact Finset.single_le_sum (f := fun j => A.coeff i j * v j)
    (fun j _ => Nat.zero_le _) (Finset.mem_univ i)

/-- A positive diagonal entry makes the matrix action coordinatewise expansive at `i`. -/
theorem coord_le_act_of_diag_pos {d : Nat} (A : MixedMatrix d) (v : MatrixVec d) (i : Fin d)
    (hA : 1 ≤ A.coeff i i) :
    v i ≤ A.act v i :=
  le_trans (Nat.le_mul_of_pos_left (v i) hA) (diag_mul_le_act A v i)

end MixedMatrix

/-- A natural matrix interpretation of a step-duplicating schema: every constructor acts by
natural `d × d` matrices on the argument vectors plus a bias vector. No weight vector and no
scalarization certificate are part of the data. -/
structure NatMatrixMeasure (S : StepDuplicatingSchema) (d : Nat) where
  eval : S.T → MatrixVec d
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

/-- Strict monotonicity of the wrapper interpretation at coordinate `i`: both wrapper
matrices carry a positive `(i, i)` entry. For the Endrullis-Waldmann-Zantema order this is
the standard monotonicity requirement at `i = 0`. -/
def WrapDiagPositive {S : StepDuplicatingSchema} {d : Nat} (M : NatMatrixMeasure S d)
    (i : Fin d) : Prop :=
  1 ≤ M.wrap_left.coeff i i ∧ 1 ≤ M.wrap_right.coeff i i

/-- The wrapper value at coordinate `i` dominates the sum of both argument coordinates. -/
theorem wrap_coord_lower_bound {S : StepDuplicatingSchema} {d : Nat}
    (M : NatMatrixMeasure S d) {i : Fin d} (hi : WrapDiagPositive M i) (x y : S.T) :
    M.eval x i + M.eval y i ≤ M.eval (S.wrap x y) i := by
  rw [M.eval_wrap]
  have h1 := MixedMatrix.coord_le_act_of_diag_pos M.wrap_left (M.eval x) i hi.1
  have h2 := MixedMatrix.coord_le_act_of_diag_pos M.wrap_right (M.eval y) i hi.2
  simp only [vecAdd]
  omega

/-- Coordinate decomposition of the recursor value. -/
theorem recur_coord_eq {S : StepDuplicatingSchema} {d : Nat}
    (M : NatMatrixMeasure S d) (b s n : S.T) (i : Fin d) :
    M.eval (S.recur b s n) i =
      M.recur_bias i + M.recur_base.act (M.eval b) i +
        M.recur_step.act (M.eval s) i + M.recur_counter.act (M.eval n) i := by
  rw [M.eval_recur]
  simp only [vecAdd]
  omega

/-- If coordinate `i` never increases across the duplicating step, every term's coordinate
`i` is bounded by the constant `(recur_counter · eval (succ base)) i`. -/
theorem coord_bounded_of_nonincreasing {S : StepDuplicatingSchema} {d : Nat}
    (M : NatMatrixMeasure S d) {i : Fin d} (hi : WrapDiagPositive M i)
    (h : ∀ b s n : S.T,
      M.eval (S.wrap s (S.recur b s n)) i ≤ M.eval (S.recur b s (S.succ n)) i)
    (s : S.T) :
    M.eval s i ≤ M.recur_counter.act (M.eval (S.succ S.base)) i := by
  have hs := h S.base s S.base
  have hw := wrap_coord_lower_bound M hi s (S.recur S.base s S.base)
  have e1 := recur_coord_eq M S.base s S.base i
  have e2 := recur_coord_eq M S.base s (S.succ S.base) i
  omega

/-- The self-nested wrapper chain is unbounded in coordinate `i` from any positive start. -/
theorem eval_wrapDouble_coord_ge {S : StepDuplicatingSchema} {d : Nat}
    (M : NatMatrixMeasure S d) {i : Fin d} (hi : WrapDiagPositive M i)
    {t : S.T} (ht : 1 ≤ M.eval t i) (k : Nat) :
    k + 1 ≤ M.eval (wrapDouble S t k) i := by
  induction k with
  | zero => simpa using ht
  | succ k ih =>
      have hw := wrap_coord_lower_bound M hi (wrapDouble S t k) (wrapDouble S t k)
      rw [wrapDouble_succ]
      omega

/-- **Natural-matrix barrier, nonincreasing form.** Any order whose strict comparison forces
coordinate `i` to be nonincreasing fails to orient the duplicating step, provided the wrapper
matrices are strictly monotone at `i` and coordinate `i` is positive somewhere. -/
theorem no_natMatrix_orients_dup_step_of_tracked_nonincreasing
    {S : StepDuplicatingSchema} {d : Nat}
    (M : NatMatrixMeasure S d) {i : Fin d} (hi : WrapDiagPositive M i)
    {R : MatrixVec d → MatrixVec d → Prop}
    (hR : ∀ {u v : MatrixVec d}, R u v → u i ≤ v i)
    (hpos : ∃ t : S.T, 1 ≤ M.eval t i) :
    ¬ (∀ (b s n : S.T),
      R (M.eval (S.wrap s (S.recur b s n))) (M.eval (S.recur b s (S.succ n)))) := by
  intro h
  rcases hpos with ⟨t, ht⟩
  have hbound := coord_bounded_of_nonincreasing M hi (fun b s n => hR (h b s n))
  have hk :=
    eval_wrapDouble_coord_ge M hi ht (M.recur_counter.act (M.eval (S.succ S.base)) i)
  have hb := hbound (wrapDouble S t (M.recur_counter.act (M.eval (S.succ S.base)) i))
  omega

/-- **Natural-matrix barrier, strict form.** Any order whose strict comparison forces strict
decrease of coordinate `i` fails to orient the duplicating step, provided only that the two
wrapper matrices are strictly monotone at `i`. No certificate, no pump, no positivity premise:
orientation at `(base, base, base)` supplies the positive value. -/
theorem no_natMatrix_orients_dup_step_of_tracked_strict
    {S : StepDuplicatingSchema} {d : Nat}
    (M : NatMatrixMeasure S d) {i : Fin d} (hi : WrapDiagPositive M i)
    {R : MatrixVec d → MatrixVec d → Prop}
    (hR : ∀ {u v : MatrixVec d}, R u v → u i < v i) :
    ¬ (∀ (b s n : S.T),
      R (M.eval (S.wrap s (S.recur b s n))) (M.eval (S.recur b s (S.succ n)))) := by
  intro h
  have hpos : 1 ≤ M.eval (S.recur S.base S.base (S.succ S.base)) i := by
    have := hR (h S.base S.base S.base)
    omega
  exact no_natMatrix_orients_dup_step_of_tracked_nonincreasing M hi
    (fun huv => Nat.le_of_lt (hR huv)) ⟨_, hpos⟩ h

/-! ## Named order instances -/

/-- Strict componentwise order. -/
theorem no_natMatrix_orients_dup_step_componentwise
    {S : StepDuplicatingSchema} {d : Nat}
    (M : NatMatrixMeasure S d) {i : Fin d} (hi : WrapDiagPositive M i) :
    ¬ (∀ (b s n : S.T),
      VecLt (M.eval (S.wrap s (S.recur b s n))) (M.eval (S.recur b s (S.succ n)))) :=
  no_natMatrix_orients_dup_step_of_tracked_strict M hi (fun h => h i)

/-- The Endrullis-Waldmann-Zantema matrix order: weak decrease in every coordinate, strict
decrease in the tracked coordinate. -/
theorem no_natMatrix_orients_dup_step_ewz
    {S : StepDuplicatingSchema} {d : Nat}
    (M : NatMatrixMeasure S d) {tracked : Fin d} (hi : WrapDiagPositive M tracked) :
    ¬ (∀ (b s n : S.T),
      VecLeLt tracked (M.eval (S.wrap s (S.recur b s n)))
        (M.eval (S.recur b s (S.succ n)))) :=
  no_natMatrix_orients_dup_step_of_tracked_strict M hi (fun h => h.2)

/-- Finite lexicographic order with the primary coordinate first. -/
theorem no_natMatrix_orients_dup_step_lexD_of_primary_pos
    {S : StepDuplicatingSchema} {d : Nat}
    (M : NatMatrixMeasure S (d + 1)) (hi : WrapDiagPositive M (primaryIdx d))
    (hpos : ∃ t : S.T, 1 ≤ M.eval t (primaryIdx d)) :
    ¬ (∀ (b s n : S.T),
      VecLexLt (M.eval (S.wrap s (S.recur b s n))) (M.eval (S.recur b s (S.succ n)))) :=
  no_natMatrix_orients_dup_step_of_tracked_nonincreasing M hi
    (fun h => primary_le_of_vecLexLt h) hpos

/-- Permutation-priority lexicographic order. -/
theorem no_natMatrix_orients_dup_step_lexPermD_of_primary_pos
    {S : StepDuplicatingSchema} {d : Nat} (σ : Equiv.Perm (Fin (d + 1)))
    (M : NatMatrixMeasure S (d + 1)) (hi : WrapDiagPositive M (permPrimaryIdx σ))
    (hpos : ∃ t : S.T, 1 ≤ M.eval t (permPrimaryIdx σ)) :
    ¬ (∀ (b s n : S.T),
      VecPermLexLt σ (M.eval (S.wrap s (S.recur b s n)))
        (M.eval (S.recur b s (S.succ n)))) :=
  no_natMatrix_orients_dup_step_of_tracked_nonincreasing M hi
    (fun h => permPrimary_le_of_vecPermLexLt h) hpos

/-- Componentwise weak order with one designated strict coordinate
(`MatrixOrderInterfaces.ComponentwiseWeakStrictOrder`). -/
theorem no_natMatrix_orients_dup_step_componentwiseWeakStrict
    {S : StepDuplicatingSchema} {d : Nat}
    (M : NatMatrixMeasure S d) (O : OperatorKO7.MatrixOrderInterfaces.ComponentwiseWeakStrictOrder d)
    (hi : WrapDiagPositive M O.tracked) :
    ¬ (∀ (b s n : S.T),
      O.rel (M.eval (S.wrap s (S.recur b s n))) (M.eval (S.recur b s (S.succ n)))) :=
  no_natMatrix_orients_dup_step_of_tracked_strict M hi (fun h => O.strict_tracked h)

/-- Lex-priority order with strict decrease at the tracked primary
(`MatrixOrderInterfaces.LexPriorityOrder`). -/
theorem no_natMatrix_orients_dup_step_lexPriority
    {S : StepDuplicatingSchema} {d : Nat}
    (M : NatMatrixMeasure S d) (O : OperatorKO7.MatrixOrderInterfaces.LexPriorityOrder d)
    (hi : WrapDiagPositive M O.trackedPrimary) :
    ¬ (∀ (b s n : S.T),
      O.rel (M.eval (S.wrap s (S.recur b s n))) (M.eval (S.recur b s (S.succ n)))) :=
  no_natMatrix_orients_dup_step_of_tracked_strict M hi (fun h => O.strict_trackedPrimary h)

/-- Permutation lex-priority order (`MatrixOrderInterfaces.PermutationLexPriorityOrder`). -/
theorem no_natMatrix_orients_dup_step_permutationLexPriority
    {S : StepDuplicatingSchema} {d : Nat}
    (M : NatMatrixMeasure S d)
    (O : OperatorKO7.MatrixOrderInterfaces.PermutationLexPriorityOrder d)
    (hi : WrapDiagPositive M O.trackedPrimary) :
    ¬ (∀ (b s n : S.T),
      O.rel (M.eval (S.wrap s (S.recur b s n))) (M.eval (S.recur b s (S.succ n)))) :=
  no_natMatrix_orients_dup_step_of_tracked_strict M hi (fun h => O.strict_trackedPrimary h)

/-- Pareto/product order (`MatrixOrderInterfaces.ParetoProductOrder`): weak in every
coordinate, so any coordinate with strictly monotone wrappers and a positive value blocks. -/
theorem no_natMatrix_orients_dup_step_paretoProduct_of_pos
    {S : StepDuplicatingSchema} {d : Nat}
    (M : NatMatrixMeasure S d) (O : OperatorKO7.MatrixOrderInterfaces.ParetoProductOrder d)
    {i : Fin d} (hi : WrapDiagPositive M i) (hpos : ∃ t : S.T, 1 ≤ M.eval t i) :
    ¬ (∀ (b s n : S.T),
      O.rel (M.eval (S.wrap s (S.recur b s n))) (M.eval (S.recur b s (S.succ n)))) :=
  no_natMatrix_orients_dup_step_of_tracked_nonincreasing M hi (fun h => O.weak_all h i) hpos

/-- Row-column dominance order (`MatrixUnrestrictedSplit.RowColumnDominanceOrder`). -/
theorem no_natMatrix_orients_dup_step_rowColumnDominance_of_pos
    {S : StepDuplicatingSchema} {d : Nat}
    (M : NatMatrixMeasure S d) (O : OperatorKO7.MatrixUnrestrictedSplit.RowColumnDominanceOrder d)
    {i : Fin d} (hi : WrapDiagPositive M i) (hpos : ∃ t : S.T, 1 ≤ M.eval t i) :
    ¬ (∀ (b s n : S.T),
      O.rel (M.eval (S.wrap s (S.recur b s n))) (M.eval (S.recur b s (S.succ n)))) :=
  no_natMatrix_orients_dup_step_of_tracked_nonincreasing M hi (fun h => O.weak_all h i) hpos

/-- Cone-positive order (`MatrixUnrestrictedSplit.ConePositiveOrder`). -/
theorem no_natMatrix_orients_dup_step_conePositive_of_pos
    {S : StepDuplicatingSchema} {d : Nat}
    (M : NatMatrixMeasure S d) (O : OperatorKO7.MatrixUnrestrictedSplit.ConePositiveOrder d)
    {i : Fin d} (hi : WrapDiagPositive M i) (hpos : ∃ t : S.T, 1 ≤ M.eval t i) :
    ¬ (∀ (b s n : S.T),
      O.rel (M.eval (S.wrap s (S.recur b s n))) (M.eval (S.recur b s (S.succ n)))) :=
  no_natMatrix_orients_dup_step_of_tracked_nonincreasing M hi (fun h => O.cone_witness h i) hpos

/-- Spectral-norm order (`MatrixUnrestrictedSplit.SpectralNormOrder`). -/
theorem no_natMatrix_orients_dup_step_spectralNorm_of_pos
    {S : StepDuplicatingSchema} {d : Nat}
    (M : NatMatrixMeasure S d) (O : OperatorKO7.MatrixUnrestrictedSplit.SpectralNormOrder d)
    {i : Fin d} (hi : WrapDiagPositive M i) (hpos : ∃ t : S.T, 1 ≤ M.eval t i) :
    ¬ (∀ (b s n : S.T),
      O.rel (M.eval (S.wrap s (S.recur b s n))) (M.eval (S.recur b s (S.succ n)))) :=
  no_natMatrix_orients_dup_step_of_tracked_nonincreasing M hi (fun h => O.norm_witness h i) hpos

/-! ## Global forms -/

theorem no_global_orients_natMatrix_of_tracked_strict
    {Sys : StepDuplicatingSystem} {d : Nat}
    (M : NatMatrixMeasure Sys.toStepDuplicatingSchema d) {i : Fin d} (hi : WrapDiagPositive M i)
    {R : MatrixVec d → MatrixVec d → Prop}
    (hR : ∀ {u v : MatrixVec d}, R u v → u i < v i) :
    ¬ GlobalOrients Sys M.eval R := by
  intro h
  exact no_natMatrix_orients_dup_step_of_tracked_strict (S := Sys.toStepDuplicatingSchema)
    M hi hR (fun b s n => h (Sys.dup_step b s n))

theorem no_global_orients_natMatrix_of_tracked_nonincreasing
    {Sys : StepDuplicatingSystem} {d : Nat}
    (M : NatMatrixMeasure Sys.toStepDuplicatingSchema d) {i : Fin d} (hi : WrapDiagPositive M i)
    {R : MatrixVec d → MatrixVec d → Prop}
    (hR : ∀ {u v : MatrixVec d}, R u v → u i ≤ v i)
    (hpos : ∃ t : Sys.toStepDuplicatingSchema.T, 1 ≤ M.eval t i) :
    ¬ GlobalOrients Sys M.eval R := by
  intro h
  exact no_natMatrix_orients_dup_step_of_tracked_nonincreasing
    (S := Sys.toStepDuplicatingSchema) M hi hR hpos (fun b s n => h (Sys.dup_step b s n))

theorem no_global_orients_natMatrix_componentwise
    {Sys : StepDuplicatingSystem} {d : Nat}
    (M : NatMatrixMeasure Sys.toStepDuplicatingSchema d) {i : Fin d}
    (hi : WrapDiagPositive M i) :
    ¬ GlobalOrients Sys M.eval VecLt :=
  no_global_orients_natMatrix_of_tracked_strict M hi (fun h => h i)

theorem no_global_orients_natMatrix_ewz
    {Sys : StepDuplicatingSystem} {d : Nat}
    (M : NatMatrixMeasure Sys.toStepDuplicatingSchema d) {tracked : Fin d}
    (hi : WrapDiagPositive M tracked) :
    ¬ GlobalOrients Sys M.eval (VecLeLt tracked) :=
  no_global_orients_natMatrix_of_tracked_strict M hi (fun h => h.2)

theorem no_global_orients_natMatrix_lexD_of_primary_pos
    {Sys : StepDuplicatingSystem} {d : Nat}
    (M : NatMatrixMeasure Sys.toStepDuplicatingSchema (d + 1))
    (hi : WrapDiagPositive M (primaryIdx d))
    (hpos : ∃ t : Sys.toStepDuplicatingSchema.T, 1 ≤ M.eval t (primaryIdx d)) :
    ¬ GlobalOrients Sys M.eval VecLexLt :=
  no_global_orients_natMatrix_of_tracked_nonincreasing M hi
    (fun h => primary_le_of_vecLexLt h) hpos

theorem no_global_orients_natMatrix_lexPermD_of_primary_pos
    {Sys : StepDuplicatingSystem} {d : Nat} (σ : Equiv.Perm (Fin (d + 1)))
    (M : NatMatrixMeasure Sys.toStepDuplicatingSchema (d + 1))
    (hi : WrapDiagPositive M (permPrimaryIdx σ))
    (hpos : ∃ t : Sys.toStepDuplicatingSchema.T, 1 ≤ M.eval t (permPrimaryIdx σ)) :
    ¬ GlobalOrients Sys M.eval (VecPermLexLt σ) :=
  no_global_orients_natMatrix_of_tracked_nonincreasing M hi
    (fun h => permPrimary_le_of_vecPermLexLt h) hpos

/-! ## Relation to the certificate-backed interface -/

/-- Forget the scalarization certificate of a `MatrixArbitraryMeasure`. -/
def MatrixArbitraryMeasure.toNatMatrixMeasure {S : StepDuplicatingSchema} {d : Nat}
    (M : MatrixArbitraryMeasure S d) : NatMatrixMeasure S d where
  eval := M.eval
  base_vec := M.base_vec
  succ_bias := M.succ_bias
  succ_mat := M.succ_mat
  wrap_bias := M.wrap_bias
  wrap_left := M.wrap_left
  wrap_right := M.wrap_right
  recur_bias := M.recur_bias
  recur_base := M.recur_base
  recur_step := M.recur_step
  recur_counter := M.recur_counter
  eval_base := M.eval_base
  eval_succ := M.eval_succ
  eval_wrap := M.eval_wrap
  eval_recur := M.eval_recur

@[simp] theorem MatrixArbitraryMeasure.toNatMatrixMeasure_eval {S : StepDuplicatingSchema}
    {d : Nat} (M : MatrixArbitraryMeasure S d) :
    M.toNatMatrixMeasure.eval = M.eval := rfl

end StepDuplicatingSchema

end OperatorKO7.StepDuplicating
