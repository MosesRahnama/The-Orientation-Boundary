import OperatorKO7.Meta.MatrixBarrierNatural_Schema
import OperatorKO7.Meta.MatrixBarrierLexD_Schema
import OperatorKO7.Meta.CompositionalMeasure_Impossibility

set_option autoImplicit false

/-!
# EWZ monotonicity forces the wrapper diagonal

Endrullis, Waldmann, and Zantema require `(Aᵢ)₀₀ ≥ 1` of every constructor matrix
for strict monotonicity under their vector order. On `NatMatrixMeasure` that
condition is `EWZMonotone`. It implies `WrapDiagPositive M 0`, so the
certificate-free natural-matrix barrier of `MatrixBarrierNatural_Schema` applies
with no extra premise: every EWZ-monotone interpretation in every positive
dimension fails the duplicating step under the EWZ order, the strict
componentwise order, and (with one positive primary value) the lexicographic
order at coordinate 0.

The zero-diagonal interpretation `constantZeroNatMatrixMeasure` is the compiled
non-example: `coeff 0 0 = 0` on every matrix, the nonstrict comparison holds at
every triple, and `EWZMonotoneInterpretation` fails. Monotonicity is therefore
load-bearing.

Relation: the schema duplicating step at the root; `GlobalOrients` for systems.
Closure: root; global versions quantify over every step.
External trust: none. Mathlib only.
Named method: natural matrix interpretations under the EWZ monotonicity law.
-/

open scoped BigOperators

namespace OperatorKO7.StepDuplicating

namespace StepDuplicatingSchema

open Finset

/-- Endrullis-Waldmann-Zantema strict monotonicity of one matrix argument:
the `(0,0)` entry is at least one. Requires a positive dimension so that
coordinate `0` exists. -/
def EWZMonotone {d : Nat} [NeZero d] (A : MixedMatrix d) : Prop :=
  1 ≤ A.coeff 0 0

/-- An interpretation is EWZ-monotone when every constructor matrix satisfies
`EWZMonotone`. -/
structure EWZMonotoneInterpretation
    {S : StepDuplicatingSchema} {d : Nat} [NeZero d]
    (M : NatMatrixMeasure S d) : Prop where
  succ_mat : EWZMonotone M.succ_mat
  wrap_left : EWZMonotone M.wrap_left
  wrap_right : EWZMonotone M.wrap_right
  recur_base : EWZMonotone M.recur_base
  recur_step : EWZMonotone M.recur_step
  recur_counter : EWZMonotone M.recur_counter

/-- EWZ monotonicity of the two wrapper matrices is exactly `WrapDiagPositive`
at coordinate `0`. -/
theorem ewz_monotone_wrapDiagPositive
    {S : StepDuplicatingSchema} {d : Nat} [NeZero d]
    {M : NatMatrixMeasure S d} (h : EWZMonotoneInterpretation M) :
    WrapDiagPositive M (0 : Fin d) :=
  ⟨h.wrap_left, h.wrap_right⟩

/-- Coordinate `0` of a `(d+1)`-dimensional vector is the lexicographic primary. -/
theorem ewzCoord_eq_primary {d : Nat} :
    (0 : Fin (d + 1)) = primaryIdx d :=
  Fin.ext rfl

/-- Every EWZ-monotone natural matrix interpretation fails the duplicating step
under the EWZ order at coordinate `0`. No certificate, no pump, no positivity
premise. -/
theorem no_ewz_monotone_orients_dup_step
    {S : StepDuplicatingSchema} {d : Nat} [NeZero d]
    (M : NatMatrixMeasure S d) (h : EWZMonotoneInterpretation M) :
    ¬ (∀ (b s n : S.T),
      VecLeLt (0 : Fin d)
        (M.eval (S.wrap s (S.recur b s n)))
        (M.eval (S.recur b s (S.succ n)))) :=
  no_natMatrix_orients_dup_step_ewz M (ewz_monotone_wrapDiagPositive h)

/-- The same class statement under the strict componentwise order. -/
theorem no_ewz_monotone_orients_dup_step_componentwise
    {S : StepDuplicatingSchema} {d : Nat} [NeZero d]
    (M : NatMatrixMeasure S d) (h : EWZMonotoneInterpretation M) :
    ¬ (∀ (b s n : S.T),
      VecLt (M.eval (S.wrap s (S.recur b s n)))
        (M.eval (S.recur b s (S.succ n)))) :=
  no_natMatrix_orients_dup_step_componentwise M (ewz_monotone_wrapDiagPositive h)

/-- Lexicographic reading at coordinate `0`. The order is nonincreasing on the
primary, so one positive primary value remains. -/
theorem no_ewz_monotone_orients_dup_step_lexD_of_primary_pos
    {S : StepDuplicatingSchema} {d : Nat}
    (M : NatMatrixMeasure S (d + 1)) (h : EWZMonotoneInterpretation M)
    (hpos : ∃ t : S.T, 1 ≤ M.eval t (primaryIdx d)) :
    ¬ (∀ (b s n : S.T),
      VecLexLt (M.eval (S.wrap s (S.recur b s n)))
        (M.eval (S.recur b s (S.succ n)))) := by
  have hi : WrapDiagPositive M (primaryIdx d) := by
    rw [← ewzCoord_eq_primary]
    exact ewz_monotone_wrapDiagPositive h
  exact no_natMatrix_orients_dup_step_lexD_of_primary_pos M hi hpos

/-- Global form of the EWZ class barrier. -/
theorem no_global_orients_ewzMonotone
    {Sys : StepDuplicatingSystem} {d : Nat} [NeZero d]
    (M : NatMatrixMeasure Sys.toStepDuplicatingSchema d)
    (h : EWZMonotoneInterpretation M) :
    ¬ GlobalOrients Sys M.eval (VecLeLt (0 : Fin d)) :=
  no_global_orients_natMatrix_ewz (Sys := Sys) M (ewz_monotone_wrapDiagPositive h)

/-- Global form under the strict componentwise order. -/
theorem no_global_orients_ewzMonotone_componentwise
    {Sys : StepDuplicatingSystem} {d : Nat} [NeZero d]
    (M : NatMatrixMeasure Sys.toStepDuplicatingSchema d)
    (h : EWZMonotoneInterpretation M) :
    ¬ GlobalOrients Sys M.eval VecLt :=
  no_global_orients_natMatrix_componentwise (Sys := Sys) M
    (ewz_monotone_wrapDiagPositive h)

/-- Global lexicographic form at coordinate `0`. -/
theorem no_global_orients_ewzMonotone_lexD_of_primary_pos
    {Sys : StepDuplicatingSystem} {d : Nat}
    (M : NatMatrixMeasure Sys.toStepDuplicatingSchema (d + 1))
    (h : EWZMonotoneInterpretation M)
    (hpos : ∃ t : Sys.toStepDuplicatingSchema.T,
      1 ≤ M.eval t (primaryIdx d)) :
    ¬ GlobalOrients Sys M.eval VecLexLt := by
  have hi : WrapDiagPositive M (primaryIdx d) := by
    rw [← ewzCoord_eq_primary]
    exact ewz_monotone_wrapDiagPositive h
  exact no_global_orients_natMatrix_lexD_of_primary_pos (Sys := Sys) M hi hpos

/-! ## Non-example: the zero diagonal -/

/-- The zero `d × d` matrix. -/
def zeroMixedMatrix (d : Nat) : MixedMatrix d where
  coeff := fun _ _ => 0

theorem zeroMixedMatrix_act {d : Nat} (v : MatrixVec d) (i : Fin d) :
    (zeroMixedMatrix d).act v i = 0 := by
  simp [zeroMixedMatrix, MixedMatrix.act]

/-- Every matrix entry `0`, every value `0`: the chain never moves. -/
def constantZeroNatMatrixMeasure (S : StepDuplicatingSchema) {d : Nat} :
    NatMatrixMeasure S d where
  eval := fun _ _ => 0
  base_vec := fun _ => 0
  succ_bias := fun _ => 0
  succ_mat := zeroMixedMatrix d
  wrap_bias := fun _ => 0
  wrap_left := zeroMixedMatrix d
  wrap_right := zeroMixedMatrix d
  recur_bias := fun _ => 0
  recur_base := zeroMixedMatrix d
  recur_step := zeroMixedMatrix d
  recur_counter := zeroMixedMatrix d
  eval_base := rfl
  eval_succ := by
    intro t
    funext i
    simp [vecAdd, zeroMixedMatrix, MixedMatrix.act]
  eval_wrap := by
    intro x y
    funext i
    simp [vecAdd, zeroMixedMatrix, MixedMatrix.act]
  eval_recur := by
    intro b s n
    funext i
    simp [vecAdd, zeroMixedMatrix, MixedMatrix.act]

/-- With `coeff 0 0 = 0` the nonstrict comparison holds at every triple. -/
theorem constantZeroNatMatrixMeasure_nonstrict_orients
    (S : StepDuplicatingSchema) {d : Nat} [NeZero d] :
    ∀ (b s n : S.T),
      (constantZeroNatMatrixMeasure S).eval (S.wrap s (S.recur b s n)) (0 : Fin d) ≤
        (constantZeroNatMatrixMeasure S).eval (S.recur b s (S.succ n)) (0 : Fin d) :=
  fun _ _ _ => le_rfl

/-- The zero interpretation is not EWZ-monotone. -/
theorem constantZeroNatMatrixMeasure_not_ewzMonotone
    (S : StepDuplicatingSchema) {d : Nat} [NeZero d] :
    ¬ EWZMonotoneInterpretation (constantZeroNatMatrixMeasure (S := S) (d := d)) := by
  intro h
  have : 1 ≤ (0 : Nat) := h.wrap_left
  omega

/-- Its wrapper diagonal entries are `0`, so `WrapDiagPositive` fails at coordinate `0`. -/
theorem constantZeroNatMatrixMeasure_not_wrapDiagPositive
    (S : StepDuplicatingSchema) {d : Nat} [NeZero d] :
    ¬ WrapDiagPositive (constantZeroNatMatrixMeasure (S := S) (d := d)) (0 : Fin d) := by
  intro h
  have : 1 ≤ (0 : Nat) := h.1
  omega

end StepDuplicatingSchema

end OperatorKO7.StepDuplicating

namespace OperatorKO7.MatrixBarrierNaturalEWZ

open OperatorKO7
open OperatorKO7.Trace
open OperatorKO7.StepDuplicating
open OperatorKO7.StepDuplicating.StepDuplicatingSchema
open OperatorKO7.CompositionalImpossibility

/-- KO7: every EWZ-monotone natural matrix interpretation fails global orientation
of `Step` under the EWZ order at coordinate `0`. -/
theorem no_global_step_orientation_ewzMonotone
    {d : Nat} [NeZero d]
    (M : NatMatrixMeasure ko7Schema d) (h : EWZMonotoneInterpretation M) :
    ¬ GlobalOrients ko7System M.eval (VecLeLt (0 : Fin d)) :=
  no_global_orients_ewzMonotone (Sys := ko7System) M h

/-- KO7 componentwise form. -/
theorem no_global_step_orientation_ewzMonotone_componentwise
    {d : Nat} [NeZero d]
    (M : NatMatrixMeasure ko7Schema d) (h : EWZMonotoneInterpretation M) :
    ¬ GlobalOrients ko7System M.eval VecLt :=
  no_global_orients_ewzMonotone_componentwise (Sys := ko7System) M h

/-- KO7 lexicographic form at coordinate `0`. -/
theorem no_global_step_orientation_ewzMonotone_lexD_of_primary_pos
    {d : Nat}
    (M : NatMatrixMeasure ko7Schema (d + 1)) (h : EWZMonotoneInterpretation M)
    (hpos : ∃ t : Trace, 1 ≤ M.eval t (primaryIdx d)) :
    ¬ GlobalOrients ko7System M.eval VecLexLt :=
  no_global_orients_ewzMonotone_lexD_of_primary_pos (Sys := ko7System) M h hpos

end OperatorKO7.MatrixBarrierNaturalEWZ
