import OperatorKO7.Meta.DistinctionBoundary.MinimalFork.UniversalEmbedding
import OperatorKO7.Meta.DistinctionBoundary.MinimalFork.KO7ExactClosureBridge

/-!
# KO7 as an exact diagonal-fork schema instance

The instance uses the live kernel root relation `Step`. It proves the terminal
and determined hypotheses for **every** diagonal `eqW a a`; the historically
important closed `a = void` cone is then a specialization and is linked to the
three-node `KO7LocalCone` bridge separately.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.DistinctionBoundary.MinimalFork.KO7SchemaInstance

open OperatorKO7
open OperatorKO7.Trace
open OperatorKO7.Meta.DistinctionBoundary.Quantitative
open OperatorKO7.Meta.DistinctionBoundary.MinimalFork

/-- Exact KO7 equality-witness schema over the full root `Step` relation. -/
def ko7ExactDiagonalFork : ExactDiagonalForkSchema Trace where
  R := Step
  E := eqW
  Z := void
  D := fun a b => integrate (merge a b)
  refl_rule := Step.R_eq_refl
  diff_rule := Step.R_eq_diff

/-- `void` is a full-root `Step` normal form. -/
theorem ko7_void_root_normal :
    OperatorKO7.Meta.DistinctionBoundary.Quantitative.NormalForm Step void := by
  intro y h
  cases h

/-- Every diagonal difference verdict `integrate (merge a a)` is a full-root
normal form. The inner `merge` is not rewritten by root-only `Step`. -/
theorem ko7_diffVerdict_root_normal (a : Trace) :
    OperatorKO7.Meta.DistinctionBoundary.Quantitative.NormalForm Step
      (integrate (merge a a)) := by
  intro y h
  cases h

/-- The two KO7 diagonal verdicts are constructor-distinct. -/
theorem ko7_diagonal_verdicts_distinct (a : Trace) :
    void ≠ integrate (merge a a) := by
  intro h
  cases h

/-- Terminal certificate for every KO7 equality diagonal. -/
theorem ko7_terminalDiagonal (a : Trace) :
    TerminalDiagonal ko7ExactDiagonalFork a where
  equal_normal := ko7_void_root_normal
  different_normal := ko7_diffVerdict_root_normal a
  verdicts_distinct := ko7_diagonal_verdicts_distinct a

/-- Every root step out of `eqW a a` is one of the two equality-witness verdicts. -/
theorem ko7_diagonalDetermined (a : Trace) :
    DiagonalDetermined ko7ExactDiagonalFork a := by
  intro t h
  cases h with
  | R_eq_refl _ => exact Or.inl rfl
  | R_eq_diff _ _ => exact Or.inr rfl

/-- Full-root local confluence fails at every KO7 equality diagonal. -/
theorem ko7_every_diagonal_not_localJoin (a : Trace) :
    ¬ LocalJoinAt ko7ExactDiagonalFork (eqW a a) :=
  localConfluence_fails_of_terminal_distinct
    ko7ExactDiagonalFork a (ko7_terminalDiagonal a)

/-- Canonical closed specialization at `eqW void void`. -/
theorem ko7_void_diagonal_not_localJoin :
    ¬ LocalJoinAt ko7ExactDiagonalFork (eqW void void) :=
  ko7_every_diagonal_not_localJoin void

/-- Every KO7 diagonal contains the canonical three-state obstruction. -/
def ko7Fork3Embedding (a : Trace) :=
  fork3Embedding ko7ExactDiagonalFork a (ko7_terminalDiagonal a)

/-- The canonical embedding is injective for every diagonal. -/
theorem ko7Fork3Embedding_injective (a : Trace) :
    Function.Injective (ko7Fork3Embedding a).toFun :=
  fork3Embedding_injective ko7ExactDiagonalFork a (ko7_terminalDiagonal a)

/-- Every determined KO7 diagonal has exactly the `Fork3` marked local cone. -/
noncomputable def ko7DiagonalLocalConeIso (a : Trace) :
    RelIso Fork3Step
      (LocalConeStep ko7ExactDiagonalFork a (ko7_terminalDiagonal a)) :=
  determined_terminal_diagonal_localCone_equiv_fork3
    ko7ExactDiagonalFork a (ko7_terminalDiagonal a) (ko7_diagonalDetermined a)

/-- Nonvacuity at the closed canonical witness. -/
theorem ko7_void_exact_peak :
    Step (eqW void void) void ∧
    Step (eqW void void) (integrate (merge void void)) :=
  ⟨Step.R_eq_refl void, Step.R_eq_diff void void⟩

end OperatorKO7.Meta.DistinctionBoundary.MinimalFork.KO7SchemaInstance
