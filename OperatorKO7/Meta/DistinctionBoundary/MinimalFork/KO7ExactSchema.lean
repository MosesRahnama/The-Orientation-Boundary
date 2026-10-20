import OperatorKO7.Meta.DistinctionBoundary.MinimalFork.KO7SchemaInstance
import OperatorKO7.Meta.DistinctionBoundary.MinimalFork.KO7ExactClosureBridge

/-!
# Roadmap-stable KO7 exact-schema surface

Relation: full kernel root `Step`.
Closure: `Quantitative.Reach Step`, with an explicit equivalence theorem to
kernel `StepStar`.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.DistinctionBoundary.MinimalFork

open OperatorKO7
open OperatorKO7.Trace
open OperatorKO7.Meta.DistinctionBoundary.Quantitative

/-- Roadmap-stable exact-schema name. -/
def ko7ExactDiagonalForkSchema :=
  KO7SchemaInstance.ko7ExactDiagonalFork

/-- Closed canonical terminal certificate. -/
theorem ko7TerminalDiagonal : TerminalDiagonal ko7ExactDiagonalForkSchema void :=
  KO7SchemaInstance.ko7_terminalDiagonal void

/-- Closed canonical determined-diagonal certificate. -/
theorem ko7DiagonalDetermined : DiagonalDetermined ko7ExactDiagonalForkSchema void :=
  KO7SchemaInstance.ko7_diagonalDetermined void

/-- Canonical Fork3 embedding into the closed KO7 diagonal. -/
def ko7_contains_fork3 := KO7SchemaInstance.ko7Fork3Embedding void

/-- The embedding is genuinely injective. -/
theorem ko7_contains_fork3_injective :
    Function.Injective ko7_contains_fork3.toFun :=
  KO7SchemaInstance.ko7Fork3Embedding_injective void

/-- Stable closure equivalence name. -/
theorem stepStar_iff_quantitativeReach {x y : Trace} :
    StepStar x y ↔ Reach Step x y :=
  KO7ExactClosureBridge.stepStar_iff_reach

end OperatorKO7.Meta.DistinctionBoundary.MinimalFork
