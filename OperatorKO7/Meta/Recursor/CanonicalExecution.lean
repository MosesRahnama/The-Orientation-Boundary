import OperatorKO7.Meta.ComputationalLayerCrossing
import OperatorKO7.Meta.Recursor.CircularIdentity

/-!
# Fixed-input canonical execution

`RecursorInputFamily b s n` varies the input counter with `n`.  It is retained
as a compatibility name for the former `RecursorOrbit`, but it is not an
execution from one source term.

`canonicalExecution Sys b s k` is instead the finite, fixed-source execution
already supplied by `BaseDuplicatingSystem.canonicalTrace`, indexed by
`Fin (k + 1)`.  The results below expose its source, successive stages,
counter descent, payload ascent, and terminal stage without identifying it
with the self-embedding input family.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.Recursor.CanonicalExecution

open OperatorKO7
open OperatorKO7.Trace
open OperatorKO7.Meta.Recursor.CircularIdentity
open OperatorKO7.StepDuplicating.StepDuplicatingSchema
open OperatorKO7.StepDuplicating.StepDuplicatingSchema.BaseDuplicatingSystem

/-! ## Input family versus fixed execution -/

/-- Compatibility name for `RecursorOrbit`.  Its index selects a different
source input; it is not a sequence of reducts from one fixed source. -/
abbrev RecursorInputFamily := RecursorOrbit

/-- The compatibility name exposes exactly the old input-depth family. This
theorem deliberately says nothing about edges between successive indices. -/
@[simp] theorem recursorInputFamily_apply (b s : Trace) (n : Nat) :
    RecursorInputFamily b s n = recΔ b s (counterTrace n) :=
  rfl

/-- A finite execution of depth `k` on one fixed base/payload/input triple. -/
abbrev FixedInputExecution (Sys : BaseDuplicatingSystem)
    (b s : Sys.T) (k : Nat) := Fin (k + 1) -> Sys.T

/-- The canonical fixed-input execution, obtained by restricting
`canonicalTrace Sys b s k` to its `k + 1` displayed stages. -/
def canonicalExecution (Sys : BaseDuplicatingSystem)
    (b s : Sys.T) (k : Nat) : FixedInputExecution Sys b s k :=
  fun i => Sys.canonicalTrace b s k i.val

@[simp] theorem canonicalExecution_apply (Sys : BaseDuplicatingSystem)
    (b s : Sys.T) (k : Nat) (i : Fin (k + 1)) :
    canonicalExecution Sys b s k i = Sys.canonicalTrace b s k i.val :=
  rfl

/-- The first stage is the single fixed source with counter depth `k`. -/
@[simp] theorem canonicalExecution_source (Sys : BaseDuplicatingSystem)
    (b s : Sys.T) (k : Nat) :
    canonicalExecution Sys b s k (0 : Fin (k + 1)) =
      Sys.recur b s (Sys.counter k) := by
  simp [canonicalExecution]

/-- Consecutive finite stages are connected by the exact contextual
reflexive-transitive relation used by `SchemaCanonicalTrace`. -/
theorem canonicalExecution_stage_step (Sys : BaseDuplicatingSystem)
    (hwrap : WrapContextClosed Sys) (b s : Sys.T) (k : Nat) (i : Fin k) :
    BaseDuplicatingSystem.StepStar (Sys := Sys)
      (canonicalExecution Sys b s k i.castSucc)
      (canonicalExecution Sys b s k i.succ) := by
  simpa [canonicalExecution] using
    (Sys.canonical_stage_step hwrap b s i.isLt)

/-- The displayed counter coordinate drops by exactly one between adjacent
stages of the fixed execution. -/
theorem canonicalExecution_counter_descent (k : Nat) (i : Fin k) :
    trace_ctr k i.castSucc.val = trace_ctr k i.succ.val + 1 := by
  simpa using (per_step_exchange k i.val i.isLt).1

/-- The displayed payload coordinate rises by exactly one between adjacent
stages of the fixed execution. -/
theorem canonicalExecution_payload_ascent (k : Nat) (i : Fin k) :
    trace_pay i.succ.val = trace_pay i.castSucc.val + 1 := by
  simpa using (per_step_exchange k i.val i.isLt).2

/-- The final displayed stage contains the base redex under exactly `k`
wrappers. -/
@[simp] theorem canonicalExecution_terminal_stage
    (Sys : BaseDuplicatingSystem) (b s : Sys.T) (k : Nat) :
    canonicalExecution Sys b s k
        (show Fin (k + 1) from ⟨k, Nat.lt_succ_self k⟩) =
      Sys.wrapChain s k (Sys.recur b s Sys.base) := by
  simp [canonicalExecution, BaseDuplicatingSystem.canonicalTrace]

/-- The terminal base redex reaches the wrapped output. -/
theorem canonicalExecution_terminal_reaches_output
    (Sys : BaseDuplicatingSystem) (hwrap : WrapContextClosed Sys)
    (b s : Sys.T) (k : Nat) :
    BaseDuplicatingSystem.StepStar (Sys := Sys)
      (canonicalExecution Sys b s k
        (show Fin (k + 1) from ⟨k, Nat.lt_succ_self k⟩))
      (Sys.wrapChain s k b) := by
  have hbase : BaseDuplicatingSystem.StepStar (Sys := Sys)
      (Sys.recur b s Sys.base) b :=
    BaseDuplicatingSystem.StepStar.single (Sys.canonical_base_step b s)
  have hlift := BaseDuplicatingSystem.StepStar.wrapChain (Sys := Sys) hwrap s k hbase
  rw [canonicalExecution_terminal_stage]
  exact hlift

/-- The fixed source reaches the wrapped output.  This is the execution
statement; it does not compare the source-indexed family with another orbit. -/
theorem canonicalExecution_source_reaches_output
    (Sys : BaseDuplicatingSystem) (hwrap : WrapContextClosed Sys)
    (b s : Sys.T) (k : Nat) :
    BaseDuplicatingSystem.StepStar (Sys := Sys)
      (canonicalExecution Sys b s k (0 : Fin (k + 1)))
      (Sys.wrapChain s k b) := by
  simpa [canonicalExecution] using
    (Sys.canonical_trace_full hwrap b s k)

/-! ## A named object-level observer on the fixed execution -/

/-- The projected counter observer reads a term, not an execution index. -/
def projectedCounterObserver {Sys : BaseDuplicatingSystem}
    (K : SemanticProjectionKernel Sys) : Sys.T -> Nat :=
  fun t => K.projectedRank.rank (K.project t)

/-- Along the fixed-input execution, the named projected-counter observer is
exactly the remaining counter coordinate. -/
theorem projectedCounterObserver_on_canonicalExecution
    {Sys : BaseDuplicatingSystem} (K : SemanticProjectionKernel Sys)
    (b s : Sys.T) (k : Nat) (i : Fin (k + 1)) :
    projectedCounterObserver K (canonicalExecution Sys b s k i) =
      trace_ctr k i.val := by
  exact K.projectedRank_canonical k i.val (Nat.le_of_lt_succ i.isLt)

/-- The named object-level observer drops by one at adjacent stages. -/
theorem projectedCounterObserver_drops_one
    {Sys : BaseDuplicatingSystem} (K : SemanticProjectionKernel Sys)
    (b s : Sys.T) (k : Nat) (i : Fin k) :
    projectedCounterObserver K (canonicalExecution Sys b s k i.succ) + 1 =
      projectedCounterObserver K (canonicalExecution Sys b s k i.castSucc) := by
  rw [projectedCounterObserver_on_canonicalExecution,
    projectedCounterObserver_on_canonicalExecution]
  exact (canonicalExecution_counter_descent k i).symm

end OperatorKO7.Meta.Recursor.CanonicalExecution
