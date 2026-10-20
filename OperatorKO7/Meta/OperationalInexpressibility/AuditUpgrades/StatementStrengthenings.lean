import OperatorKO7.Meta.Recursor.RaryDuplicator
import OperatorKO7.Meta.Recursor.TRSEquivalence
import OperatorKO7.Meta.ComputationalLayerCrossing
import OperatorKO7.Meta.Methods.OrientationClosure.DependencyPairSoundness

/-!
# Three statement strengthenings on the concrete systems

Proves: (1) in the r-ary positional syntax, `m` emitted frames over one preserved active site carry
`r * m + 1` payload occurrences; (2) a projection transaction on the free system whose license is
the dependency-pair soundness statement of the free recursor at the projection to its step
argument: the subterm criterion holds there, and every term terminates; (3) the licensed quotient
of the orbit-function space used for the family correspondence is a group action: the unit acts
as the identity and the action is compatible with the group product.
Relation: `RStep r` on `RTerm`; `Step freeRecursorTRS` on first-order terms.
Closure: as declared in each statement.
Strategy: not applicable.
Trust: kernel-only.
Scope: `r`, `m` natural numbers; the quotient `trsEquivalenceLQ`.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.OperationalInexpressibility.AuditUpgrades.StatementStrengthenings

open OperatorKO7.StepDuplicating
open OperatorKO7.StepDuplicating.StepDuplicatingSchema
open OperatorKO7.StepDuplicating.StepDuplicatingSchema.BaseDuplicatingSystem
open OperatorKO7.Meta.BoundaryOperator
open OperatorKO7.Meta.Recursor.TRSEquivalence
open OperatorKO7.Meta.Recursor.RaryDuplicator
open OperatorKO7.Meta.Rewriting
open OperatorKO7.Methods.OrientationClosure.DependencyPairSoundness

/-! ## (1) Payload count of the r-ary frames -/

/-- `m` frames of the r-ary syntax over one preserved active site carry `r * m + 1` payload
occurrences. -/
theorem rary_frames_payload_count (ia ib r m n : Nat) :
    countPayR (rGPow (List.replicate r (.pay ib)) m (.F (.base ia) (.pay ib) (rSPow n))) =
      r * m + 1 := by
  rw [countPayR_rGPow]
  simp [countPayR, countPayR_rSPow, Nat.mul_comm]

/-! ## (2) A projection transaction licensed by dependency-pair soundness -/

/-- The license `AG(π)`: the subterm criterion holds for the free recursor at the projection to
its step argument, and every term of the free recursor terminates. -/
def freeRecursorArtsGieslLicense : Prop :=
  SubtermCriterion freeRecursorTRS freeProj ∧ ∀ t : Term FreeSym Nat, SN freeRecursorTRS t

/-- Dependency-pair soundness discharges the license. -/
theorem freeRecursorArtsGieslLicense_holds : freeRecursorArtsGieslLicense :=
  ⟨freeRecursorTRS_subtermCriterion,
    terminating_of_subtermCriterion freeRecursorTRS freeRecursorTRS_vars
      freeRecursorTRS_subtermCriterion⟩

/-- The projection to the step argument selects the third argument of the recursor symbol. -/
theorem freeProj_recur : freeProj FreeSym.recur = 2 := rfl

/-- The projection transaction of the free system whose license is `AG(π)`. -/
def freeProjectionTransactionAG :
    ProjectionTransaction freeBaseSystem.toStepDuplicatingSchema :=
  freeProjectiveRecordEmitter.toProjectionTransaction freeRecursorArtsGieslLicense
    freeRecursorArtsGieslLicense_holds

theorem freeProjectionTransactionAG_license :
    freeProjectionTransactionAG.license = freeRecursorArtsGieslLicense := rfl

/-! ## (3) The licensed quotient of the orbit-function space is a group action -/

/-- Group-action laws for the action map of a licensed quotient. -/
def IsGroupAction {X : Type} (L : LicensedQuotient X) : Prop :=
  (∀ x : X, L.action 1 x = x) ∧ ∀ (g h : L.G) (x : X), L.action (g * h) x = L.action g (L.action h x)

/-- The quotient of the family correspondence satisfies the group-action laws. -/
theorem trsEquivalenceLQ_isGroupAction : IsGroupAction trsEquivalenceLQ :=
  ⟨fun _ => rfl, fun _ _ _ => rfl⟩

end OperatorKO7.Meta.OperationalInexpressibility.AuditUpgrades.StatementStrengthenings
