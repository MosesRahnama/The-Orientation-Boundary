import OperatorKO7.Meta.RightDuplicatingRecursorSchema
import OperatorKO7.Meta.DuplicatingRecursiveFamily

/-!
Reach test for the Phase A `RightDuplicatingRecursorSchema` and
`DuplicatingRecursiveFamily` shell.

This file checks that the new public names compile under the pinned toolchain. It
does not prove the eventual recursive-family boundary theorem; that lands in
Phase B once `DirectWholeTermObserver` is added.
-/

open OperatorKO7.StepDuplicating

section RDRSReach

example : True := by
  have := @RightDuplicatingRecursorSchema
  trivial

example : True := by
  have := @DuplicatingRecursiveFamily
  trivial

example : True := by
  have := @RightDuplicatingRecursorSchema.distinguishedDuplicationGap
  trivial

example : True := by
  have := @RightDuplicatingRecursorSchema.one_le_distinguishedDuplicationGap
  trivial

example : True := by
  have := @RightDuplicatingRecursorSchema.rhs_count_gt_lhs_count
  trivial

example : True := by
  have := @RightDuplicatingRecursorSchema.distinguished_payload_count_rhs_pos
  trivial

example : True := by
  have := @DuplicatingRecursiveFamily.distinguishedPayload
  trivial

example : True := by
  have := @DuplicatingRecursiveFamily.distinguished_payload_count_strict
  trivial

example : True := by
  have := @DuplicatingRecursiveFamily.distinguishedDuplicationGap
  trivial

example : True := by
  have := @DuplicatingRecursiveFamily.one_le_distinguishedDuplicationGap
  trivial

example (S : RightDuplicatingRecursorSchema) :
    S.payloadCount S.distinguishedPayload S.lhs <
      S.payloadCount S.distinguishedPayload S.rhs :=
  S.rhs_count_gt_lhs_count

example (S : RightDuplicatingRecursorSchema) :
    1 ≤ S.distinguishedDuplicationGap :=
  S.one_le_distinguishedDuplicationGap

example (F : DuplicatingRecursiveFamily) :
    F.schema.payloadCount F.distinguishedPayload F.schema.lhs <
      F.schema.payloadCount F.distinguishedPayload F.schema.rhs :=
  F.distinguished_payload_count_strict

example (F : DuplicatingRecursiveFamily) :
    1 ≤ F.distinguishedDuplicationGap :=
  F.one_le_distinguishedDuplicationGap

end RDRSReach
