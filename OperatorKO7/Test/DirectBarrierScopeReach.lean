import OperatorKO7.Meta.DirectBarrierScope

/-!
Reach test for the Phase A.5 `DirectBarrierScope` / `InScope` layer.

This file checks that the scope record, the `InScope` predicate, the positive
sentinel `fullScope`, and each of the six named negative witnesses compile and
keep their stated types under the pinned toolchain.
-/

open OperatorKO7.StepDuplicating

section DirectBarrierScopeReach

example : True := by
  have := @DirectBarrierScope
  trivial

example : True := by
  have := @InScope
  trivial

example : True := by
  have := @fullScope
  trivial

example : True := by
  have := @fullScope_InScope
  trivial

-- Positive control: the canonical fully-in-scope sentinel is in scope.
example : InScope fullScope := fullScope_InScope

-- Six negative witnesses, one per named exclusion in the scope paragraph.

example : ¬ InScope sharingScope := sharingScope_not_InScope

example : ¬ InScope binderScope := binderScope_not_InScope

example : ¬ InScope innermostOnlyScope := innermostOnlyScope_not_InScope

example : ¬ InScope coOrderScope := coOrderScope_not_InScope

example : ¬ InScope computabilityScope := computabilityScope_not_InScope

example : ¬ InScope acQuotientScope := acQuotientScope_not_InScope

-- Theorem identifiers are reachable.

example : True := by
  have := @sharingScope_not_InScope
  trivial

example : True := by
  have := @binderScope_not_InScope
  trivial

example : True := by
  have := @innermostOnlyScope_not_InScope
  trivial

example : True := by
  have := @coOrderScope_not_InScope
  trivial

example : True := by
  have := @computabilityScope_not_InScope
  trivial

example : True := by
  have := @acQuotientScope_not_InScope
  trivial

end DirectBarrierScopeReach
