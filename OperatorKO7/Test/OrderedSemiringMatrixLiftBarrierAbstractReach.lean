import OperatorKO7.Meta.OrderedSemiringMatrixLiftBarrierAbstract

set_option autoImplicit false

namespace OrderedSemiringMatrixLiftBarrierAbstractReach

open OperatorKO7
open OperatorKO7.StepDuplicating
open OperatorKO7.StepDuplicating.StepDuplicatingSchema
open OperatorKO7.OrderedSemiringMatrixLift
open OperatorKO7.Meta.OrderedSemiringMatrixLiftBarrierAbstract

#check @BoolMatrix1Le
#check @BoolMatrix1Lt
#check @MonotoneBoolMatrix1Schema
#check @LiftBarrierPredicateP
#check @liftBarrierPredicateP_iff
#check @naturalSemiring_in_liftBarrierPredicateP
#check @arcticSemiring_in_liftBarrierPredicateP
#check @tropicalSemiring_in_liftBarrierPredicateP
#check @booleanSemiring_boundary_theorem
#check @booleanSemiring_certificate_free_barrier_false

example : LiftBarrierPredicateP .arcticSemiring :=
  arcticSemiring_in_liftBarrierPredicateP

example : LiftBarrierPredicateP .tropicalSemiring :=
  tropicalSemiring_in_liftBarrierPredicateP

example :
    liftToMatrixAlgebra .booleanSemiring = .booleanMatrix :=
  rfl

example :
    ¬ LiftBarrierPredicateP .booleanSemiring := by
  rcases booleanSemiring_boundary_theorem with ⟨_, hboundary, _⟩
  exact hboundary

example :
    ∃ (Sys : StepDuplicatingSystem) (μ : Sys.T → Bool),
      MonotoneBoolMatrix1Schema Sys.toStepDuplicatingSchema μ ∧
      GlobalOrients Sys μ BoolMatrix1Lt := by
  rcases booleanSemiring_boundary_theorem with ⟨_, _, hwitness⟩
  exact hwitness

example :
    ¬ (∀ (Sys : StepDuplicatingSystem) (μ : Sys.T → Bool),
        MonotoneBoolMatrix1Schema Sys.toStepDuplicatingSchema μ →
        ¬ GlobalOrients Sys μ BoolMatrix1Lt) :=
  booleanSemiring_certificate_free_barrier_false

end OrderedSemiringMatrixLiftBarrierAbstractReach
