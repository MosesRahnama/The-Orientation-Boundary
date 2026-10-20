import OperatorKO7.Meta.BoundaryOperator.TypedRefusalCompleteness

namespace BoundaryOperatorTypedRefusalReach

open OperatorKO7.Meta.BoundaryOperator
open OperatorKO7.MetaHalt.Predicate

#check RefusalType
#check refusalTypeSupport
#check refusalType_mem_support
#check TypedRefusalClassifier
#check TypedRefusalCompleteness
#check typedOutputToRefusalType
#check typedOutputToRefusalType_mem_support
#check typedOutputClassifier
#check TypedOutputBoundaryOperatorCompleteness

example : typedOutputToRefusalType
    (TypedOutput.T4_abstention "resource" ["TRS"] ["MPO"]) = RefusalType.H := by
  rfl

example : typedOutputToRefusalType
    (TypedOutput.T5_impossibilityCert "meta" "cert") = RefusalType.U := by
  rfl

example {X : Type} (B : BoundaryOperator X TypedOutput) :
    ∃ (Y_typed : Set TypedOutput) (refusal_classifier : TypedOutput → RefusalType),
      Y_typed = Set.univ ∧
      ∀ y, refusal_classifier y ∈ refusalTypeSupport :=
  TypedOutputBoundaryOperatorCompleteness B

-- WS-A5.3: engine-grade exhaustiveness reach.
#check refusalType_exhaustive
#check @TypedRefusalCompleteness_engine_grade
#check @TypedOutputBoundaryOperatorCompleteness_engine_grade

example (r : RefusalType) :
    r = RefusalType.Y ∨ r = RefusalType.N
      ∨ r = RefusalType.U ∨ r = RefusalType.H :=
  refusalType_exhaustive r

example {X : Type} (B : BoundaryOperator X TypedOutput) :
    (∃ (Y_typed : Set TypedOutput)
        (refusal_classifier : TypedOutput → RefusalType),
        Y_typed = Set.univ ∧
        ∀ y, refusal_classifier y ∈ refusalTypeSupport)
    ∧
    (∀ y : TypedOutput,
        typedOutputToRefusalType y = RefusalType.Y
          ∨ typedOutputToRefusalType y = RefusalType.N
          ∨ typedOutputToRefusalType y = RefusalType.U
          ∨ typedOutputToRefusalType y = RefusalType.H) :=
  TypedOutputBoundaryOperatorCompleteness_engine_grade B

end BoundaryOperatorTypedRefusalReach
