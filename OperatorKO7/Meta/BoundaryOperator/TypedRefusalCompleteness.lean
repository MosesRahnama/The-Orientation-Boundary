import OperatorKO7.Meta.BoundaryOperator
import OperatorKO7.Meta.MetaHalt_Predicate

/-!
This module enumerates four refusal constructors and packages arbitrary classifiers into that
carrier. Set.univ supplies carrier membership. The results establish constructor coverage and
classifier codomain typing; semantic classification correctness and disjointness require
additional predicates.
-/

namespace OperatorKO7.Meta.BoundaryOperator

open OperatorKO7.MetaHalt.Predicate

universe u v

/-- Carrier with the constructors displayed below. -/
inductive RefusalType where
  | Y
  | N
  | U
  | H
  deriving DecidableEq, Repr

/-- Definition with formal content given by the displayed type and body.
-/
def refusalTypeSupport : Set RefusalType :=
  Set.univ

theorem refusalType_mem_support (r : RefusalType) : r ∈ refusalTypeSupport := by
  trivial

/-- Data record whose requirements are the fields displayed below.
-/
structure TypedRefusalClassifier (Y : Type v) where
  classify : Y → RefusalType

/-- Definition with formal content given by the displayed type and body. -/
def typedOutputToRefusalType : TypedOutput → RefusalType
  | .T1_complete _ => .Y
  | .T2_construction _ _ => .Y
  | .T3_confession _ _ _ _ => .N
  | .T4_abstention _ _ _ => .H
  | .T5_impossibilityCert _ _ => .U

theorem typedOutputToRefusalType_mem_support (out : TypedOutput) :
    typedOutputToRefusalType out ∈ refusalTypeSupport := by
  exact refusalType_mem_support (typedOutputToRefusalType out)

/-- Definition with formal content given by the displayed type and body. -/
def typedOutputClassifier : TypedRefusalClassifier TypedOutput where
  classify := typedOutputToRefusalType

/-- The displayed proposition follows from the stated hypotheses.

-/
theorem TypedRefusalCompleteness
    {X : Type u} {Y : Type v}
    (_B : BoundaryOperator X Y)
    (C : TypedRefusalClassifier Y) :
    ∃ (Y_typed : Set Y) (refusal_classifier : Y → RefusalType),
      Y_typed = Set.univ ∧
      ∀ y, refusal_classifier y ∈ refusalTypeSupport := by
  refine ⟨Set.univ, C.classify, rfl, ?_⟩
  intro y
  exact refusalType_mem_support (C.classify y)

/-- The displayed proposition follows from the stated hypotheses.
-/
theorem TypedOutputBoundaryOperatorCompleteness
    {X : Type u}
    (B : BoundaryOperator X TypedOutput) :
    ∃ (Y_typed : Set TypedOutput) (refusal_classifier : TypedOutput → RefusalType),
      Y_typed = Set.univ ∧
      ∀ y, refusal_classifier y ∈ refusalTypeSupport :=
  TypedRefusalCompleteness B typedOutputClassifier

/-- The displayed proposition follows from the stated hypotheses.


-/
theorem refusalType_exhaustive (r : RefusalType) :
    r = RefusalType.Y ∨ r = RefusalType.N
      ∨ r = RefusalType.U ∨ r = RefusalType.H := by
  cases r <;> simp

/-- The displayed proposition follows from the stated hypotheses.



-/
theorem TypedRefusalCompleteness_engine_grade
    {X : Type u} {Y : Type v}
    (B : BoundaryOperator X Y)
    (C : TypedRefusalClassifier Y) :
    (∃ (Y_typed : Set Y) (refusal_classifier : Y → RefusalType),
        Y_typed = Set.univ ∧
        ∀ y, refusal_classifier y ∈ refusalTypeSupport)
    ∧
    (∀ y : Y, C.classify y = RefusalType.Y
              ∨ C.classify y = RefusalType.N
              ∨ C.classify y = RefusalType.U
              ∨ C.classify y = RefusalType.H) :=
  ⟨TypedRefusalCompleteness B C,
   fun y => refusalType_exhaustive (C.classify y)⟩

/-- The displayed proposition follows from the stated hypotheses.
-/
theorem TypedOutputBoundaryOperatorCompleteness_engine_grade
    {X : Type u}
    (B : BoundaryOperator X TypedOutput) :
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
  TypedRefusalCompleteness_engine_grade B typedOutputClassifier

end OperatorKO7.Meta.BoundaryOperator
