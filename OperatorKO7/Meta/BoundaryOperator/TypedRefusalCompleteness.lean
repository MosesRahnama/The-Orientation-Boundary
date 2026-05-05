import OperatorKO7.Meta.BoundaryOperator
import OperatorKO7.Meta.MetaHalt_Predicate

/-!
# Boundary Operator Typed Refusal Completeness

This file packages the finite refusal carrier required by WS-D and connects it
to the existing META-HALT typed-output algebra.
-/

namespace OperatorKO7.Meta.BoundaryOperator

open OperatorKO7.MetaHalt.Predicate

universe u v

/-- The finite refusal surface required by the procedure-facing boundary operator. -/
inductive RefusalType where
  | Y
  | N
  | U
  | H
  deriving DecidableEq, Repr

/-- Support set for the finite refusal carrier. Every refusal constructor is
available at the execution boundary, so the support is total. -/
def refusalTypeSupport : Set RefusalType :=
  Set.univ

theorem refusalType_mem_support (r : RefusalType) : r ∈ refusalTypeSupport := by
  trivial

/-- The classification data needed to turn a boundary-operator codomain into the
finite refusal carrier. -/
structure TypedRefusalClassification (Y : Type v) where
  classify : Y → RefusalType

/-- The exact typed-output bridge required by WS-D. -/
def typedOutputToRefusalType : TypedOutput → RefusalType
  | .T1_complete _ => .Y
  | .T2_construction _ _ => .Y
  | .T3_confession _ _ _ _ => .N
  | .T4_abstention _ _ _ => .H
  | .T5_impossibilityCert _ _ => .U

theorem typedOutputToRefusalType_mem_support (out : TypedOutput) :
    typedOutputToRefusalType out ∈ refusalTypeSupport := by
  exact refusalType_mem_support (typedOutputToRefusalType out)

/-- The canonical classification on the existing META-HALT typed-output algebra. -/
def typedOutputClassification : TypedRefusalClassification TypedOutput where
  classify := typedOutputToRefusalType

/-- The typed-refusal completeness transport in honest conditional form: once a
classification into the finite refusal carrier is provided, the codomain is totally
typed by that carrier. -/
theorem TypedRefusalCompleteness
    {X : Type u} {Y : Type v}
    (_B : BoundaryOperator X Y)
    (C : TypedRefusalClassification Y) :
    ∃ (Y_typed : Set Y) (refusal_classification : Y → RefusalType),
      Y_typed = Set.univ ∧
      ∀ y, refusal_classification y ∈ refusalTypeSupport := by
  refine ⟨Set.univ, C.classify, rfl, ?_⟩
  intro y
  exact refusalType_mem_support (C.classify y)

/-- The existing META-HALT typed-output algebra satisfies the finite refusal
carrier directly. -/
theorem TypedOutputBoundaryOperatorCompleteness
    {X : Type u}
    (B : BoundaryOperator X TypedOutput) :
    ∃ (Y_typed : Set TypedOutput) (refusal_classification : TypedOutput → RefusalType),
      Y_typed = Set.univ ∧
      ∀ y, refusal_classification y ∈ refusalTypeSupport :=
  TypedRefusalCompleteness B typedOutputClassification

/-- Procedure-grade four-class exhaustiveness lemma (LONG-10 WS-A5.3).
Every `RefusalType` is one of the four named constructors; this is
the carrier-level exhaustiveness statement that agent 3's
TypedUniversal Lean bridge consumes. -/
theorem refusalType_exhaustive (r : RefusalType) :
    r = RefusalType.Y ∨ r = RefusalType.N
      ∨ r = RefusalType.U ∨ r = RefusalType.H := by
  cases r <;> simp

/-- Procedure-grade typed-output partition (LONG-10 WS-A5.3). For every
classification into the finite refusal carrier, the four-class partition
covers the entire codomain — no `y` lands outside `{Y, N, U, H}`.
This is the form agent 3's `OperatorKO7/Meta/Universal/Classify
Universal.lean` cites as `typed_refusal_partition_exhaustive`. -/
theorem TypedRefusalCompleteness_procedure_grade
    {X : Type u} {Y : Type v}
    (B : BoundaryOperator X Y)
    (C : TypedRefusalClassification Y) :
    (∃ (Y_typed : Set Y) (refusal_classification : Y → RefusalType),
        Y_typed = Set.univ ∧
        ∀ y, refusal_classification y ∈ refusalTypeSupport)
    ∧
    (∀ y : Y, C.classify y = RefusalType.Y
              ∨ C.classify y = RefusalType.N
              ∨ C.classify y = RefusalType.U
              ∨ C.classify y = RefusalType.H) :=
  ⟨TypedRefusalCompleteness B C,
   fun y => refusalType_exhaustive (C.classify y)⟩

/-- Discharge of the procedure-grade typed-refusal completeness on the
META-HALT classification (the canonical typed-output algebra). -/
theorem TypedOutputBoundaryOperatorCompleteness_procedure_grade
    {X : Type u}
    (B : BoundaryOperator X TypedOutput) :
    (∃ (Y_typed : Set TypedOutput)
        (refusal_classification : TypedOutput → RefusalType),
        Y_typed = Set.univ ∧
        ∀ y, refusal_classification y ∈ refusalTypeSupport)
    ∧
    (∀ y : TypedOutput,
        typedOutputToRefusalType y = RefusalType.Y
          ∨ typedOutputToRefusalType y = RefusalType.N
          ∨ typedOutputToRefusalType y = RefusalType.U
          ∨ typedOutputToRefusalType y = RefusalType.H) :=
  TypedRefusalCompleteness_procedure_grade B typedOutputClassification

end OperatorKO7.Meta.BoundaryOperator
