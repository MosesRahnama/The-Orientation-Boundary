import OperatorKO7.Meta.OrderedSemiringMatrixLiftBarrier

set_option autoImplicit false

/-!
# Ordered-Semiring Matrix-Lift Barrier, abstract certificate-free boundary

This module closes the open prove-or-refute branch for the certificate-free
ordered-semiring matrix-lift barrier at the sharpest true form currently justified
by the live library.

The current landed theorem
`OrderedSemiringMatrixLiftBarrier.ordered_semiring_matrix_lift_barrier_arbitrary`
is genuine, but scalar-dominance-conditional: it needs a
`LiftBarrierCertificate`. The remaining open question was whether that
certificate could be removed uniformly over the closed `BaseSemiringKind`
universe.

This file gives the negative answer.

1. It isolates the exact currently theorem-backed subclass `LiftBarrierPredicateP`:
   the natural, arctic, and tropical rows, which are the rows for which the live
   library already exposes concrete scalar-dominance certificates.
2. It constructs a concrete Boolean-row counterexample: a monotone 1x1 Boolean
   interpretation whose induced system globally orients the duplicating step.
3. It packages the Boolean boundary as a named theorem, showing that the
   certificate-free blanket claim is false on the Boolean row.

No new axioms are introduced. No existing barrier theorem is weakened. The point
is instead to record, formally and scope-honestly, that the unconditional
certificate-free abstraction is not available in the current closed universe.
-/

open OperatorKO7
open OperatorKO7.StepDuplicating
open OperatorKO7.StepDuplicating.StepDuplicatingSchema
open OperatorKO7.OrderedSemiringMatrixLift

namespace OperatorKO7.Meta.OrderedSemiringMatrixLiftBarrierAbstract

/-- Boolean preorder on the 1x1 Boolean matrix carrier.

This is the usual `false ≤ true` order, written directly on `Bool` because the
closed lift universe only records the Boolean row at the tag level. -/
def BoolMatrix1Le : Bool → Bool → Prop
  | false, _ => True
  | true, b => b = true

/-- Strict Boolean order on the 1x1 Boolean matrix carrier. -/
def BoolMatrix1Lt : Bool → Bool → Prop
  | false, true => True
  | _, _ => False

/-- A Boolean-valued interpretation is monotone on the 1x1 Boolean matrix carrier
when the constructor actions preserve `BoolMatrix1Le`. -/
def MonotoneBoolMatrix1Schema (S : StepDuplicatingSchema) (μ : S.T → Bool) : Prop :=
  (∀ {x y : S.T},
      BoolMatrix1Le (μ x) (μ y) →
      BoolMatrix1Le (μ (S.succ x)) (μ (S.succ y))) ∧
  (∀ {x₁ x₂ y₁ y₂ : S.T},
      BoolMatrix1Le (μ x₁) (μ y₁) →
      BoolMatrix1Le (μ x₂) (μ y₂) →
      BoolMatrix1Le (μ (S.wrap x₁ x₂)) (μ (S.wrap y₁ y₂))) ∧
  (∀ {b₁ b₂ s₁ s₂ n₁ n₂ : S.T},
      BoolMatrix1Le (μ b₁) (μ b₂) →
      BoolMatrix1Le (μ s₁) (μ s₂) →
      BoolMatrix1Le (μ n₁) (μ n₂) →
      BoolMatrix1Le (μ (S.recur b₁ s₁ n₁)) (μ (S.recur b₂ s₂ n₂)))

/-- The exact theorem-backed subclass currently justified by the landed
scalar-dominance barrier stack.

This is the sharpest true class presently supported by named concrete rows in the
live library: natural, arctic, and tropical. The Boolean row is excluded by the
counterexample below, and the integer/rational/real rows are not overclaimed here. -/
def LiftBarrierPredicateP : BaseSemiringKind → Prop
  | .naturalSemiring => True
  | .arcticSemiring => True
  | .tropicalSemiring => True
  | _ => False

/-- Exact characterization of the current theorem-backed subclass `LiftBarrierPredicateP`. -/
theorem liftBarrierPredicateP_iff (k : BaseSemiringKind) :
    LiftBarrierPredicateP k ↔
      k = .naturalSemiring ∨ k = .arcticSemiring ∨ k = .tropicalSemiring := by
  cases k <;> simp [LiftBarrierPredicateP]

/-- The arctic row lies in the current theorem-backed subclass `LiftBarrierPredicateP`. -/
theorem arcticSemiring_in_liftBarrierPredicateP :
    LiftBarrierPredicateP .arcticSemiring := by
  simp [LiftBarrierPredicateP]

/-- The tropical row lies in the current theorem-backed subclass `LiftBarrierPredicateP`. -/
theorem tropicalSemiring_in_liftBarrierPredicateP :
    LiftBarrierPredicateP .tropicalSemiring := by
  simp [LiftBarrierPredicateP]

/-- The natural row lies in the current theorem-backed subclass `LiftBarrierPredicateP`. -/
theorem naturalSemiring_in_liftBarrierPredicateP :
    LiftBarrierPredicateP .naturalSemiring := by
  simp [LiftBarrierPredicateP]

private def booleanCounterexampleSchema : StepDuplicatingSchema where
  T := Bool
  base := false
  succ := fun _ => true
  wrap := fun _ _ => false
  recur := fun _ _ _ => true

private def booleanCounterexampleSystem : StepDuplicatingSystem where
  toStepDuplicatingSchema := booleanCounterexampleSchema
  Step := fun a b => a = true ∧ b = false
  dup_step := by
    intro b s n
    simp [booleanCounterexampleSchema]

private theorem booleanCounterexampleMonotone :
    MonotoneBoolMatrix1Schema booleanCounterexampleSchema (fun x => x) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x y hxy
    simp [booleanCounterexampleSchema, BoolMatrix1Le]
  · intro x₁ x₂ y₁ y₂ hx₁ hx₂
    simp [booleanCounterexampleSchema, BoolMatrix1Le]
  · intro b₁ b₂ s₁ s₂ n₁ n₂ hb hs hn
    simp [booleanCounterexampleSchema, BoolMatrix1Le]

private theorem booleanCounterexampleGlobalOrients :
    GlobalOrients booleanCounterexampleSystem (fun x => x) BoolMatrix1Lt := by
  intro a b hab
  rcases hab with ⟨ha, hb⟩
  subst ha
  subst hb
  simp [BoolMatrix1Lt]

/-- Boolean-row boundary theorem.

The Boolean row is genuinely present in the closed lift universe, but it does not
lie in the theorem-backed scalar-dominance subclass `LiftBarrierPredicateP`. More
strongly, there exists a monotone Boolean-valued 1x1 interpretation whose induced
system globally orients the duplicating step, so the blanket certificate-free
barrier fails on this row. -/
theorem booleanSemiring_boundary_theorem :
    liftToMatrixAlgebra .booleanSemiring = .booleanMatrix ∧
    ¬ LiftBarrierPredicateP .booleanSemiring ∧
    ∃ (Sys : StepDuplicatingSystem) (μ : Sys.T → Bool),
      MonotoneBoolMatrix1Schema Sys.toStepDuplicatingSchema μ ∧
      GlobalOrients Sys μ BoolMatrix1Lt := by
  refine ⟨rfl, ?_, ?_⟩
  · simp [LiftBarrierPredicateP]
  · refine ⟨booleanCounterexampleSystem, (fun x => x), ?_, ?_⟩
    · exact booleanCounterexampleMonotone
    · exact booleanCounterexampleGlobalOrients

/-- The blanket certificate-free Boolean-row barrier is false. -/
theorem booleanSemiring_certificate_free_barrier_false :
    ¬ (∀ (Sys : StepDuplicatingSystem) (μ : Sys.T → Bool),
        MonotoneBoolMatrix1Schema Sys.toStepDuplicatingSchema μ →
        ¬ GlobalOrients Sys μ BoolMatrix1Lt) := by
  intro h
  rcases booleanSemiring_boundary_theorem with ⟨_, _, ⟨Sys, μ, hmono, horient⟩⟩
  exact (h Sys μ hmono) horient

end OperatorKO7.Meta.OrderedSemiringMatrixLiftBarrierAbstract
