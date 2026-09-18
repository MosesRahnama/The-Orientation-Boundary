import OperatorKO7.Meta.MutualDuplication_FiniteSchema_Builder

/-!
# Constructors and Witness Instances for First-Class Finite-Cycle Schemas

This module packages reusable small finite-cycle constructors and re-expresses the existing
concrete witness systems through those constructors.
-/

namespace OperatorKO7.MutualDuplicationFiniteSchema

open OperatorKO7.StepDuplicating

namespace Constructors

/-- Reusable two-rule constructor data. -/
structure TwoRuleData where
  T : Type
  base : T
  succ : T → T
  wrap : T → T → T
  recurA : T → T → T → T
  recurB : T → T → T → T
  Step : T → T → Prop
  stepA_succ : ∀ b s n, Step (recurA b s (succ n)) (wrap s (recurB b s n))
  stepB_succ : ∀ b s n, Step (recurB b s (succ n)) (wrap s (recurA b s n))

/-- Re-express the two-rule constructor through the arbitrary finite-cycle builder surface. -/
def TwoRuleData.toFiniteCycleBuilder (D : TwoRuleData) : FiniteCycleBuilder.Builder 1 where
  T := D.T
  base := D.base
  succ := D.succ
  wrap := D.wrap
  recur := fun i =>
    match i.1 with
    | 0 => D.recurA
    | _ => D.recurB
  Step := D.Step
  step_succ := by
    intro i b s n
    fin_cases i
    · simpa [FiniteCycleBuilder.advance] using D.stepA_succ b s n
    · simpa [FiniteCycleBuilder.advance] using D.stepB_succ b s n

/-- Reconstruct the theorem-native two-rule mutual system. -/
def TwoRuleData.toMutualSystem (D : TwoRuleData) : OperatorKO7.MutualDuplicationSchema.System where
  T := D.T
  base := D.base
  succ := D.succ
  wrap := D.wrap
  recurA := D.recurA
  recurB := D.recurB
  Step := D.Step
  stepA_succ := D.stepA_succ
  stepB_succ := D.stepB_succ

/-- Reconstruct the first-class finite-cycle system of length `2`. -/
def TwoRuleData.toKCycleSystem (D : TwoRuleData) : KCycleSystem 1 :=
  OperatorKO7.MutualDuplicationSchema.System.toKCycleSystem_two D.toMutualSystem

/-- Any two-rule constructor instance realizes its finite-cycle path at either node. -/
theorem TwoRuleData.cycle_realized_at
    (D : TwoRuleData) (i : Fin 2) (b s n : D.T) :
    Relation.TransGen (KCycleSystem.StepCtx D.toKCycleSystem)
      (KCycleSchema.cycleSource D.toKCycleSystem.toKCycleSchema i b s n)
      (KCycleSchema.cycleTarget D.toKCycleSystem.toKCycleSchema i b s n) := by
  exact KCycleSystem.cycle_realized_via_kNode D.toKCycleSystem i b s n

/-- Reusable three-rule constructor data. -/
structure ThreeRuleData where
  T : Type
  base : T
  succ : T → T
  wrap : T → T → T
  recur0 : T → T → T → T
  recur1 : T → T → T → T
  recur2 : T → T → T → T
  Step : T → T → Prop
  step0_succ : ∀ b s n, Step (recur0 b s (succ n)) (wrap s (recur1 b s n))
  step1_succ : ∀ b s n, Step (recur1 b s (succ n)) (wrap s (recur2 b s n))
  step2_succ : ∀ b s n, Step (recur2 b s (succ n)) (wrap s (recur0 b s n))

/-- Re-express the three-rule constructor through the arbitrary finite-cycle builder surface. -/
def ThreeRuleData.toFiniteCycleBuilder (D : ThreeRuleData) : FiniteCycleBuilder.Builder 2 where
  T := D.T
  base := D.base
  succ := D.succ
  wrap := D.wrap
  recur := fun i =>
    match i.1 with
    | 0 => D.recur0
    | 1 => D.recur1
    | _ => D.recur2
  Step := D.Step
  step_succ := by
    intro i b s n
    fin_cases i
    · simpa [FiniteCycleBuilder.advance] using D.step0_succ b s n
    · simpa [FiniteCycleBuilder.advance] using D.step1_succ b s n
    · simpa [FiniteCycleBuilder.advance] using D.step2_succ b s n

/-- Reconstruct the first-class finite-cycle system of length `3`. -/
def ThreeRuleData.toKCycleSystem (D : ThreeRuleData) : KCycleSystem 2 where
  T := D.T
  base := D.base
  succ := D.succ
  wrap := D.wrap
  recur := fun i =>
    match i.1 with
    | 0 => D.recur0
    | 1 => D.recur1
    | _ => D.recur2
  Step := D.Step
  step_succ := by
    intro i b s n
    fin_cases i
    · exact D.step0_succ b s n
    · exact D.step1_succ b s n
    · exact D.step2_succ b s n

/-- Any three-rule constructor instance realizes its finite-cycle path at any node. -/
theorem ThreeRuleData.cycle_realized_at
    (D : ThreeRuleData) (i : Fin 3) (b s n : D.T) :
    Relation.TransGen (KCycleSystem.StepCtx D.toKCycleSystem)
      (KCycleSchema.cycleSource D.toKCycleSystem.toKCycleSchema i b s n)
      (KCycleSchema.cycleTarget D.toKCycleSystem.toKCycleSchema i b s n) := by
  exact KCycleSystem.cycle_realized_via_kNode D.toKCycleSystem i b s n

end Constructors

namespace KCycleSystem

/-- Constructor view of the concrete two-rule witness system. -/
def twoRuleWitnessData : Constructors.TwoRuleData where
  T := OperatorKO7.MutualDuplicationCase.AltTerm
  base := OperatorKO7.MutualDuplicationCase.AltTerm.base
  succ := OperatorKO7.MutualDuplicationCase.AltTerm.succ
  wrap := OperatorKO7.MutualDuplicationCase.AltTerm.wrap
  recurA := OperatorKO7.MutualDuplicationCase.AltTerm.recurA
  recurB := OperatorKO7.MutualDuplicationCase.AltTerm.recurB
  Step := OperatorKO7.MutualDuplicationCase.AltStep
  stepA_succ := by
    intro b s n
    exact OperatorKO7.MutualDuplicationCase.AltStep.R_A_succ b s n
  stepB_succ := by
    intro b s n
    exact OperatorKO7.MutualDuplicationCase.AltStep.R_B_succ b s n

@[simp] theorem twoRuleWitnessData_toKCycleSystem_eq :
    twoRuleWitnessData.toKCycleSystem = twoRuleWitnessSystem :=
  rfl

/-- Constructor view of the concrete three-rule witness system. -/
def threeRuleWitnessData : Constructors.ThreeRuleData where
  T := ThreeRuleWitness.Term
  base := ThreeRuleWitness.Term.base
  succ := ThreeRuleWitness.Term.succ
  wrap := ThreeRuleWitness.Term.wrap
  recur0 := ThreeRuleWitness.Term.recur0
  recur1 := ThreeRuleWitness.Term.recur1
  recur2 := ThreeRuleWitness.Term.recur2
  Step := ThreeRuleWitness.Step
  step0_succ := by
    intro b s n
    exact ThreeRuleWitness.Step.R0_succ b s n
  step1_succ := by
    intro b s n
    exact ThreeRuleWitness.Step.R1_succ b s n
  step2_succ := by
    intro b s n
    exact ThreeRuleWitness.Step.R2_succ b s n

@[simp] theorem threeRuleWitnessData_toKCycleSystem_eq :
    threeRuleWitnessData.toKCycleSystem = threeRuleWitnessSystem :=
  rfl

/-- Concrete additive barrier specialization over the two-rule witness system. -/
theorem twoRuleWitnessSystem_no_global_orients_ctx_additive
    (M : KCycleSchema.AdditiveMeasure twoRuleWitnessSystem.toKCycleSchema) :
    ¬ GlobalOrientsCtx twoRuleWitnessSystem M.eval (· < ·) := by
  exact no_global_orients_ctx_additive M

/-- Concrete arbitrary-node affine barrier specialization over the two-rule witness system. -/
theorem twoRuleWitnessSystem_no_global_orients_ctx_affine_of_unbounded_at
    (M : KCycleSchema.AffineMeasure twoRuleWitnessSystem.toKCycleSchema)
    (i : Fin 2)
    (hunbounded : StepDuplicatingSchema.HasUnboundedRange (KCycleAffineAt i M)) :
    ¬ GlobalOrientsCtx twoRuleWitnessSystem M.eval (· < ·) := by
  exact no_global_orients_ctx_affine_of_unbounded_at M i hunbounded

/-- Concrete additive barrier specialization over the three-rule witness system. -/
theorem threeRuleWitnessSystem_no_global_orients_ctx_additive
    (M : KCycleSchema.AdditiveMeasure threeRuleWitnessSystem.toKCycleSchema) :
    ¬ GlobalOrientsCtx threeRuleWitnessSystem M.eval (· < ·) := by
  exact no_global_orients_ctx_additive M

/-- Concrete arbitrary-node affine barrier specialization over the three-rule witness system. -/
theorem threeRuleWitnessSystem_no_global_orients_ctx_affine_of_unbounded_at
    (M : KCycleSchema.AffineMeasure threeRuleWitnessSystem.toKCycleSchema)
    (i : Fin 3)
    (hunbounded : StepDuplicatingSchema.HasUnboundedRange (KCycleAffineAt i M)) :
    ¬ GlobalOrientsCtx threeRuleWitnessSystem M.eval (· < ·) := by
  exact no_global_orients_ctx_affine_of_unbounded_at M i hunbounded

end KCycleSystem

end OperatorKO7.MutualDuplicationFiniteSchema
