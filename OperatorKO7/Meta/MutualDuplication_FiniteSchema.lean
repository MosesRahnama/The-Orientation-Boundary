import OperatorKO7.Meta.MutualDuplication_SchemaBarrier
import OperatorKO7.Meta.MutualDuplication_KNode_Abstract
import OperatorKO7.Meta.MutualDuplication_Case

/-!
# First-Class Finite-Cycle Mutual Step-Duplicating Schema

This module re-exports the existing finite `k + 1`-node SCC infrastructure through a
first-class mutual-recursion surface. The point is to expose the finite-cycle objects and
barrier theorems under the mutual-schema lane without duplicating the older proof stack.
-/

namespace OperatorKO7.MutualDuplicationFiniteSchema

open OperatorKO7.StepDuplicating

/-- First-class finite nonempty mutual-recursion schema, factored through the existing
finite `k + 1`-node SCC interface. -/
abbrev KCycleSchema (k : Nat) :=
  OperatorKO7.MutualDuplicationKNode.CyclicDupSchema k

/-- First-class finite nonempty mutual-recursion system, factored through the existing
finite `k + 1`-node SCC interface. -/
abbrev KCycleSystem (k : Nat) :=
  OperatorKO7.MutualDuplicationKNode.CyclicDupSchema.CyclicDupSystem k

namespace KCycleSchema

abbrev toKNodeSchema {k : Nat} (S : KCycleSchema k) :
    OperatorKO7.MutualDuplicationKNode.CyclicDupSchema k :=
  S

abbrev AdditiveMeasure {k : Nat} (S : KCycleSchema k) :=
  OperatorKO7.MutualDuplicationKNode.CyclicDupSchema.AdditiveMeasure S

abbrev AffineMeasure {k : Nat} (S : KCycleSchema k) :=
  OperatorKO7.MutualDuplicationKNode.CyclicDupSchema.AffineMeasure S

/-- The ordinary node schema at a fixed cycle index. -/
def toNodeSchema {k : Nat} (S : KCycleSchema k) (i : Fin (k + 1)) : StepDuplicatingSchema :=
  OperatorKO7.MutualDuplicationKNodeAbstract.CyclicDupSchema.toNodeSchema S.toKNodeSchema i

/-- The one-cycle derived duplication schema at a fixed cycle index. -/
def toCycleSchemaAt {k : Nat} (S : KCycleSchema k) (i : Fin (k + 1)) : StepDuplicatingSchema :=
  OperatorKO7.MutualDuplicationKNode.CyclicDupSchema.toDupKSchemaAt S.toKNodeSchema i

/-- One full finite cycle source term at node `i`. -/
def cycleSource {k : Nat} (S : KCycleSchema k) (i : Fin (k + 1)) (b s n : S.T) : S.T :=
  S.recur i b s (OperatorKO7.MutualDuplicationKNode.CyclicDupSchema.cycleSucc S.toKNodeSchema n)

/-- One full finite cycle target term at node `i`. -/
def cycleTarget {k : Nat} (S : KCycleSchema k) (i : Fin (k + 1)) (b s n : S.T) : S.T :=
  OperatorKO7.MutualDuplicationKNode.CyclicDupSchema.cycleWrap S.toKNodeSchema s
    (S.recur i b s n)

abbrev AffineMeasure.toCycleMeasureAt {k : Nat} {S : KCycleSchema k}
    (M : AffineMeasure S) (i : Fin (k + 1)) :
    StepDuplicatingSchema.AffineMeasure (S.toCycleSchemaAt i) :=
  OperatorKO7.MutualDuplicationKNode.CyclicDupSchema.AffineMeasure.toDupKMeasureAt M i

/-- Additive direct orienters fail on the first-class finite-cycle mutual schema. -/
theorem no_additive_orients_cycle
    {k : Nat} {S : KCycleSchema k} (M : AdditiveMeasure S) :
    ¬ (∀ (i : Fin (k + 1)) (b s n : S.T),
      M.eval (cycleTarget S i b s n) < M.eval (cycleSource S i b s n)) := by
  intro h
  exact
    OperatorKO7.MutualDuplicationKNode.CyclicDupSchema.no_additive_orients_cyclic_dup_composite
      (S := S.toKNodeSchema) M
      (fun i b s n => by simpa [cycleSource, cycleTarget] using h i b s n)

/-- Affine direct orienters fail on the first-class finite-cycle mutual schema at any fixed
cycle index whose derived one-cycle schema has the usual unbounded pump. -/
theorem no_affine_orients_cycle_of_unbounded
    {k : Nat} {S : KCycleSchema k} (M : AffineMeasure S) (i : Fin (k + 1))
    (hunbounded : StepDuplicatingSchema.HasUnboundedRange (M.toCycleMeasureAt i)) :
    ¬ (∀ (b s n : S.T),
      M.eval (cycleTarget S i b s n) < M.eval (cycleSource S i b s n)) := by
  simpa [cycleSource, cycleTarget, toCycleSchemaAt] using
    (OperatorKO7.MutualDuplicationKNode.CyclicDupSchema.no_affine_orients_cyclic_dup_composite_of_unbounded
      (S := S.toKNodeSchema) M i hunbounded)

end KCycleSchema

namespace KCycleSystem

abbrev toKCycleSchema {k : Nat} (Sys : KCycleSystem k) : KCycleSchema k :=
  Sys.toCyclicDupSchema

/-- Bridge back to the legacy `k + 1`-node SCC witness layer. -/
abbrev toKNodeWitness {k : Nat} (Sys : KCycleSystem k) :
    OperatorKO7.MutualDuplicationKNode.CyclicDupSchema.CyclicDupSystem k :=
  Sys

abbrev StepCtx {k : Nat} (Sys : KCycleSystem k) : Sys.T → Sys.T → Prop :=
  OperatorKO7.MutualDuplicationKNode.CyclicDupSchema.StepCtx Sys.toKNodeWitness

/-- Orientation of the finite-cycle contextual relation. -/
def GlobalOrientsCtx {k : Nat} {α : Type} (Sys : KCycleSystem k) (m : Sys.T → α)
    (lt : α → α → Prop) : Prop :=
  ∀ {a b : Sys.T}, StepCtx Sys a b → lt (m b) (m a)

/-- First-class cycle witness obtained from the abstract delayed-cycle layer at the base node. -/
def toCycleWitness {k : Nat} (Sys : KCycleSystem k) :
    OperatorKO7.MutualDuplicationCycleFlow.CycleWitness
      (KCycleSchema.toNodeSchema Sys.toKCycleSchema (0 : Fin (k + 1))) (k + 1) :=
  OperatorKO7.MutualDuplicationKNodeAbstract.CyclicDupSystem.cycleWitness Sys.toKNodeWitness

/-- The finite-cycle path realized by the legacy `k + 1`-node SCC development is exactly the
first-class finite-cycle path. -/
theorem cycle_realized_via_kNode
    {k : Nat} (Sys : KCycleSystem k) (i : Fin (k + 1)) (b s n : Sys.T) :
    Relation.TransGen (StepCtx Sys)
      (KCycleSchema.cycleSource Sys.toKCycleSchema i b s n)
      (KCycleSchema.cycleTarget Sys.toKCycleSchema i b s n) := by
  simpa [StepCtx, KCycleSchema.cycleSource, KCycleSchema.cycleTarget] using
    (OperatorKO7.MutualDuplicationKNode.CyclicDupSchema.CyclicDupSystem.cycle_realized
      Sys.toKNodeWitness i b s n)

/-- The first-class finite-cycle contextual relation inherits the additive barrier. -/
theorem no_global_orients_ctx_additive
    {k : Nat} {Sys : KCycleSystem k} (M : KCycleSchema.AdditiveMeasure Sys.toKCycleSchema) :
    ¬ GlobalOrientsCtx Sys M.eval (· < ·) := by
  intro h
  exact
    (OperatorKO7.MutualDuplicationKNodeAbstract.CyclicDupSystem.no_global_orients_ctx_additive_via_cycleFlow
      Sys.toKNodeWitness M)
      (by
        intro a b hstep
        exact h hstep)

/-- The cycle-flow affine witness at node `i` used by the first-class finite-cycle
contextual affine barrier. -/
abbrev KCycleAffineAt {k : Nat} {Sys : KCycleSystem k}
    (i : Fin (k + 1)) (M : KCycleSchema.AffineMeasure Sys.toKCycleSchema) :=
  OperatorKO7.MutualDuplicationCycleFlow.AffineOps.toDupMeasure
    (OperatorKO7.MutualDuplicationKNodeAbstract.CyclicDupSchema.AffineMeasure.toNodeMeasure
      M i)
    (k + 1) (Nat.succ_pos _)

abbrev KCycleAffineAtZero {k : Nat} {Sys : KCycleSystem k}
    (M : KCycleSchema.AffineMeasure Sys.toKCycleSchema) :=
  KCycleAffineAt (0 : Fin (k + 1)) M

/-- The first-class finite-cycle contextual relation inherits the affine barrier at any fixed
cycle index whose derived one-cycle schema has the usual unbounded pump. -/
theorem no_global_orients_ctx_affine_of_unbounded_at
    {k : Nat} {Sys : KCycleSystem k} (M : KCycleSchema.AffineMeasure Sys.toKCycleSchema)
    (i : Fin (k + 1))
    (hunbounded : StepDuplicatingSchema.HasUnboundedRange (KCycleAffineAt i M)) :
    ¬ GlobalOrientsCtx Sys M.eval (· < ·) := by
  intro h
  have hcomp :
      ∀ (b s n : Sys.T),
        M.eval (KCycleSchema.cycleTarget Sys.toKCycleSchema i b s n) <
          M.eval (KCycleSchema.cycleSource Sys.toKCycleSchema i b s n) := by
    intro b s n
    have horient : DependencyPairsFragment.GlobalOrients (StepCtx Sys) M.eval (· < ·) := by
      intro a b hstep
      exact h hstep
    exact
      DependencyPairsFragment.transGen_drop
        (R := StepCtx Sys) (m := M.eval) horient
        (cycle_realized_via_kNode Sys i b s n)
  exact
    KCycleSchema.no_affine_orients_cycle_of_unbounded
      (S := Sys.toKCycleSchema) M i hunbounded hcomp

/-- Compatibility wrapper for the node-`0` affine contextual barrier. -/
theorem no_global_orients_ctx_affine_of_unbounded
    {k : Nat} {Sys : KCycleSystem k} (M : KCycleSchema.AffineMeasure Sys.toKCycleSchema)
    (hunbounded : StepDuplicatingSchema.HasUnboundedRange (KCycleAffineAtZero M)) :
    ¬ GlobalOrientsCtx Sys M.eval (· < ·) := by
  exact no_global_orients_ctx_affine_of_unbounded_at M (0 : Fin (k + 1)) hunbounded

end KCycleSystem

end OperatorKO7.MutualDuplicationFiniteSchema

namespace OperatorKO7.MutualDuplicationSchema.Schema

/-- The first-class two-rule mutual schema as a first-class finite-cycle schema of length `2`. -/
def toKCycleSchema_two (S : OperatorKO7.MutualDuplicationSchema.Schema) :
    OperatorKO7.MutualDuplicationFiniteSchema.KCycleSchema 1 where
  T := S.T
  base := S.base
  succ := S.succ
  wrap := S.wrap
  recur := fun i =>
    match i.1 with
    | 0 => S.recurA
    | _ => S.recurB

@[simp] theorem cycleSource_two_eq
    (S : OperatorKO7.MutualDuplicationSchema.Schema) (b s n : S.T) :
    OperatorKO7.MutualDuplicationFiniteSchema.KCycleSchema.cycleSource (toKCycleSchema_two S) 0 b s n =
      S.recurA b s (S.succ (S.succ n)) := by
  simp [OperatorKO7.MutualDuplicationFiniteSchema.KCycleSchema.cycleSource,
    toKCycleSchema_two, OperatorKO7.MutualDuplicationKNode.CyclicDupSchema.cycleSucc,
    OperatorKO7.MutualDuplicationKNode.CyclicDupSchema.succIter]

@[simp] theorem cycleTarget_two_eq
    (S : OperatorKO7.MutualDuplicationSchema.Schema) (b s n : S.T) :
    OperatorKO7.MutualDuplicationFiniteSchema.KCycleSchema.cycleTarget (toKCycleSchema_two S) 0 b s n =
      S.wrap s (S.wrap s (S.recurA b s n)) := by
  simp [OperatorKO7.MutualDuplicationFiniteSchema.KCycleSchema.cycleTarget,
    toKCycleSchema_two, OperatorKO7.MutualDuplicationKNode.CyclicDupSchema.cycleWrap,
    OperatorKO7.MutualDuplicationKNode.CyclicDupSchema.wrapNest]

@[simp] theorem cycleSource_two_eq_schema
    (S : OperatorKO7.MutualDuplicationSchema.Schema) (b s n : S.T) :
    OperatorKO7.MutualDuplicationFiniteSchema.KCycleSchema.cycleSource (toKCycleSchema_two S) 0 b s n =
      OperatorKO7.MutualDuplicationSchema.Schema.cycleSource S b s n := by
  rw [OperatorKO7.MutualDuplicationSchema.Schema.cycleSource]
  exact cycleSource_two_eq S b s n

@[simp] theorem cycleTarget_two_eq_schema
    (S : OperatorKO7.MutualDuplicationSchema.Schema) (b s n : S.T) :
    OperatorKO7.MutualDuplicationFiniteSchema.KCycleSchema.cycleTarget (toKCycleSchema_two S) 0 b s n =
      OperatorKO7.MutualDuplicationSchema.Schema.cycleTarget S b s n := by
  rw [OperatorKO7.MutualDuplicationSchema.Schema.cycleTarget]
  exact cycleTarget_two_eq S b s n

end OperatorKO7.MutualDuplicationSchema.Schema

namespace OperatorKO7.MutualDuplicationSchema.System

/-- The first-class two-rule mutual system as a first-class finite-cycle system of length `2`. -/
def toKCycleSystem_two (Sys : OperatorKO7.MutualDuplicationSchema.System) :
    OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem 1 where
  T := Sys.T
  base := Sys.base
  succ := Sys.succ
  wrap := Sys.wrap
  recur := fun i =>
    match i.1 with
    | 0 => Sys.recurA
    | _ => Sys.recurB
  Step := Sys.Step
  step_succ := by
    intro i b s n
    fin_cases i
    · simpa using Sys.stepA_succ b s n
    · simpa [OperatorKO7.MutualDuplicationKNode.CyclicDupSchema.advance] using Sys.stepB_succ b s n

end OperatorKO7.MutualDuplicationSchema.System

namespace OperatorKO7.MutualDuplicationSchema.System

/-- The two-rule first-class finite-cycle bridge realizes the same canonical cycle path as the
theorem-native mutual schema. -/
theorem cycle_realized_via_finiteSchema
    (Sys : OperatorKO7.MutualDuplicationSchema.System) (b s n : Sys.T) :
    Relation.TransGen
      (OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.StepCtx (toKCycleSystem_two Sys))
      (OperatorKO7.MutualDuplicationSchema.Schema.cycleSource Sys.toSchema b s n)
      (OperatorKO7.MutualDuplicationSchema.Schema.cycleTarget Sys.toSchema b s n) := by
  simpa using
    (OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.cycle_realized_via_kNode
      (toKCycleSystem_two Sys) (0 : Fin 2) b s n)

end OperatorKO7.MutualDuplicationSchema.System

namespace OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem

/-- The concrete first-class two-rule finite-cycle witness system. -/
abbrev twoRuleWitnessSystem : KCycleSystem 1 :=
  OperatorKO7.MutualDuplicationSchema.System.toKCycleSystem_two
    OperatorKO7.MutualDuplicationCase.mutualWitnessSystem

/-- The concrete first-class two-rule finite-cycle path is realized. -/
theorem two_rule_nonvacuous (b s n : OperatorKO7.MutualDuplicationCase.AltTerm) :
    Relation.TransGen (StepCtx twoRuleWitnessSystem)
      (KCycleSchema.cycleSource twoRuleWitnessSystem.toKCycleSchema 0 b s n)
      (KCycleSchema.cycleTarget twoRuleWitnessSystem.toKCycleSchema 0 b s n) := by
  simpa using cycle_realized_via_kNode twoRuleWitnessSystem (0 : Fin 2) b s n

namespace ThreeRuleWitness

inductive Term : Type
| base : Term
| succ : Term → Term
| wrap : Term → Term → Term
| recur0 : Term → Term → Term → Term
| recur1 : Term → Term → Term → Term
| recur2 : Term → Term → Term → Term
deriving DecidableEq, Repr

open Term

inductive Step : Term → Term → Prop
| R0_succ : ∀ b s n, Step (recur0 b s (succ n)) (wrap s (recur1 b s n))
| R1_succ : ∀ b s n, Step (recur1 b s (succ n)) (wrap s (recur2 b s n))
| R2_succ : ∀ b s n, Step (recur2 b s (succ n)) (wrap s (recur0 b s n))

end ThreeRuleWitness

/-- A concrete first-class three-rule finite-cycle witness system. -/
def threeRuleWitnessSystem : KCycleSystem 2 where
  T := ThreeRuleWitness.Term
  base := ThreeRuleWitness.Term.base
  succ := ThreeRuleWitness.Term.succ
  wrap := ThreeRuleWitness.Term.wrap
  recur := fun i =>
    match i.1 with
    | 0 => ThreeRuleWitness.Term.recur0
    | 1 => ThreeRuleWitness.Term.recur1
    | _ => ThreeRuleWitness.Term.recur2
  Step := ThreeRuleWitness.Step
  step_succ := by
    intro i b s n
    fin_cases i
    · exact ThreeRuleWitness.Step.R0_succ b s n
    · exact ThreeRuleWitness.Step.R1_succ b s n
    · exact ThreeRuleWitness.Step.R2_succ b s n

/-- The concrete first-class three-rule finite-cycle path is realized. -/
theorem three_rule_nonvacuous (b s n : ThreeRuleWitness.Term) :
    Relation.TransGen (StepCtx threeRuleWitnessSystem)
      (KCycleSchema.cycleSource threeRuleWitnessSystem.toKCycleSchema 0 b s n)
      (KCycleSchema.cycleTarget threeRuleWitnessSystem.toKCycleSchema 0 b s n) := by
  simpa using cycle_realized_via_kNode threeRuleWitnessSystem (0 : Fin 3) b s n

end OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem
