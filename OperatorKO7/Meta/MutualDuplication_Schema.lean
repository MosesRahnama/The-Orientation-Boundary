import OperatorKO7.Meta.StepDuplicatingSchema
import OperatorKO7.Meta.MutualDuplication_CycleFlow

/-!
# First-Class Two-Rule Mutual Step-Duplicating Schema

This module packages the two-rule mutual-recursion shape directly.  The first-class
object is the mutual schema itself together with its canonical one-cycle data and the
minimal context closure that realizes that cycle.
-/

namespace OperatorKO7.MutualDuplicationSchema

open OperatorKO7.StepDuplicating

/-- First-class two-rule mutual step-duplicating schema. -/
structure Schema where
  T : Type
  base : T
  succ : T → T
  wrap : T → T → T
  recurA : T → T → T → T
  recurB : T → T → T → T

namespace Schema

/-- Forget the second recursor and expose the primary schema used by the abstract cycle layer. -/
def toPrimarySchema (S : Schema) : StepDuplicatingSchema where
  T := S.T
  base := S.base
  succ := S.succ
  wrap := S.wrap
  recur := S.recurA

/-- Source of the canonical one-cycle mutual composite. -/
def cycleSource (S : Schema) (b s n : S.T) : S.T :=
  S.recurA b s (S.succ (S.succ n))

/-- Midpoint of the canonical one-cycle mutual composite. -/
def cycleMid (S : Schema) (b s n : S.T) : S.T :=
  S.wrap s (S.recurB b s (S.succ n))

/-- Target of the canonical one-cycle mutual composite. -/
def cycleTarget (S : Schema) (b s n : S.T) : S.T :=
  S.wrap s (S.wrap s (S.recurA b s n))

/-- Reusable one-cycle data for the two-rule mutual schema. -/
structure CompositeCycleData (S : Schema) where
  source : S.T
  mid : S.T
  target : S.T

/-- The canonical one-cycle composite attached to the mutual schema. -/
def compositeCycleData (S : Schema) (b s n : S.T) : CompositeCycleData S where
  source := S.cycleSource b s n
  mid := S.cycleMid b s n
  target := S.cycleTarget b s n

@[simp] theorem cycleSource_eq_cycleFlow (S : Schema) (b s n : S.T) :
    OperatorKO7.MutualDuplicationCycleFlow.cycleSource (toPrimarySchema S) 2 b s n =
      cycleSource S b s n := by
  simp [OperatorKO7.MutualDuplicationCycleFlow.cycleSource,
    OperatorKO7.MutualDuplicationCycleFlow.succIterOn, cycleSource, toPrimarySchema]

@[simp] theorem cycleTarget_eq_cycleFlow (S : Schema) (b s n : S.T) :
    OperatorKO7.MutualDuplicationCycleFlow.cycleTarget (toPrimarySchema S) 2 b s n =
      cycleTarget S b s n := by
  simp [OperatorKO7.MutualDuplicationCycleFlow.cycleTarget,
    OperatorKO7.MutualDuplicationCycleFlow.wrapNest, cycleTarget, toPrimarySchema]

/-- Uniform additive measures on the mutual schema. -/
structure AdditiveMeasure (S : Schema) where
  eval : S.T → Nat
  w_base : Nat
  w_succ : Nat
  w_wrap : Nat
  w_recur : Nat
  eval_base : eval S.base = w_base
  eval_succ : ∀ t, eval (S.succ t) = w_succ + eval t
  eval_wrap : ∀ x y, eval (S.wrap x y) = w_wrap + eval x + eval y
  eval_recurA :
    ∀ b s n, eval (S.recurA b s n) = w_recur + eval b + eval s + eval n
  eval_recurB :
    ∀ b s n, eval (S.recurB b s n) = w_recur + eval b + eval s + eval n
  h_wrap_pos : 1 ≤ w_wrap

/-- Forget the second recursor and expose the additive measure used by the abstract cycle layer. -/
def AdditiveMeasure.toPrimaryMeasure {S : Schema} (M : AdditiveMeasure S) :
    StepDuplicatingSchema.AdditiveMeasure (toPrimarySchema S) where
  eval := M.eval
  w_base := M.w_base
  w_succ := M.w_succ
  w_wrap := M.w_wrap
  w_recur := M.w_recur
  eval_base := M.eval_base
  eval_succ := M.eval_succ
  eval_wrap := M.eval_wrap
  eval_recur := M.eval_recurA
  h_wrap_pos := M.h_wrap_pos

/-- The ordinary wrapper pump is available on the first-class mutual schema. -/
lemma eval_wrapIter_ge {S : Schema} (M : AdditiveMeasure S) (k : Nat) :
    M.eval (StepDuplicatingSchema.wrapIter (toPrimarySchema S) k) ≥ k := by
  simpa [AdditiveMeasure.toPrimaryMeasure] using
    (StepDuplicatingSchema.eval_wrapIter_ge
      (S := toPrimarySchema S) (M := M.toPrimaryMeasure) k)

/-- Uniform affine measures on the mutual schema. -/
structure AffineMeasure (S : Schema) where
  eval : S.T → Nat
  c_base : Nat
  succ_bias : Nat
  succ_scale : Nat
  wrap_const : Nat
  wrap_left : Nat
  wrap_right : Nat
  recur_const : Nat
  recur_base : Nat
  recur_step : Nat
  recur_counter : Nat
  eval_base : eval S.base = c_base
  eval_succ : ∀ t, eval (S.succ t) = succ_bias + succ_scale * eval t
  eval_wrap :
    ∀ x y, eval (S.wrap x y) = wrap_const + wrap_left * eval x + wrap_right * eval y
  eval_recurA :
    ∀ b s n,
      eval (S.recurA b s n) =
        recur_const + recur_base * eval b + recur_step * eval s + recur_counter * eval n
  eval_recurB :
    ∀ b s n,
      eval (S.recurB b s n) =
        recur_const + recur_base * eval b + recur_step * eval s + recur_counter * eval n
  h_wrap_left_pos : 1 ≤ wrap_left
  h_wrap_right_pos : 1 ≤ wrap_right

/-- Forget the second recursor and expose the affine measure used by the abstract cycle layer. -/
def AffineMeasure.toPrimaryMeasure {S : Schema} (M : AffineMeasure S) :
    StepDuplicatingSchema.AffineMeasure (toPrimarySchema S) where
  eval := M.eval
  c_base := M.c_base
  succ_bias := M.succ_bias
  succ_scale := M.succ_scale
  wrap_const := M.wrap_const
  wrap_left := M.wrap_left
  wrap_right := M.wrap_right
  recur_const := M.recur_const
  recur_base := M.recur_base
  recur_step := M.recur_step
  recur_counter := M.recur_counter
  eval_base := M.eval_base
  eval_succ := M.eval_succ
  eval_wrap := M.eval_wrap
  eval_recur := M.eval_recurA
  h_wrap_left_pos := M.h_wrap_left_pos
  h_wrap_right_pos := M.h_wrap_right_pos

/-- Derived two-step affine measure used by the composite-cycle barrier. -/
def AffineMeasure.toCompositeMeasure {S : Schema} (M : AffineMeasure S) :
    StepDuplicatingSchema.AffineMeasure
      (OperatorKO7.MutualDuplicationCycleFlow.toDupSchema (toPrimarySchema S) 2) :=
  OperatorKO7.MutualDuplicationCycleFlow.AffineOps.toDupMeasure
    M.toPrimaryMeasure 2 (by decide)

end Schema

/-- A two-rule mutual step-duplicating system. -/
structure System extends Schema where
  Step : T → T → Prop
  stepA_succ : ∀ b s n, Step (recurA b s (succ n)) (wrap s (recurB b s n))
  stepB_succ : ∀ b s n, Step (recurB b s (succ n)) (wrap s (recurA b s n))

namespace System

/-- Minimal context closure needed to realize the mutual one-cycle composite. -/
inductive StepCtx (Sys : System) : Sys.T → Sys.T → Prop
| root : ∀ {a b}, Sys.Step a b → StepCtx Sys a b
| wrap_right : ∀ s {a b}, StepCtx Sys a b → StepCtx Sys (Sys.wrap s a) (Sys.wrap s b)

/-- Orientation of the induced mutual context relation. -/
def GlobalOrientsCtx {α : Type} (Sys : System) (m : Sys.T → α)
    (lt : α → α → Prop) : Prop :=
  ∀ {a b : Sys.T}, StepCtx Sys a b → lt (m b) (m a)

/-- Reusable realization data for the canonical mutual one-cycle composite. -/
structure ContextRealization (Sys : System) where
  cycle : Schema.CompositeCycleData Sys.toSchema
  source_mid : StepCtx Sys cycle.source cycle.mid
  mid_target : StepCtx Sys cycle.mid cycle.target

theorem ContextRealization.path {Sys : System} (R : ContextRealization Sys) :
    Relation.TransGen (StepCtx Sys) R.cycle.source R.cycle.target := by
  exact Relation.TransGen.tail (Relation.TransGen.single R.source_mid) R.mid_target

/-- The canonical one-cycle realization is theorem-native on the mutual schema itself. -/
def cycleRealization (Sys : System) (b s n : Sys.T) : ContextRealization Sys where
  cycle := Schema.compositeCycleData Sys.toSchema b s n
  source_mid := StepCtx.root (Sys.stepA_succ b s (Sys.succ n))
  mid_target := StepCtx.wrap_right s (StepCtx.root (Sys.stepB_succ b s n))

theorem cyclePath (Sys : System) (b s n : Sys.T) :
    Relation.TransGen (StepCtx Sys)
      (Schema.cycleSource Sys.toSchema b s n)
      (Schema.cycleTarget Sys.toSchema b s n) := by
  simpa using (ContextRealization.path (R := cycleRealization Sys b s n))

/-- Extension seam into the abstract delayed-cycle layer at `copies = 2`. -/
def toCycleWitness (Sys : System) :
    OperatorKO7.MutualDuplicationCycleFlow.CycleWitness
      (Schema.toPrimarySchema Sys.toSchema) 2 where
  StepCtx := StepCtx Sys
  cycle_realized := by
    intro b s n
    simpa using cyclePath Sys b s n

end System

end OperatorKO7.MutualDuplicationSchema
