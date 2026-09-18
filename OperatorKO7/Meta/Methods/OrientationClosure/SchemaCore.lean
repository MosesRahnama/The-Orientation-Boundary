import OperatorKO7.Meta.StepDuplicatingSchema
import Mathlib.Tactic

/-!
# Orientation Boundary free schema

A free first-order carrier for the two recursor rules used by the Orientation
Boundary. The definitions in this file contain no concrete KO7 term or step.
-/

set_option autoImplicit false

namespace OperatorKO7.Methods.OrientationClosure.SchemaCore

universe u v w

variable {ν : Type u} {μ : Type v} {κ : Type w}

/-- Free first-order terms for the recursor schema. -/
inductive FreeTerm (ν : Type u) where
  | var (x : ν)
  | zero
  | succ (t : FreeTerm ν)
  | wrap (s t : FreeTerm ν)
  | recur (b s n : FreeTerm ν)
  deriving Repr

namespace FreeTerm

/-- Capture-free first-order substitution. -/
def subst (σ : ν → FreeTerm μ) : FreeTerm ν → FreeTerm μ
  | .var x => σ x
  | .zero => .zero
  | .succ t => .succ (subst σ t)
  | .wrap s t => .wrap (subst σ s) (subst σ t)
  | .recur b s n => .recur (subst σ b) (subst σ s) (subst σ n)

@[simp] theorem subst_var (σ : ν → FreeTerm μ) (x : ν) :
    subst σ (.var x) = σ x := rfl

@[simp] theorem subst_zero (σ : ν → FreeTerm μ) :
    subst σ (.zero : FreeTerm ν) = .zero := rfl

@[simp] theorem subst_succ (σ : ν → FreeTerm μ) (t : FreeTerm ν) :
    subst σ (.succ t) = .succ (subst σ t) := rfl

@[simp] theorem subst_wrap (σ : ν → FreeTerm μ) (s t : FreeTerm ν) :
    subst σ (.wrap s t) = .wrap (subst σ s) (subst σ t) := rfl

@[simp] theorem subst_recur (σ : ν → FreeTerm μ) (b s n : FreeTerm ν) :
    subst σ (.recur b s n) = .recur (subst σ b) (subst σ s) (subst σ n) := rfl

/-- Identity substitution. -/
theorem subst_id (t : FreeTerm ν) : subst FreeTerm.var t = t := by
  induction t <;> simp_all

/-- Composition of substitutions. -/
theorem subst_comp (t : FreeTerm ν) (σ : ν → FreeTerm μ) (τ : μ → FreeTerm κ) :
    subst τ (subst σ t) = subst (fun x => subst τ (σ x)) t := by
  induction t <;> simp_all

end FreeTerm

/-- One-hole constructor contexts. -/
inductive FreeContext (ν : Type u) where
  | hole
  | succ (C : FreeContext ν)
  | wrapLeft (C : FreeContext ν) (t : FreeTerm ν)
  | wrapRight (s : FreeTerm ν) (C : FreeContext ν)
  | recurBase (C : FreeContext ν) (s n : FreeTerm ν)
  | recurStep (b : FreeTerm ν) (C : FreeContext ν) (n : FreeTerm ν)
  | recurCounter (b s : FreeTerm ν) (C : FreeContext ν)
  deriving Repr

namespace FreeContext

/-- Insert a term into a one-hole context. -/
def plug : FreeContext ν → FreeTerm ν → FreeTerm ν
  | .hole, t => t
  | .succ C, t => .succ (plug C t)
  | .wrapLeft C r, t => .wrap (plug C t) r
  | .wrapRight l C, t => .wrap l (plug C t)
  | .recurBase C s n, t => .recur (plug C t) s n
  | .recurStep b C n, t => .recur b (plug C t) n
  | .recurCounter b s C, t => .recur b s (plug C t)

/-- Substitute the fixed terms stored in a context. -/
def subst (σ : ν → FreeTerm μ) : FreeContext ν → FreeContext μ
  | .hole => .hole
  | .succ C => .succ (subst σ C)
  | .wrapLeft C r => .wrapLeft (subst σ C) (FreeTerm.subst σ r)
  | .wrapRight l C => .wrapRight (FreeTerm.subst σ l) (subst σ C)
  | .recurBase C s n =>
      .recurBase (subst σ C) (FreeTerm.subst σ s) (FreeTerm.subst σ n)
  | .recurStep b C n =>
      .recurStep (FreeTerm.subst σ b) (subst σ C) (FreeTerm.subst σ n)
  | .recurCounter b s C =>
      .recurCounter (FreeTerm.subst σ b) (FreeTerm.subst σ s) (subst σ C)

/-- Context composition. -/
def comp : FreeContext ν → FreeContext ν → FreeContext ν
  | .hole, D => D
  | .succ C, D => .succ (comp C D)
  | .wrapLeft C r, D => .wrapLeft (comp C D) r
  | .wrapRight l C, D => .wrapRight l (comp C D)
  | .recurBase C s n, D => .recurBase (comp C D) s n
  | .recurStep b C n, D => .recurStep b (comp C D) n
  | .recurCounter b s C, D => .recurCounter b s (comp C D)

@[simp] theorem plug_hole (t : FreeTerm ν) : plug .hole t = t := rfl

/-- Plugging after context composition equals nested plugging. -/
theorem plug_comp (C D : FreeContext ν) (t : FreeTerm ν) :
    plug (comp C D) t = plug C (plug D t) := by
  induction C <;> simp [comp, plug, *]

/-- Substitution commutes with plugging. -/
theorem subst_plug (C : FreeContext ν) (t : FreeTerm ν) (σ : ν → FreeTerm μ) :
    FreeTerm.subst σ (plug C t) = plug (subst σ C) (FreeTerm.subst σ t) := by
  induction C <;> simp [plug, subst, *]

end FreeContext

/-- The two root rules of the free recursor. -/
inductive RootStep : FreeTerm ν → FreeTerm ν → Prop where
  | recurZero (b s : FreeTerm ν) :
      RootStep (.recur b s .zero) b
  | recurSucc (b s n : FreeTerm ν) :
      RootStep (.recur b s (.succ n)) (.wrap s (.recur b s n))

namespace RootStep

/-- Root rewriting is stable under first-order substitution. -/
theorem subst {t u : FreeTerm ν} (h : RootStep t u) (σ : ν → FreeTerm μ) :
    RootStep (FreeTerm.subst σ t) (FreeTerm.subst σ u) := by
  cases h with
  | recurZero b s => exact .recurZero _ _
  | recurSucc b s n => exact .recurSucc _ _ _

end RootStep

/-- Constructor-context closure of the root relation. -/
inductive ContextStep : FreeTerm ν → FreeTerm ν → Prop where
  | lift (C : FreeContext ν) {t u : FreeTerm ν} (h : RootStep t u) :
      ContextStep (C.plug t) (C.plug u)

/-- Every root step is a contextual step. -/
theorem rootStep_contextStep {t u : FreeTerm ν} (h : RootStep t u) : ContextStep t u := by
  simpa using ContextStep.lift (.hole : FreeContext ν) h

/-- Contextual rewriting is stable under an outer constructor context. -/
theorem ContextStep.outer {t u : FreeTerm ν} (h : ContextStep t u) (D : FreeContext ν) :
    ContextStep (D.plug t) (D.plug u) := by
  cases h with
  | lift C hroot =>
      simpa [FreeContext.plug_comp] using ContextStep.lift (FreeContext.comp D C) hroot

/-- Contextual rewriting is stable under first-order substitution. -/
theorem ContextStep.subst {t u : FreeTerm ν} (h : ContextStep t u)
    (σ : ν → FreeTerm μ) :
    ContextStep (FreeTerm.subst σ t) (FreeTerm.subst σ u) := by
  cases h with
  | lift C hroot =>
      rw [FreeContext.subst_plug, FreeContext.subst_plug]
      exact ContextStep.lift (FreeContext.subst σ C) (hroot.subst σ)

/-- The free term carrier as the abstract step-duplicating constructor schema. -/
def freeSchema (ν : Type) : OperatorKO7.StepDuplicating.StepDuplicatingSchema where
  T := FreeTerm ν
  base := .zero
  succ := .succ
  wrap := .wrap
  recur := .recur

/-- The free root relation as a step-duplicating system. -/
def freeRootSystem (ν : Type) :
    OperatorKO7.StepDuplicating.StepDuplicatingSchema.StepDuplicatingSystem where
  toStepDuplicatingSchema := freeSchema ν
  Step := RootStep
  dup_step := RootStep.recurSucc

/-- The duplicating schema rule is literally the second free root rule. -/
theorem freeRootSystem_dup (ν : Type) (b s n : FreeTerm ν) :
    (freeRootSystem ν).Step
      ((freeRootSystem ν).recur b s ((freeRootSystem ν).succ n))
      ((freeRootSystem ν).wrap s ((freeRootSystem ν).recur b s n)) := by
  exact RootStep.recurSucc b s n

end OperatorKO7.Methods.OrientationClosure.SchemaCore
