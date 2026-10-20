import OperatorKO7.Meta.Methods.OrientationClosure.SchemaCore
import Mathlib.Tactic

/-!
# Interpretation laws for the free recursor

Generic evaluation, substitution, context monotonicity, and well-foundedness
transfer for the free Orientation Boundary syntax.
-/

set_option autoImplicit false

namespace OperatorKO7.Methods.OrientationClosure.InterpretationLaws

open OperatorKO7.Methods.OrientationClosure.SchemaCore

universe u v w

variable {α : Type w}

/-- Interpretation of the four constructors in an arbitrary carrier. -/
structure Interpretation (α : Type v) where
  zero : α
  succ : α → α
  wrap : α → α → α
  recur : α → α → α → α

namespace Interpretation

/-- Evaluate a free term under a variable valuation. -/
def eval {ν : Type u} (I : Interpretation α) (ρ : ν → α) : FreeTerm ν → α
  | .var x => ρ x
  | .zero => I.zero
  | .succ t => I.succ (eval I ρ t)
  | .wrap s t => I.wrap (eval I ρ s) (eval I ρ t)
  | .recur b s n => I.recur (eval I ρ b) (eval I ρ s) (eval I ρ n)

@[simp] theorem eval_var {ν : Type u} (I : Interpretation α) (ρ : ν → α) (x : ν) :
    eval I ρ (.var x) = ρ x := rfl

@[simp] theorem eval_zero {ν : Type u} (I : Interpretation α) (ρ : ν → α) :
    eval I ρ (.zero : FreeTerm ν) = I.zero := rfl

@[simp] theorem eval_succ {ν : Type u} (I : Interpretation α) (ρ : ν → α) (t : FreeTerm ν) :
    eval I ρ (.succ t) = I.succ (eval I ρ t) := rfl

@[simp] theorem eval_wrap {ν : Type u} (I : Interpretation α) (ρ : ν → α)
    (s t : FreeTerm ν) :
    eval I ρ (.wrap s t) = I.wrap (eval I ρ s) (eval I ρ t) := rfl

@[simp] theorem eval_recur {ν : Type u} (I : Interpretation α) (ρ : ν → α)
    (b s n : FreeTerm ν) :
    eval I ρ (.recur b s n) = I.recur (eval I ρ b) (eval I ρ s) (eval I ρ n) := rfl

/-- Evaluation commutes with first-order substitution. -/
theorem eval_subst {ν : Type u} {μ : Type v} {α : Type w}
    (I : Interpretation α) (ρ : μ → α) (σ : ν → FreeTerm μ) (t : FreeTerm ν) :
    eval I ρ (FreeTerm.subst σ t) =
      eval I (fun x => eval I ρ (σ x)) t := by
  induction t <;> simp [FreeTerm.subst, eval, *]

end Interpretation

/-- Strict monotonicity in every constructor argument. -/
structure StrictContextLaws {α : Type v} (I : Interpretation α)
    (lt : α → α → Prop) : Prop where
  succ : ∀ {x y}, lt x y → lt (I.succ x) (I.succ y)
  wrapLeft : ∀ {x y} z, lt x y → lt (I.wrap x z) (I.wrap y z)
  wrapRight : ∀ z {x y}, lt x y → lt (I.wrap z x) (I.wrap z y)
  recurBase : ∀ {x y} s n, lt x y → lt (I.recur x s n) (I.recur y s n)
  recurStep : ∀ b {x y} n, lt x y → lt (I.recur b x n) (I.recur b y n)
  recurCounter : ∀ b s {x y}, lt x y → lt (I.recur b s x) (I.recur b s y)

/-- Weak monotonicity in every constructor argument. -/
structure WeakContextLaws {α : Type v} (I : Interpretation α)
    (le : α → α → Prop) : Prop where
  succ : ∀ {x y}, le x y → le (I.succ x) (I.succ y)
  wrapLeft : ∀ {x y} z, le x y → le (I.wrap x z) (I.wrap y z)
  wrapRight : ∀ z {x y}, le x y → le (I.wrap z x) (I.wrap z y)
  recurBase : ∀ {x y} s n, le x y → le (I.recur x s n) (I.recur y s n)
  recurStep : ∀ b {x y} n, le x y → le (I.recur b x n) (I.recur b y n)
  recurCounter : ∀ b s {x y}, le x y → le (I.recur b s x) (I.recur b s y)

/-- Algebraic orientation of the two root rules. -/
structure RootRuleOrients {α : Type v} (I : Interpretation α)
    (lt : α → α → Prop) : Prop where
  recurZero : ∀ b s, lt b (I.recur b s I.zero)
  recurSucc : ∀ b s n,
    lt (I.wrap s (I.recur b s n)) (I.recur b s (I.succ n))

/-- The algebraic root conditions orient every interpreted root instance. -/
theorem eval_rootStep_decreases
    {ν : Type u} {α : Type v} {I : Interpretation α} {lt : α → α → Prop}
    (hroot : RootRuleOrients I lt) (ρ : ν → α)
    {t u : FreeTerm ν} (h : RootStep t u) :
    lt (I.eval ρ u) (I.eval ρ t) := by
  cases h with
  | recurZero _ _ =>
      simpa [Interpretation.eval] using hroot.recurZero _ _
  | recurSucc _ _ _ =>
      simpa [Interpretation.eval] using hroot.recurSucc _ _ _

/-- Strict constructor laws transport a strict comparison through any one-hole
context. -/
theorem eval_plug_strict
    {ν : Type u} {α : Type v} {I : Interpretation α} {lt : α → α → Prop}
    (hlaws : StrictContextLaws I lt) (ρ : ν → α)
    (C : FreeContext ν) {t u : FreeTerm ν}
    (h : lt (I.eval ρ u) (I.eval ρ t)) :
    lt (I.eval ρ (C.plug u)) (I.eval ρ (C.plug t)) := by
  induction C with
  | hole => simpa [FreeContext.plug] using h
  | succ C ih =>
      simpa [FreeContext.plug, Interpretation.eval] using hlaws.succ ih
  | wrapLeft C r ih =>
      simpa [FreeContext.plug, Interpretation.eval] using
        hlaws.wrapLeft (I.eval ρ r) ih
  | wrapRight l C ih =>
      simpa [FreeContext.plug, Interpretation.eval] using
        hlaws.wrapRight (I.eval ρ l) ih
  | recurBase C s n ih =>
      simpa [FreeContext.plug, Interpretation.eval] using
        hlaws.recurBase (I.eval ρ s) (I.eval ρ n) ih
  | recurStep b C n ih =>
      simpa [FreeContext.plug, Interpretation.eval] using
        hlaws.recurStep (I.eval ρ b) (I.eval ρ n) ih
  | recurCounter b s C ih =>
      simpa [FreeContext.plug, Interpretation.eval] using
        hlaws.recurCounter (I.eval ρ b) (I.eval ρ s) ih

/-- Root orientation plus strict constructor monotonicity orients the entire
constructor-context closure. -/
theorem eval_contextStep_decreases
    {ν : Type u} {α : Type v} {I : Interpretation α} {lt : α → α → Prop}
    (hroot : RootRuleOrients I lt) (hlaws : StrictContextLaws I lt)
    (ρ : ν → α) {t u : FreeTerm ν} (h : ContextStep t u) :
    lt (I.eval ρ u) (I.eval ρ t) := by
  cases h with
  | lift C hstep =>
      exact eval_plug_strict hlaws ρ C (eval_rootStep_decreases hroot ρ hstep)

/-- A well-founded target comparison and strict interpretation prove
well-foundedness of reverse contextual rewriting. -/
theorem contextStep_reverse_wellFounded
    {ν : Type u} {α : Type v} {I : Interpretation α} {lt : α → α → Prop}
    (hroot : RootRuleOrients I lt) (hlaws : StrictContextLaws I lt)
    (hlt : WellFounded lt) (ρ : ν → α) :
    WellFounded (fun u t : FreeTerm ν => ContextStep t u) := by
  apply Subrelation.wf
    (r := fun u t : FreeTerm ν => lt (I.eval ρ u) (I.eval ρ t))
  · intro u t h
    exact eval_contextStep_decreases hroot hlaws ρ h
  · exact InvImage.wf (f := I.eval ρ) hlt

/-- Uniform root orientation is stable under substitution because evaluation of
substituted terms is evaluation under the induced valuation. -/
theorem substituted_rootStep_decreases
    {ν : Type u} {μ : Type v} {α : Type w}
    {I : Interpretation α} {lt : α → α → Prop}
    (hroot : RootRuleOrients I lt) (ρ : μ → α)
    {t u : FreeTerm ν} (h : RootStep t u) (σ : ν → FreeTerm μ) :
    lt (I.eval ρ (FreeTerm.subst σ u)) (I.eval ρ (FreeTerm.subst σ t)) := by
  exact eval_rootStep_decreases hroot ρ (h.subst σ)

end OperatorKO7.Methods.OrientationClosure.InterpretationLaws
