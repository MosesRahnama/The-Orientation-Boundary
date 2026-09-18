import OperatorKO7.Meta.Methods.OrientationClosure.CellClassification
import OperatorKO7.Meta.Methods.OrientationClosure.InterpretationLaws
import OperatorKO7.Meta.Methods.OrientationClosure.TransportLaws

/-!
# Context-lift consumption theorem

The negative direction uses only the identity context: any measure orienting the
constructor-context closure orients every root instance. The positive direction
reuses the interpretation laws that push a strict root comparison through every
constructor context. Two controls mark the premises: an interpretation with a
minimum wrapper orients both root rules and fails on the context closure, and a
zero-step simulation of a loop does not transfer termination.
-/

set_option autoImplicit false

namespace OperatorKO7.Methods.OrientationClosure.ContextLiftMetatheorem

open OperatorKO7.Methods.OrientationClosure.SchemaCore
open OperatorKO7.Methods.OrientationClosure.CellClassification
open OperatorKO7.Methods.OrientationClosure.InterpretationLaws

universe u v

/-- Orientation of the free contextual relation. -/
def OrientsFreeContext {ν : Type u} {α : Type v}
    (M : FreeTerm ν → α) (lt : α → α → Prop) : Prop :=
  ∀ {a b : FreeTerm ν}, ContextStep a b → lt (M b) (M a)

/-- Every contextual orienter restricts to a root orienter. -/
theorem free_context_orientation_implies_root
    {ν : Type u} {α : Type v} {M : FreeTerm ν → α} {lt : α → α → Prop}
    (h : OrientsFreeContext M lt) :
    ∀ {a b : FreeTerm ν}, RootStep a b → lt (M b) (M a) := by
  intro a b hab
  exact h (rootStep_contextStep hab)

/-- The P3.2 barrier cell survives constructor-context closure on the free
schema. -/
theorem barrier_cell_excludes_context_orientation
    (M : FreeTerm Empty → Nat) (b n : FreeTerm Empty)
    (hw : WrapUnboundedAt (S := freeSchema Empty) M b n)
    (hg : GainBoundedAt (S := freeSchema Empty) M b n) :
    ¬ OrientsFreeContext M (· < ·) := by
  intro hctx
  apply barrier_cell_excludes_orientation (S := freeSchema Empty) M b n hw hg
  intro s
  exact free_context_orientation_implies_root hctx (RootStep.recurSucc b s n)

/-- Strict context laws turn root orientation into contextual decrease, for any
relation on any carrier. -/
theorem interpretation_context_consumption
    {α : Type v} (I : Interpretation α) (lt : α → α → Prop)
    (laws : StrictContextLaws I lt)
    (roots : RootRuleOrients I lt)
    {ν : Type u} (ρ : ν → α) :
    OrientsFreeContext (I.eval ρ) lt := by
  intro a b h
  exact eval_contextStep_decreases roots laws ρ h

/-- A well-founded relation, strict context laws and root orientation certify
termination of the reverse free contextual relation. -/
theorem interpretation_context_reverse_wellFounded
    {α : Type v} (I : Interpretation α) (lt : α → α → Prop)
    (laws : StrictContextLaws I lt)
    (roots : RootRuleOrients I lt)
    (hwf : WellFounded lt)
    {ν : Type u} (ρ : ν → α) :
    WellFounded (fun y x : FreeTerm ν => ContextStep x y) :=
  contextStep_reverse_wellFounded roots laws hwf ρ

/-! ## Controls -/

/-- C10 interpretation: the wrapper takes the minimum of its two arguments, and the
recursor adds its base and counter values. -/
def minWrapInterpretation : Interpretation Nat where
  zero := 0
  succ := fun x => x + 1
  wrap := fun x y => min x y
  recur := fun b _ n => b + n + 1

/-- The minimum-wrapper interpretation orients both free root rules. -/
theorem minWrapInterpretation_rootRuleOrients :
    RootRuleOrients minWrapInterpretation (· < ·) where
  recurZero := by
    intro b s
    show b < b + 0 + 1
    omega
  recurSucc := by
    intro b s n
    show min s (b + n + 1) < b + (n + 1) + 1
    have hmin : min s (b + n + 1) ≤ b + n + 1 := min_le_right _ _
    omega

/-- The minimum-wrapper interpretation fails on one contextual step: inside the left
wrapper argument, the smaller right argument hides the root decrease. -/
theorem minWrapInterpretation_not_context_orienter :
    ¬ OrientsFreeContext (minWrapInterpretation.eval (Empty.elim : Empty → Nat)) (· < ·) := by
  intro h
  have hlt := h (ContextStep.lift
    (FreeContext.wrapLeft FreeContext.hole (FreeTerm.zero : FreeTerm Empty))
    (RootStep.recurSucc (FreeTerm.zero : FreeTerm Empty) FreeTerm.zero FreeTerm.zero))
  simp [FreeContext.plug, minWrapInterpretation, Interpretation.eval] at hlt

/-- The P3.4 controls: C10 separates root orientation from contextual orientation when
strict context laws fail, and C19 shows that a zero-step simulation does not transfer
termination. -/
theorem context_lift_controls :
    RootRuleOrients minWrapInterpretation (· < ·) ∧
      ¬ OrientsFreeContext (minWrapInterpretation.eval (Empty.elim : Empty → Nat)) (· < ·) ∧
      (Nonempty (TransportLaws.ReflexiveSimulation Unit Unit
          TransportLaws.LoopSource TransportLaws.EmptyTarget) ∧
        WellFounded (fun y x : Unit => TransportLaws.EmptyTarget x y) ∧
        ¬ WellFounded (fun y x : Unit => TransportLaws.LoopSource x y)) :=
  ⟨minWrapInterpretation_rootRuleOrients, minWrapInterpretation_not_context_orienter,
    TransportLaws.reflexiveSimulation_does_not_transfer_termination⟩

end OperatorKO7.Methods.OrientationClosure.ContextLiftMetatheorem
