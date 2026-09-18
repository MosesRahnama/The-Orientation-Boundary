import OperatorKO7.Meta.Methods.OrientationClosure.InterpretationLaws
import OperatorKO7.Meta.Methods.OrientationClosure.PolynomialRegion

/-!
# Contextual termination by the coupled polynomial region

The positive side of the Orientation Boundary is not merely a root-rule
calculation.  Every parameter pair alpha >= 1, beta >= 2 gives a natural-valued
interpretation that is strictly monotone in every constructor argument and
orients both recursor rules.  The generic interpretation theorem therefore
proves strong normalization of the full one-hole contextual closure of the free
schema, with no concrete KO7 term or rule in the statement.
-/

set_option autoImplicit false

namespace OperatorKO7.Methods.OrientationClosure.FreePolynomialTermination

open OperatorKO7.Methods.OrientationClosure.SchemaCore
open OperatorKO7.Methods.OrientationClosure.InterpretationLaws
open OperatorKO7.Methods.OrientationClosure.PolynomialRegion

universe u

/-- Coupled polynomial interpretation on the independent free syntax. -/
def coupledInterpretation (α β : Nat) : Interpretation Nat where
  zero := 0
  succ := successorEval
  wrap := wrapperEval
  recur := recursorEval α β

/-- The entire parameter region orients both root rules. -/
theorem coupled_rootRuleOrients
    {α β : Nat} (hα : 1 ≤ α) (hβ : 2 ≤ β) :
    RootRuleOrients (coupledInterpretation α β) (fun x y : Nat => x < y) where
  recurZero := by
    intro b s
    exact orientsZero_of_region hα hβ b s
  recurSucc := by
    intro b s n
    exact orientsSuccessor_of_region hα hβ b s n

/-- Successor is strictly monotone. -/
theorem successor_strict {x y : Nat} (h : x < y) :
    successorEval x < successorEval y := by
  simp [successorEval]
  omega

/-- Wrapper is strictly monotone in the retained payload argument. -/
theorem wrapper_strict_left_general {x y z : Nat} (h : x < y) :
    wrapperEval x z < wrapperEval y z := by
  simp [wrapperEval]
  omega

/-- Wrapper is strictly monotone in its recursive-result argument. -/
theorem wrapper_strict_right_general {x y z : Nat} (h : x < y) :
    wrapperEval z x < wrapperEval z y := by
  simp [wrapperEval]
  omega

/-- The recursor is strictly monotone in the base argument throughout the
parameter region. -/
theorem recursor_strict_base_general
    (α β s n : Nat) {x y : Nat} (h : x < y) :
    recursorEval α β x s n < recursorEval α β y s n := by
  have hinner : α * s + x + β < α * s + y + β := by omega
  exact Nat.mul_lt_mul_of_pos_left hinner (by omega)

/-- A positive step coefficient makes the recursor strictly monotone in its
step/payload argument. -/
theorem recursor_strict_step_general
    {α : Nat} (hα : 1 ≤ α) (β b n : Nat) {x y : Nat} (h : x < y) :
    recursorEval α β b x n < recursorEval α β b y n := by
  have hscaled : α * x < α * y :=
    Nat.mul_lt_mul_of_pos_left h (by omega)
  have hinner : α * x + b + β < α * y + b + β := by omega
  exact Nat.mul_lt_mul_of_pos_left hinner (by omega)

/-- Positive recursor bias makes the recursor strictly monotone in the counter
argument. -/
theorem recursor_strict_counter_general
    {β : Nat} (hβ : 1 ≤ β) (α b s : Nat) {x y : Nat} (h : x < y) :
    recursorEval α β b s x < recursorEval α β b s y := by
  have hfactor : 0 < α * s + b + β := by omega
  have hsucc : x + 1 < y + 1 := by omega
  exact Nat.mul_lt_mul_of_pos_right hsucc hfactor

/-- Strict monotonicity in every free-constructor argument. -/
theorem coupled_strictContextLaws
    {α β : Nat} (hα : 1 ≤ α) (hβ : 2 ≤ β) :
    StrictContextLaws (coupledInterpretation α β) (fun x y : Nat => x < y) where
  succ := by
    intro x y h
    exact successor_strict h
  wrapLeft := by
    intro x y z h
    exact wrapper_strict_left_general h
  wrapRight := by
    intro z x y h
    exact wrapper_strict_right_general h
  recurBase := by
    intro x y s n h
    exact recursor_strict_base_general α β s n h
  recurStep := by
    intro b x y n h
    exact recursor_strict_step_general hα β b n h
  recurCounter := by
    intro b s x y h
    exact recursor_strict_counter_general (by omega) α b s h

/-- Every contextual step strictly decreases the coupled polynomial value under
any valuation. -/
theorem coupled_contextStep_decreases
    {ν : Type u} {α β : Nat} (hα : 1 ≤ α) (hβ : 2 ≤ β)
    (ρ : ν → Nat) {t u : FreeTerm ν} (h : ContextStep t u) :
    (coupledInterpretation α β).eval ρ u <
      (coupledInterpretation α β).eval ρ t :=
  eval_contextStep_decreases
    (coupled_rootRuleOrients hα hβ)
    (coupled_strictContextLaws hα hβ) ρ h

/-- Main positive theorem: every interpretation in the exact parameter region
proves strong normalization of the full contextual free recursor relation. -/
theorem free_contextStep_reverse_wellFounded
    (ν : Type u) {α β : Nat} (hα : 1 ≤ α) (hβ : 2 ≤ β) :
    WellFounded (fun u t : FreeTerm ν => ContextStep t u) := by
  exact contextStep_reverse_wellFounded
    (coupled_rootRuleOrients hα hβ)
    (coupled_strictContextLaws hα hβ)
    Nat.lt_wfRel.wf
    (fun _ : ν => 0)

/-- The paper's alpha=1, beta=2 witness is a concrete contextual termination
certificate, not only a root orientation. -/
theorem main_free_contextual_termination (ν : Type u) :
    WellFounded (fun u t : FreeTerm ν => ContextStep t u) :=
  free_contextStep_reverse_wellFounded ν (α := 1) (β := 2) (by decide) (by decide)

/-- Root rewriting is also well founded as a subrelation of the contextual
closure. -/
theorem main_free_root_termination (ν : Type u) :
    WellFounded (fun u t : FreeTerm ν => RootStep t u) := by
  apply Subrelation.wf
    (r := fun u t : FreeTerm ν => ContextStep t u)
  · intro u t h
    exact ContextStep.lift .hole h
  · exact main_free_contextual_termination ν

end OperatorKO7.Methods.OrientationClosure.FreePolynomialTermination
