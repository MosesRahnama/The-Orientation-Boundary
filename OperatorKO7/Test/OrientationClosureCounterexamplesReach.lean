import OperatorKO7.Meta.Methods.OrientationClosure.PathOrderNativeSemantics

/-!
# Orientation closure comparator counterexamples

These fixtures record two defects in the provisional ORI-1 comparator layer.
They are regressions for the P5 repairs of generalized KBO and AC KBO.
-/

set_option autoImplicit false

namespace OperatorKO7.Test.OrientationClosureCounterexamples

open OperatorKO7.SymbolicComparatorBarrier
open OperatorKO7.Methods.PathOrderRows
open OperatorKO7.Methods.OrientationClosure.PathOrderNativeSemantics

/-- Lex-status KBO fixture used to expose the AC comparison self-loop. -/
def lexKBO : NativeKBOData :=
  { nativeKBOWithStatusWitness with status := fun _ => .lex }

/-- Left AC representative. -/
def leftTerm : STerm := .wrap (.succ .base) .base

/-- Right AC representative. -/
def rightTerm : STerm := .wrap .base (.succ .base)

/-- The provisional AC comparison is reflexive on `leftTerm`. -/
theorem acComparison_self_loop : NativeACKBOGt lexKBO leftTerm leftTerm := by
  refine ⟨leftTerm, rightTerm, Relation.EqvGen.refl _,
    Relation.EqvGen.rel _ _ (ACRearrange.commWrap _ _), ?_⟩
  apply NativeKBOGt.wrapLexLeft
  · rfl
  · intro v
    cases v <;> decide
  · rfl
  · apply NativeKBOGt.precedence
    · intro v
      cases v <;> decide
    · rfl
    · decide

/-- The provisional AC comparison therefore fails well-foundedness. -/
theorem acComparison_not_wellFounded :
    ¬ WellFounded (fun y x => NativeACKBOGt lexKBO x y) := by
  intro hwf
  exact (hwf.asymmetric leftTerm leftTerm acComparison_self_loop) acComparison_self_loop

/-- The provisional generalized KBO has this comparison before a unary context is added. -/
theorem generalized_comparison_before_context :
    GeneralizedKBOGt generalizedNatKBOWitness
      (.wrap .base .base) (.succ (.succ .base)) := by
  constructor
  · intro v
    cases v <;> decide
  · exact Or.inr ⟨rfl, by decide⟩

/-- The same comparison disappears under a common unary successor context. -/
theorem generalized_comparison_lost_under_context :
    ¬ GeneralizedKBOGt generalizedNatKBOWitness
      (.succ (.wrap .base .base)) (.succ (.succ (.succ .base))) := by
  rintro ⟨_, hw | ⟨_, hp⟩⟩
  · norm_num [generalizedKBOWeight, generalizedNatKBOWitness] at hw
  · norm_num [generalizedRootRank, generalizedNatKBOWitness, methodRoot] at hp

#check @lexKBO
#print axioms lexKBO
#check @leftTerm
#print axioms leftTerm
#check @rightTerm
#print axioms rightTerm
#check @acComparison_self_loop
#print axioms acComparison_self_loop
#check @acComparison_not_wellFounded
#print axioms acComparison_not_wellFounded
#check @generalized_comparison_before_context
#print axioms generalized_comparison_before_context
#check @generalized_comparison_lost_under_context
#print axioms generalized_comparison_lost_under_context

end OperatorKO7.Test.OrientationClosureCounterexamples
