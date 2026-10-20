import OperatorKO7.Meta.Methods.OrientationClosure.FreeDerivationalComplexity

/-! # FreeDerivationalComplexity reach and axiom check -/

#check @OperatorKO7.Methods.OrientationClosure.FreeDerivationalComplexity.termSize
#print axioms OperatorKO7.Methods.OrientationClosure.FreeDerivationalComplexity.termSize
#check @OperatorKO7.Methods.OrientationClosure.FreeDerivationalComplexity.freeWeight
#print axioms OperatorKO7.Methods.OrientationClosure.FreeDerivationalComplexity.freeWeight
#check @OperatorKO7.Methods.OrientationClosure.FreeDerivationalComplexity.freeWeight_eq_qw
#print axioms OperatorKO7.Methods.OrientationClosure.FreeDerivationalComplexity.freeWeight_eq_qw
#check @OperatorKO7.Methods.OrientationClosure.FreeDerivationalComplexity.freeWeight_rootStep
#print axioms OperatorKO7.Methods.OrientationClosure.FreeDerivationalComplexity.freeWeight_rootStep
#check @OperatorKO7.Methods.OrientationClosure.FreeDerivationalComplexity.freeWeight_plug_lt
#print axioms OperatorKO7.Methods.OrientationClosure.FreeDerivationalComplexity.freeWeight_plug_lt
#check @OperatorKO7.Methods.OrientationClosure.FreeDerivationalComplexity.freeWeight_contextStep
#print axioms OperatorKO7.Methods.OrientationClosure.FreeDerivationalComplexity.freeWeight_contextStep
#check @OperatorKO7.Methods.OrientationClosure.FreeDerivationalComplexity.relPow_le_freeWeight
#print axioms OperatorKO7.Methods.OrientationClosure.FreeDerivationalComplexity.relPow_le_freeWeight
#check @OperatorKO7.Methods.OrientationClosure.FreeDerivationalComplexity.relPow_le_qw
#print axioms OperatorKO7.Methods.OrientationClosure.FreeDerivationalComplexity.relPow_le_qw
#check @OperatorKO7.Methods.OrientationClosure.FreeDerivationalComplexity.freeWeight_add_two_le_pow
#print axioms OperatorKO7.Methods.OrientationClosure.FreeDerivationalComplexity.freeWeight_add_two_le_pow
#check @OperatorKO7.Methods.OrientationClosure.FreeDerivationalComplexity.qw_add_two_le_pow
#print axioms OperatorKO7.Methods.OrientationClosure.FreeDerivationalComplexity.qw_add_two_le_pow
#check @OperatorKO7.Methods.OrientationClosure.FreeDerivationalComplexity.derivation_lt_pow_size
#print axioms OperatorKO7.Methods.OrientationClosure.FreeDerivationalComplexity.derivation_lt_pow_size
#check @OperatorKO7.Methods.OrientationClosure.FreeDerivationalComplexity.sucOn
#print axioms OperatorKO7.Methods.OrientationClosure.FreeDerivationalComplexity.sucOn
#check @OperatorKO7.Methods.OrientationClosure.FreeDerivationalComplexity.wrapPow
#print axioms OperatorKO7.Methods.OrientationClosure.FreeDerivationalComplexity.wrapPow
#check @OperatorKO7.Methods.OrientationClosure.FreeDerivationalComplexity.relPow_plug
#print axioms OperatorKO7.Methods.OrientationClosure.FreeDerivationalComplexity.relPow_plug
#check @OperatorKO7.Methods.OrientationClosure.FreeDerivationalComplexity.unfold_steps
#print axioms OperatorKO7.Methods.OrientationClosure.FreeDerivationalComplexity.unfold_steps
#check @OperatorKO7.Methods.OrientationClosure.FreeDerivationalComplexity.reduce_copies
#print axioms OperatorKO7.Methods.OrientationClosure.FreeDerivationalComplexity.reduce_copies
#check @OperatorKO7.Methods.OrientationClosure.FreeDerivationalComplexity.nestFamily
#print axioms OperatorKO7.Methods.OrientationClosure.FreeDerivationalComplexity.nestFamily
#check @OperatorKO7.Methods.OrientationClosure.FreeDerivationalComplexity.nest
#print axioms OperatorKO7.Methods.OrientationClosure.FreeDerivationalComplexity.nest
#check @OperatorKO7.Methods.OrientationClosure.FreeDerivationalComplexity.termSize_sucOn
#print axioms OperatorKO7.Methods.OrientationClosure.FreeDerivationalComplexity.termSize_sucOn
#check @OperatorKO7.Methods.OrientationClosure.FreeDerivationalComplexity.termSize_nestFamily
#print axioms OperatorKO7.Methods.OrientationClosure.FreeDerivationalComplexity.termSize_nestFamily
#check @OperatorKO7.Methods.OrientationClosure.FreeDerivationalComplexity.termSize_nest
#print axioms OperatorKO7.Methods.OrientationClosure.FreeDerivationalComplexity.termSize_nest
#check @OperatorKO7.Methods.OrientationClosure.FreeDerivationalComplexity.nestFamily_long_derivation
#print axioms OperatorKO7.Methods.OrientationClosure.FreeDerivationalComplexity.nestFamily_long_derivation
#check @OperatorKO7.Methods.OrientationClosure.FreeDerivationalComplexity.nest_long_derivation
#print axioms OperatorKO7.Methods.OrientationClosure.FreeDerivationalComplexity.nest_long_derivation
#check @OperatorKO7.Methods.OrientationClosure.FreeDerivationalComplexity.exponential_sandwich
#print axioms OperatorKO7.Methods.OrientationClosure.FreeDerivationalComplexity.exponential_sandwich
#check @OperatorKO7.Methods.OrientationClosure.FreeDerivationalComplexity.callChain_length_eq
#print axioms OperatorKO7.Methods.OrientationClosure.FreeDerivationalComplexity.callChain_length_eq

namespace OrientationClosureFreeDerivationalComplexityReach

open OperatorKO7.Methods.OrientationClosure.SchemaCore
open OperatorKO7.Methods.OrientationClosure.ProcessorSemantics
open OperatorKO7.Methods.OrientationClosure.SourceChainSoundness
open OperatorKO7.Methods.OrientationClosure.FreeDerivationalComplexity

/-! The natural-number statements of the module before the generalization are instances of the
general statements. -/

example : ∀ {m : Nat} {t u : FreeTerm Nat}, RelPow ContextStep m t u → m + 2 ≤ 3 ^ termSize t :=
  fun h => derivation_lt_pow_size h

example :
    (∀ {m : Nat} {t u : FreeTerm Nat}, RelPow ContextStep m t u → m + 2 ≤ 3 ^ termSize t) ∧
      ∀ d : Nat, termSize (nest 2 d) = 5 * d + 4 ∧
        ∃ m u, 2 ^ d ≤ m ∧ RelPow ContextStep m (nest 2 d) u :=
  exponential_sandwich

example {m : Nat} {a c : FreeTerm Nat} (h : RelPow FreeRecursiveCallPair m a c) :
    m + recursiveCallRank c = recursiveCallRank a :=
  callChain_length_eq h

/-! Non-vacuity at other variable types: closed terms, Boolean variables and string variables. -/

example : ∃ m u, 2 ^ 3 ≤ m ∧ RelPow ContextStep m (nestFamily (ν := Empty) 2 3) u :=
  nestFamily_long_derivation 2 3

example : termSize (nestFamily (ν := Bool) 2 2) = 14 := rfl

example : termSize (nestFamily (ν := Bool) 3 2) = 16 := rfl

example : RelPow ContextStep 1 (FreeTerm.recur (FreeTerm.var "b") (FreeTerm.var "s") .zero)
    (FreeTerm.var "b") :=
  RelPow.succ (RelPow.zero _) (rootStep_contextStep (.recurZero _ _))

example : 1 + 2 ≤ 3 ^ termSize (FreeTerm.recur (FreeTerm.var "b") (FreeTerm.var "s") .zero) :=
  derivation_lt_pow_size (u := FreeTerm.var "b")
    (RelPow.succ (RelPow.zero _) (rootStep_contextStep (.recurZero _ _)))

example : freeWeight (FreeTerm.var true) < freeWeight (FreeTerm.recur (FreeTerm.var true) .zero .zero) :=
  freeWeight_contextStep (rootStep_contextStep (.recurZero _ _))

end OrientationClosureFreeDerivationalComplexityReach
