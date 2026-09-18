import OperatorKO7.Meta.ReverseMath.NewmanRCA0Upper
import OperatorKO7.Meta.ReverseMath.ConfluenceOrderType
import OperatorKO7.Meta.DistinctionBoundary.GlobalConfluence

set_option autoImplicit false

namespace OperatorKO7.Meta.ReverseMath.GuardedNewmanRCA0

open OperatorKO7 Trace
open Ordinal

structure GuardedNewmanUpper where
  stronglyNormalizing : WellFounded MetaSN_KO7.SafeStepRev
  locallyJoinable : ∀ a : Trace, MetaSN_KO7.LocalJoinAt a
  globallyConfluent : MetaSN_KO7.ConfluentSafe
  contextualConfluent : MetaSN_KO7.ConfluentSafeCtx
  standardModelUpper :
    OperatorKO7.ReverseMath.StdCarrier ⊨
      OperatorKO7.ReverseMath.newmanSentence
  orderBound : ∀ t : Trace,
    OperatorKO7.MetaDM.lex3cToOrd (OperatorKO7.MetaCM.mu3c t) <
      ((ω : Ordinal) ^ (ω : Ordinal)) * (2 : Nat)

def safeStep_guardedNewmanUpper : GuardedNewmanUpper where
  stronglyNormalizing :=
    OperatorKO7.Meta.DistinctionBoundary.GlobalConfluence.safeStep_strongly_normalizing
  locallyJoinable :=
    OperatorKO7.Meta.DistinctionBoundary.GlobalConfluence.safeStep_locally_confluent
  globallyConfluent :=
    OperatorKO7.Meta.DistinctionBoundary.GlobalConfluence.safeStep_globally_confluent
  contextualConfluent :=
    OperatorKO7.Meta.DistinctionBoundary.GlobalConfluence.safeStepCtx_globally_confluent
  standardModelUpper :=
    OperatorKO7.ReverseMath.stdModel_newmanSentence
  orderBound :=
    OperatorKO7.ReverseMath.confluence_measure_trace_bound

theorem guarded_newman_upper_package :
    GuardedNewmanUpper :=
  safeStep_guardedNewmanUpper

theorem guarded_newman_order_below_epsilon0 (t : Trace) :
    OperatorKO7.MetaDM.lex3cToOrd (OperatorKO7.MetaCM.mu3c t) <
      ε₀ :=
  OperatorKO7.ReverseMath.confluence_measure_below_epsilon0 t

#print axioms safeStep_guardedNewmanUpper
#print axioms guarded_newman_upper_package
#print axioms guarded_newman_order_below_epsilon0

end OperatorKO7.Meta.ReverseMath.GuardedNewmanRCA0
