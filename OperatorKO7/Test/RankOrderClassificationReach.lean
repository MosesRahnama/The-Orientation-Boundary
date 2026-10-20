import OperatorKO7.Meta.Rewriting.RankOrderClassification

/-! Complete named-declaration and axiom checks for RankOrderClassification. -/

#check @OperatorKO7.Meta.Rewriting.RankOrderClassification.NaturalRank
#check @OperatorKO7.Meta.Rewriting.RankOrderClassification.RankSameOrder
#check @OperatorKO7.Meta.Rewriting.RankOrderClassification.rankOrderSetoid
#check @OperatorKO7.Meta.Rewriting.RankOrderClassification.RankOrderQuotient
#check @OperatorKO7.Meta.Rewriting.RankOrderClassification.rankOrderClass
#check @OperatorKO7.Meta.Rewriting.RankOrderClassification.rankOrderClass_eq_iff
#check @OperatorKO7.Meta.Rewriting.RankOrderClassification.CounterSystem
#check @OperatorKO7.Meta.Rewriting.RankOrderClassification.CounterSystem.rank
#check @OperatorKO7.Meta.Rewriting.RankOrderClassification.CounterSystem.FiberConstant
#check @OperatorKO7.Meta.Rewriting.RankOrderClassification.CounterSystem.CounterRank
#check @OperatorKO7.Meta.Rewriting.RankOrderClassification.CounterSystem.canonicalRank
#check @OperatorKO7.Meta.Rewriting.RankOrderClassification.CounterSystem.recoding
#check @OperatorKO7.Meta.Rewriting.RankOrderClassification.CounterSystem.recoding_strictMono
#check @OperatorKO7.Meta.Rewriting.RankOrderClassification.CounterSystem.rank_factors
#check @OperatorKO7.Meta.Rewriting.RankOrderClassification.CounterSystem.counterRank_same_order
#check @OperatorKO7.Meta.Rewriting.RankOrderClassification.CounterSystem.fiberConstant_iff_same_order
#check @OperatorKO7.Meta.Rewriting.RankOrderClassification.CounterSystem.StrictRecoding
#check @OperatorKO7.Meta.Rewriting.RankOrderClassification.CounterSystem.rankOfRecoding
#check @OperatorKO7.Meta.Rewriting.RankOrderClassification.CounterSystem.ranksEquivStrictRecoding
#check @OperatorKO7.Meta.Rewriting.RankOrderClassification.CounterSystem.recoding_decreases_iff
#check @OperatorKO7.Meta.Rewriting.RankOrderClassification.CounterSystem.orderSetoid
#check @OperatorKO7.Meta.Rewriting.RankOrderClassification.CounterSystem.OrderQuotient
#check @OperatorKO7.Meta.Rewriting.RankOrderClassification.CounterSystem.all_counterRanks_same_order
#check @OperatorKO7.Meta.Rewriting.RankOrderClassification.CounterSystem.orderQuotient_subsingleton
#check @OperatorKO7.Meta.Rewriting.RankOrderClassification.CounterSystem.orderQuotientEquivPUnit
#check @OperatorKO7.Meta.Rewriting.RankOrderClassification.CounterSystem.counter_order_classification
#check @OperatorKO7.Meta.Rewriting.RankOrderClassification.rankWithInvariant
#check @OperatorKO7.Meta.Rewriting.RankOrderClassification.invariant_ranks_separate
#check @OperatorKO7.Meta.Rewriting.RankOrderClassification.invariant_rank_classes_injective
#check @OperatorKO7.Meta.Rewriting.RankOrderClassification.rankOrderQuotient_infinite_of_independent_invariant
#check @OperatorKO7.Meta.Rewriting.RankOrderClassification.rankOrderQuotient_infinite_of_axis_witnesses
#check @OperatorKO7.Meta.Rewriting.RankOrderClassification.productCountdown
#check @OperatorKO7.Meta.Rewriting.RankOrderClassification.productCountdown_all_order_quotient_infinite
#check @OperatorKO7.Meta.Rewriting.RankOrderClassification.productCountdown_counter_order_unique
#check @OperatorKO7.Meta.Rewriting.RankOrderClassification.emptyBoolRank
#check @OperatorKO7.Meta.Rewriting.RankOrderClassification.empty_relation_has_distinct_orders

#print axioms OperatorKO7.Meta.Rewriting.RankOrderClassification.NaturalRank
#print axioms OperatorKO7.Meta.Rewriting.RankOrderClassification.RankSameOrder
#print axioms OperatorKO7.Meta.Rewriting.RankOrderClassification.rankOrderSetoid
#print axioms OperatorKO7.Meta.Rewriting.RankOrderClassification.RankOrderQuotient
#print axioms OperatorKO7.Meta.Rewriting.RankOrderClassification.rankOrderClass
#print axioms OperatorKO7.Meta.Rewriting.RankOrderClassification.rankOrderClass_eq_iff
#print axioms OperatorKO7.Meta.Rewriting.RankOrderClassification.CounterSystem
#print axioms OperatorKO7.Meta.Rewriting.RankOrderClassification.CounterSystem.rank
#print axioms OperatorKO7.Meta.Rewriting.RankOrderClassification.CounterSystem.FiberConstant
#print axioms OperatorKO7.Meta.Rewriting.RankOrderClassification.CounterSystem.CounterRank
#print axioms OperatorKO7.Meta.Rewriting.RankOrderClassification.CounterSystem.canonicalRank
#print axioms OperatorKO7.Meta.Rewriting.RankOrderClassification.CounterSystem.recoding
#print axioms OperatorKO7.Meta.Rewriting.RankOrderClassification.CounterSystem.recoding_strictMono
#print axioms OperatorKO7.Meta.Rewriting.RankOrderClassification.CounterSystem.rank_factors
#print axioms OperatorKO7.Meta.Rewriting.RankOrderClassification.CounterSystem.counterRank_same_order
#print axioms OperatorKO7.Meta.Rewriting.RankOrderClassification.CounterSystem.fiberConstant_iff_same_order
#print axioms OperatorKO7.Meta.Rewriting.RankOrderClassification.CounterSystem.StrictRecoding
#print axioms OperatorKO7.Meta.Rewriting.RankOrderClassification.CounterSystem.rankOfRecoding
#print axioms OperatorKO7.Meta.Rewriting.RankOrderClassification.CounterSystem.ranksEquivStrictRecoding
#print axioms OperatorKO7.Meta.Rewriting.RankOrderClassification.CounterSystem.recoding_decreases_iff
#print axioms OperatorKO7.Meta.Rewriting.RankOrderClassification.CounterSystem.orderSetoid
#print axioms OperatorKO7.Meta.Rewriting.RankOrderClassification.CounterSystem.OrderQuotient
#print axioms OperatorKO7.Meta.Rewriting.RankOrderClassification.CounterSystem.all_counterRanks_same_order
#print axioms OperatorKO7.Meta.Rewriting.RankOrderClassification.CounterSystem.orderQuotient_subsingleton
#print axioms OperatorKO7.Meta.Rewriting.RankOrderClassification.CounterSystem.orderQuotientEquivPUnit
#print axioms OperatorKO7.Meta.Rewriting.RankOrderClassification.CounterSystem.counter_order_classification
#print axioms OperatorKO7.Meta.Rewriting.RankOrderClassification.rankWithInvariant
#print axioms OperatorKO7.Meta.Rewriting.RankOrderClassification.invariant_ranks_separate
#print axioms OperatorKO7.Meta.Rewriting.RankOrderClassification.invariant_rank_classes_injective
#print axioms OperatorKO7.Meta.Rewriting.RankOrderClassification.rankOrderQuotient_infinite_of_independent_invariant
#print axioms OperatorKO7.Meta.Rewriting.RankOrderClassification.rankOrderQuotient_infinite_of_axis_witnesses
#print axioms OperatorKO7.Meta.Rewriting.RankOrderClassification.productCountdown
#print axioms OperatorKO7.Meta.Rewriting.RankOrderClassification.productCountdown_all_order_quotient_infinite
#print axioms OperatorKO7.Meta.Rewriting.RankOrderClassification.productCountdown_counter_order_unique
#print axioms OperatorKO7.Meta.Rewriting.RankOrderClassification.emptyBoolRank
#print axioms OperatorKO7.Meta.Rewriting.RankOrderClassification.empty_relation_has_distinct_orders

open OperatorKO7.Meta.Rewriting.RankOrderClassification

example : Infinite (RankOrderQuotient productCountdown.Step) :=
  productCountdown_all_order_quotient_infinite

example : Infinite (RankOrderQuotient productCountdown.Step) :=
  rankOrderQuotient_infinite_of_axis_witnesses productCountdown.rank
    Prod.snd (fun h => h.2) ⟨(17, 3), by decide⟩ (fun n => ⟨(n, 0), rfl, rfl⟩)

example : Nonempty (productCountdown.OrderQuotient ≃ PUnit) :=
  productCountdown_counter_order_unique

example : ¬ RankSameOrder (emptyBoolRank false) (emptyBoolRank true) :=
  empty_relation_has_distinct_orders

example : StrictMono (fun n : Nat => 2 * n + 3) := by
  intro a b hab
  change 2 * a + 3 < 2 * b + 3
  omega
