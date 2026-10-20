import OperatorKO7.Meta.DistinctionBoundary.GodelQuoteEvalPeak

/-!
# Reach and axiom gate for the quote/eval peak
-/


set_option autoImplicit false

namespace OperatorKO7.Meta.DistinctionBoundary.GodelPartial

#check @BehaviorJoinAt
#check @quote_merge_void_void_converges
#check @quote_void_diverges_at_void
#check @quote_diverge_blocks_join
#check @not_BehaviorJoinAt_quote_R5
#check @QuoteEvalCfg
#check @QuoteEvalCfg.evalQuoted
#check @QuoteEvalCfg.value
#check @QuoteEvalCfg.diverged
#check @QuoteEvalStep
#check @QuoteEvalStep.underQuote
#check @QuoteEvalStep.evalConverge
#check @QuoteEvalStep.evalDiverge
#check @QuoteEvalStar
#check @QuoteEvalStar.refl
#check @QuoteEvalStar.tail
#check @QuoteEvalJoin
#check @freezePeakSource
#check @freeze_peak_eval_converge
#check @freeze_peak_under_quote
#check @freeze_peak_eval_diverge
#check @freeze_peak_two_reductions
#check @value_ne_diverged
#check @no_step_from_value
#check @no_step_from_diverged
#check @star_from_value
#check @star_from_diverged
#check @freeze_peak_does_not_join
#check @quote_eval_nonjoinable_peak
#check @freeze_peak_eval_converge_frozen
#check @no_underQuote_when_frozen
#check @quote_congruence_freeze_kills_underQuote_arm
#check @eqW_kernel_freeze_does_not_remove_quote_peak
#check @QuotePairJoins
#check @quote_integrate_eq_diverge
#check @quote_eqW_eq_diverge
#check @quote_rec_eq_diverge
#check @pair_both_diverge
#check @QuoteCriticalPair
#check @QuoteCriticalPair.intDelta
#check @QuoteCriticalPair.mergeVoidLeft
#check @QuoteCriticalPair.mergeVoidRight
#check @QuoteCriticalPair.mergeCancel
#check @QuoteCriticalPair.recZero
#check @QuoteCriticalPair.recSucc
#check @QuoteCriticalPair.eqRefl
#check @QuoteCriticalPair.eqDiff
#check @QuoteCriticalPair.source
#check @QuoteCriticalPair.target
#check @QuoteCriticalPair.kernelStep
#check @QuoteCriticalPair.kernelStep_holds
#check @QuoteCriticalPair.quoteJoins
#check @quote_app_void_rec_eq_diverge
#check @QuoteCriticalPair.quoteJoins_correct
#check @least_freeze_includes_quote_congruence
#print axioms BehaviorJoinAt
#print axioms quote_merge_void_void_converges
#print axioms quote_void_diverges_at_void
#print axioms quote_diverge_blocks_join
#print axioms not_BehaviorJoinAt_quote_R5
#print axioms QuoteEvalCfg
#print axioms QuoteEvalCfg.evalQuoted
#print axioms QuoteEvalCfg.value
#print axioms QuoteEvalCfg.diverged
#print axioms QuoteEvalStep
#print axioms QuoteEvalStep.underQuote
#print axioms QuoteEvalStep.evalConverge
#print axioms QuoteEvalStep.evalDiverge
#print axioms QuoteEvalStar
#print axioms QuoteEvalStar.refl
#print axioms QuoteEvalStar.tail
#print axioms QuoteEvalJoin
#print axioms freezePeakSource
#print axioms freeze_peak_eval_converge
#print axioms freeze_peak_under_quote
#print axioms freeze_peak_eval_diverge
#print axioms freeze_peak_two_reductions
#print axioms value_ne_diverged
#print axioms no_step_from_value
#print axioms no_step_from_diverged
#print axioms star_from_value
#print axioms star_from_diverged
#print axioms freeze_peak_does_not_join
#print axioms quote_eval_nonjoinable_peak
#print axioms freeze_peak_eval_converge_frozen
#print axioms no_underQuote_when_frozen
#print axioms quote_congruence_freeze_kills_underQuote_arm
#print axioms eqW_kernel_freeze_does_not_remove_quote_peak
#print axioms QuotePairJoins
#print axioms quote_integrate_eq_diverge
#print axioms quote_eqW_eq_diverge
#print axioms quote_rec_eq_diverge
#print axioms pair_both_diverge
#print axioms QuoteCriticalPair
#print axioms QuoteCriticalPair.intDelta
#print axioms QuoteCriticalPair.mergeVoidLeft
#print axioms QuoteCriticalPair.mergeVoidRight
#print axioms QuoteCriticalPair.mergeCancel
#print axioms QuoteCriticalPair.recZero
#print axioms QuoteCriticalPair.recSucc
#print axioms QuoteCriticalPair.eqRefl
#print axioms QuoteCriticalPair.eqDiff
#print axioms QuoteCriticalPair.source
#print axioms QuoteCriticalPair.target
#print axioms QuoteCriticalPair.kernelStep
#print axioms QuoteCriticalPair.kernelStep_holds
#print axioms QuoteCriticalPair.quoteJoins
#print axioms quote_app_void_rec_eq_diverge
#print axioms QuoteCriticalPair.quoteJoins_correct
#print axioms least_freeze_includes_quote_congruence

end OperatorKO7.Meta.DistinctionBoundary.GodelPartial
