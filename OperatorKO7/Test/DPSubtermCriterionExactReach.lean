import OperatorKO7.Meta.DPSubtermCriterionExact

/-!
# Phase F+ DP Subterm Criterion Exact Reach Checks

Reach checks for the Phase F+ exact subterm-criterion certificate surface.
Every public name listed in the dispatch is exercised by an `#check` here, and
a few small projection facts on the canonical KO7 certificate are stated as
`example` results.

This file is a structural-shape sanity layer; it does not introduce any new
theorems. All assertions are decidable / immediate from the module surface.
-/

namespace OperatorKO7.DPSubtermCriterionExactNS

open OperatorKO7.DPSubtermCriterionExactNS
open OperatorKO7.MetaDependencyPairs
open OperatorKO7.TTT2CertificateReplay

/-! ## Public-name reach checks -/

#check @DPSubtermCriterionExact
#check @ko7DPSubtermCriterionExact
#check @internal_dp_subterm_criterion_exact
#check @external_ceta_supports_same_dp_route
#check @dp_subterm_and_ceta_independent_support
#check @phaseFplus_dp_subterm_closed

/-! ## Concrete-certificate projections

The canonical certificate `ko7DPSubtermCriterionExact` records paper-side
projection index `3` (zero-based Lean index `2`), packages `dpRank` as the
subterm-criterion rank, and proves both strict pair descent and reverse-pair
well-foundedness.
-/

example : ko7DPSubtermCriterionExact.projectionIndex = 2 := rfl

example : ko7DPSubtermCriterionExact.projectionIndex_paper = 3 := rfl

example :
    ko7DPSubtermCriterionExact.projectionIndex + 1
      = ko7DPSubtermCriterionExact.projectionIndex_paper :=
  ko7DPSubtermCriterionExact.projectionIndex_correspondence

example : ko7DPSubtermCriterionExact.rank = dpRank := rfl

/-! ## Internal subterm criterion strict-descent reach -/

open OperatorKO7 in
example {b s n : Trace} :
    dpRank (Trace.recΔ b s n) < dpRank (Trace.recΔ b s (Trace.delta n)) :=
  internal_dp_subterm_criterion_exact (DPPair.rec_succ b s n)

/-! ## External CeTA / TTT2 alignment reach -/

example : ko7FastReplay.projectionProblem.Pair = DPPair :=
  (external_ceta_supports_same_dp_route).1

example : ko7FastReplay.projectionIndexPaper = 3 :=
  (external_ceta_supports_same_dp_route).2.1

example : ko7FastReplay.pairCount = 1 :=
  (external_ceta_supports_same_dp_route).2.2.1

example : WellFounded ko7FastReplay.projectionProblem.Rev :=
  (external_ceta_supports_same_dp_route).2.2.2

/-! ## Independent-support bridge reach -/

example : WellFounded DPPairRev :=
  dp_subterm_and_ceta_independent_support.2.2

/-! ## Phase F+ closure marker reach -/

example : WellFounded DPPairRev :=
  phaseFplus_dp_subterm_closed.2.2.2

example :
    ko7DPSubtermCriterionExact.projectionIndex_paper
      = ko7FastReplay.projectionIndexPaper :=
  phaseFplus_dp_subterm_closed.2.2.1

end OperatorKO7.DPSubtermCriterionExactNS
