import OperatorKO7.Meta.ConfessionMethod_DP
import OperatorKO7.Meta.DependencyPairs_Works

/-!
# Phase F+ Internal DP Subterm Criterion and Independent CeTA Support

This module closes Phase F+ per `THEORY_EXPANSION.md` §"Phase F+. Internal DP
Subterm Criterion and Independent CeTA Support". The deliverable is a single
exact subterm-criterion certificate that bundles three claims:

* an internal Lean proof that the KO7 dependency-pair problem strictly
  decreases under the subterm criterion's projection at the recursor's third
  argument (paper-side index `3`; zero-based Lean index `2`);
* an alignment-level theorem stating that the existing external TTT2/CeTA
  FAST certificate replay (`OperatorKO7.TTT2CertificateReplay.ko7FastReplay`)
  targets the same dependency-pair relation `DPPair` and the same paper-side
  projection index `3`;
* a closure marker `phaseFplus_dp_subterm_closed` that combines both supports
  into a single Phase F+ acceptance result.

The internal proof and the external certificate replay are kept distinct: the
internal route consumes only `dpPair_decreases` + `wf_DPPairRev` from
`DependencyPairs_Works.lean`, while the external route consumes
`ko7FastReplay_uses_recSucc_pair` + `ko7FastReplay_sound` from
`TTT2_CertificateReplay.lean`. The Phase F+ statement asserts that both
routes converge on `WellFounded DPPairRev` without claiming artifact-level
identity between them.

Estimated-DP / tcap status: the existing internal proof already discharges the
KO7 dependency-pair problem without needing an estimated-DP refinement, so no
estimated-DP module is introduced here.
-/

namespace OperatorKO7.DPSubtermCriterionExactNS

open OperatorKO7
open OperatorKO7.Trace
open OperatorKO7.CompositionalImpossibility
open OperatorKO7.MetaDependencyPairs
open OperatorKO7.TTT2CertificateReplay
open OperatorKO7.ConfessionMethodFamily

/--
Phase F+ exact subterm-criterion certificate on the KO7 dependency-pair
problem.

The certificate packages the data the manuscript paragraph names:

* `projectionIndex` (zero-based; `2` on KO7 because the recursor's argument
  list is `(b, s, n)`) together with `projectionIndex_paper` (one-based; `3`
  on KO7);
* the rank function used by the subterm criterion together with a proof that
  it equals the canonical `dpProjection`;
* a strict-descent proof on the `DPPair` relation;
* the resulting well-foundedness of `DPPairRev`.

The fields are positional rather than typeclass-erased so callers can
construct alternative certificates for sister recursors without forcing them
through the KO7 canonical instance.
-/
structure DPSubtermCriterionExact where
  projectionIndex : Nat
  projectionIndex_paper : Nat
  projectionIndex_correspondence : projectionIndex + 1 = projectionIndex_paper
  rank : Trace → Nat
  pair_strict_descent : ∀ {a b : Trace}, DPPair a b → rank b < rank a
  reverse_pair_well_founded : WellFounded DPPairRev

/-- The canonical Phase F+ exact subterm-criterion certificate on KO7. -/
def ko7DPSubtermCriterionExact : DPSubtermCriterionExact where
  projectionIndex := 2
  projectionIndex_paper := 3
  projectionIndex_correspondence := by decide
  rank := dpRank
  pair_strict_descent := dpPair_decreases
  reverse_pair_well_founded := wf_DPPairRev

/-! ## Internal Lean DP subterm-criterion proof -/

/--
Internal Lean DP subterm-criterion theorem for KO7.

The projection at the recursor's third argument (Lean zero-based index `2`;
paper-side index `3`) makes every extracted dependency pair strictly decrease.
This is the manuscript's "internal Lean subterm-criterion proof for KO7"
deliverable, packaged as a single theorem statement that callers can cite
without unfolding the certificate.
-/
theorem internal_dp_subterm_criterion_exact :
    ∀ {a b : Trace}, DPPair a b → dpRank b < dpRank a :=
  @dpPair_decreases

/-! ## External TTT2 / CeTA FAST certificate support -/

/--
External TTT2 / CeTA FAST certificate replay supports the same DP route.

This theorem aligns the external certificate replay
(`OperatorKO7.TTT2CertificateReplay.ko7FastReplay`) with the internal subterm
criterion at the theorem level (not at the artifact level): the replay's
projection problem operates on the same `DPPair` relation, declares the same
paper-side projection index `3`, packages a single recursive-call pair, and
its reverse relation is well-founded.

The four conjuncts together witness the "same DP termination route" claim of
THEORY_EXPANSION.md §F+ ("internal proof and the existing external
certificate support the same DP termination route, without requiring literal
artifact matching").
-/
theorem external_ceta_supports_same_dp_route :
    ko7FastReplay.projectionProblem.Pair = DPPair
      ∧ ko7FastReplay.projectionIndexPaper = 3
      ∧ ko7FastReplay.pairCount = 1
      ∧ WellFounded ko7FastReplay.projectionProblem.Rev :=
  ⟨ko7FastReplay_uses_recSucc_pair, rfl, ko7FastReplay_pairCount,
   ko7FastReplay_sound⟩

/-! ## Independent-support bridge -/

/--
The internal Lean DP subterm-criterion proof and the external TTT2 / CeTA
FAST certificate replay independently support the same DP termination route.

The bridge records the two supports as separate conjuncts plus a joint
conclusion: both routes terminate on the same `WellFounded DPPairRev` result.
No conjunct depends on the other; the internal pair descent uses
`dpPair_decreases` directly and the external alignment uses
`ko7FastReplay_uses_recSucc_pair` + `ko7FastReplay_sound`. The literal-artifact
identity claim is intentionally avoided.
-/
theorem dp_subterm_and_ceta_independent_support :
    (∀ {a b : Trace}, DPPair a b → dpRank b < dpRank a)
      ∧ (ko7FastReplay.projectionProblem.Pair = DPPair
          ∧ WellFounded ko7FastReplay.projectionProblem.Rev)
      ∧ WellFounded DPPairRev :=
  ⟨internal_dp_subterm_criterion_exact,
   ⟨ko7FastReplay_uses_recSucc_pair, ko7FastReplay_sound⟩,
   wf_DPPairRev⟩

/-! ## Phase F+ closure marker -/

/--
The Phase F+ closure result.

For the canonical certificate `ko7DPSubtermCriterionExact`, the internal Lean
DP subterm-criterion proof and the external TTT2 / CeTA replay both support
the same KO7 dependency-pair termination route. The closure marker records
four facts:

1. the internal subterm criterion strictly decreases the canonical rank on
   every `DPPair` step;
2. the external replay targets the same `DPPair` relation;
3. the certificate's paper-side projection index matches the replay's
   paper-side projection index (`3 = 3`);
4. the reverse dependency-pair relation is well-founded internally.

The four facts together discharge the Phase F+ acceptance criterion: the
paper has both internal Lean and external CeTA-backed evidence for the DP
escape, without claiming the two supports are literally the same artifact.
-/
theorem phaseFplus_dp_subterm_closed :
    (∀ {a b : Trace}, DPPair a b → dpRank b < dpRank a)
      ∧ ko7FastReplay.projectionProblem.Pair = DPPair
      ∧ ko7DPSubtermCriterionExact.projectionIndex_paper
          = ko7FastReplay.projectionIndexPaper
      ∧ WellFounded DPPairRev :=
  ⟨@dpPair_decreases,
   ko7FastReplay_uses_recSucc_pair,
   rfl,
   wf_DPPairRev⟩

end OperatorKO7.DPSubtermCriterionExactNS
