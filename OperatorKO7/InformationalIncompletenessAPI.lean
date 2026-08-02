import OperatorKO7.Meta.InformationalIncompleteness.ShannonFinite
import OperatorKO7.Meta.InformationalIncompleteness.CarrierBurden
import OperatorKO7.Meta.InformationalIncompleteness.DiagonalEntropy
import OperatorKO7.Meta.InformationalIncompleteness.QueryInterface
import OperatorKO7.Meta.InformationalIncompleteness.WitnessChannelBoundary
import OperatorKO7.Meta.InformationalIncompleteness.RecursorPayloadErasure
import OperatorKO7.Meta.InformationalIncompleteness.UniversalDeficit
import OperatorKO7.Meta.InformationalIncompleteness.CarrierAddressability
import OperatorKO7.Meta.InformationalIncompleteness.LicensedFactorisation
import OperatorKO7.Meta.InformationalIncompleteness.ForcedTrilemma
import OperatorKO7.Meta.InformationalIncompleteness.SharpnessCounterexample
import OperatorKO7.Meta.InformationalIncompleteness.ConditionalEntropy
import OperatorKO7.Meta.InformationalIncompleteness.GradedDeficit
import OperatorKO7.Meta.InformationalIncompleteness.CertFragmentWitness
import OperatorKO7.Meta.InformationalIncompleteness.UnivDeficitViaChar
import OperatorKO7.Meta.InformationalIncompleteness.SemanticWitnessBridge
import OperatorKO7.Meta.InformationalIncompleteness.LicensedChannelDeficit
import OperatorKO7.Meta.InformationalIncompleteness.ParticipatoryQuery
import OperatorKO7.Meta.InformationalIncompleteness.PropagationResidual
import OperatorKO7.Meta.InformationalIncompleteness.MemoryDistinction
import OperatorKO7.Meta.InformationalIncompleteness.DiagonalInert
import OperatorKO7.Meta.InformationalIncompleteness.AxisGrowthSeparation
import OperatorKO7.Meta.InformationalIncompleteness.EqWDiagonalDeficit
import OperatorKO7.Meta.InformationalIncompleteness.ConfluenceForcedTrilemma
import OperatorKO7.Meta.InformationalIncompleteness.LicensedCollapseDeficit
import OperatorKO7.Meta.InformationalIncompleteness.VerdictDeficit

/-!
# Informational Incompleteness: paper-facing API root

Single import surface for the mechanized fragment of
`Rahnama_Informational_Incompleteness.tex`. Manuscript-label crosswalk to the
load-bearing Lean declarations:

| Paper label | Lean declaration |
|---|---|
| `lem:diagonal` (Lemma 4.1) | `DiagonalEntropy.diagonal_entropy_eq` (full pushforward form), `ShannonFinite.H_relabel_eq` (relabel core) |
| `def:raw-burden` (Def 4.3) | `CarrierBurden.carrierRaw`, `CarrierBurden.carrierRaw_two_mul` |
| `thm:query-confession` (Thm 3.3) | `QueryInterface.query_confession_condEntropy_pos`, `QueryInterface.query_confession_mi_pos` |
| `thm:duality` (Thm 5.5) | `WitnessChannelBoundary.witnessChannel_coordinate_of_OB` |
| `thm:universal-deficit` cl.(2) | `UniversalDeficit.universal_witnessChannel_deficit` |
| `thm:carrier-capacity` (conditional replacement) | `CarrierAddressability.individuallyAddressable_exceeds_fixed_budget`, conditional on `IndividuallyAddressable` |
| `thm:universal-char` / gauge-fixing | `LicensedFactorisation` (`export` surface) |
| `thm:trilemma` (scoped support only) | `ForcedTrilemma.forced_output_trilemma_no_decisive_support` |
| recursor counter-domination spine | `RecursorPayloadErasure.iiRecursor_orienting_measure_counter_dominated` |
| sharpness (boundary-as-theorem) | `SharpnessCounterexample.payloadErasure_hypothesis_necessary` |
| licensed-channel deficit + circular reference (T-Move 7) | `LicensedChannelDeficit.deficit_nonneg`, `LicensedChannelDeficit.circular_reference_zero_deficit` |
| participatory query / resolution arc (T-Move 7) | `ParticipatoryQuery.participation_creates_correlation`, `ParticipatoryQuery.resolution_arc` |
| propagation residual + first reactor (Boundary Propagation Program) | `PropagationResidual.residual_nonneg`, `PropagationResidual.residual_zero_of_measurable` (synchronization), `PropagationResidual.firstReactor_positive_and_open` |
| sound-verdict cell deficit | `VerdictDeficit.verdict_deficit_zero_of_terminating` (general), `VerdictDeficit.ko7_recursor_verdict_deficit_zero` (recursor instance) |

Trust: the pre-Tier-17 declarations above retain their prior kernel-check and
trust-surface receipts.  `CarrierAddressability` and `VerdictDeficit` passed
the targeted Tier-17B elaboration, reach, API-preservation, and explicit
`#print axioms` gates on 2026-08-02.  Importing them here does not enlarge the
scope recorded by their declarations or by the dated Tier-17B receipt.

This root now also re-exports the remaining live II support and paper-facing
surface: `ConditionalEntropy`, `GradedDeficit` (`prop:deficit-monotone`),
`CertFragmentWitness` (`thm:cert-fragment-info`), `UnivDeficitViaChar`
(`cor:univ-deficit-via-char`), and `SemanticWitnessBridge`.
-/

namespace OperatorKO7.InformationalIncompletenessAPI

/-- Stable list of the paper-facing audit anchors (fully-qualified declaration
names) for the mechanized Informational Incompleteness fragment. -/
def informationalIncompletenessAnchors : List String :=
  ["OperatorKO7.Meta.InformationalIncompleteness.DiagonalEntropy.diagonal_entropy_eq",
   "OperatorKO7.Meta.InformationalIncompleteness.CarrierBurden.carrierRaw_two_mul",
   "OperatorKO7.Meta.InformationalIncompleteness.QueryInterface.query_confession_condEntropy_pos",
   "OperatorKO7.Meta.InformationalIncompleteness.WitnessChannelBoundary.witnessChannel_coordinate_of_OB",
   "OperatorKO7.Meta.InformationalIncompleteness.UniversalDeficit.universal_witnessChannel_deficit",
   "OperatorKO7.Meta.InformationalIncompleteness.CarrierAddressability.individuallyAddressable_exceeds_fixed_budget",
   "OperatorKO7.Meta.InformationalIncompleteness.GradedDeficit.gradedDeficit_monotone",
   "OperatorKO7.Meta.InformationalIncompleteness.ForcedTrilemma.forced_output_trilemma_no_decisive_support",
   "OperatorKO7.Meta.InformationalIncompleteness.CertFragmentWitness.cert_fragment_zero_deficit",
   "OperatorKO7.Meta.InformationalIncompleteness.UnivDeficitViaChar.univ_deficit_via_char_direct",
   "OperatorKO7.Meta.InformationalIncompleteness.RecursorPayloadErasure.iiRecursor_orienting_measure_counter_dominated",
   "OperatorKO7.Meta.InformationalIncompleteness.SharpnessCounterexample.payloadErasure_hypothesis_necessary",
   "OperatorKO7.Meta.InformationalIncompleteness.LicensedChannelDeficit.deficit_nonneg",
   "OperatorKO7.Meta.InformationalIncompleteness.LicensedChannelDeficit.circular_reference_zero_deficit",
   "OperatorKO7.Meta.InformationalIncompleteness.ParticipatoryQuery.participation_creates_correlation",
   "OperatorKO7.Meta.InformationalIncompleteness.ParticipatoryQuery.resolution_arc",
   "OperatorKO7.Meta.InformationalIncompleteness.PropagationResidual.residual_nonneg",
   "OperatorKO7.Meta.InformationalIncompleteness.PropagationResidual.residual_zero_of_measurable",
   "OperatorKO7.Meta.InformationalIncompleteness.PropagationResidual.firstReactor_positive_and_open",
   -- Distinction-Boundary bridge surface (T1-T6): the confluence axis read information-theoretically.
   "OperatorKO7.Meta.InformationalIncompleteness.MemoryDistinction.memory_distinction_information_equiv",
   "OperatorKO7.Meta.InformationalIncompleteness.DiagonalInert.diagonal_inert_trinity",
   "OperatorKO7.Meta.InformationalIncompleteness.AxisGrowthSeparation.axis_growth_separation",
   "OperatorKO7.Meta.InformationalIncompleteness.EqWDiagonalDeficit.eqW_diagonal_echo_vacuum_with_fork",
   "OperatorKO7.Meta.InformationalIncompleteness.ConfluenceForcedTrilemma.confluence_forced_trilemma",
   "OperatorKO7.Meta.InformationalIncompleteness.LicensedCollapseDeficit.boundary_collapse_unified",
   "OperatorKO7.Meta.InformationalIncompleteness.VerdictDeficit.verdict_deficit_zero_of_terminating",
   "OperatorKO7.Meta.InformationalIncompleteness.VerdictDeficit.ko7_recursor_verdict_deficit_zero"]

/-- The public anchor list names twenty-seven declarations after removing the
unconditional carrier-capacity and three demoted support anchors, and adding
the general and concrete sound-verdict deficit anchors. -/
theorem informationalIncompletenessAnchors_length :
  informationalIncompletenessAnchors.length = 27 := by rfl

end OperatorKO7.InformationalIncompletenessAPI
