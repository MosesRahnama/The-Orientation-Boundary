import OperatorKO7.Meta.InformationalIncompleteness.RecursorPayloadErasure
import OperatorKO7.Meta.InformationalIncompleteness.CarrierBurden
import OperatorKO7.Meta.InformationalIncompleteness.WitnessChannelBoundary
import OperatorKO7.Meta.InformationalIncompleteness.UniversalDeficit
import OperatorKO7.Meta.InformationalIncompleteness.CarrierAddressability
import OperatorKO7.Meta.InformationalIncompleteness.ForcedTrilemma
import OperatorKO7.Meta.InformationalIncompleteness.LicensedFactorisation
import OperatorKO7.Meta.InformationalIncompleteness.ShannonFinite
import OperatorKO7.Meta.InformationalIncompleteness.DiagonalEntropy
import OperatorKO7.Meta.InformationalIncompleteness.QueryInterface
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

/-!
# Reach + axiom audit for the Informational Incompleteness Lean surface

Imports the current Informational Incompleteness public surface and `#check`s
its paper-facing declarations so the import closure is exercised by a reach
test. The
`#print axioms` block is the Gate R1 / R7 trust-surface evidence: every release
theorem must depend only on the foundational allowlist
`{propext, Classical.choice, Quot.sound}` (or fewer), with no `sorryAx`,
`native_decide`, or user axiom. The Tier-17 addressability declarations are
source-stage requests until an authorized external run records their output.
-/

namespace OperatorKO7.Test.InformationalIncompletenessReach

open OperatorKO7.Meta.InformationalIncompleteness

-- Reach: every public release theorem of the surface.
#check @CarrierBurden.carrierRaw
#check @CarrierBurden.carrierRaw_two_mul
#check @CarrierBurden.carrierRaw_le_succ
#check @RecursorPayloadErasure.iiRecursorPayloadErasure
#check @RecursorPayloadErasure.iiRecursor_orienting_measure_counter_dominated
#check @RecursorPayloadErasure.iiRecursor_no_decisive_payload_sensitive
#check @WitnessChannelBoundary.witnessChannel_coordinate_of_OB
#check @WitnessChannelBoundary.ob_iff_directInterfaceEmpty
#check @UniversalDeficit.universal_witnessChannel_deficit
#check @CarrierAddressability.IndividuallyAddressable
#check @CarrierAddressability.individuallyAddressable_exceeds_fixed_budget
#check @CarrierAddressability.addressability_hypothesis_nonvacuous
#check @ForcedTrilemma.forced_output_trilemma_no_decisive_support
#check @ShannonFinite.H
#check @ShannonFinite.H_nonneg
#check @ShannonFinite.H_relabel_eq
#check @LicensedFactorisation.universal_confession_characterization
#check @LicensedFactorisation.all_existing_confession_routes_are_HEquivalent_to_canonical
#check @ShannonFinite.H_pointMass
#check @DiagonalEntropy.diagonal_entropy_eq
#check @DiagonalEntropy.H_pushforward_injective
#check @QueryInterface.query_confession_condEntropy_pos
#check @QueryInterface.query_confession_mi_pos
#check @SharpnessCounterexample.payloadErasure_hypothesis_necessary
#check @ConditionalEntropy.condEntropy_le_H_mixture
#check @GradedDeficit.gradedDeficit_monotone
#check @GradedDeficit.gradedDeficit_terminates
#check @CertFragmentWitness.cert_fragment_complement
#check @CertFragmentWitness.cert_fragment_nonvacuous
#check @UnivDeficitViaChar.univ_deficit_via_char_direct
#check @UnivDeficitViaChar.univ_deficit_via_char_recursor
#check @SemanticWitnessBridge.semanticBridge_OB
#check @SemanticWitnessBridge.semanticBridge_deficit_positive
#check @SemanticWitnessBridge.semanticBridge_cert_complement

-- Axiom audit (Gate R1 / R7): the trust surface of every release theorem.
#print axioms CarrierBurden.carrierRaw_two_mul
#print axioms RecursorPayloadErasure.iiRecursor_orienting_measure_counter_dominated
#print axioms RecursorPayloadErasure.iiRecursor_no_decisive_payload_sensitive
#print axioms WitnessChannelBoundary.witnessChannel_coordinate_of_OB
#print axioms UniversalDeficit.universal_witnessChannel_deficit
#print axioms CarrierAddressability.individuallyAddressable_exceeds_fixed_budget
#print axioms CarrierAddressability.addressability_hypothesis_nonvacuous
#print axioms ForcedTrilemma.forced_output_trilemma_no_decisive_support
#print axioms ShannonFinite.H_nonneg
#print axioms ShannonFinite.H_relabel_eq
#print axioms DiagonalEntropy.diagonal_entropy_eq
#print axioms QueryInterface.query_confession_condEntropy_pos
#print axioms SharpnessCounterexample.payloadErasure_hypothesis_necessary
#print axioms ConditionalEntropy.condEntropy_le_H_mixture
#print axioms GradedDeficit.gradedDeficit_monotone
#print axioms CertFragmentWitness.cert_fragment_complement
#print axioms CertFragmentWitness.cert_fragment_nonvacuous
#print axioms UnivDeficitViaChar.univ_deficit_via_char_direct
#print axioms SemanticWitnessBridge.semanticBridge_deficit_positive
#print axioms SemanticWitnessBridge.semanticBridge_cert_complement

-- T-Move 7: licensed-channel deficit / circular reference + participatory query
-- (general information-theory surface; the finance instantiation lives in the Boundary Premium Program).
#check @LicensedChannelDeficit.deficit
#check @LicensedChannelDeficit.deficit_nonneg
#check @LicensedChannelDeficit.circular_reference_zero_deficit
#check @LicensedChannelDeficit.positive_deficit_requires_exogeny
#check @LicensedChannelDeficit.deficit_witness_pos
#check @LicensedChannelDeficit.circular_reference_witness_zero
#check @ParticipatoryQuery.participationInfo
#check @ParticipatoryQuery.null_action_zero_correlation
#check @ParticipatoryQuery.participation_creates_correlation
#check @ParticipatoryQuery.effective_action_perturbs_object
#check @ParticipatoryQuery.resolution_arc
#check @ParticipatoryQuery.participation_witness_pos
#check @ParticipatoryQuery.null_witness_zero

#print axioms LicensedChannelDeficit.deficit_nonneg
#print axioms LicensedChannelDeficit.circular_reference_zero_deficit
#print axioms LicensedChannelDeficit.positive_deficit_requires_exogeny
#print axioms LicensedChannelDeficit.deficit_witness_pos
#print axioms LicensedChannelDeficit.circular_reference_witness_zero
#print axioms ParticipatoryQuery.null_action_zero_correlation
#print axioms ParticipatoryQuery.participation_creates_correlation
#print axioms ParticipatoryQuery.effective_action_perturbs_object
#print axioms ParticipatoryQuery.resolution_arc
#print axioms ParticipatoryQuery.participation_witness_pos
#print axioms ParticipatoryQuery.null_witness_zero

-- Boundary Propagation Program: propagation residual / lead / synchronization + first reactor
-- (general information-theory surface; the finance instantiation lives in the Boundary Propagation Program).
#check @PropagationResidual.propagationResidual
#check @PropagationResidual.lead
#check @PropagationResidual.residual_nonneg
#check @PropagationResidual.lead_nonneg
#check @PropagationResidual.residual_zero_of_measurable
#check @PropagationResidual.positive_residual_not_synchronized
#check @PropagationResidual.DiagonalEcho
#check @PropagationResidual.FirstReactor
#check @PropagationResidual.firstReactor_positive_and_open
#check @PropagationResidual.firstReactor_not_diagonalEcho
#check @PropagationResidual.residual_witness_zero
#check @PropagationResidual.lead_witness_pos

#print axioms PropagationResidual.residual_nonneg
#print axioms PropagationResidual.lead_nonneg
#print axioms PropagationResidual.residual_zero_of_measurable
#print axioms PropagationResidual.positive_residual_not_synchronized
#print axioms PropagationResidual.firstReactor_positive_and_open
#print axioms PropagationResidual.firstReactor_not_diagonalEcho
#print axioms PropagationResidual.residual_witness_zero
#print axioms PropagationResidual.lead_witness_pos

-- Distinction-Boundary bridge surface (T1-T6): the confluence axis read information-theoretically.
-- T5 memory⟺distinction⟺information; T3 diagonal-inert fusion; T6 axis-growth separation;
-- T4 eqW-diagonal echo vacuum; T2 confluence forced-output trilemma + false formal legitimacy;
-- T1 unified licensed-collapse deficit.
#check @MemoryDistinction.memory_distinction_information_equiv
#check @MemoryDistinction.memory_distinction_information_witness
#check @DiagonalInert.record_emission_iff_distinction
#check @DiagonalInert.diagonal_inert_trinity
#check @AxisGrowthSeparation.axis_growth_separation
#check @AxisGrowthSeparation.termination_marginal_unbounded
#check @EqWDiagonalDeficit.eqW_diagonal_echo_vacuum
#check @EqWDiagonalDeficit.eqW_diagonal_echo_vacuum_with_fork
#check @ConfluenceForcedTrilemma.confluence_forced_trilemma
#check @ConfluenceForcedTrilemma.diagonal_emission_is_false_formal_legitimacy
#check @LicensedCollapseDeficit.boundary_collapse_unified
#check @LicensedCollapseDeficit.confluence_collapse_matches_branch_entropy
#check @LicensedCollapseDeficit.confluence_collapse_bears_landauer_floor

#print axioms MemoryDistinction.memory_distinction_information_equiv
#print axioms MemoryDistinction.memory_distinction_information_witness
#print axioms DiagonalInert.record_emission_iff_distinction
#print axioms DiagonalInert.diagonal_inert_trinity
#print axioms AxisGrowthSeparation.axis_growth_separation
#print axioms AxisGrowthSeparation.termination_marginal_unbounded
#print axioms EqWDiagonalDeficit.eqW_diagonal_echo_vacuum_with_fork
#print axioms ConfluenceForcedTrilemma.confluence_forced_trilemma
#print axioms ConfluenceForcedTrilemma.diagonal_emission_is_false_formal_legitimacy
#print axioms LicensedCollapseDeficit.boundary_collapse_unified
#print axioms LicensedCollapseDeficit.confluence_collapse_matches_branch_entropy
#print axioms LicensedCollapseDeficit.confluence_collapse_bears_landauer_floor

end OperatorKO7.Test.InformationalIncompletenessReach
