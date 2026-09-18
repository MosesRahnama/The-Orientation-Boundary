import OperatorKO7.Meta.Recursor.MassProfileIdentity
import OperatorKO7.Meta.Recursor.NonvacuousClosure
import OperatorKO7.Meta.Recursor.TerminalDecoderScope
import OperatorKO7.Meta.ReverseMath.SizeChangeSoundness
import OperatorKO7.Meta.LCELBoundaryReimportRepair
import OperatorKO7.Meta.RecordEmissionDynamic
import OperatorKO7.Meta.SchemaExplicitDescriptionGap
import OperatorKO7.Meta.ArtsGiesl_ProofLengthBySize
import OperatorKO7.Meta.BoundaryGeneral.ProjectionSensitivityAndProvenance

/-!
# Reach gate for the gap-closure modules

Pins every headline theorem introduced to close the review findings, and audits the axiom
dependency of each. Every entry below must report a subset of the baseline whitelist
`{propext, Classical.choice, Quot.sound}`.
-/

set_option autoImplicit false

namespace OperatorKO7.Test.GapClosureReach

open OperatorKO7.Meta.Recursor.MassProfileIdentity
open OperatorKO7.Meta.Recursor.NonvacuousClosure
open OperatorKO7.Meta.Recursor.TerminalDecoderScope
open OperatorKO7.ReverseMath.SizeChangeSoundness
open OperatorKO7.Meta.LCELBoundaryReimportRepair
open OperatorKO7.Meta.RecordEmissionDynamic
open OperatorKO7.Meta.SchemaExplicitDescriptionGap
open OperatorKO7.Meta.ArtsGieslProofLengthBySize
open OperatorKO7.Meta.BoundaryGeneral.ProjectionSensitivityAndProvenance

-- B3: pointwise mass-profile identity and the separation-failure theorem.
#print axioms recursorOrbit_selfEmbeddingOrbit_massProfile_pointwise_eq
#print axioms massProfileObserver_cannot_separate_recursorOrbit_from_selfEmbeddingOrbit
#print axioms selfEmbeddingStep_admits_no_strictlyDecreasing_natMeasure
#print axioms mergeChainOrbit_massProfile_never_eq_recursorOrbit
#print axioms descentVerdict_pointwise_eq_on_recursorOrbit_and_selfEmbeddingOrbit

-- B2: the LCEL clause collision and the repaired annotated schema.
#print axioms boundary_and_reimport_overlap_is_impossible
#print axioms godelShaped_violates_conservativity_clause
#print axioms godelShaped_satisfies_annotated_clauses
#print axioms annotated_clauses_strictly_weaker_than_conservativity

-- B1: size-change soundness and the extracted dependency pair.
#print axioms sizeChangeGraph_has_no_infinite_call_chain
#print axioms sizeChangeGraph_boundedSN
#print axioms sizeChangeGraph_wellFounded
#print axioms dupDP_boundedSN
#print axioms dupDPStep_wellFounded
#print axioms dupDPProjection_surjective

-- M1, M2, M3: non-vacuous closure forms.
#print axioms massProfileLicensedQuotient_separates
#print axioms massProfileLicensedQuotient_identifies_recursor_and_circular
#print axioms orbit_isomorphism_does_not_transport_termination
#print axioms information_equivalence_for_every_functional
#print axioms slopeFunctional_is_not_constant_on_linearGrowth

-- M5: the dynamic record-emission bridge.
#print axioms recordStep_canonicalStage_succ
#print axioms canonicalStage_carries_frame_and_active_generator_positions
#print axioms every_positive_stage_duplicates_the_generator

-- M9: terminal-decoder scope and the sort separation.
#print axioms schemaTerm_base_is_never_frame_headed
#print axioms decodeRecord_isSome_on_canonical_positive_depth
#print axioms unsortedTerminalRecord_depth_not_recoverable

-- M10: the explicit-description gap threshold.
#print axioms explicitDescription_gap_fails_at_zero
#print axioms explicitDescription_gap_positive
#print axioms explicitDescription_gap_threshold_is_attained

-- M6: proof length by rule size.
#print axioms agProofLength_le_of_nonempty
#print axioms constructionCost_unbounded_in_ruleSize
#print axioms agProofLength_recursor_closed_form

-- M7, M13, M14: determination, staticity, provenance.
#print axioms statements_not_determined_by_reversible_layer_lie_outside_base_derivability
#print axioms wrapperParity_is_not_determined_by_reversible_layer
#print axioms static_of_stepInvariant_license
#print axioms stepInvariance_hypothesis_is_load_bearing
#print axioms provenance_does_not_entail_license
#print axioms endogenous_provenance_collapse

end OperatorKO7.Test.GapClosureReach
