import OperatorKO7.Meta.BoundaryGeneral

/-!
# Reach test: boundary-general cross-paper packet

Exercises every public theorem of the mechanized boundary-general theories so that the paper-facing
surface is reachable from the root and cannot rot. Each `#check` forces the cited declaration into
the import closure with its full type.
-/

set_option autoImplicit false

namespace OperatorKO7.Test.BoundaryGeneralReach

open OperatorKO7.Meta.BoundaryGeneral

-- Theory II: provenance is not license
#check @ProvenanceLicense.provenance_not_license
#check @ProvenanceLicense.unlicensed_example

-- Theory III: whole-term indistinguishability
#check @WholeTermIndistinguishability.whole_term_indistinguishable
#check @WholeTermIndistinguishability.projection_escape

-- Theory IV: costed confession
#check @CostedConfession.composition_le
#check @CostedConfession.composition_eq_of_disjoint
#check @CostedConfession.canonical_lower_bound

-- Theory V: universality gate
#check @UniversalityGate.missing_row_failure
#check @UniversalityGate.ugate_fails_example

-- Theory VI: payload stress
#check @PayloadStress.two_mul_cumulativeCarrier
#check @PayloadStress.cumulativeCarrier_unbounded
#check @PayloadStress.stress_ratio_unbounded

-- Theory VII: C4 classifier
#check @C4Classifier.recursor_is_interfaceInexpr
#check @C4Classifier.externalMeta_classified

-- Theory VIII: witness-first gate
#check @WitnessFirst.provenance_without_license_rejected
#check @WitnessFirst.carrier_blind_projection_rejected

-- Theory IX: endogenous provenance
#check @EndogenousProvenance.provenance_collapse_exogenous_zero
#check @EndogenousProvenance.lived_exogenous_zero

-- Theory X: diagonal mirror
#check @DiagonalMirror.mirror_cost_separation
#check @DiagonalMirror.ko7_mirror_cost_separation

-- Theory XI: distinction-record primitive
#check @DistinctionRecord.equality_record_inert
#check @DistinctionRecord.ko7_equality_record_inert

-- Theory XII: grammar-closure barrier
#check @DirectMeasureGrammarClosure.eval_payloadMonotone
#check @DirectMeasureGrammarClosure.grammar_measure_blocked
#check @DirectMeasureGrammarClosure.payloadEffective_payloadUnbounded
#check @DirectMeasureGrammarClosure.payloadEffective_measures_blocked
#check @DirectMeasureGrammarClosure.positiveFloor?_eq_true_iff
#check @DirectMeasureGrammarClosure.payloadEffective?_sound
#check @DirectMeasureGrammarClosure.payloadEffective?_eq_true_iff
#check @DirectMeasureGrammarClosure.payloadEffective?_blocked
#check @DirectMeasureGrammarClosure.payloadEffective_orientation_boundary
#check @DirectMeasureGrammarClosure.zero_smul_payload_not_payloadEffective
#check @DirectMeasureGrammarClosure.orientation_boundary_grammar
#check @DirectMeasureGrammarClosure.orients_implies_counterStrict
#check @DirectMeasureGrammarClosure.payloadBlind_and_counterStrict_implies_orients
#check @DirectMeasureGrammarClosure.orients_iff_payloadBlind_and_counterStrict
#check @DirectMeasureGrammarClosure.counterAdmissible_orients_iff_payloadBlind
#check @DirectMeasureGrammarClosure.counter_is_counterAdmissible
#check @DirectMeasureGrammarClosure.counter_orients_via_exact_boundary
#check @DirectMeasureGrammarClosure.const_zero_not_orients

-- Theory XIV: wavepacket core
#check @Wavepacket.born_density
#check @Wavepacket.mixture_not_amplitude

end OperatorKO7.Test.BoundaryGeneralReach
