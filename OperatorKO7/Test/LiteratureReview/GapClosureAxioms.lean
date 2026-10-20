import OperatorKO7.Meta.BoundaryObserver.ConservedRecording
import OperatorKO7.Meta.BoundaryObserver.CountableGibbsGeneral
import OperatorKO7.Meta.BoundaryObserver.ConditionalReset
import OperatorKO7.Meta.BoundaryObserver.FiniteReservoir
import OperatorKO7.Meta.BoundaryObserver.BellMemoryEquality
import OperatorKO7.Meta.BoundaryObserver.StoppedHorizonError
import OperatorKO7.Meta.BoundaryObserver.PurifiedFiberGeneralLaw
import OperatorKO7.Meta.BoundaryObserver.HaltingTerminalGap
import OperatorKO7.Meta.BoundaryObserver.ForcedVerdictEcho
import OperatorKO7.Meta.BoundaryObserver.RuinWalkInformation
import OperatorKO7.Meta.BoundaryObserver.SequentialRatioTest
import OperatorKO7.Meta.BoundaryObserver.ZenoLimit
import OperatorKO7.Meta.BoundaryObserver.PersistentGuardContext
import OperatorKO7.Meta.BoundaryObserver.EqualityRepair
import OperatorKO7.Meta.BoundaryObserver.PrimrecDefinability
import OperatorKO7.Meta.BoundaryObserver.SoundExtensionIncompleteness
import OperatorKO7.Meta.BoundaryObserver.EqualityRepairChecker
import OperatorKO7.Meta.BoundaryObserver.EqualityRepairGodel
import OperatorKO7.Meta.BoundaryObserver.CheckerGaps

/-! Axiom checks for the gap-closure modules of the Observation-Boundary Principle. -/

open OperatorKO7.Meta.BoundaryObserver

#check @ConservedRecording.wigner_araki_yanase
#print axioms ConservedRecording.wigner_araki_yanase
#check @ConservedRecording.wigner_araki_yanase_observable
#print axioms ConservedRecording.wigner_araki_yanase_observable
#check @ConservedRecording.wigner_araki_yanase_range
#print axioms ConservedRecording.wigner_araki_yanase_range
#check @CountableGibbsGeneral.gibbs_unique_maximum
#print axioms CountableGibbsGeneral.gibbs_unique_maximum
#check @CountableGibbsGeneral.law_properties
#print axioms CountableGibbsGeneral.law_properties
#check @CountableGibbsGeneral.burden_instance
#print axioms CountableGibbsGeneral.burden_instance
#check @CountableGibbsGeneral.linear_law
#print axioms CountableGibbsGeneral.linear_law
#check @CountableGibbsGeneral.linear_mean
#print axioms CountableGibbsGeneral.linear_mean
#check @CountableGibbsGeneral.linear_hypotheses
#print axioms CountableGibbsGeneral.linear_hypotheses
#check @CountableGibbsGeneral.logCost_hypotheses
#print axioms CountableGibbsGeneral.logCost_hypotheses
#check @CountableGibbsGeneral.logCost_partition_zeta
#print axioms CountableGibbsGeneral.logCost_partition_zeta
#check @CountableGibbsGeneral.logCost_law
#print axioms CountableGibbsGeneral.logCost_law
#check @ConditionalReset.condEntropy_eq_sum_entropy
#print axioms ConditionalReset.condEntropy_eq_sum_entropy
#check @ConditionalReset.condEntropy_chain
#print axioms ConditionalReset.condEntropy_chain
#check @ConditionalReset.condHeat_bound
#print axioms ConditionalReset.condHeat_bound
#check @ConditionalReset.condHeat_attains
#print axioms ConditionalReset.condHeat_attains
#check @ConditionalReset.condHeat_least_limit
#print axioms ConditionalReset.condHeat_least_limit
#check @ConditionalReset.condEntropy_eq_zero_iff
#print axioms ConditionalReset.condEntropy_eq_zero_iff
#check @ConditionalReset.condEntropy_eq_entropy_iff
#print axioms ConditionalReset.condEntropy_eq_entropy_iff
#check @FiniteReservoir.reservoir_entropy_gain
#print axioms FiniteReservoir.reservoir_entropy_gain
#check @FiniteReservoir.remainder_nonneg
#print axioms FiniteReservoir.remainder_nonneg
#check @FiniteReservoir.reservoir_remainder
#print axioms FiniteReservoir.reservoir_remainder
#check @FiniteReservoir.reservoir_quadratic
#print axioms FiniteReservoir.reservoir_quadratic
#check @FiniteReservoir.excess_le_of_parameter
#print axioms FiniteReservoir.excess_le_of_parameter
#check @FiniteReservoir.dimension_of_excess
#print axioms FiniteReservoir.dimension_of_excess
#check @FiniteReservoir.dimension_of_tolerance
#print axioms FiniteReservoir.dimension_of_tolerance
#check @FiniteReservoir.dimension_bound_tendsto
#print axioms FiniteReservoir.dimension_bound_tendsto
#check @FiniteReservoir.operation_dimension
#print axioms FiniteReservoir.operation_dimension
#check @FiniteReservoir.sum_excess_bound
#print axioms FiniteReservoir.sum_excess_bound
#check @FiniteReservoir.staircase_excess
#print axioms FiniteReservoir.staircase_excess
#check @FiniteReservoir.staircase_step_count
#print axioms FiniteReservoir.staircase_step_count
#check @FiniteReservoir.staircase_resources
#print axioms FiniteReservoir.staircase_resources
#check @BellMemoryEquality.entropy_of_sq_eq_smul
#print axioms BellMemoryEquality.entropy_of_sq_eq_smul
#check @BellMemoryEquality.entropy_pureState
#print axioms BellMemoryEquality.entropy_pureState
#check @BellMemoryEquality.condEntropy_pureState
#print axioms BellMemoryEquality.condEntropy_pureState
#check @BellMemoryEquality.condEntropy_basisRecord
#print axioms BellMemoryEquality.condEntropy_basisRecord
#check @BellMemoryEquality.one_div_card_le_maxOverlap
#print axioms BellMemoryEquality.one_div_card_le_maxOverlap
#check @BellMemoryEquality.maxOverlap_eq_iff
#print axioms BellMemoryEquality.maxOverlap_eq_iff
#check @BellMemoryEquality.memory_uncertainty
#print axioms BellMemoryEquality.memory_uncertainty
#check @BellMemoryEquality.hadamard_unitary
#print axioms BellMemoryEquality.hadamard_unitary
#check @BellMemoryEquality.pauli_memory_equality
#print axioms BellMemoryEquality.pauli_memory_equality
#check @StoppedHorizonError.horizonError_le
#print axioms StoppedHorizonError.horizonError_le
#check @StoppedHorizonError.horizonErrorAll_eq
#print axioms StoppedHorizonError.horizonErrorAll_eq
#check @StoppedHorizonError.activeError_le
#print axioms StoppedHorizonError.activeError_le
#check @StoppedHorizonError.fullError_le_horizonErrorAll
#print axioms StoppedHorizonError.fullError_le_horizonErrorAll
#check @PurifiedFiberGeneralLaw.recordProjection_weightedCopy
#print axioms PurifiedFiberGeneralLaw.recordProjection_weightedCopy
#check @PurifiedFiberGeneralLaw.bornMass_recordProjection_weightedCopy
#print axioms PurifiedFiberGeneralLaw.bornMass_recordProjection_weightedCopy
#check @PurifiedFiberGeneralLaw.marginal_weightedCopy
#print axioms PurifiedFiberGeneralLaw.marginal_weightedCopy
#check @PurifiedFiberGeneralLaw.entropy_branch
#print axioms PurifiedFiberGeneralLaw.entropy_branch
#check @PurifiedFiberGeneralLaw.expected_branch_entropy
#print axioms PurifiedFiberGeneralLaw.expected_branch_entropy
#check @PurifiedFiberGeneralLaw.recordProjection_fiberConstant
#print axioms PurifiedFiberGeneralLaw.recordProjection_fiberConstant
#check @PurifiedFiberGeneralLaw.recordObject_schmidt
#print axioms PurifiedFiberGeneralLaw.recordObject_schmidt
#check @PurifiedFiberGeneralLaw.schmidtVec_orthonormal
#print axioms PurifiedFiberGeneralLaw.schmidtVec_orthonormal
#check @PurifiedFiberGeneralLaw.marginal_recordObject
#print axioms PurifiedFiberGeneralLaw.marginal_recordObject
#check @PurifiedFiberGeneralLaw.entropy_recordObject
#print axioms PurifiedFiberGeneralLaw.entropy_recordObject
#check @PurifiedFiberGeneralLaw.mutualInformation_record
#print axioms PurifiedFiberGeneralLaw.mutualInformation_record
#check @HaltingTerminalGap.fair_entropy
#print axioms HaltingTerminalGap.fair_entropy
#check @HaltingTerminalGap.boundedRecord_rows_zero
#print axioms HaltingTerminalGap.boundedRecord_rows_zero
#check @HaltingTerminalGap.halting_terminal_gap
#print axioms HaltingTerminalGap.halting_terminal_gap
#check @ForcedVerdictEcho.licensed_verdict_needs_direct
#print axioms ForcedVerdictEcho.licensed_verdict_needs_direct
#check @ForcedVerdictEcho.echo_iff_orientationBoundary
#print axioms ForcedVerdictEcho.echo_iff_orientationBoundary
#check @ForcedVerdictEcho.licensed_null_at_boundary
#print axioms ForcedVerdictEcho.licensed_null_at_boundary
#check @ForcedVerdictEcho.raw_verdict_ffl_at_boundary
#print axioms ForcedVerdictEcho.raw_verdict_ffl_at_boundary
#check @ForcedVerdictEcho.forced_trichotomy
#print axioms ForcedVerdictEcho.forced_trichotomy
#check @ProtocolDynkin.protocol_dynkin
#print axioms ProtocolDynkin.protocol_dynkin
#check @ProtocolDynkin.activeBelow_eq_sum
#print axioms ProtocolDynkin.activeBelow_eq_sum
#check @ProtocolDynkin.expectedCost_unit
#print axioms ProtocolDynkin.expectedCost_unit
#check @ProtocolDynkin.activeMass_tendsto_zero_of_bounded
#print axioms ProtocolDynkin.activeMass_tendsto_zero_of_bounded
#check @RuinWalkInformation.ruinWalk_zero_information
#print axioms RuinWalkInformation.ruinWalk_zero_information
#check @RuinWalkInformation.pot_drift
#print axioms RuinWalkInformation.pot_drift
#check @RuinWalkInformation.activeBelow_le
#print axioms RuinWalkInformation.activeBelow_le
#check @RuinWalkInformation.ruinWalk_stops
#print axioms RuinWalkInformation.ruinWalk_stops
#check @RuinWalkInformation.expectedCost_le
#print axioms RuinWalkInformation.expectedCost_le
#check @RuinWalkInformation.expectedCost_tendsto
#print axioms RuinWalkInformation.expectedCost_tendsto
#check @RuinWalkInformation.expectedCost_unbounded
#print axioms RuinWalkInformation.expectedCost_unbounded
#check @SequentialRatioTest.wald_identity
#print axioms SequentialRatioTest.wald_identity
#check @SequentialRatioTest.wald_identity_false
#print axioms SequentialRatioTest.wald_identity_false
#check @SequentialRatioTest.kl_pos
#print axioms SequentialRatioTest.kl_pos
#check @SequentialRatioTest.activeBelow_true_le
#print axioms SequentialRatioTest.activeBelow_true_le
#check @SequentialRatioTest.activeBelow_false_le
#print axioms SequentialRatioTest.activeBelow_false_le
#check @SequentialRatioTest.sprt_stops
#print axioms SequentialRatioTest.sprt_stops
#check @SequentialRatioTest.likelihood_ratio
#print axioms SequentialRatioTest.likelihood_ratio
#check @SequentialRatioTest.error_false_le
#print axioms SequentialRatioTest.error_false_le
#check @SequentialRatioTest.error_true_le
#print axioms SequentialRatioTest.error_true_le
#check @SequentialRatioTest.kl_ge_neg_two_log_bc
#print axioms SequentialRatioTest.kl_ge_neg_two_log_bc
#check @SequentialRatioTest.neg_two_log_bc_ge
#print axioms SequentialRatioTest.neg_two_log_bc_ge
#check @SequentialRatioTest.biasStep_ge
#print axioms SequentialRatioTest.biasStep_ge
#check @SequentialRatioTest.biasRows_kl
#print axioms SequentialRatioTest.biasRows_kl
#check @SequentialRatioTest.biasRows_discrimination
#print axioms SequentialRatioTest.biasRows_discrimination
#check @SequentialRatioTest.biased_walk_test
#print axioms SequentialRatioTest.biased_walk_test
#check @ZenoLimit.norm_deph_le
#print axioms ZenoLimit.norm_deph_le
#check @ZenoLimit.deph_deph
#print axioms ZenoLimit.deph_deph
#check @ZenoLimit.deph_mul_block
#print axioms ZenoLimit.deph_mul_block
#check @ZenoLimit.deph_flow
#print axioms ZenoLimit.deph_flow
#check @ZenoLimit.norm_flow_le
#print axioms ZenoLimit.norm_flow_le
#check @ZenoLimit.flow_iterate
#print axioms ZenoLimit.flow_iterate
#check @ZenoLimit.hasDerivAt_flow
#print axioms ZenoLimit.hasDerivAt_flow
#check @ZenoLimit.iterate_sub_le
#print axioms ZenoLimit.iterate_sub_le
#check @ZenoLimit.zeno_step_estimate
#print axioms ZenoLimit.zeno_step_estimate
#check @ZenoLimit.zeno_limit
#print axioms ZenoLimit.zeno_limit
#check @ZenoLimit.zeno_tendsto
#print axioms ZenoLimit.zeno_tendsto
#check @PersistentGuardContext.newman_lemma
#print axioms PersistentGuardContext.newman_lemma
#check @PersistentGuardContext.diffLicense_iff_interior
#print axioms PersistentGuardContext.diffLicense_iff_interior
#check @PersistentGuardContext.diffInterior_forward
#print axioms PersistentGuardContext.diffInterior_forward
#check @PersistentGuardContext.le_diffInterior
#print axioms PersistentGuardContext.le_diffInterior
#check @PersistentGuardContext.diffLicense_of_starL
#print axioms PersistentGuardContext.diffLicense_of_starL
#check @PersistentGuardContext.diffLicense_of_starR
#print axioms PersistentGuardContext.diffLicense_of_starR
#check @PersistentGuardContext.not_diffLicense_of_join
#print axioms PersistentGuardContext.not_diffLicense_of_join
#check @PersistentGuardContext.diffLicense_void_delta_void
#print axioms PersistentGuardContext.diffLicense_void_delta_void
#check @PersistentGuardContext.pstepCtx_sub_eqGuardedCtx
#print axioms PersistentGuardContext.pstepCtx_sub_eqGuardedCtx
#check @PersistentGuardContext.pstepCtx_sub_stepCtxFull
#print axioms PersistentGuardContext.pstepCtx_sub_stepCtxFull
#check @PersistentGuardContext.pstepCtx_wf
#print axioms PersistentGuardContext.pstepCtx_wf
#check @PersistentGuardContext.pLocalJoin_all
#print axioms PersistentGuardContext.pLocalJoin_all
#check @PersistentGuardContext.pstepCtx_confluent
#print axioms PersistentGuardContext.pstepCtx_confluent
#check @PersistentGuardContext.repaired_terminates_and_confluent
#print axioms PersistentGuardContext.repaired_terminates_and_confluent
#check @PersistentGuardContext.witness_not_licensed
#print axioms PersistentGuardContext.witness_not_licensed
#check @PersistentGuardContext.witness_unique_normal_form
#print axioms PersistentGuardContext.witness_unique_normal_form
#check @EqualityRepair.check_to_checkE
#print axioms EqualityRepair.check_to_checkE
#check @EqualityRepair.provable_to_provableE
#print axioms EqualityRepair.provable_to_provableE
#check @EqualityRepair.eval_isAxiomE
#print axioms EqualityRepair.eval_isAxiomE
#check @EqualityRepair.checkE_sound
#print axioms EqualityRepair.checkE_sound
#check @EqualityRepair.provableE_consistent
#print axioms EqualityRepair.provableE_consistent
#check @EqualityRepair.pE_numAdd
#print axioms EqualityRepair.pE_numAdd
#check @EqualityRepair.pE_numMul
#print axioms EqualityRepair.pE_numMul
#check @EqualityRepair.pE_closed_numeral
#print axioms EqualityRepair.pE_closed_numeral
#check @EqualityRepair.closed_eq_complete
#print axioms EqualityRepair.closed_eq_complete
#check @EqualityRepair.closed_eq_iff
#print axioms EqualityRepair.closed_eq_iff
#check @EqualityRepair.repaired_example
#print axioms EqualityRepair.repaired_example
#check @PrimrecDefinability.eval_PairF
#print axioms PrimrecDefinability.eval_PairF
#check @PrimrecDefinability.rec_eq_precSeq
#print axioms PrimrecDefinability.rec_eq_precSeq
#check @PrimrecDefinability.precForm_defines
#print axioms PrimrecDefinability.precForm_defines
#check @PrimrecDefinability.definable_of_primrec
#print axioms PrimrecDefinability.definable_of_primrec
#check @SoundExtensionIncompleteness.prfInd_primrec
#print axioms SoundExtensionIncompleteness.prfInd_primrec
#check @SoundExtensionIncompleteness.bewForm_spec
#print axioms SoundExtensionIncompleteness.bewForm_spec
#check @SoundExtensionIncompleteness.sound_primrec_incompleteness
#print axioms SoundExtensionIncompleteness.sound_primrec_incompleteness
#check @EqualityRepairChecker.isAxiomCodeEB_primrec
#print axioms EqualityRepairChecker.isAxiomCodeEB_primrec
#check @EqualityRepairChecker.isAxiomCodeEB_encode
#print axioms EqualityRepairChecker.isAxiomCodeEB_encode
#check @EqualityRepairChecker.isProofCodeCB_sound
#print axioms EqualityRepairChecker.isProofCodeCB_sound
#check @EqualityRepairChecker.isProofCodeCB_primrec
#print axioms EqualityRepairChecker.isProofCodeCB_primrec
#check @EqualityRepairChecker.checkProofCodeE_encode
#print axioms EqualityRepairChecker.checkProofCodeE_encode
#check @EqualityRepairChecker.checkProofCodeE_primrec
#print axioms EqualityRepairChecker.checkProofCodeE_primrec
#check @EqualityRepairChecker.proofRelE_primrec
#print axioms EqualityRepairChecker.proofRelE_primrec
#check @EqualityRepairChecker.exists_proofRelE_iff
#print axioms EqualityRepairChecker.exists_proofRelE_iff
#check @EqualityRepairGodel.equality_repair_godel_sentence
#print axioms EqualityRepairGodel.equality_repair_godel_sentence
#check @EqualityRepairGodel.godel_equality_repair
#print axioms EqualityRepairGodel.godel_equality_repair
#check @EqualityRepairGodel.gammaE_spec
#print axioms EqualityRepairGodel.gammaE_spec
#check @EqualityRepairGodel.gammaE_collision
#print axioms EqualityRepairGodel.gammaE_collision
#check @EqualityRepairGodel.gammaE_side_symbol_iff
#print axioms EqualityRepairGodel.gammaE_side_symbol_iff
#check @EqualityRepairGodel.exists_bewE
#print axioms EqualityRepairGodel.exists_bewE
#check @EqualityRepairGodel.consistency_collision_E
#print axioms EqualityRepairGodel.consistency_collision_E
#check @EqualityRepairGodel.godel_equality_repair_corollary
#print axioms EqualityRepairGodel.godel_equality_repair_corollary
#check @CheckerGaps.evalAlt_subst_closed
#print axioms CheckerGaps.evalAlt_subst_closed
#check @CheckerGaps.evalFormIn_subst_free
#print axioms CheckerGaps.evalFormIn_subst_free
#check @CheckerGaps.evalAlt_inductionAxiom
#print axioms CheckerGaps.evalAlt_inductionAxiom
#check @CheckerGaps.check_sound_alt
#print axioms CheckerGaps.check_sound_alt
#check @CheckerGaps.base_checker_equation_gap
#print axioms CheckerGaps.base_checker_equation_gap
#check @CheckerGaps.evalNeg_subst_closed
#print axioms CheckerGaps.evalNeg_subst_closed
#check @CheckerGaps.evalNeg_isAxiomE
#print axioms CheckerGaps.evalNeg_isAxiomE
#check @CheckerGaps.checkE_sound_neg
#print axioms CheckerGaps.checkE_sound_neg
#check @CheckerGaps.evalNeg_inductionAxiom
#print axioms CheckerGaps.evalNeg_inductionAxiom
#check @CheckerGaps.repaired_checker_negation_gap
#print axioms CheckerGaps.repaired_checker_negation_gap
