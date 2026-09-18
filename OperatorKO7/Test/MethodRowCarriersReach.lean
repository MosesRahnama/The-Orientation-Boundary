import OperatorKO7.Meta.Methods.PathOrderRows
import OperatorKO7.Meta.Methods.AlgebraicInterpretationRows
import OperatorKO7.Meta.Methods.NaturalMatrixInterpretationRows
import OperatorKO7.Meta.Methods.OrderedMatrixInterpretationRows
import OperatorKO7.Meta.Methods.SemanticStructuralRows
import OperatorKO7.Meta.Methods.DependencyPairTypedRows
import OperatorKO7.Meta.Methods.AdmittanceInapplicabilityRows
import OperatorKO7.Meta.Methods.SubstrateChangeRows
import OperatorKO7.Meta.RDRSCoverageEvidenceLedger

/-!
Reach gate for the ORIENTATION method-interface modules. Every local anchor carries a paired
`#check @` and `#print axioms`. The historical split remains visible as a compatibility receipt;
the native-semantic split below is the Dispatch ORIENTATION 76/0 author candidate.
-/

open OperatorKO7.Methods.PathOrderRows
open OperatorKO7.Methods.AlgebraicInterpretationRows
open OperatorKO7.Methods.NaturalMatrixInterpretationRows
open OperatorKO7.Methods.OrderedMatrixInterpretationRows
open OperatorKO7.Methods.SemanticStructuralRows
open OperatorKO7.Methods.DependencyPairTypedRows
open OperatorKO7.Methods.AdmittanceInapplicabilityRows
open OperatorKO7.Methods.SubstrateChangeRows
open OperatorKO7.RDRSCoverageLedger.Evidence

/-! ## Historical adapter split and native-semantic closure -/

#check @theoremBackedRows_count
#print axioms theoremBackedRows_count
#check @curatedRows_count
#print axioms curatedRows_count

theorem methodRowCarriers_legacy_adapter_split :
    theoremBackedRows.length = 16 ∧ curatedRows.length = 60 :=
  ⟨theoremBackedRows_count, curatedRows_count⟩

#check @methodRowCarriers_legacy_adapter_split
#print axioms methodRowCarriers_legacy_adapter_split

/-- Backward-compatible name retained for prior audit references. -/
theorem methodRowCarriers_current_public_split :
    theoremBackedRows.length = 16 ∧ curatedRows.length = 60 :=
  methodRowCarriers_legacy_adapter_split

#check @methodRowCarriers_current_public_split
#print axioms methodRowCarriers_current_public_split

#check @OperatorKO7.Methods.OrientationClosure.NativeSemanticCoverage.missingNativeRows_count
#print axioms OperatorKO7.Methods.OrientationClosure.NativeSemanticCoverage.missingNativeRows_count
#check @OperatorKO7.Methods.OrientationClosure.NativeSemanticCoverage.missing_native_coverage_closed
#print axioms OperatorKO7.Methods.OrientationClosure.NativeSemanticCoverage.missing_native_coverage_closed
#check @OperatorKO7.Methods.OrientationClosure.ResearchPackages.orientation_research_packages_closed
#print axioms OperatorKO7.Methods.OrientationClosure.ResearchPackages.orientation_research_packages_closed
#check @OperatorKO7.RDRSCoverageLedger.Evidence.Native.nativeTheoremBackedRows_count
#print axioms OperatorKO7.RDRSCoverageLedger.Evidence.Native.nativeTheoremBackedRows_count
#check @OperatorKO7.RDRSCoverageLedger.Evidence.Native.nativeCuratedRows_count
#print axioms OperatorKO7.RDRSCoverageLedger.Evidence.Native.nativeCuratedRows_count
#check @OperatorKO7.RDRSCoverageLedger.Evidence.Native.rdrs_native_coverage_evidence_ledger_closed
#print axioms OperatorKO7.RDRSCoverageLedger.Evidence.Native.rdrs_native_coverage_evidence_ledger_closed

theorem methodRowCarriers_native_semantic_split :
    OperatorKO7.RDRSCoverageLedger.Evidence.Native.nativeTheoremBackedRows.length = 76 ∧
      OperatorKO7.RDRSCoverageLedger.Evidence.Native.nativeCuratedRows.length = 0 :=
  ⟨OperatorKO7.RDRSCoverageLedger.Evidence.Native.nativeTheoremBackedRows_count,
    OperatorKO7.RDRSCoverageLedger.Evidence.Native.nativeCuratedRows_count⟩

#check @methodRowCarriers_native_semantic_split
#print axioms methodRowCarriers_native_semantic_split

/-! ## E1: path orders -/

#check @kboWithStatus_row_anchor
#print axioms kboWithStatus_row_anchor
#check @generalizedKBO_row_anchor
#print axioms generalizedKBO_row_anchor
#check @acKBO_row_anchor
#print axioms acKBO_row_anchor
#check @transfiniteKBO_row_anchor
#print axioms transfiniteKBO_row_anchor
#check @lambdaFreeKBO_row_anchor
#print axioms lambdaFreeKBO_row_anchor
#check @polynomialKBO_row_anchor
#print axioms polynomialKBO_row_anchor
#check @acRPO_row_anchor
#print axioms acRPO_row_anchor
#check @EquationalPathOrderCertificate
#print axioms EquationalPathOrderCertificate
#check @TraceAppACOne
#print axioms TraceAppACOne
#check @W_traceAppACOne
#print axioms W_traceAppACOne
#check @TraceAppAC
#print axioms TraceAppAC
#check @W_traceAppAC
#print axioms W_traceAppAC
#check @traceAppAC_nontrivial
#print axioms traceAppAC_nontrivial
#check @ko7AppACReductionOrder
#print axioms ko7AppACReductionOrder
#check @ko7AppACReductionOrder_nontrivial
#print axioms ko7AppACReductionOrder_nontrivial
#check @ko7EmptyEquationalRPO
#print axioms ko7EmptyEquationalRPO
#check @ko7EmptyEquationalRPO_equiv_iff_eq
#print axioms ko7EmptyEquationalRPO_equiv_iff_eq
#check @lpoOrder_KO7_wellFounded
#print axioms lpoOrder_KO7_wellFounded
#check @rpoModuloPermutation_row_anchor
#print axioms rpoModuloPermutation_row_anchor
#check @PermutationRPOCertificate
#print axioms PermutationRPOCertificate
#check @permuteApp
#print axioms permuteApp
#check @identityPermutationStatus
#print axioms identityPermutationStatus
#check @swapAppPermutationStatus
#print axioms swapAppPermutationStatus
#check @swapAppPermutationStatus_moves_zero
#print axioms swapAppPermutationStatus_moves_zero
#check @swapAppPermutationStatus_nonidentity
#print axioms swapAppPermutationStatus_nonidentity
#check @permuteApp_swap
#print axioms permuteApp_swap
#check @ko7PermutationRPO
#print axioms ko7PermutationRPO
#check @popStarFamily_row_anchor
#print axioms popStarFamily_row_anchor
#check @simpleTerminationOrderType_row_anchor
#print axioms simpleTerminationOrderType_row_anchor
#check @cichonSlowGrowing_row_anchor
#print axioms cichonSlowGrowing_row_anchor
#check @weightedSizeOrder
#print axioms weightedSizeOrder
#check @weightedSizeOrder_nondegenerate
#print axioms weightedSizeOrder_nondegenerate
#check @countVar_acRearrange
#print axioms countVar_acRearrange
#check @countVar_acRearrange_star
#print axioms countVar_acRearrange_star
#check @countVarApp_curry
#print axioms countVarApp_curry
#check @appTermSize
#print axioms appTermSize
#check @lambdaFreeKBOWitness_nondegenerate
#print axioms lambdaFreeKBOWitness_nondegenerate
#check @rootSafeCount
#print axioms rootSafeCount
#check @PredicativeSafeLinear
#print axioms PredicativeSafeLinear
#check @rootSafeCount_dupSrc_s
#print axioms rootSafeCount_dupSrc_s
#check @rootSafeCount_dupTgt_s
#print axioms rootSafeCount_dupTgt_s
#check @dup_rule_not_predicative_safe_linear
#print axioms dup_rule_not_predicative_safe_linear
#check @KO7POPStarCertificate
#print axioms KO7POPStarCertificate
#check @no_ko7POPStarCertificate
#print axioms no_ko7POPStarCertificate
#check @stermSize_acRearrange_star
#print axioms stermSize_acRearrange_star

/-! ## E2: algebraic interpretations -/

#check @linearPolyQ_row_anchor
#print axioms linearPolyQ_row_anchor
#check @linearPolyR_row_anchor
#print axioms linearPolyR_row_anchor
#check @TruncatedAffineMeasure
#print axioms TruncatedAffineMeasure
#check @truncatedAffine_wrap_debt_bound
#print axioms truncatedAffine_wrap_debt_bound
#check @truncatedAffine_succIter_ge
#print axioms truncatedAffine_succIter_ge
#check @negativeCoefficientPolynomial_row_anchor
#print axioms negativeCoefficientPolynomial_row_anchor
#check @maxPolynomial_row_anchor
#print axioms maxPolynomial_row_anchor
#check @nonlinearHigherDegreePolynomial_row_anchor
#print axioms nonlinearHigherDegreePolynomial_row_anchor
#check @multilinearInterpretation_row_anchor
#print axioms multilinearInterpretation_row_anchor
#check @matrixNScalarProjection_row_anchor
#print axioms matrixNScalarProjection_row_anchor
#check @matrixQRScalarProjection_row_anchor
#print axioms matrixQRScalarProjection_row_anchor
#check @arcticScalarProjection_row_anchor
#print axioms arcticScalarProjection_row_anchor
#check @tropicalScalarProjection_row_anchor
#print axioms tropicalScalarProjection_row_anchor
#check @triangularMatrix_row_anchor
#print axioms triangularMatrix_row_anchor
#check @crossCoupledTupleEval
#print axioms crossCoupledTupleEval
#check @crossCoupledTupleEval_orients
#print axioms crossCoupledTupleEval_orients
#check @tupleInterpretationStrictS_row_anchor
#print axioms tupleInterpretationStrictS_row_anchor
#check @crossCoupledTupleEval_not_affine_first_component
#print axioms crossCoupledTupleEval_not_affine_first_component
#check @tupleInterpretationStrictS_exact_boundary
#print axioms tupleInterpretationStrictS_exact_boundary
#check @higherOrderTupleInterpretation_row_anchor
#print axioms higherOrderTupleInterpretation_row_anchor
#check @HigherOrderTupleRestriction.eval_restriction_first
#print axioms HigherOrderTupleRestriction.eval_restriction_first
#check @strictMonotoneAlgebraArchimedean_row_anchor
#print axioms strictMonotoneAlgebraArchimedean_row_anchor
#check @archimedean_unbounded
#print axioms archimedean_unbounded

/-! ## E3: semantic and structural -/

#check @extendedMonotoneAlgebra_row_anchor
#print axioms extendedMonotoneAlgebra_row_anchor
#check @finiteModelTermination_row_anchor
#print axioms finiteModelTermination_row_anchor
#check @finiteModelInterpretation_impossible
#print axioms finiteModelInterpretation_impossible
#check @matchBounds_row_anchor
#print axioms matchBounds_row_anchor
#check @raiseConsistencyMatchBounds_row_anchor
#print axioms raiseConsistencyMatchBounds_row_anchor
#check @RaiseConsistentMatchBoundCertificate
#print axioms RaiseConsistentMatchBoundCertificate
#check @no_raiseConsistentMatchBoundCertificate
#print axioms no_raiseConsistentMatchBoundCertificate
#check @leftLinearMatchBounds_row_anchor
#print axioms leftLinearMatchBounds_row_anchor
#check @semanticLabeling_row_anchor
#print axioms semanticLabeling_row_anchor
#check @predictiveLabeling_row_anchor
#print axioms predictiveLabeling_row_anchor
#check @predictiveLabelling
#print axioms predictiveLabelling
#check @rootLabeling_row_anchor
#print axioms rootLabeling_row_anchor
#check @selfLabelingEquational_row_anchor
#print axioms selfLabelingEquational_row_anchor
#check @selfLabelling
#print axioms selfLabelling
#check @selfLabelling_dup_root_labels_ne
#print axioms selfLabelling_dup_root_labels_ne
#check @categoricalToposTermination_row_anchor
#print axioms categoricalToposTermination_row_anchor
#check @RelationalCategoryCarrier
#print axioms RelationalCategoryCarrier
#check @stepStar_W_le
#print axioms stepStar_W_le
#check @stepStar_W_lt_of_ne
#print axioms stepStar_W_lt_of_ne
#check @ko7RelationalCategory
#print axioms ko7RelationalCategory
#check @relationalCategory_contains_equality_fork
#print axioms relationalCategory_contains_equality_fork
#check @deterministic_graph_obstruction_not_categorical_obstruction
#print axioms deterministic_graph_obstruction_not_categorical_obstruction
#check @no_deterministicGraphTransport
#print axioms no_deterministicGraphTransport
#check @forwardClosures_row_anchor
#print axioms forwardClosures_row_anchor
#check @quasiDecreasingness_row_anchor
#print axioms quasiDecreasingness_row_anchor
#check @abstractQuasiDecreasing_noConditions_iff
#print axioms abstractQuasiDecreasing_noConditions_iff
#check @no_linear_complexity_certificate
#print axioms no_linear_complexity_certificate
#check @labelling_preserves_duplication
#print axioms labelling_preserves_duplication
#check @erasureFactoredVariableCondition_refuses
#print axioms erasureFactoredVariableCondition_refuses
#check @rootLabelGt_wellFounded
#print axioms rootLabelGt_wellFounded
#check @rootLabelGt_transitive
#print axioms rootLabelGt_transitive
#check @constructorRootLabelling_orients_duplication
#print axioms constructorRootLabelling_orients_duplication
#check @constructorRootLabelling_not_erasureFactored
#print axioms constructorRootLabelling_not_erasureFactored
#check @SuccContextCompatible
#print axioms SuccContextCompatible
#check @rootLabelGt_not_succContextCompatible
#print axioms rootLabelGt_not_succContextCompatible
#check @semanticLabeling_exact_boundary
#print axioms semanticLabeling_exact_boundary
#check @step_not_functional
#print axioms step_not_functional
#check @categoricalToposRecord
#print axioms categoricalToposRecord
#check @dup_not_rightLinear
#print axioms dup_not_rightLinear

/-! ## E4: dependency pairs and typed transformations -/

#check @ContextSensitiveStep
#print axioms ContextSensitiveStep
#check @contextSensitiveStep_sub_stepCtxFull
#print axioms contextSensitiveStep_sub_stepCtxFull
#check @contextSensitiveStep_wellFounded
#print axioms contextSensitiveStep_wellFounded
#check @counterOnly_delta_active
#print axioms counterOnly_delta_active
#check @counterOnly_recur_counter_active
#print axioms counterOnly_recur_counter_active
#check @counterOnly_recur_base_frozen
#print axioms counterOnly_recur_base_frozen
#check @counterOnly_recur_payload_frozen
#print axioms counterOnly_recur_payload_frozen
#check @counterOnly_wrap_payload_frozen
#print axioms counterOnly_wrap_payload_frozen
#check @counterOnly_wrap_continuation_active
#print axioms counterOnly_wrap_continuation_active
#check @counterOnly_contextSensitiveStep_cases
#print axioms counterOnly_contextSensitiveStep_cases
#check @TwoDDimension
#print axioms TwoDDimension
#check @KO7TwoDDP
#print axioms KO7TwoDDP
#check @ko7TwoDDP_dependency_iff
#print axioms ko7TwoDDP_dependency_iff
#check @ko7TwoDDP_condition_empty
#print axioms ko7TwoDDP_condition_empty
#check @KO7TwoDDPAny
#print axioms KO7TwoDDPAny
#check @ko7TwoDDPAny_iff_DPPair
#print axioms ko7TwoDDPAny_iff_DPPair
#check @wf_KO7TwoDDPAnyRev
#print axioms wf_KO7TwoDDPAnyRev
#check @ConditionsHold
#print axioms ConditionsHold
#check @KO7ConditionalOperationalStep
#print axioms KO7ConditionalOperationalStep
#check @ko7ConditionalOperationalStep_iff_step
#print axioms ko7ConditionalOperationalStep_iff_step
#check @ko7ConditionalOperationalStep_eq_step
#print axioms ko7ConditionalOperationalStep_eq_step
#check @ko7ConditionalOperationalTermination_iff
#print axioms ko7ConditionalOperationalTermination_iff
#check @ko7ConditionalOperationalTermination
#print axioms ko7ConditionalOperationalTermination
#check @ConstrainedDPPair
#print axioms ConstrainedDPPair
#check @constrainedDPPair_iff_DPPair
#print axioms constrainedDPPair_iff_DPPair
#check @constrainedDPPair_decreases
#print axioms constrainedDPPair_decreases
#check @wf_ConstrainedDPPairRev
#print axioms wf_ConstrainedDPPairRev
#check @encodeTraceHO
#print axioms encodeTraceHO
#check @decodeTraceHO
#print axioms decodeTraceHO
#check @decodeTraceHO_encodeTraceHO
#print axioms decodeTraceHO_encodeTraceHO
#check @encodeTraceHO_injective
#print axioms encodeTraceHO_injective
#check @encodeTraceHO_closed
#print axioms encodeTraceHO_closed
#check @higherOrderCounter
#print axioms higherOrderCounter
#check @higherOrderCounter_encodeTraceHO
#print axioms higherOrderCounter_encodeTraceHO
#check @HigherOrderConstrainedDPPair
#print axioms HigherOrderConstrainedDPPair
#check @higherOrderConstrainedDPPair_on_image_iff
#print axioms higherOrderConstrainedDPPair_on_image_iff
#check @higherOrderConstrainedDPPair_decreases
#print axioms higherOrderConstrainedDPPair_decreases
#check @HigherOrderConstraint
#print axioms HigherOrderConstraint
#check @higherOrderConstrainedDPPair_source_constrained
#print axioms higherOrderConstrainedDPPair_source_constrained
#check @wf_HigherOrderConstrainedDPPairRev
#print axioms wf_HigherOrderConstrainedDPPairRev

#check @dpProcessorClassification_row_anchor
#print axioms dpProcessorClassification_row_anchor
#check @dpArgumentFiltering_row_anchor
#print axioms dpArgumentFiltering_row_anchor
#check @scaledCounterReductionPair
#print axioms scaledCounterReductionPair
#check @scaledCounterReductionPair_probe
#print axioms scaledCounterReductionPair_probe
#check @scaledCounterReductionPair_rank_injective
#print axioms scaledCounterReductionPair_rank_injective
#check @dpReductionPairProcessor_row_anchor
#print axioms dpReductionPairProcessor_row_anchor
#check @dpNeutralProcessors_row_anchor
#print axioms dpNeutralProcessors_row_anchor
#check @dpReductionTriples_row_anchor
#print axioms dpReductionTriples_row_anchor
#check @formativeRules_row_anchor
#print axioms formativeRules_row_anchor
#check @FormativePairTag
#print axioms FormativePairTag
#check @FormativePair
#print axioms FormativePair
#check @formativePair_iff_dppair
#print axioms formativePair_iff_dppair
#check @formativePair_decreases
#print axioms formativePair_decreases
#check @wf_FormativePairRev
#print axioms wf_FormativePairRev
#check @typeIntroduction_row_anchor
#print axioms typeIntroduction_row_anchor
#check @SortedTransport.eraseCnt
#print axioms SortedTransport.eraseCnt
#check @SortedTransport.eraseStep
#print axioms SortedTransport.eraseStep
#check @SortedTransport.eraseRes
#print axioms SortedTransport.eraseRes
#check @SortedTransport.TypedRecSuccStep
#print axioms SortedTransport.TypedRecSuccStep
#check @SortedTransport.typedRecSuccStep_iff
#print axioms SortedTransport.typedRecSuccStep_iff
#check @SortedTransport.eraseRes_typedRecSuccStep
#print axioms SortedTransport.eraseRes_typedRecSuccStep
#check @SortedTransport.typedRecSuccStep_wellFounded
#print axioms SortedTransport.typedRecSuccStep_wellFounded
#check @SortedTransport.typedRecSuccStep_nonempty
#print axioms SortedTransport.typedRecSuccStep_nonempty
#check @manySortedPersistence_row_anchor
#print axioms manySortedPersistence_row_anchor
#check @OrderSortedTerm
#print axioms OrderSortedTerm
#check @orderSortRank
#print axioms orderSortRank
#check @OrderSubsort
#print axioms OrderSubsort
#check @orderSubsort_refl
#print axioms orderSubsort_refl
#check @orderSubsort_trans
#print axioms orderSubsort_trans
#check @orderSubsort_cnt_step
#print axioms orderSubsort_cnt_step
#check @orderSubsort_step_res
#print axioms orderSubsort_step_res
#check @orderSortOf
#print axioms orderSortOf
#check @OrderSortedDPPair
#print axioms OrderSortedDPPair
#check @orderSortedDPPair_res_iff
#print axioms orderSortedDPPair_res_iff
#check @orderSortedDPPair_result_sorted
#print axioms orderSortedDPPair_result_sorted
#check @eraseOrderSorted
#print axioms eraseOrderSorted
#check @eraseOrderSorted_pair
#print axioms eraseOrderSorted_pair
#check @orderSortedDPRank
#print axioms orderSortedDPRank
#check @orderSortedDPPair_decreases
#print axioms orderSortedDPPair_decreases
#check @orderSortedDPPair_wellFounded
#print axioms orderSortedDPPair_wellFounded
#check @orderSortedDPPair_nonempty
#print axioms orderSortedDPPair_nonempty
#check @orderSortedDP_row_anchor
#print axioms orderSortedDP_row_anchor
#check @contextSensitiveDP_row_anchor
#print axioms contextSensitiveDP_row_anchor
#check @twoDDPForCTRS_row_anchor
#print axioms twoDDPForCTRS_row_anchor
#check @operationalTerminationCTRS_row_anchor
#print axioms operationalTerminationCTRS_row_anchor
#check @integerTermRewriting_row_anchor
#print axioms integerTermRewriting_row_anchor
#check @lctrs_row_anchor
#print axioms lctrs_row_anchor
#check @higherOrderLCTRS_row_anchor
#print axioms higherOrderLCTRS_row_anchor
#check @BellantoniCookAdmissible
#print axioms BellantoniCookAdmissible
#check @no_bellantoniCookAdmissible
#print axioms no_bellantoniCookAdmissible
#check @bellantoniCookSplit_row_anchor
#print axioms bellantoniCookSplit_row_anchor
#check @counterProjectionCore_holds
#print axioms counterProjectionCore_holds
#check @dppair_iff_recSucc_shape
#print axioms dppair_iff_recSucc_shape
#check @reductionPairs_differ
#print axioms reductionPairs_differ

/-! ## E5: admittance and inapplicability -/

#check @horpoAdmittance_row_anchor
#print axioms horpoAdmittance_row_anchor
#check @cpoAdmittance_row_anchor
#print axioms cpoAdmittance_row_anchor
#check @FirstOrderComputabilityClosure
#print axioms FirstOrderComputabilityClosure
#check @firstOrderComputabilityClosure_iff
#print axioms firstOrderComputabilityClosure_iff
#check @firstOrderComputabilityClosure_wellFounded
#print axioms firstOrderComputabilityClosure_wellFounded
#check @ko7_recursive_counter_in_computabilityClosure
#print axioms ko7_recursive_counter_in_computabilityClosure
#check @generalSchemaAdmittance_row_anchor
#print axioms generalSchemaAdmittance_row_anchor
#check @sizedTypesAdmittance_row_anchor
#print axioms sizedTypesAdmittance_row_anchor
#check @coqGuardAdmittance_row_anchor
#print axioms coqGuardAdmittance_row_anchor
#check @ResourceSoundRuleTyping
#print axioms ResourceSoundRuleTyping
#check @no_resourceSoundRuleTyping_derives_dup
#print axioms no_resourceSoundRuleTyping_derives_dup
#check @maximalResourceSoundRuleTyping
#print axioms maximalResourceSoundRuleTyping
#check @maximalResourceSoundRuleTyping_accepts_identity
#print axioms maximalResourceSoundRuleTyping_accepts_identity
#check @linearLogicTypingBarrier_row_anchor
#print axioms linearLogicTypingBarrier_row_anchor
#check @ramifiedRecursionTypingBarrier_row_anchor
#print axioms ramifiedRecursionTypingBarrier_row_anchor
#check @abstractInterpretationAdmittance_row_anchor
#print axioms abstractInterpretationAdmittance_row_anchor
#check @infinitaryRewritingTermination_row_anchor
#print axioms infinitaryRewritingTermination_row_anchor
#check @FiniteTraceInduction
#print axioms FiniteTraceInduction
#check @finiteTraceInduction_holds
#print axioms finiteTraceInduction_holds
#check @InfiniteForwardReduction
#print axioms InfiniteForwardReduction
#check @no_infinite_stepCtxFull_reduction
#print axioms no_infinite_stepCtxFull_reduction
#check @sizeChangeTerminationEscape_row_anchor
#print axioms sizeChangeTerminationEscape_row_anchor
#check @counterDescent
#print axioms counterDescent
#check @matchedCounter
#print axioms matchedCounter
#check @recursiveCallCounter
#print axioms recursiveCallCounter
#check @dupSrc_matchedCounter
#print axioms dupSrc_matchedCounter
#check @dupTgt_recursiveCallCounter
#print axioms dupTgt_recursiveCallCounter
#check @StrictSubterm
#print axioms StrictSubterm
#check @strictSubterm_size_lt
#print axioms strictSubterm_size_lt
#check @strictSubterm_wellFounded
#print axioms strictSubterm_wellFounded
#check @ko7_recursive_counter_strict_subterm
#print axioms ko7_recursive_counter_strict_subterm
#check @dup_not_linearTypable
#print axioms dup_not_linearTypable
#check @dupSrc_leftLinear
#print axioms dupSrc_leftLinear
#check @no_ramified_assignment
#print axioms no_ramified_assignment

/-! ## E6: substrate change -/

#check @CertifiedSubstrateChange
#print axioms CertifiedSubstrateChange
#check @CertifiedSubstrateChange.source_wellFounded
#print axioms CertifiedSubstrateChange.source_wellFounded
#check @ExactStrictSubstrateExtension
#print axioms ExactStrictSubstrateExtension
#check @ExactStrictSubstrateExtension.source_wellFounded
#print axioms ExactStrictSubstrateExtension.source_wellFounded
#check @noninjective_readBack_alone_does_not_certify_termination
#print axioms noninjective_readBack_alone_does_not_certify_termination
#check @sharingNonConservativity_row_anchor
#print axioms sharingNonConservativity_row_anchor
#check @weightedTypeGraphEscape_row_anchor
#print axioms weightedTypeGraphEscape_row_anchor
#check @generalizedWeightedTypeGraphs_row_anchor
#print axioms generalizedWeightedTypeGraphs_row_anchor
#check @equationalQuotientNonConservativity_row_anchor
#print axioms equationalQuotientNonConservativity_row_anchor
#check @piCalculusTerminationTranslation_row_anchor
#print axioms piCalculusTerminationTranslation_row_anchor
#check @lambdaMuSNViaCPS_row_anchor
#print axioms lambdaMuSNViaCPS_row_anchor
#check @quasiInterpretationsSharingAware_row_anchor
#print axioms quasiInterpretationsSharingAware_row_anchor
#check @unshare_not_injective
#print axioms unshare_not_injective
#check @sharedSize_shared_lt_node
#print axioms sharedSize_shared_lt_node
#check @quasiInterpretation_never_strict
#print axioms quasiInterpretation_never_strict
#check @quasiInterpretation_axioms_do_not_force_strict
#print axioms quasiInterpretation_axioms_do_not_force_strict
#check @QuasiInterpretationPathPair
#print axioms QuasiInterpretationPathPair
#check @ko7QuasiInterpretationPathPair
#print axioms ko7QuasiInterpretationPathPair
#check @graphReadBack_not_injective
#print axioms graphReadBack_not_injective
#check @graphEncode_injective
#print axioms graphEncode_injective
#check @EncodedGraphNode
#print axioms EncodedGraphNode
#check @graphImageEquiv
#print axioms graphImageEquiv
#check @graphImageEquiv_step_iff
#print axioms graphImageEquiv_step_iff
#check @graphForeign_not_encoded
#print axioms graphForeign_not_encoded
#check @graphForeignSource_not_encoded
#print axioms graphForeignSource_not_encoded
#check @graphLiftStep_has_foreign_source
#print axioms graphLiftStep_has_foreign_source
#check @graphWeight
#print axioms graphWeight
#check @graphLiftStep_weight_decreases
#print axioms graphLiftStep_weight_decreases
#check @graphLiftStep_iff
#print axioms graphLiftStep_iff
#check @graphLiftStep_wellFounded
#print axioms graphLiftStep_wellFounded
#check @weightedTypeGraphTransport
#print axioms weightedTypeGraphTransport
#check @LabelledGraphNode
#print axioms LabelledGraphNode
#check @labelledGraphEncode
#print axioms labelledGraphEncode
#check @labelledGraphReadBack
#print axioms labelledGraphReadBack
#check @labelledGraphReadBack_encode
#print axioms labelledGraphReadBack_encode
#check @labelledGraphEncode_injective
#print axioms labelledGraphEncode_injective
#check @LabelledGraphStep
#print axioms LabelledGraphStep
#check @labelledGraphStep_encode_iff
#print axioms labelledGraphStep_encode_iff
#check @labelledGraphStep_rank_decreases
#print axioms labelledGraphStep_rank_decreases
#check @labelledGraphStep_wellFounded
#print axioms labelledGraphStep_wellFounded
#check @boolLabelledGraphReadBack_not_injective
#print axioms boolLabelledGraphReadBack_not_injective
#check @processReadBack_not_injective
#print axioms processReadBack_not_injective
#check @processEncode_injective
#print axioms processEncode_injective
#check @EncodedProcessTerm
#print axioms EncodedProcessTerm
#check @processImageEquiv
#print axioms processImageEquiv
#check @processImageEquiv_step_iff
#print axioms processImageEquiv_step_iff
#check @processForeign_not_encoded
#print axioms processForeign_not_encoded
#check @processForeignSource_not_encoded
#print axioms processForeignSource_not_encoded
#check @processLiftStep_has_foreign_source
#print axioms processLiftStep_has_foreign_source
#check @processRank
#print axioms processRank
#check @processLiftStep_rank_decreases
#print axioms processLiftStep_rank_decreases
#check @processLiftStep_iff
#print axioms processLiftStep_iff
#check @processLiftStep_wellFounded
#print axioms processLiftStep_wellFounded
#check @piCalculusTransport
#print axioms piCalculusTransport
#check @cpsLiftStep_iff
#print axioms cpsLiftStep_iff
#check @cpsEncode_injective
#print axioms cpsEncode_injective
#check @EncodedCPSTerm
#print axioms EncodedCPSTerm
#check @cpsImageEquiv
#print axioms cpsImageEquiv
#check @cpsImageEquiv_step_iff
#print axioms cpsImageEquiv_step_iff
#check @cpsForeign_not_encoded
#print axioms cpsForeign_not_encoded
#check @cpsForeignSource_not_encoded
#print axioms cpsForeignSource_not_encoded
#check @cpsLiftStep_has_foreign_source
#print axioms cpsLiftStep_has_foreign_source
#check @cpsRank
#print axioms cpsRank
#check @cpsLiftStep_rank_decreases
#print axioms cpsLiftStep_rank_decreases
#check @cpsLiftStep_wellFounded
#print axioms cpsLiftStep_wellFounded
#check @lambdaMuCPSTransport
#print axioms lambdaMuCPSTransport
#check @weightedTypeGraphTransport_exactStrict
#print axioms weightedTypeGraphTransport_exactStrict
#check @piCalculusTransport_exactStrict
#print axioms piCalculusTransport_exactStrict
#check @lambdaMuCPSTransport_exactStrict
#print axioms lambdaMuCPSTransport_exactStrict
#check @graph_process_cps_exact_strict_extensions
#print axioms graph_process_cps_exact_strict_extensions
