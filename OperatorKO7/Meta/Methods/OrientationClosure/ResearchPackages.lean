import OperatorKO7.Meta.Methods.OrientationClosure.NativeSemanticCoverage
import OperatorKO7.Meta.Methods.OrientationClosure.PathOrderNativeSemantics
import OperatorKO7.Meta.Methods.OrientationClosure.AlgebraicNativeSemantics
import OperatorKO7.Meta.Methods.OrientationClosure.SemanticStructuralNativeSemantics
import OperatorKO7.Meta.Methods.OrientationClosure.DependencyPairNativeSemantics
import OperatorKO7.Meta.Methods.OrientationClosure.HigherOrderNativeSemantics
import OperatorKO7.Meta.Methods.OrientationClosure.SubstrateChangeNativeSemantics
import OperatorKO7.Meta.Methods.OrientationClosure.ExistingSixteenGeneralization

/-!
# Dispatch ORIENTATION research-package capstones

Proof-bearing package boundaries for ORI-1 through ORI-6.  Every field is the
exact method-native row proposition from its reserved implementation module.
No classifier equality, theorem-name String, or generic `True` surrogate appears
in these capstones.

ORI-7 lives in `RDRSCoverageEvidenceLedger.lean`, where these sixty rows are
combined with the historical sixteen adapted rows.

Author status: source candidate only. Supervisor compilation and axiom review
are required before promotion.
-/

set_option autoImplicit false

namespace OperatorKO7.Methods.OrientationClosure.ResearchPackages

open OperatorKO7.Methods.PathOrderRows
open OperatorKO7.Methods.AlgebraicInterpretationRows
open OperatorKO7.Methods.OrderedMatrixInterpretationRows
open OperatorKO7.Methods.SemanticStructuralRows
open OperatorKO7.Methods.DependencyPairTypedRows
open OperatorKO7.Methods.AdmittanceInapplicabilityRows
open OperatorKO7.Methods.SubstrateChangeRows
open OperatorKO7.Methods.OrientationClosure.NativeSemanticCoverage
open OperatorKO7.Methods.OrientationClosure.PathOrderNativeSemantics
open OperatorKO7.Methods.OrientationClosure.AlgebraicNativeSemantics
open OperatorKO7.Methods.OrientationClosure.SemanticStructuralNativeSemantics
open OperatorKO7.Methods.OrientationClosure.DependencyPairNativeSemantics
open OperatorKO7.Methods.OrientationClosure.HigherOrderNativeSemantics
open OperatorKO7.Methods.OrientationClosure.SubstrateChangeNativeSemantics
open OperatorKO7.Methods.OrientationClosure.ExistingSixteenGeneralization

/-- ORI-1: ten path-order and KBO-family native semantics. -/
structure ORI1Closed : Prop where
  nativeSemantics : Nonempty ORI1NativeSemantics
  kboWithStatus : KBOWithStatusRowClaim
  generalizedKBO : GeneralizedKBORowClaim
  acKBO : ACKBORowClaim
  transfiniteKBO : TransfiniteKBORowClaim
  lambdaFreeKBO : LambdaFreeKBORowClaim
  polynomialKBO : PolynomialKBORowClaim
  acRPO : ACRPORowClaim
  rpoModuloPermutation : RPOModuloPermutationRowClaim
  popStarFamily : PopStarFamilyRowClaim
  simpleTerminationOrderType : SimpleTerminationOrderTypeRowClaim

theorem ori1_closed : ORI1Closed where
  nativeSemantics := ⟨ori1NativeSemantics⟩
  kboWithStatus := kboWithStatus_row_anchor
  generalizedKBO := generalizedKBO_row_anchor
  acKBO := acKBO_row_anchor
  transfiniteKBO := transfiniteKBO_row_anchor
  lambdaFreeKBO := lambdaFreeKBO_row_anchor
  polynomialKBO := polynomialKBO_row_anchor
  acRPO := acRPO_row_anchor
  rpoModuloPermutation := rpoModuloPermutation_row_anchor
  popStarFamily := popStarFamily_row_anchor
  simpleTerminationOrderType := simpleTerminationOrderType_row_anchor

/-- ORI-2: ten algebraic/native interpretation semantics. The Q/R matrix field
uses the genuine ordered-field implementation, not the natural-cast adapter. -/
structure ORI2Closed : Prop where
  nativeSemantics : Nonempty AlgebraicNativeBundle
  negativeCoefficientPolynomial : NegativeCoefficientPolynomialRowClaim
  maxPolynomial : MaxPolynomialRowClaim
  nonlinearHigherDegreePolynomial : NonlinearHigherDegreePolynomialRowClaim
  multilinearInterpretation : MultilinearInterpretationRowClaim
  matrixQRScalarProjection :
    OrderedMatrixExactRowClaim ℚ ∧ OrderedMatrixExactRowClaim ℝ
  arcticScalarProjection : ArcticScalarProjectionRowClaim
  tropicalScalarProjection : TropicalScalarProjectionRowClaim
  tupleInterpretationStrictS : TupleInterpretationStrictSRowClaim
  higherOrderTupleInterpretation : HigherOrderTupleInterpretationRowClaim
  strictMonotoneAlgebraArchimedean : StrictMonotoneAlgebraArchimedeanRowClaim

theorem ori2_closed : ORI2Closed where
  nativeSemantics := ⟨algebraicNativeBundle⟩
  negativeCoefficientPolynomial := negativeCoefficientPolynomial_row_anchor
  maxPolynomial := maxPolynomial_row_anchor
  nonlinearHigherDegreePolynomial := nonlinearHigherDegreePolynomial_row_anchor
  multilinearInterpretation := multilinearInterpretation_row_anchor
  matrixQRScalarProjection := rational_real_matrix_exact_row
  arcticScalarProjection := arcticScalarProjection_row_anchor
  tropicalScalarProjection := tropicalScalarProjection_row_anchor
  tupleInterpretationStrictS := tupleInterpretationStrictS_row_anchor
  higherOrderTupleInterpretation := higherOrderTupleInterpretation_row_anchor
  strictMonotoneAlgebraArchimedean := strictMonotoneAlgebraArchimedean_row_anchor

/-- ORI-3: twelve semantic and structural rows. The categorical field is the
scoped relational-category separation theorem implemented by that row; it is
not promoted here to a topos-wide theorem. -/
structure ORI3Closed : Prop where
  nativeSemantics : Nonempty SemanticStructuralNativeBundle
  extendedMonotoneAlgebra : ExtendedMonotoneAlgebraRowClaim
  finiteModelTermination : FiniteModelTerminationRowClaim
  matchBounds : MatchBoundsRowClaim
  raiseConsistencyMatchBounds : RaiseConsistencyMatchBoundsRowClaim
  leftLinearMatchBounds : LeftLinearMatchBoundsRowClaim
  semanticLabeling : SemanticLabelingRowClaim
  predictiveLabeling : PredictiveLabelingRowClaim
  rootLabeling : RootLabelingRowClaim
  selfLabelingEquational : SelfLabelingEquationalRowClaim
  categoricalToposTermination : CategoricalToposTerminationRowClaim
  forwardClosures : ForwardClosuresRowClaim
  quasiDecreasingness : QuasiDecreasingnessRowClaim

theorem ori3_closed : ORI3Closed where
  nativeSemantics := ⟨semanticStructuralNativeBundle⟩
  extendedMonotoneAlgebra := extendedMonotoneAlgebra_row_anchor
  finiteModelTermination := finiteModelTermination_row_anchor
  matchBounds := matchBounds_row_anchor
  raiseConsistencyMatchBounds := raiseConsistencyMatchBounds_row_anchor
  leftLinearMatchBounds := leftLinearMatchBounds_row_anchor
  semanticLabeling := semanticLabeling_row_anchor
  predictiveLabeling := predictiveLabeling_row_anchor
  rootLabeling := rootLabeling_row_anchor
  selfLabelingEquational := selfLabelingEquational_row_anchor
  categoricalToposTermination := categoricalToposTermination_row_anchor
  forwardClosures := forwardClosures_row_anchor
  quasiDecreasingness := quasiDecreasingness_row_anchor

/-- ORI-4: thirteen dependency-pair, sorted, conditional, and constrained
method semantics. -/
structure ORI4Closed : Prop where
  nativeSemantics : Nonempty DependencyPairNativeBundle
  dpProcessorClassification : DPProcessorClassificationRowClaim
  dpReductionPairProcessor : DPReductionPairProcessorRowClaim
  dpReductionTriples : DPReductionTriplesRowClaim
  orderSortedDP : OrderSortedDPRowClaim
  contextSensitiveDP : ContextSensitiveDPRowClaim
  twoDDPForCTRS : TwoDDPForCTRSRowClaim
  formativeRules : FormativeRulesRowClaim
  typeIntroduction : TypeIntroductionRowClaim
  manySortedPersistence : ManySortedPersistenceRowClaim
  operationalTerminationCTRS : OperationalTerminationCTRSRowClaim
  integerTermRewriting : IntegerTermRewritingRowClaim
  lctrs : LCTRSRowClaim
  higherOrderLCTRS : HigherOrderLCTRSRowClaim

theorem ori4_closed : ORI4Closed where
  nativeSemantics := ⟨dependencyPairNativeBundle⟩
  dpProcessorClassification := dpProcessorClassification_row_anchor
  dpReductionPairProcessor := dpReductionPairProcessor_row_anchor
  dpReductionTriples := dpReductionTriples_row_anchor
  orderSortedDP := orderSortedDP_row_anchor
  contextSensitiveDP := contextSensitiveDP_row_anchor
  twoDDPForCTRS := twoDDPForCTRS_row_anchor
  formativeRules := formativeRules_row_anchor
  typeIntroduction := typeIntroduction_row_anchor
  manySortedPersistence := manySortedPersistence_row_anchor
  operationalTerminationCTRS := operationalTerminationCTRS_row_anchor
  integerTermRewriting := integerTermRewriting_row_anchor
  lctrs := lctrs_row_anchor
  higherOrderLCTRS := higherOrderLCTRS_row_anchor

/-- ORI-5: ten higher-order-admittance, typing, infinitary, and abstraction
semantics. HORPO and CPO retain their explicitly stated first-order admittance
scope; this capstone does not claim a complete arbitrary higher-order calculus. -/
structure ORI5Closed : Prop where
  nativeSemantics : Nonempty HigherOrderNativeBundle
  horpoAdmittance : HorpoAdmittanceRowClaim
  cpoAdmittance : CpoAdmittanceRowClaim
  generalSchemaAdmittance : GeneralSchemaAdmittanceRowClaim
  sizedTypesAdmittance : SizedTypesAdmittanceRowClaim
  coqGuardAdmittance : CoqGuardAdmittanceRowClaim
  bellantoniCookSplit : BellantoniCookSplitRowClaim
  linearLogicTypingBarrier : LinearLogicTypingBarrierRowClaim
  ramifiedRecursionTypingBarrier : RamifiedRecursionTypingBarrierRowClaim
  infinitaryRewritingTermination : InfinitaryRewritingTerminationRowClaim
  abstractInterpretationAdmittance : AbstractInterpretationAdmittanceRowClaim

theorem ori5_closed : ORI5Closed where
  nativeSemantics := ⟨higherOrderNativeBundle⟩
  horpoAdmittance := horpoAdmittance_row_anchor
  cpoAdmittance := cpoAdmittance_row_anchor
  generalSchemaAdmittance := generalSchemaAdmittance_row_anchor
  sizedTypesAdmittance := sizedTypesAdmittance_row_anchor
  coqGuardAdmittance := coqGuardAdmittance_row_anchor
  bellantoniCookSplit := bellantoniCookSplit_row_anchor
  linearLogicTypingBarrier := linearLogicTypingBarrier_row_anchor
  ramifiedRecursionTypingBarrier := ramifiedRecursionTypingBarrier_row_anchor
  infinitaryRewritingTermination := infinitaryRewritingTermination_row_anchor
  abstractInterpretationAdmittance := abstractInterpretationAdmittance_row_anchor

/-- ORI-6: five substrate-change methods with explicit encode/readback and
source-transport laws or the sharing-aware composite certificate. -/
structure ORI6Closed : Prop where
  nativeSemantics : Nonempty ORI6NativeSemantics
  weightedTypeGraphEscape : WeightedTypeGraphEscapeRowClaim
  generalizedWeightedTypeGraphs : GeneralizedWeightedTypeGraphsRowClaim
  piCalculusTerminationTranslation : PiCalculusTerminationTranslationRowClaim
  lambdaMuSNViaCPS : LambdaMuSNViaCPSRowClaim
  quasiInterpretationsSharingAware : QuasiInterpretationsSharingAwareRowClaim

theorem ori6_closed : ORI6Closed where
  nativeSemantics := ⟨ori6NativeSemantics⟩
  weightedTypeGraphEscape := weightedTypeGraphEscape_row_anchor
  generalizedWeightedTypeGraphs := generalizedWeightedTypeGraphs_row_anchor
  piCalculusTerminationTranslation := piCalculusTerminationTranslation_row_anchor
  lambdaMuSNViaCPS := lambdaMuSNViaCPS_row_anchor
  quasiInterpretationsSharingAware := quasiInterpretationsSharingAware_row_anchor

/-- The six research packages account for exactly the sixty-row complementary
wave and preserve its typed evidence closure. -/
structure OrientationResearchPackagesClosed : Prop where
  existingSixteen : ExistingSixteenGeneralized
  ori1 : ORI1Closed
  ori2 : ORI2Closed
  ori3 : ORI3Closed
  ori4 : ORI4Closed
  ori5 : ORI5Closed
  ori6 : ORI6Closed
  complementaryRowCount : missingNativeRows.length = 60
  complementaryEvidence : MissingNativeCoverageClosed

theorem orientation_research_packages_closed : OrientationResearchPackagesClosed where
  existingSixteen := existing_sixteen_generalized
  ori1 := ori1_closed
  ori2 := ori2_closed
  ori3 := ori3_closed
  ori4 := ori4_closed
  ori5 := ori5_closed
  ori6 := ori6_closed
  complementaryRowCount := missingNativeRows_count
  complementaryEvidence := missing_native_coverage_closed

end OperatorKO7.Methods.OrientationClosure.ResearchPackages
