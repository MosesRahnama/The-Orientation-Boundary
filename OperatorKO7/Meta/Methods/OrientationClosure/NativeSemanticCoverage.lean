import OperatorKO7.Meta.RDRSTerminationMethodUniverse
import OperatorKO7.Meta.Methods.PathOrderRows
import OperatorKO7.Meta.Methods.AlgebraicInterpretationRows
import OperatorKO7.Meta.Methods.OrderedMatrixInterpretationRows
import OperatorKO7.Meta.Methods.SemanticStructuralRows
import OperatorKO7.Meta.Methods.DependencyPairTypedRows
import OperatorKO7.Meta.Methods.AdmittanceInapplicabilityRows
import OperatorKO7.Meta.Methods.SubstrateChangeRows
import OperatorKO7.Meta.Methods.OrientationClosure.PathOrderNativeSemantics
import OperatorKO7.Meta.Methods.OrientationClosure.AlgebraicNativeSemantics
import OperatorKO7.Meta.Methods.OrientationClosure.SemanticStructuralNativeSemantics
import OperatorKO7.Meta.Methods.OrientationClosure.DependencyPairNativeSemantics
import OperatorKO7.Meta.Methods.OrientationClosure.HigherOrderNativeSemantics
import OperatorKO7.Meta.Methods.OrientationClosure.SubstrateChangeNativeSemantics

/-!
# Native semantic coverage for the sixty previously curated RDRS rows

This module is the author-side ORIENTATION closure adapter.  It does not change
`RDRSMethodFamily` or any six-way classification.  Instead it binds each of the
sixty rows that were previously curated in `RDRSCoverageEvidenceLedger` to the
exact method-native proposition already implemented in its reserved row module.

The sixteen legacy theorem-backed rows are deliberately assigned `False` here.
They remain owned by the existing evidence interface.  Therefore the list
`missingNativeRows` is a mechanically distinct sixty-row complement, not a
renaming of the full seventy-six-row universe.

For `matrixQRScalarProjection` the native row is the ordered-field matrix
semantics from `OrderedMatrixInterpretationRows`, including genuine rational and
real coefficients.  It is not the older natural-matrix cast adapter.

No compilation, axiom query, or naming regeneration is performed by the author.
Supervisor validation is required before these declarations are promoted.
-/

set_option autoImplicit false

namespace OperatorKO7.Methods.OrientationClosure.NativeSemanticCoverage

open OperatorKO7.RDRSTerminationMethodUniverse
open OperatorKO7.Methods.PathOrderRows
open OperatorKO7.Methods.AlgebraicInterpretationRows
open OperatorKO7.Methods.OrderedMatrixInterpretationRows
open OperatorKO7.Methods.SemanticStructuralRows
open OperatorKO7.Methods.DependencyPairTypedRows
open OperatorKO7.Methods.AdmittanceInapplicabilityRows
open OperatorKO7.Methods.SubstrateChangeRows
open OperatorKO7.Methods.OrientationClosure.PathOrderNativeSemantics
open OperatorKO7.Methods.OrientationClosure.AlgebraicNativeSemantics
open OperatorKO7.Methods.OrientationClosure.SemanticStructuralNativeSemantics
open OperatorKO7.Methods.OrientationClosure.DependencyPairNativeSemantics
open OperatorKO7.Methods.OrientationClosure.HigherOrderNativeSemantics
open OperatorKO7.Methods.OrientationClosure.SubstrateChangeNativeSemantics

/-- Exact native semantics for the sixty rows that were previously curated.
The sixteen rows already carried by the legacy evidence interface map to
`False`, making accidental double-promotion impossible at this layer. -/
def MissingNativeRowClaim : RDRSMethodFamily → Prop
  | .standardKBO => False
  | .kboWithStatus => KBOWithStatusRowClaim
  | .generalizedKBO => GeneralizedKBORowClaim
  | .subtermCoefficientKBO => False
  | .acKBO => ACKBORowClaim
  | .transfiniteKBO => TransfiniteKBORowClaim
  | .lambdaFreeKBO => LambdaFreeKBORowClaim
  | .acRPO => ACRPORowClaim
  | .rpoModuloPermutation => RPOModuloPermutationRowClaim
  | .popStarFamily => PopStarFamilyRowClaim
  | .simpleTerminationOrderType => SimpleTerminationOrderTypeRowClaim
  | .cichonSlowGrowing => False
  | .linearPolyQ => False
  | .linearPolyR => False
  | .negativeCoefficientPolynomial => NegativeCoefficientPolynomialRowClaim
  | .maxPolynomial => MaxPolynomialRowClaim
  | .nonlinearHigherDegreePolynomial => NonlinearHigherDegreePolynomialRowClaim
  | .multilinearInterpretation => MultilinearInterpretationRowClaim
  | .matrixNScalarProjection => False
  | .matrixQRScalarProjection =>
      OrderedMatrixExactRowClaim ℚ ∧ OrderedMatrixExactRowClaim ℝ
  | .arcticScalarProjection => ArcticScalarProjectionRowClaim
  | .tropicalScalarProjection => TropicalScalarProjectionRowClaim
  | .triangularMatrix => False
  | .tupleInterpretationStrictS => TupleInterpretationStrictSRowClaim
  | .higherOrderTupleInterpretation => HigherOrderTupleInterpretationRowClaim
  | .polynomialKBO => PolynomialKBORowClaim
  | .strictMonotoneAlgebraArchimedean => StrictMonotoneAlgebraArchimedeanRowClaim
  | .extendedMonotoneAlgebra => ExtendedMonotoneAlgebraRowClaim
  | .semanticLabeling => SemanticLabelingRowClaim
  | .predictiveLabeling => PredictiveLabelingRowClaim
  | .rootLabeling => RootLabelingRowClaim
  | .selfLabelingEquational => SelfLabelingEquationalRowClaim
  | .finiteModelTermination => FiniteModelTerminationRowClaim
  | .categoricalToposTermination => CategoricalToposTerminationRowClaim
  | .forwardClosures => ForwardClosuresRowClaim
  | .matchBounds => MatchBoundsRowClaim
  | .raiseConsistencyMatchBounds => RaiseConsistencyMatchBoundsRowClaim
  | .quasiDecreasingness => QuasiDecreasingnessRowClaim
  | .dpProcessorClassification => DPProcessorClassificationRowClaim
  | .dpSubtermCriterion => False
  | .dpArgumentFiltering => False
  | .dpReductionPairProcessor => DPReductionPairProcessorRowClaim
  | .dpNeutralProcessors => False
  | .dpReductionTriples => DPReductionTriplesRowClaim
  | .usableRulesMinimality => False
  | .formativeRules => FormativeRulesRowClaim
  | .typeIntroduction => TypeIntroductionRowClaim
  | .manySortedPersistence => ManySortedPersistenceRowClaim
  | .orderSortedDP => OrderSortedDPRowClaim
  | .contextSensitiveDP => ContextSensitiveDPRowClaim
  | .twoDDPForCTRS => TwoDDPForCTRSRowClaim
  | .operationalTerminationCTRS => OperationalTerminationCTRSRowClaim
  | .integerTermRewriting => IntegerTermRewritingRowClaim
  | .lctrs => LCTRSRowClaim
  | .higherOrderLCTRS => HigherOrderLCTRSRowClaim
  | .horpoAdmittance => HorpoAdmittanceRowClaim
  | .cpoAdmittance => CpoAdmittanceRowClaim
  | .generalSchemaAdmittance => GeneralSchemaAdmittanceRowClaim
  | .sizedTypesAdmittance => SizedTypesAdmittanceRowClaim
  | .coqGuardAdmittance => CoqGuardAdmittanceRowClaim
  | .bellantoniCookSplit => BellantoniCookSplitRowClaim
  | .linearLogicTypingBarrier => LinearLogicTypingBarrierRowClaim
  | .ramifiedRecursionTypingBarrier => RamifiedRecursionTypingBarrierRowClaim
  | .sharingNonConservativity => False
  | .weightedTypeGraphEscape => WeightedTypeGraphEscapeRowClaim
  | .generalizedWeightedTypeGraphs => GeneralizedWeightedTypeGraphsRowClaim
  | .equationalQuotientNonConservativity => False
  | .cycleRewritingInapplicability => False
  | .stringRewritingInapplicability => False
  | .leftLinearMatchBounds => LeftLinearMatchBoundsRowClaim
  | .sizeChangeTerminationEscape => False
  | .infinitaryRewritingTermination => InfinitaryRewritingTerminationRowClaim
  | .piCalculusTerminationTranslation => PiCalculusTerminationTranslationRowClaim
  | .lambdaMuSNViaCPS => LambdaMuSNViaCPSRowClaim
  | .abstractInterpretationAdmittance => AbstractInterpretationAdmittanceRowClaim
  | .quasiInterpretationsSharingAware => QuasiInterpretationsSharingAwareRowClaim

/-! ## Indexed native method interpretations -/

/-- Closed row-indexed method objects for the sixty ORIENTATION rows. Each
constructor carries concrete native method data from its ORI package. The
sixteen historical rows have no constructor here and remain in the legacy
`MethodInterpretation` family. -/
inductive MissingNativeInterpretation : RDRSMethodFamily → Type 1
  | kboWithStatus (P : ORI1NativeSemantics.{0}) : MissingNativeInterpretation .kboWithStatus
  | generalizedKBO (P : ORI1NativeSemantics.{0}) : MissingNativeInterpretation .generalizedKBO
  | acKBO (P : ORI1NativeSemantics.{0}) : MissingNativeInterpretation .acKBO
  | transfiniteKBO (P : ORI1NativeSemantics.{0}) : MissingNativeInterpretation .transfiniteKBO
  | lambdaFreeKBO (P : ORI1NativeSemantics.{0}) : MissingNativeInterpretation .lambdaFreeKBO
  | acRPO (P : ORI1NativeSemantics.{0}) : MissingNativeInterpretation .acRPO
  | rpoModuloPermutation (P : ORI1NativeSemantics.{0}) : MissingNativeInterpretation .rpoModuloPermutation
  | popStarFamily (P : ORI1NativeSemantics.{0}) : MissingNativeInterpretation .popStarFamily
  | simpleTerminationOrderType (P : ORI1NativeSemantics.{0}) :
      MissingNativeInterpretation .simpleTerminationOrderType
  | negativeCoefficientPolynomial (P : AlgebraicNativeBundle) :
      MissingNativeInterpretation .negativeCoefficientPolynomial
  | maxPolynomial (P : AlgebraicNativeBundle) : MissingNativeInterpretation .maxPolynomial
  | nonlinearHigherDegreePolynomial (P : AlgebraicNativeBundle) :
      MissingNativeInterpretation .nonlinearHigherDegreePolynomial
  | multilinearInterpretation (P : AlgebraicNativeBundle) :
      MissingNativeInterpretation .multilinearInterpretation
  | matrixQRScalarProjection (P : AlgebraicNativeBundle) :
      MissingNativeInterpretation .matrixQRScalarProjection
  | arcticScalarProjection (P : AlgebraicNativeBundle) :
      MissingNativeInterpretation .arcticScalarProjection
  | tropicalScalarProjection (P : AlgebraicNativeBundle) :
      MissingNativeInterpretation .tropicalScalarProjection
  | tupleInterpretationStrictS (P : AlgebraicNativeBundle) :
      MissingNativeInterpretation .tupleInterpretationStrictS
  | higherOrderTupleInterpretation (P : AlgebraicNativeBundle) :
      MissingNativeInterpretation .higherOrderTupleInterpretation
  | polynomialKBO (P : ORI1NativeSemantics.{0}) : MissingNativeInterpretation .polynomialKBO
  | strictMonotoneAlgebraArchimedean (P : AlgebraicNativeBundle) :
      MissingNativeInterpretation .strictMonotoneAlgebraArchimedean
  | extendedMonotoneAlgebra (P : SemanticStructuralNativeBundle) :
      MissingNativeInterpretation .extendedMonotoneAlgebra
  | semanticLabeling (P : SemanticStructuralNativeBundle) :
      MissingNativeInterpretation .semanticLabeling
  | predictiveLabeling (P : SemanticStructuralNativeBundle) :
      MissingNativeInterpretation .predictiveLabeling
  | rootLabeling (P : SemanticStructuralNativeBundle) : MissingNativeInterpretation .rootLabeling
  | selfLabelingEquational (P : SemanticStructuralNativeBundle) :
      MissingNativeInterpretation .selfLabelingEquational
  | finiteModelTermination (P : SemanticStructuralNativeBundle) :
      MissingNativeInterpretation .finiteModelTermination
  | categoricalToposTermination (P : SemanticStructuralNativeBundle) :
      MissingNativeInterpretation .categoricalToposTermination
  | forwardClosures (P : SemanticStructuralNativeBundle) : MissingNativeInterpretation .forwardClosures
  | matchBounds (P : SemanticStructuralNativeBundle) : MissingNativeInterpretation .matchBounds
  | raiseConsistencyMatchBounds (P : SemanticStructuralNativeBundle) :
      MissingNativeInterpretation .raiseConsistencyMatchBounds
  | quasiDecreasingness (P : SemanticStructuralNativeBundle) :
      MissingNativeInterpretation .quasiDecreasingness
  | dpProcessorClassification (P : DependencyPairNativeBundle) :
      MissingNativeInterpretation .dpProcessorClassification
  | dpReductionPairProcessor (P : DependencyPairNativeBundle) :
      MissingNativeInterpretation .dpReductionPairProcessor
  | dpReductionTriples (P : DependencyPairNativeBundle) : MissingNativeInterpretation .dpReductionTriples
  | formativeRules (P : DependencyPairNativeBundle) : MissingNativeInterpretation .formativeRules
  | typeIntroduction (P : DependencyPairNativeBundle) : MissingNativeInterpretation .typeIntroduction
  | manySortedPersistence (P : DependencyPairNativeBundle) :
      MissingNativeInterpretation .manySortedPersistence
  | orderSortedDP (P : DependencyPairNativeBundle) : MissingNativeInterpretation .orderSortedDP
  | contextSensitiveDP (P : DependencyPairNativeBundle) :
      MissingNativeInterpretation .contextSensitiveDP
  | twoDDPForCTRS (P : DependencyPairNativeBundle) : MissingNativeInterpretation .twoDDPForCTRS
  | operationalTerminationCTRS (P : DependencyPairNativeBundle) :
      MissingNativeInterpretation .operationalTerminationCTRS
  | integerTermRewriting (P : DependencyPairNativeBundle) :
      MissingNativeInterpretation .integerTermRewriting
  | lctrs (P : DependencyPairNativeBundle) : MissingNativeInterpretation .lctrs
  | higherOrderLCTRS (P : DependencyPairNativeBundle) : MissingNativeInterpretation .higherOrderLCTRS
  | horpoAdmittance (P : HigherOrderNativeBundle) : MissingNativeInterpretation .horpoAdmittance
  | cpoAdmittance (P : HigherOrderNativeBundle) : MissingNativeInterpretation .cpoAdmittance
  | generalSchemaAdmittance (P : HigherOrderNativeBundle) :
      MissingNativeInterpretation .generalSchemaAdmittance
  | sizedTypesAdmittance (P : HigherOrderNativeBundle) :
      MissingNativeInterpretation .sizedTypesAdmittance
  | coqGuardAdmittance (P : HigherOrderNativeBundle) : MissingNativeInterpretation .coqGuardAdmittance
  | bellantoniCookSplit (P : HigherOrderNativeBundle) : MissingNativeInterpretation .bellantoniCookSplit
  | linearLogicTypingBarrier (P : HigherOrderNativeBundle) :
      MissingNativeInterpretation .linearLogicTypingBarrier
  | ramifiedRecursionTypingBarrier (P : HigherOrderNativeBundle) :
      MissingNativeInterpretation .ramifiedRecursionTypingBarrier
  | weightedTypeGraphEscape (P : ORI6NativeSemantics) :
      MissingNativeInterpretation .weightedTypeGraphEscape
  | generalizedWeightedTypeGraphs (P : ORI6NativeSemantics) :
      MissingNativeInterpretation .generalizedWeightedTypeGraphs
  | leftLinearMatchBounds (P : SemanticStructuralNativeBundle) :
      MissingNativeInterpretation .leftLinearMatchBounds
  | infinitaryRewritingTermination (P : HigherOrderNativeBundle) :
      MissingNativeInterpretation .infinitaryRewritingTermination
  | piCalculusTerminationTranslation (P : ORI6NativeSemantics) :
      MissingNativeInterpretation .piCalculusTerminationTranslation
  | lambdaMuSNViaCPS (P : ORI6NativeSemantics) : MissingNativeInterpretation .lambdaMuSNViaCPS
  | abstractInterpretationAdmittance (P : HigherOrderNativeBundle) :
      MissingNativeInterpretation .abstractInterpretationAdmittance
  | quasiInterpretationsSharingAware (P : ORI6NativeSemantics) :
      MissingNativeInterpretation .quasiInterpretationsSharingAware

/-- Canonical native interpretation for each complementary row. The historical
sixteen return `none`. -/
noncomputable def missingNativeInterpretation :
    (f : RDRSMethodFamily) → Option (MissingNativeInterpretation f)
  | .standardKBO => none
  | .kboWithStatus => some (.kboWithStatus ori1NativeSemantics)
  | .generalizedKBO => some (.generalizedKBO ori1NativeSemantics)
  | .subtermCoefficientKBO => none
  | .acKBO => some (.acKBO ori1NativeSemantics)
  | .transfiniteKBO => some (.transfiniteKBO ori1NativeSemantics)
  | .lambdaFreeKBO => some (.lambdaFreeKBO ori1NativeSemantics)
  | .acRPO => some (.acRPO ori1NativeSemantics)
  | .rpoModuloPermutation => some (.rpoModuloPermutation ori1NativeSemantics)
  | .popStarFamily => some (.popStarFamily ori1NativeSemantics)
  | .simpleTerminationOrderType => some (.simpleTerminationOrderType ori1NativeSemantics)
  | .cichonSlowGrowing => none
  | .linearPolyQ => none
  | .linearPolyR => none
  | .negativeCoefficientPolynomial => some (.negativeCoefficientPolynomial algebraicNativeBundle)
  | .maxPolynomial => some (.maxPolynomial algebraicNativeBundle)
  | .nonlinearHigherDegreePolynomial => some (.nonlinearHigherDegreePolynomial algebraicNativeBundle)
  | .multilinearInterpretation => some (.multilinearInterpretation algebraicNativeBundle)
  | .matrixNScalarProjection => none
  | .matrixQRScalarProjection => some (.matrixQRScalarProjection algebraicNativeBundle)
  | .arcticScalarProjection => some (.arcticScalarProjection algebraicNativeBundle)
  | .tropicalScalarProjection => some (.tropicalScalarProjection algebraicNativeBundle)
  | .triangularMatrix => none
  | .tupleInterpretationStrictS => some (.tupleInterpretationStrictS algebraicNativeBundle)
  | .higherOrderTupleInterpretation => some (.higherOrderTupleInterpretation algebraicNativeBundle)
  | .polynomialKBO => some (.polynomialKBO ori1NativeSemantics)
  | .strictMonotoneAlgebraArchimedean => some (.strictMonotoneAlgebraArchimedean algebraicNativeBundle)
  | .extendedMonotoneAlgebra => some (.extendedMonotoneAlgebra semanticStructuralNativeBundle)
  | .semanticLabeling => some (.semanticLabeling semanticStructuralNativeBundle)
  | .predictiveLabeling => some (.predictiveLabeling semanticStructuralNativeBundle)
  | .rootLabeling => some (.rootLabeling semanticStructuralNativeBundle)
  | .selfLabelingEquational => some (.selfLabelingEquational semanticStructuralNativeBundle)
  | .finiteModelTermination => some (.finiteModelTermination semanticStructuralNativeBundle)
  | .categoricalToposTermination => some (.categoricalToposTermination semanticStructuralNativeBundle)
  | .forwardClosures => some (.forwardClosures semanticStructuralNativeBundle)
  | .matchBounds => some (.matchBounds semanticStructuralNativeBundle)
  | .raiseConsistencyMatchBounds => some (.raiseConsistencyMatchBounds semanticStructuralNativeBundle)
  | .quasiDecreasingness => some (.quasiDecreasingness semanticStructuralNativeBundle)
  | .dpProcessorClassification => some (.dpProcessorClassification dependencyPairNativeBundle)
  | .dpSubtermCriterion => none
  | .dpArgumentFiltering => none
  | .dpReductionPairProcessor => some (.dpReductionPairProcessor dependencyPairNativeBundle)
  | .dpNeutralProcessors => none
  | .dpReductionTriples => some (.dpReductionTriples dependencyPairNativeBundle)
  | .usableRulesMinimality => none
  | .formativeRules => some (.formativeRules dependencyPairNativeBundle)
  | .typeIntroduction => some (.typeIntroduction dependencyPairNativeBundle)
  | .manySortedPersistence => some (.manySortedPersistence dependencyPairNativeBundle)
  | .orderSortedDP => some (.orderSortedDP dependencyPairNativeBundle)
  | .contextSensitiveDP => some (.contextSensitiveDP dependencyPairNativeBundle)
  | .twoDDPForCTRS => some (.twoDDPForCTRS dependencyPairNativeBundle)
  | .operationalTerminationCTRS => some (.operationalTerminationCTRS dependencyPairNativeBundle)
  | .integerTermRewriting => some (.integerTermRewriting dependencyPairNativeBundle)
  | .lctrs => some (.lctrs dependencyPairNativeBundle)
  | .higherOrderLCTRS => some (.higherOrderLCTRS dependencyPairNativeBundle)
  | .horpoAdmittance => some (.horpoAdmittance higherOrderNativeBundle)
  | .cpoAdmittance => some (.cpoAdmittance higherOrderNativeBundle)
  | .generalSchemaAdmittance => some (.generalSchemaAdmittance higherOrderNativeBundle)
  | .sizedTypesAdmittance => some (.sizedTypesAdmittance higherOrderNativeBundle)
  | .coqGuardAdmittance => some (.coqGuardAdmittance higherOrderNativeBundle)
  | .bellantoniCookSplit => some (.bellantoniCookSplit higherOrderNativeBundle)
  | .linearLogicTypingBarrier => some (.linearLogicTypingBarrier higherOrderNativeBundle)
  | .ramifiedRecursionTypingBarrier => some (.ramifiedRecursionTypingBarrier higherOrderNativeBundle)
  | .sharingNonConservativity => none
  | .weightedTypeGraphEscape => some (.weightedTypeGraphEscape ori6NativeSemantics)
  | .generalizedWeightedTypeGraphs => some (.generalizedWeightedTypeGraphs ori6NativeSemantics)
  | .equationalQuotientNonConservativity => none
  | .cycleRewritingInapplicability => none
  | .stringRewritingInapplicability => none
  | .leftLinearMatchBounds => some (.leftLinearMatchBounds semanticStructuralNativeBundle)
  | .sizeChangeTerminationEscape => none
  | .infinitaryRewritingTermination => some (.infinitaryRewritingTermination higherOrderNativeBundle)
  | .piCalculusTerminationTranslation => some (.piCalculusTerminationTranslation ori6NativeSemantics)
  | .lambdaMuSNViaCPS => some (.lambdaMuSNViaCPS ori6NativeSemantics)
  | .abstractInterpretationAdmittance => some (.abstractInterpretationAdmittance higherOrderNativeBundle)
  | .quasiInterpretationsSharingAware => some (.quasiInterpretationsSharingAware ori6NativeSemantics)

/-- Lift one row proposition into a type-valued optional evidence payload. -/
def evidenceSome {f : RDRSMethodFamily} (h : MissingNativeRowClaim f) :
    Option (PLift (MissingNativeRowClaim f)) := some ⟨h⟩

/-- Proof-bearing native interpretation for each of the sixty complementary
rows. Each `some` payload contains the row theorem lifted into `Type`; the
legacy sixteen return `none`. -/
def missingNativeEvidence :
    (f : RDRSMethodFamily) → Option (PLift (MissingNativeRowClaim f))
  | .standardKBO => none
  | .kboWithStatus => evidenceSome kboWithStatus_row_anchor
  | .generalizedKBO => evidenceSome generalizedKBO_row_anchor
  | .subtermCoefficientKBO => none
  | .acKBO => evidenceSome acKBO_row_anchor
  | .transfiniteKBO => evidenceSome transfiniteKBO_row_anchor
  | .lambdaFreeKBO => evidenceSome lambdaFreeKBO_row_anchor
  | .acRPO => evidenceSome acRPO_row_anchor
  | .rpoModuloPermutation => evidenceSome rpoModuloPermutation_row_anchor
  | .popStarFamily => evidenceSome popStarFamily_row_anchor
  | .simpleTerminationOrderType => evidenceSome simpleTerminationOrderType_row_anchor
  | .cichonSlowGrowing => none
  | .linearPolyQ => none
  | .linearPolyR => none
  | .negativeCoefficientPolynomial => evidenceSome negativeCoefficientPolynomial_row_anchor
  | .maxPolynomial => evidenceSome maxPolynomial_row_anchor
  | .nonlinearHigherDegreePolynomial => evidenceSome nonlinearHigherDegreePolynomial_row_anchor
  | .multilinearInterpretation => evidenceSome multilinearInterpretation_row_anchor
  | .matrixNScalarProjection => none
  | .matrixQRScalarProjection => evidenceSome rational_real_matrix_exact_row
  | .arcticScalarProjection => evidenceSome arcticScalarProjection_row_anchor
  | .tropicalScalarProjection => evidenceSome tropicalScalarProjection_row_anchor
  | .triangularMatrix => none
  | .tupleInterpretationStrictS => evidenceSome tupleInterpretationStrictS_row_anchor
  | .higherOrderTupleInterpretation => evidenceSome higherOrderTupleInterpretation_row_anchor
  | .polynomialKBO => evidenceSome polynomialKBO_row_anchor
  | .strictMonotoneAlgebraArchimedean => evidenceSome strictMonotoneAlgebraArchimedean_row_anchor
  | .extendedMonotoneAlgebra => evidenceSome extendedMonotoneAlgebra_row_anchor
  | .semanticLabeling => evidenceSome semanticLabeling_row_anchor
  | .predictiveLabeling => evidenceSome predictiveLabeling_row_anchor
  | .rootLabeling => evidenceSome rootLabeling_row_anchor
  | .selfLabelingEquational => evidenceSome selfLabelingEquational_row_anchor
  | .finiteModelTermination => evidenceSome finiteModelTermination_row_anchor
  | .categoricalToposTermination => evidenceSome categoricalToposTermination_row_anchor
  | .forwardClosures => evidenceSome forwardClosures_row_anchor
  | .matchBounds => evidenceSome matchBounds_row_anchor
  | .raiseConsistencyMatchBounds => evidenceSome raiseConsistencyMatchBounds_row_anchor
  | .quasiDecreasingness => evidenceSome quasiDecreasingness_row_anchor
  | .dpProcessorClassification => evidenceSome dpProcessorClassification_row_anchor
  | .dpSubtermCriterion => none
  | .dpArgumentFiltering => none
  | .dpReductionPairProcessor => evidenceSome dpReductionPairProcessor_row_anchor
  | .dpNeutralProcessors => none
  | .dpReductionTriples => evidenceSome dpReductionTriples_row_anchor
  | .usableRulesMinimality => none
  | .formativeRules => evidenceSome formativeRules_row_anchor
  | .typeIntroduction => evidenceSome typeIntroduction_row_anchor
  | .manySortedPersistence => evidenceSome manySortedPersistence_row_anchor
  | .orderSortedDP => evidenceSome orderSortedDP_row_anchor
  | .contextSensitiveDP => evidenceSome contextSensitiveDP_row_anchor
  | .twoDDPForCTRS => evidenceSome twoDDPForCTRS_row_anchor
  | .operationalTerminationCTRS => evidenceSome operationalTerminationCTRS_row_anchor
  | .integerTermRewriting => evidenceSome integerTermRewriting_row_anchor
  | .lctrs => evidenceSome lctrs_row_anchor
  | .higherOrderLCTRS => evidenceSome higherOrderLCTRS_row_anchor
  | .horpoAdmittance => evidenceSome horpoAdmittance_row_anchor
  | .cpoAdmittance => evidenceSome cpoAdmittance_row_anchor
  | .generalSchemaAdmittance => evidenceSome generalSchemaAdmittance_row_anchor
  | .sizedTypesAdmittance => evidenceSome sizedTypesAdmittance_row_anchor
  | .coqGuardAdmittance => evidenceSome coqGuardAdmittance_row_anchor
  | .bellantoniCookSplit => evidenceSome bellantoniCookSplit_row_anchor
  | .linearLogicTypingBarrier => evidenceSome linearLogicTypingBarrier_row_anchor
  | .ramifiedRecursionTypingBarrier => evidenceSome ramifiedRecursionTypingBarrier_row_anchor
  | .sharingNonConservativity => none
  | .weightedTypeGraphEscape => evidenceSome weightedTypeGraphEscape_row_anchor
  | .generalizedWeightedTypeGraphs => evidenceSome generalizedWeightedTypeGraphs_row_anchor
  | .equationalQuotientNonConservativity => none
  | .cycleRewritingInapplicability => none
  | .stringRewritingInapplicability => none
  | .leftLinearMatchBounds => evidenceSome leftLinearMatchBounds_row_anchor
  | .sizeChangeTerminationEscape => none
  | .infinitaryRewritingTermination => evidenceSome infinitaryRewritingTermination_row_anchor
  | .piCalculusTerminationTranslation => evidenceSome piCalculusTerminationTranslation_row_anchor
  | .lambdaMuSNViaCPS => evidenceSome lambdaMuSNViaCPS_row_anchor
  | .abstractInterpretationAdmittance => evidenceSome abstractInterpretationAdmittance_row_anchor
  | .quasiInterpretationsSharingAware => evidenceSome quasiInterpretationsSharingAware_row_anchor

/-- Rows that have an actual indexed ORIENTATION interpretation object. -/
noncomputable def missingNativeInterpretationRows : List RDRSMethodFamily :=
  allMethodFamilies.filter (fun f => (missingNativeInterpretation f).isSome)

/-- The indexed interpretation layer contains exactly sixty rows. -/
theorem missingNativeInterpretationRows_count :
    missingNativeInterpretationRows.length = 60 := by decide

/-- Every row selected by the indexed interpretation layer has an actual
method object, not only a row proposition. -/
theorem missingNativeInterpretationRows_have_interpretation
    (f : RDRSMethodFamily) (h : f ∈ missingNativeInterpretationRows) :
    Nonempty (MissingNativeInterpretation f) := by
  simp only [missingNativeInterpretationRows, List.mem_filter] at h
  rcases h with ⟨_, hs⟩
  cases hi : missingNativeInterpretation f with
  | none =>
      rw [hi] at hs
      contradiction
  | some i => exact ⟨i⟩

/-- The exact sixty-row complement represented by `missingNativeEvidence`. -/
def missingNativeRows : List RDRSMethodFamily :=
  allMethodFamilies.filter (fun f => (missingNativeEvidence f).isSome)

/-- Interpretation availability and theorem availability select the same sixty
row identities. -/
theorem missingNativeInterpretationRows_eq_missingNativeRows :
    missingNativeInterpretationRows = missingNativeRows := by decide

/-- The exact sixteen-row complement on which the historical adapter already
carries constructor-closed evidence. -/
def legacyNativeRows : List RDRSMethodFamily :=
  allMethodFamilies.filter (fun f => (missingNativeEvidence f).isNone)

/-- The complementary native-semantic wave contains exactly sixty rows. -/
theorem missingNativeRows_count : missingNativeRows.length = 60 := by decide

/-- The complement contains exactly the sixteen historical adapter rows. -/
theorem legacyNativeRows_count : legacyNativeRows.length = 16 := by decide

/-- The complementary list has no duplicates because it is a filter of the
closed 76-row universe. -/
theorem missingNativeRows_nodup : missingNativeRows.Nodup :=
  allMethodFamilies_nodup.filter _

/-- Every row in the complementary list carries its exact native semantic
proposition. -/
theorem missingNativeRows_have_evidence (f : RDRSMethodFamily)
    (h : f ∈ missingNativeRows) : Nonempty (MissingNativeRowClaim f) := by
  simp only [missingNativeRows, List.mem_filter] at h
  rcases h with ⟨_, hs⟩
  cases he : missingNativeEvidence f with
  | none =>
      rw [he] at hs
      contradiction
  | some p => exact ⟨p.down⟩

/-- None of the sixteen legacy theorem-backed rows is duplicated in the
complementary native-semantic list. -/
theorem legacy_rows_not_in_missingNativeRows :
    RDRSMethodFamily.standardKBO ∉ missingNativeRows ∧
    RDRSMethodFamily.subtermCoefficientKBO ∉ missingNativeRows ∧
    RDRSMethodFamily.cichonSlowGrowing ∉ missingNativeRows ∧
    RDRSMethodFamily.linearPolyQ ∉ missingNativeRows ∧
    RDRSMethodFamily.linearPolyR ∉ missingNativeRows ∧
    RDRSMethodFamily.matrixNScalarProjection ∉ missingNativeRows ∧
    RDRSMethodFamily.triangularMatrix ∉ missingNativeRows ∧
    RDRSMethodFamily.dpSubtermCriterion ∉ missingNativeRows ∧
    RDRSMethodFamily.dpArgumentFiltering ∉ missingNativeRows ∧
    RDRSMethodFamily.dpNeutralProcessors ∉ missingNativeRows ∧
    RDRSMethodFamily.usableRulesMinimality ∉ missingNativeRows ∧
    RDRSMethodFamily.sharingNonConservativity ∉ missingNativeRows ∧
    RDRSMethodFamily.equationalQuotientNonConservativity ∉ missingNativeRows ∧
    RDRSMethodFamily.cycleRewritingInapplicability ∉ missingNativeRows ∧
    RDRSMethodFamily.stringRewritingInapplicability ∉ missingNativeRows ∧
    RDRSMethodFamily.sizeChangeTerminationEscape ∉ missingNativeRows := by
  decide

structure MissingNativeCoverageClosed : Prop where
  exactCount : missingNativeRows.length = 60
  interpretationCount : missingNativeInterpretationRows.length = 60
  interpretationRowsExact : missingNativeInterpretationRows = missingNativeRows
  noDuplicates : missingNativeRows.Nodup
  everyListedRowHasInterpretation :
    ∀ f : RDRSMethodFamily, f ∈ missingNativeRows → Nonempty (MissingNativeInterpretation f)
  everyListedRowHasEvidence :
    ∀ f : RDRSMethodFamily, f ∈ missingNativeRows → Nonempty (MissingNativeRowClaim f)

theorem missing_native_coverage_closed : MissingNativeCoverageClosed where
  exactCount := missingNativeRows_count
  interpretationCount := missingNativeInterpretationRows_count
  interpretationRowsExact := missingNativeInterpretationRows_eq_missingNativeRows
  noDuplicates := missingNativeRows_nodup
  everyListedRowHasInterpretation := by
    intro f hf
    apply missingNativeInterpretationRows_have_interpretation f
    rwa [missingNativeInterpretationRows_eq_missingNativeRows]
  everyListedRowHasEvidence := missingNativeRows_have_evidence

end OperatorKO7.Methods.OrientationClosure.NativeSemanticCoverage
