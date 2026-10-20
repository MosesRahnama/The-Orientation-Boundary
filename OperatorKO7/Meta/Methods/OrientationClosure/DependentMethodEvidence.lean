import OperatorKO7.Meta.Methods.OrientationClosure.NativeSemanticCoverage

/-!
# Interpretation-dependent native method evidence

The earlier ORIENTATION layer records native method objects and row propositions
on parallel tracks.  This module adds the dependent layer: the semantic law is
indexed by, and stated about, the exact `MissingNativeInterpretation` object
being certified.  A certificate therefore cannot swap in a different package
object without changing its type.
-/

set_option autoImplicit false

namespace OperatorKO7.Methods.OrientationClosure.DependentMethodEvidence

open OperatorKO7
open OperatorKO7.StepDuplicating
open OperatorKO7.StepDuplicating.StepDuplicatingSchema
open OperatorKO7.SymbolicComparatorBarrier
open OperatorKO7.CompositionalImpossibility
open OperatorKO7.MetaDependencyPairs
open OperatorKO7.HigherOrderRewritingSyntax
open OperatorKO7.RDRSTerminationMethodUniverse
open OperatorKO7.Methods.PathOrderRows
open OperatorKO7.Methods.AlgebraicInterpretationRows
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
open OperatorKO7.Methods.OrientationClosure.NativeSemanticCoverage

/-! ## Package laws stated about the carried object -/

structure ORI1Laws (P : ORI1NativeSemantics.{0}) : Prop where
  kboBlocked : ¬ CompatibleNativeKBOGt P.kboWithStatus dupSrc dupTgt
  kboWeightWF : WellFounded
    (fun y x : STerm => NativeKBOStrictWeightGt P.kboWithStatus x y)
  generalizedWF : WellFounded (fun y x : STerm => GeneralizedKBOGt P.generalized x y)
  generalizedBlocked : ¬ GeneralizedKBOGt P.generalized dupSrc dupTgt
  acBlocked : ¬ NativeACKBOGt P.kboWithStatus dupSrc dupTgt
  acNontrivial : Relation.EqvGen ACRearrange
    (.wrap (.var SchemaVar.b) (.var SchemaVar.s))
    (.wrap (.var SchemaVar.s) (.var SchemaVar.b))
  transfiniteWF : WellFounded (fun y x : STerm => TransfiniteKBOGt P.transfinite x y)
  transfiniteBlocked : ¬ TransfiniteKBOGt P.transfinite dupSrc dupTgt
  lambdaFreeWF : WellFounded
    (fun y x : AppTerm => LambdaFreeNativeKBOGt P.lambdaFree x y)
  lambdaFreeBlocked : ¬ LambdaFreeNativeKBOGt P.lambdaFree (curry dupSrc) (curry dupTgt)
  polynomialWF : WellFounded
    (fun y x : STerm => PolynomialNativeKBOGt P.polynomial x y)
  polynomialBlocked : ¬ PolynomialNativeKBOGt P.polynomial dupSrc dupTgt
  acRpoNontrivial :
    P.acRPOOrder.equiv (.app .void (.delta .void)) (.app (.delta .void) .void)
  permutationStatusActive :
    P.permutationRPOData.status.perm .app ≠ Equiv.refl (Fin 2)
  popStarDataExact : P.popStarArgKind = ko7ArgKind
  popStarBlocked : ¬ Nonempty KO7POPStarCertificate
  simpleTerminationWF : WellFounded
    (fun y x : Trace => P.simpleTerminationOrder.gt x y)

 theorem ori1_laws (P : ORI1NativeSemantics.{0}) : ORI1Laws P where
  kboBlocked := P.kboWithStatusBlocked
  kboWeightWF := P.kboWithStatusWeightWF
  generalizedWF := P.generalizedWF
  generalizedBlocked := P.generalizedBlocked
  acBlocked := P.acBlocked
  acNontrivial := P.acTheoryNontrivial
  transfiniteWF := P.transfiniteWF
  transfiniteBlocked := P.transfiniteBlocked
  lambdaFreeWF := P.lambdaFreeWF
  lambdaFreeBlocked := P.lambdaFreeBlocked
  polynomialWF := P.polynomialWF
  polynomialBlocked := P.polynomialBlocked
  acRpoNontrivial := P.acRPOOrderNontrivial
  permutationStatusActive := P.permutationRPOStatusNonidentity
  popStarDataExact := P.popStarArgKindExact
  popStarBlocked := P.popStarNoCertificate
  simpleTerminationWF := P.simpleTerminationWF

structure ORI2Laws (P : AlgebraicNativeBundle) : Prop where
  negativeDebtActive :
    P.negative.eval (.wrap .base .base) < P.negative.eval .base + P.negative.eval .base
  maxNonconstant : P.maxMethod.eval .base < P.maxMethod.eval (.succ .base)
  maxBlocked :
    Not (forall b s n : FreeTerm,
      P.maxMethod.eval (freeSchema.wrap s (freeSchema.recur b s n)) <
        P.maxMethod.eval (freeSchema.recur b s (freeSchema.succ n)))
  polynomialInside : NoCounterExponent P.polynomialBoundary.inside
  polynomialOutside : ¬ EventuallyDominatedAtBase P.polynomialBoundary.outside
  multilinearInside : NoStepCounterCoupling P.multilinearBoundary.inside
  multilinearOutside : ¬ MultilinearDominatedAtBase P.multilinearBoundary.outside
  rationalNonNat : ¬ ∃ n : Nat,
    P.matrixFields.rational.interpretation.succ_mat.coeff 0 0 = (n : ℚ)
  realNonconstant :
    P.matrixFields.real.interpretation.eval .base ≠
      P.matrixFields.real.interpretation.eval (.succ .base)
  arcticFinite : ArcticWrapDiagFinite P.arcticMethod 0
  arcticBlocked :
    ¬ ∀ b s n : OperatorKO7.StepDuplicating.StepDuplicatingSchema.FreeTerm,
      ArcticLt
        (P.arcticMethod.eval
          (OperatorKO7.StepDuplicating.StepDuplicatingSchema.freeSchema.wrap s
            (OperatorKO7.StepDuplicating.StepDuplicatingSchema.freeSchema.recur b s n)) 0)
        (P.arcticMethod.eval
          (OperatorKO7.StepDuplicating.StepDuplicatingSchema.freeSchema.recur b s
            (OperatorKO7.StepDuplicating.StepDuplicatingSchema.freeSchema.succ n)) 0)
  tropicalRoot : ∀ b s n : FreeTerm,
    TropicalLt
      (P.tropicalMethod.eval (freeSchema.wrap s (freeSchema.recur b s n)) 0)
      (P.tropicalMethod.eval (freeSchema.recur b s (freeSchema.succ n)) 0)
  tropicalContextBlocked :
    ¬ ∀ {a b : FreeTerm}, FreeDupStepCtx a b →
      TropicalLt (P.tropicalMethod.eval b 0) (P.tropicalMethod.eval a 0)
  tupleOrients : ∀ b s n : FreeTerm,
    (P.tupleMethod (freeSchema.wrap s (freeSchema.recur b s n))).1 <
      (P.tupleMethod (freeSchema.recur b s (freeSchema.succ n))).1
  tupleNotAffine :
    ¬ ∃ T : CostSizeTupleInterpretation freeSchema, ∀ t, T.eval t = P.tupleMethod t
  higherOrderBinderActive :
    (P.higherOrderTuple.eval (.lam 0 .atom)).2 ≠ (P.higherOrderTuple.eval .atom).2
  higherOrderTupleBlocked :
    Not (forall b s n : FreeTerm,
      (P.higherOrderTuple.eval
        (P.higherOrderTuple.encode (freeSchema.wrap s (freeSchema.recur b s n)))).1 <
      (P.higherOrderTuple.eval
        (P.higherOrderTuple.encode (freeSchema.recur b s (freeSchema.succ n)))).1)
  archimedeanNonconstant :
    P.archimedean.eval .base < P.archimedean.eval (.succ .base)
  archimedeanBlocked :
    Not (forall b s n : FreeTerm,
      P.archimedean.eval (freeSchema.wrap s (freeSchema.recur b s n)) <
        P.archimedean.eval (freeSchema.recur b s (freeSchema.succ n)))

 theorem ori2_laws (P : AlgebraicNativeBundle) : ORI2Laws P where
  negativeDebtActive := P.negativeDebtActive
  maxNonconstant := P.maxNonconstant
  maxBlocked := P.maxBlocked
  polynomialInside := P.polynomialBoundary.insideNoCounterExponent
  polynomialOutside := P.polynomialBoundary.outsideViolatesDominance
  multilinearInside := P.multilinearBoundary.insideNoCoupling
  multilinearOutside := P.multilinearBoundary.outsideViolatesDominance
  rationalNonNat := P.matrixFields.rationalHasNonNatEntry
  realNonconstant := P.matrixFields.realNonconstant
  arcticFinite := P.arcticFinite
  arcticBlocked := P.arcticBlocked
  tropicalRoot := P.tropicalRootOrients
  tropicalContextBlocked := P.tropicalContextBlocked
  tupleOrients := P.tupleOrients
  tupleNotAffine := P.tupleNotAffineFirst
  higherOrderBinderActive := P.higherOrderTuple.binderSensitive
  higherOrderTupleBlocked := P.higherOrderTupleBlocked
  archimedeanNonconstant := P.archimedeanNonconstant
  archimedeanBlocked := P.archimedeanBlocked

structure ORI3Laws (P : SemanticStructuralNativeBundle) : Prop where
  semanticExact : P.labels.semantic = constructorRootLabelling
  predictiveExact : P.labels.predictive = predictiveLabelling (fun t => decide (t = dupSrc))
  selfExact : P.labels.self = selfLabelling
  extendedBlocked :
    ¬ ∀ b s n : freeSchema.T,
      P.extended.strict
        (P.extended.eval (freeSchema.wrap s (freeSchema.recur b s n)))
        (P.extended.eval (freeSchema.recur b s (freeSchema.succ n)))
  finiteWeakInhabited :
    P.weakFinite.rank (P.weakFinite.eval freeSchema.base) ≤
      P.weakFinite.rank (P.weakFinite.eval (freeSchema.wrap freeSchema.base freeSchema.base))
  matchLinear : ∀ {a b : Nat} {n : Nat},
    RelPow CountdownStep a n b → n ≤ P.countdownMatchBound.bound * (a + 1)
  semanticOrients : RootLabelGt boolLabelValue
    (labelTerm P.labels.semantic dupSrc) (labelTerm P.labels.semantic dupTgt)
  semanticContextFailure : ¬ SuccContextCompatible (RootLabelGt boolLabelValue)
  selfDistinguishes :
    [STerm.var SchemaVar.b, STerm.var SchemaVar.s, STerm.succ (STerm.var SchemaVar.n)] ≠
      [STerm.var SchemaVar.s,
        STerm.recur (STerm.var SchemaVar.b) (STerm.var SchemaVar.s) (STerm.var SchemaVar.n)]
  categoryIdentity : ∀ t, P.category.Hom t t
  categoryGenerator : ∀ {a b}, Step a b → P.category.Hom a b
  forwardRequirementFails : ¬ P.forwardBoundary.requirement
  quasiWellFounded : WellFounded (fun a b : Trace => Step b a)

 theorem ori3_laws (P : SemanticStructuralNativeBundle) : ORI3Laws P where
  semanticExact := P.labels.semanticExact
  predictiveExact := P.labels.predictiveExact
  selfExact := P.labels.selfExact
  extendedBlocked := extendedMonotoneAlgebra_row_anchor freeSchema P.extended
  finiteWeakInhabited := P.weakFinite.wrap_weak freeSchema.base freeSchema.base
  matchLinear := by
    intro a b n h
    exact P.countdownMatchBound.linear_bound h
  semanticOrients := P.labels.semanticOrients
  semanticContextFailure := P.labels.semanticContextFailure
  selfDistinguishes := P.labels.selfDistinguishes
  categoryIdentity := P.category.identity
  categoryGenerator := P.category.generator
  forwardRequirementFails := P.forwardBoundary.ko7Fails
  quasiWellFounded := P.quasiDecreasing.1

structure ORI4Laws (P : DependencyPairNativeBundle) : Prop where
  distinctStrictRelations : P.pairOne.strict ≠ P.pairTwo.strict
  pairOneWF : WellFounded (fun y x : Trace => P.pairOne.strict x y)
  pairTwoWF : WellFounded (fun y x : Trace => P.pairTwo.strict x y)
  tripleEquivReflexive : Reflexive P.triple.equiv
  formativeExact : ∀ a b : Trace, (∃ tag, FormativePair tag a b) ↔ DPPair a b
  formativeWF : WellFounded (fun y x : Trace => ∃ tag, FormativePair tag x y)
  typedWF : WellFounded
    (fun y x : OperatorKO7.TypedBarrierSurvival.Term .res =>
      SortedTransport.TypedRecSuccStep x y)
  orderedWF : WellFounded (fun y x : OrderSortedTerm => OrderSortedDPPair x y)
  replacementPayloadFrozen : P.replacement.recurAllows 1 = false
  replacementCounterActive : P.replacement.recurAllows 2 = true
  contextSensitiveWF :
    WellFounded (fun a b : Trace => ContextSensitiveStep P.replacement Step b a)
  conditionDimensionLive : FixtureTwoDDP .condition 1 0
  operationalConditionalWF : ∀ satisfies : Trace × Trace → Prop,
    WellFounded (fun a b : Trace => KO7ConditionalOperationalStep satisfies b a)
  constrainedWF : WellFounded (fun a b : Trace => ConstrainedDPPair b a)
  higherOrderConstrainedWF : WellFounded
    (fun a b : OperatorKO7.HigherOrderRewritingSyntax.HOTerm =>
      HigherOrderConstrainedDPPair b a)

 theorem ori4_laws (P : DependencyPairNativeBundle) : ORI4Laws P where
  distinctStrictRelations := P.relationSeparation
  pairOneWF := P.pairOne.strict_reverse_wellFounded
  pairTwoWF := P.pairTwo.strict_reverse_wellFounded
  tripleEquivReflexive := P.triple.equiv_refl
  formativeExact := P.formativeExact
  formativeWF := P.formativeWF
  typedWF := P.typedWF
  orderedWF := P.orderedWF
  replacementPayloadFrozen := P.replacementPayloadFrozen
  replacementCounterActive := P.replacementCounterActive
  contextSensitiveWF := P.contextSensitiveWF
  conditionDimensionLive := P.conditionEdge
  operationalConditionalWF := P.operationalConditionalWF
  constrainedWF := P.constrainedWF
  higherOrderConstrainedWF := P.higherOrderConstrainedWF

structure ORI5Laws (P : HigherOrderNativeBundle) : Prop where
  horpoCall : HORPOGt P.horpo hoMatchedCounter hoRecursiveCounter
  horpoWF : WellFounded (fun y x : HOTerm => HORPOGt P.horpo x y)
  cpoCall : HOComputabilityClosure hoRecursiveCounter hoMatchedCounter
  cpoWF : WellFounded HOComputabilityClosure
  generalSchemaDescent : HOStrictSubterm P.generalSchema.recursive P.generalSchema.matched
  guard : GuardDerivation hoRecursiveCounter hoMatchedCounter
  sized : SizedCall ⟨hoMatchedCounter, 1⟩ ⟨hoRecursiveCounter, 0⟩
  safePositive : Nonempty (SafeNormalRuleDerivation dupSrc dupSrc)
  safeDupBlocked : ¬ Nonempty (SafeNormalRuleDerivation dupSrc dupTgt)
  resourcePositive : maximalResourceSoundRuleTyping.Derivable dupSrc dupSrc
  resourceDupBlocked : ¬ maximalResourceSoundRuleTyping.Derivable dupSrc dupTgt
  ramifiedPositive : Nonempty (RamifiedRuleDerivation dupSrc dupSrc)
  ramifiedDupBlocked : ¬ Nonempty (RamifiedRuleDerivation dupSrc dupTgt)
  abstractCounterDescent :
    P.abstractMethod.abstract
      (STerm.recur (STerm.var SchemaVar.b) (STerm.var SchemaVar.s) recursiveCallCounter) 2 <
      P.abstractMethod.abstract dupSrc 2
  infinitaryControl : InfiniteForwardReduction UnitLoop

 theorem ori5_laws (P : HigherOrderNativeBundle) : ORI5Laws P where
  horpoCall := P.horpoCall
  horpoWF := horpoGt_wellFounded P.horpo
  cpoCall := P.cpoCall
  cpoWF := hoComputabilityClosure_wellFounded
  generalSchemaDescent := P.generalSchema.descent
  guard := P.guard
  sized := P.sized
  safePositive := ⟨P.safeNormalPositive⟩
  safeDupBlocked := no_safeNormalDupDerivation
  resourcePositive := P.resourcePositive
  resourceDupBlocked := P.resourceDupBlocked
  ramifiedPositive := ⟨P.ramifiedPositive⟩
  ramifiedDupBlocked := no_ramifiedDupDerivation
  abstractCounterDescent := P.abstractMethod.counterDescent
  infinitaryControl := P.infiniteControl

structure ORI6Laws (P : ORI6NativeSemantics) : Prop where
  weightedGraphExact : ExactStrictSubstrateExtension weightedTypeGraphTransport
  weightedGraphWF : WellFounded (fun y x : GraphNode => GraphLiftStep x y)
  generalizedGraphWF :
    WellFounded (fun y x : GeneralizedGraphNode => GeneralizedGraphStep x y)
  generalizedWeightActive : ∀ g : GraphNode,
    generalizedGraphWeight (1, g) ≠ generalizedGraphWeight (0, g)
  processExact : ExactStrictSubstrateExtension piCalculusTransport
  processWF : WellFounded (fun y x : ProcessTerm => ProcessLiftStep x y)
  piFragmentWF : WellFounded (fun y x : NativePiTerm => NativePiStep x y)
  cpsExact : ExactStrictSubstrateExtension lambdaMuCPSTransport
  cpsWF : WellFounded (fun y x : CPSTerm => CPSLiftStep x y)
  lambdaMuSimulation : ∀ {t u}, LambdaMuStep t u →
    NativeCPSStep (lambdaMuToCPS t) (lambdaMuToCPS u)
  nativeCPSWF : WellFounded (fun y x : NativeCPSTerm => NativeCPSStep x y)
  sharingNonconstant : P.sharingQI.eval .leaf ≠ P.sharingQI.eval (.shared .leaf)
  sharingWF : WellFounded (fun y x : SharedTerm => SharedDupStep x y)
  sharingNoninjective : ¬ Function.Injective unshare

 theorem ori6_laws (P : ORI6NativeSemantics) : ORI6Laws P where
  weightedGraphExact := P.weightedGraphExact
  weightedGraphWF := P.weightedGraphNativeWF
  generalizedGraphWF := P.generalizedGraphNativeWF
  generalizedWeightActive := P.generalizedWeightActive
  processExact := P.processExact
  processWF := P.processNativeWF
  piFragmentWF := P.piFragmentWF
  cpsExact := P.cpsExact
  cpsWF := P.cpsNativeWF
  lambdaMuSimulation := P.lambdaMuSimulation
  nativeCPSWF := P.nativeCPSWF
  sharingNonconstant := P.sharingQINonconstant
  sharingWF := P.sharingWF
  sharingNoninjective := P.sharingNoninjective

/-! ## Row-indexed dependent law -/

/-- Semantic laws attached to the exact row-indexed interpretation object.
Every branch mentions the package object stored by that constructor. -/
def NativeMethodLaws : {f : RDRSMethodFamily} → MissingNativeInterpretation f → Prop
  | _, .kboWithStatus P => ORI1Laws P
  | _, .generalizedKBO P => ORI1Laws P
  | _, .acKBO P => ORI1Laws P
  | _, .transfiniteKBO P => ORI1Laws P
  | _, .lambdaFreeKBO P => ORI1Laws P
  | _, .acRPO P => ORI1Laws P
  | _, .rpoModuloPermutation P => ORI1Laws P
  | _, .popStarFamily P => ORI1Laws P
  | _, .simpleTerminationOrderType P => ORI1Laws P
  | _, .negativeCoefficientPolynomial P => ORI2Laws P
  | _, .maxPolynomial P => ORI2Laws P
  | _, .nonlinearHigherDegreePolynomial P => ORI2Laws P
  | _, .multilinearInterpretation P => ORI2Laws P
  | _, .matrixQRScalarProjection P => ORI2Laws P
  | _, .arcticScalarProjection P => ORI2Laws P
  | _, .tropicalScalarProjection P => ORI2Laws P
  | _, .tupleInterpretationStrictS P => ORI2Laws P
  | _, .higherOrderTupleInterpretation P => ORI2Laws P
  | _, .polynomialKBO P => ORI1Laws P
  | _, .strictMonotoneAlgebraArchimedean P => ORI2Laws P
  | _, .extendedMonotoneAlgebra P => ORI3Laws P
  | _, .semanticLabeling P => ORI3Laws P
  | _, .predictiveLabeling P => ORI3Laws P
  | _, .rootLabeling P => ORI3Laws P
  | _, .selfLabelingEquational P => ORI3Laws P
  | _, .finiteModelTermination P => ORI3Laws P
  | _, .categoricalToposTermination P => ORI3Laws P
  | _, .forwardClosures P => ORI3Laws P
  | _, .matchBounds P => ORI3Laws P
  | _, .raiseConsistencyMatchBounds P => ORI3Laws P
  | _, .quasiDecreasingness P => ORI3Laws P
  | _, .dpProcessorClassification P => ORI4Laws P
  | _, .dpReductionPairProcessor P => ORI4Laws P
  | _, .dpReductionTriples P => ORI4Laws P
  | _, .formativeRules P => ORI4Laws P
  | _, .typeIntroduction P => ORI4Laws P
  | _, .manySortedPersistence P => ORI4Laws P
  | _, .orderSortedDP P => ORI4Laws P
  | _, .contextSensitiveDP P => ORI4Laws P
  | _, .twoDDPForCTRS P => ORI4Laws P
  | _, .operationalTerminationCTRS P => ORI4Laws P
  | _, .integerTermRewriting P => ORI4Laws P
  | _, .lctrs P => ORI4Laws P
  | _, .higherOrderLCTRS P => ORI4Laws P
  | _, .horpoAdmittance P => ORI5Laws P
  | _, .cpoAdmittance P => ORI5Laws P
  | _, .generalSchemaAdmittance P => ORI5Laws P
  | _, .sizedTypesAdmittance P => ORI5Laws P
  | _, .coqGuardAdmittance P => ORI5Laws P
  | _, .bellantoniCookSplit P => ORI5Laws P
  | _, .linearLogicTypingBarrier P => ORI5Laws P
  | _, .ramifiedRecursionTypingBarrier P => ORI5Laws P
  | _, .weightedTypeGraphEscape P => ORI6Laws P
  | _, .generalizedWeightedTypeGraphs P => ORI6Laws P
  | _, .leftLinearMatchBounds P => ORI3Laws P
  | _, .infinitaryRewritingTermination P => ORI5Laws P
  | _, .piCalculusTerminationTranslation P => ORI6Laws P
  | _, .lambdaMuSNViaCPS P => ORI6Laws P
  | _, .abstractInterpretationAdmittance P => ORI5Laws P
  | _, .quasiInterpretationsSharingAware P => ORI6Laws P

/-- Every row-indexed interpretation object entails laws about that same object. -/
theorem nativeMethodLaws_closed
    {f : RDRSMethodFamily} (i : MissingNativeInterpretation f) : NativeMethodLaws i := by
  cases i <;>
    first
    | exact ori1_laws _
    | exact ori2_laws _
    | exact ori3_laws _
    | exact ori4_laws _
    | exact ori5_laws _
    | exact ori6_laws _

/-- A row-specific semantic witness about the exact stored package object.
Different constructors from the same ORI package select different properties. -/
def NativeRowWitness : {f : RDRSMethodFamily} → MissingNativeInterpretation f → Prop
  | _, .kboWithStatus P =>
      ¬ CompatibleNativeKBOGt P.kboWithStatus dupSrc dupTgt
  | _, .generalizedKBO P =>
      WellFounded (fun y x : STerm => GeneralizedKBOGt P.generalized x y)
  | _, .acKBO P =>
      ORI1Laws P ∧
        Relation.EqvGen ACRearrange
          (.wrap (.var SchemaVar.b) (.var SchemaVar.s))
          (.wrap (.var SchemaVar.s) (.var SchemaVar.b))
  | _, .transfiniteKBO P =>
      ¬ TransfiniteKBOGt P.transfinite dupSrc dupTgt
  | _, .lambdaFreeKBO P =>
      ¬ LambdaFreeNativeKBOGt P.lambdaFree (curry dupSrc) (curry dupTgt)
  | _, .acRPO P =>
      WellFounded (fun y x : Trace => P.acRPOOrder.gt x y)
  | _, .rpoModuloPermutation P =>
      P.permutationRPOData.status.perm .app ≠ Equiv.refl (Fin 2)
  | _, .popStarFamily P =>
      ORI1Laws P ∧ ¬ Nonempty KO7POPStarCertificate
  | _, .simpleTerminationOrderType P =>
      WellFounded (fun y x : Trace => P.simpleTerminationOrder.gt x y)
  | _, .negativeCoefficientPolynomial P =>
      P.negative.eval (.wrap .base .base) < P.negative.eval .base + P.negative.eval .base
  | _, .maxPolynomial P =>
      Not (forall b s n : FreeTerm,
        P.maxMethod.eval (freeSchema.wrap s (freeSchema.recur b s n)) <
          P.maxMethod.eval (freeSchema.recur b s (freeSchema.succ n)))
  | _, .nonlinearHigherDegreePolynomial P =>
      forall b s n : FreeTerm,
        P.polynomialBoundary.outside.eval
            (freeSchema.wrap s (freeSchema.recur b s n)) <
          P.polynomialBoundary.outside.eval
            (freeSchema.recur b s (freeSchema.succ n))
  | _, .multilinearInterpretation P =>
      forall b s n : FreeTerm,
        P.multilinearBoundary.outside.eval
            (freeSchema.wrap s (freeSchema.recur b s n)) <
          P.multilinearBoundary.outside.eval
            (freeSchema.recur b s (freeSchema.succ n))
  | _, .matrixQRScalarProjection P =>
      ¬ ∃ n : Nat,
        P.matrixFields.rational.interpretation.succ_mat.coeff 0 0 = (n : ℚ)
  | _, .arcticScalarProjection P =>
      Not (forall b s n : OperatorKO7.StepDuplicating.StepDuplicatingSchema.FreeTerm,
        ArcticLt
          (P.arcticMethod.eval
            (OperatorKO7.StepDuplicating.StepDuplicatingSchema.freeSchema.wrap s
              (OperatorKO7.StepDuplicating.StepDuplicatingSchema.freeSchema.recur b s n)) 0)
          (P.arcticMethod.eval
            (OperatorKO7.StepDuplicating.StepDuplicatingSchema.freeSchema.recur b s
              (OperatorKO7.StepDuplicating.StepDuplicatingSchema.freeSchema.succ n)) 0))
  | _, .tropicalScalarProjection P =>
      forall b s n : FreeTerm,
        TropicalLt
          (P.tropicalMethod.eval (freeSchema.wrap s (freeSchema.recur b s n)) 0)
          (P.tropicalMethod.eval (freeSchema.recur b s (freeSchema.succ n)) 0)
  | _, .tupleInterpretationStrictS P =>
      forall b s n : FreeTerm,
        (P.tupleMethod (freeSchema.wrap s (freeSchema.recur b s n))).1 <
          (P.tupleMethod (freeSchema.recur b s (freeSchema.succ n))).1
  | _, .higherOrderTupleInterpretation P =>
      Not (forall b s n : FreeTerm,
        (P.higherOrderTuple.eval
          (P.higherOrderTuple.encode (freeSchema.wrap s (freeSchema.recur b s n)))).1 <
        (P.higherOrderTuple.eval
          (P.higherOrderTuple.encode (freeSchema.recur b s (freeSchema.succ n)))).1)
  | _, .polynomialKBO P =>
      ¬ PolynomialNativeKBOGt P.polynomial dupSrc dupTgt
  | _, .strictMonotoneAlgebraArchimedean P =>
      Not (forall b s n : FreeTerm,
        P.archimedean.eval (freeSchema.wrap s (freeSchema.recur b s n)) <
          P.archimedean.eval (freeSchema.recur b s (freeSchema.succ n)))
  | _, .extendedMonotoneAlgebra P =>
      Not (forall b s n : freeSchema.T,
        P.extended.strict
          (P.extended.eval (freeSchema.wrap s (freeSchema.recur b s n)))
          (P.extended.eval (freeSchema.recur b s (freeSchema.succ n))))
  | _, .semanticLabeling P =>
      RootLabelGt boolLabelValue
        (labelTerm P.labels.semantic dupSrc) (labelTerm P.labels.semantic dupTgt)
  | _, .predictiveLabeling P =>
      P.labels.predictive = predictiveLabelling (fun t => decide (t = dupSrc))
  | _, .rootLabeling P =>
      ORI3Laws P ∧ ¬ SuccContextCompatible (RootLabelGt boolLabelValue)
  | _, .selfLabelingEquational P =>
      P.labels.self = selfLabelling
  | _, .finiteModelTermination P =>
      forall x y,
        P.weakFinite.rank (P.weakFinite.eval y) ≤
          P.weakFinite.rank (P.weakFinite.eval (freeSchema.wrap x y))
  | _, .categoricalToposTermination P =>
      forall {a b}, Step a b → P.category.Hom a b
  | _, .forwardClosures P =>
      ¬ P.forwardBoundary.requirement
  | _, .matchBounds P =>
      forall {a b : Nat} {n : Nat}, RelPow CountdownStep a n b →
        n ≤ P.countdownMatchBound.bound * (a + 1)
  | _, .raiseConsistencyMatchBounds P =>
      forall {a b : Nat}, CountdownStep a b →
        P.countdownMatchBound.height b + 1 ≤ P.countdownMatchBound.height a
  | _, .quasiDecreasingness P =>
      ORI3Laws P ∧ WellFounded (fun a b : Trace => Step b a)
  | _, .dpProcessorClassification P =>
      forall {a c}, P.problem.pairStep a c → ∃ rhs, P.problem.sourceStep a rhs
  | _, .dpReductionPairProcessor P =>
      WellFounded (fun y x : Trace => P.pairOne.strict x y)
  | _, .dpReductionTriples P =>
      Reflexive P.triple.equiv
  | _, .formativeRules P =>
      ORI4Laws P ∧ (forall a b : Trace, (∃ tag, FormativePair tag a b) ↔ DPPair a b)
  | _, .typeIntroduction P =>
      ORI4Laws P ∧
        WellFounded
          (fun y x : OperatorKO7.TypedBarrierSurvival.Term .res =>
            SortedTransport.TypedRecSuccStep x y)
  | _, .manySortedPersistence P =>
      ORI4Laws P ∧
        OperatorKO7.ManySortedBarrierSurvival.MSort = OperatorKO7.TypedBarrierSurvival.Ty
  | _, .orderSortedDP P =>
      ORI4Laws P ∧ WellFounded (fun y x : OrderSortedTerm => OrderSortedDPPair x y)
  | _, .contextSensitiveDP P =>
      WellFounded (fun a b : Trace => ContextSensitiveStep P.replacement Step b a)
  | _, .twoDDPForCTRS P =>
      ORI4Laws P ∧ (forall a b : Trace, ¬ KO7TwoDDP .condition a b)
  | _, .operationalTerminationCTRS P =>
      ORI4Laws P ∧
        (forall satisfies : Trace × Trace → Prop,
          WellFounded (fun a b : Trace => KO7ConditionalOperationalStep satisfies b a))
  | _, .integerTermRewriting P =>
      forall {a b : Trace}, DPPair a b → P.constrained.counter b < P.constrained.counter a
  | _, .lctrs P =>
      ORI4Laws P ∧ WellFounded (fun a b : Trace => ConstrainedDPPair b a)
  | _, .higherOrderLCTRS P =>
      ORI4Laws P ∧
        WellFounded
          (fun a b : OperatorKO7.HigherOrderRewritingSyntax.HOTerm =>
            HigherOrderConstrainedDPPair b a)
  | _, .horpoAdmittance P =>
      HORPOGt P.horpo hoMatchedCounter hoRecursiveCounter
  | _, .cpoAdmittance P =>
      ORI5Laws P ∧ HOComputabilityClosure hoRecursiveCounter hoMatchedCounter
  | _, .generalSchemaAdmittance P =>
      HOStrictSubterm P.generalSchema.recursive P.generalSchema.matched
  | _, .sizedTypesAdmittance P =>
      ORI5Laws P ∧ SizedCall ⟨hoMatchedCounter, 1⟩ ⟨hoRecursiveCounter, 0⟩
  | _, .coqGuardAdmittance P =>
      ORI5Laws P ∧ GuardDerivation hoRecursiveCounter hoMatchedCounter
  | _, .bellantoniCookSplit P =>
      ORI5Laws P ∧ Nonempty (SafeNormalRuleDerivation dupSrc dupSrc)
  | _, .linearLogicTypingBarrier P =>
      ORI5Laws P ∧ ¬ maximalResourceSoundRuleTyping.Derivable dupSrc dupTgt
  | _, .ramifiedRecursionTypingBarrier P =>
      ORI5Laws P ∧ ¬ Nonempty (RamifiedRuleDerivation dupSrc dupTgt)
  | _, .weightedTypeGraphEscape P =>
      ORI6Laws P ∧ ExactStrictSubstrateExtension weightedTypeGraphTransport
  | _, .generalizedWeightedTypeGraphs P =>
      ORI6Laws P ∧
        (forall g : GraphNode,
          generalizedGraphWeight (1, g) ≠ generalizedGraphWeight (0, g))
  | _, .leftLinearMatchBounds P =>
      leftLinearDup ∧
        (forall {a b : Nat} {n : Nat}, RelPow CountdownStep a n b →
          n ≤ P.countdownMatchBound.bound * (a + 1))
  | _, .infinitaryRewritingTermination P =>
      ORI5Laws P ∧ InfiniteForwardReduction UnitLoop
  | _, .piCalculusTerminationTranslation P =>
      ORI6Laws P ∧ WellFounded (fun y x : NativePiTerm => NativePiStep x y)
  | _, .lambdaMuSNViaCPS P =>
      ORI6Laws P ∧
        (forall {t u}, LambdaMuStep t u →
          NativeCPSStep (lambdaMuToCPS t) (lambdaMuToCPS u))
  | _, .abstractInterpretationAdmittance P =>
      P.abstractMethod.abstract
        (STerm.recur (STerm.var SchemaVar.b) (STerm.var SchemaVar.s)
          recursiveCallCounter) 2 <
        P.abstractMethod.abstract dupSrc 2
  | _, .quasiInterpretationsSharingAware P =>
      P.sharingQI.eval .leaf ≠ P.sharingQI.eval (.shared .leaf)

/-- Every row-specific witness follows from the exact package object stored in
that interpretation constructor. -/
theorem nativeRowWitness_closed
    {f : RDRSMethodFamily} (i : MissingNativeInterpretation f) : NativeRowWitness i := by
  cases i with
  | kboWithStatus P => exact P.kboWithStatusBlocked
  | generalizedKBO P => exact P.generalizedWF
  | acKBO P => exact ⟨ori1_laws P, P.acTheoryNontrivial⟩
  | transfiniteKBO P => exact P.transfiniteBlocked
  | lambdaFreeKBO P => exact P.lambdaFreeBlocked
  | acRPO P => exact P.acRPOOrder.gt_wellFounded
  | rpoModuloPermutation P => exact P.permutationRPOStatusNonidentity
  | popStarFamily P => exact ⟨ori1_laws P, P.popStarNoCertificate⟩
  | simpleTerminationOrderType P => exact P.simpleTerminationWF
  | negativeCoefficientPolynomial P => exact P.negativeDebtActive
  | maxPolynomial P => exact P.maxBlocked
  | nonlinearHigherDegreePolynomial P => exact P.polynomialBoundary.outsideOrients
  | multilinearInterpretation P => exact P.multilinearBoundary.outsideOrients
  | matrixQRScalarProjection P => exact P.matrixFields.rationalHasNonNatEntry
  | arcticScalarProjection P => exact P.arcticBlocked
  | tropicalScalarProjection P => exact P.tropicalRootOrients
  | tupleInterpretationStrictS P => exact P.tupleOrients
  | higherOrderTupleInterpretation P => exact P.higherOrderTupleBlocked
  | polynomialKBO P => exact P.polynomialBlocked
  | strictMonotoneAlgebraArchimedean P => exact P.archimedeanBlocked
  | extendedMonotoneAlgebra P => exact (ori3_laws P).extendedBlocked
  | semanticLabeling P => exact P.labels.semanticOrients
  | predictiveLabeling P => exact P.labels.predictiveExact
  | rootLabeling P => exact ⟨ori3_laws P, P.labels.semanticContextFailure⟩
  | selfLabelingEquational P => exact P.labels.selfExact
  | finiteModelTermination P => exact P.weakFinite.wrap_weak
  | categoricalToposTermination P => exact P.category.generator
  | forwardClosures P => exact P.forwardBoundary.ko7Fails
  | matchBounds P =>
      intro a b n h
      exact P.countdownMatchBound.linear_bound h
  | raiseConsistencyMatchBounds P => exact P.countdownMatchBound.transition_decreases
  | quasiDecreasingness P => exact ⟨ori3_laws P, P.quasiDecreasing.1⟩
  | dpProcessorClassification P => exact P.problem.extractedFromSource
  | dpReductionPairProcessor P => exact P.pairOne.strict_reverse_wellFounded
  | dpReductionTriples P => exact P.triple.equiv_refl
  | formativeRules P => exact ⟨ori4_laws P, P.formativeExact⟩
  | typeIntroduction P => exact ⟨ori4_laws P, P.typedWF⟩
  | manySortedPersistence P => exact ⟨ori4_laws P, P.manySortedIdentity⟩
  | orderSortedDP P => exact ⟨ori4_laws P, P.orderedWF⟩
  | contextSensitiveDP P => exact P.contextSensitiveWF
  | twoDDPForCTRS P => exact ⟨ori4_laws P, P.twoDConditionEmpty⟩
  | operationalTerminationCTRS P => exact ⟨ori4_laws P, P.operationalConditionalWF⟩
  | integerTermRewriting P => exact P.constrained.decreases
  | lctrs P => exact ⟨ori4_laws P, P.constrainedWF⟩
  | higherOrderLCTRS P => exact ⟨ori4_laws P, P.higherOrderConstrainedWF⟩
  | horpoAdmittance P => exact P.horpoCall
  | cpoAdmittance P => exact ⟨ori5_laws P, P.cpoCall⟩
  | generalSchemaAdmittance P => exact P.generalSchema.descent
  | sizedTypesAdmittance P => exact ⟨ori5_laws P, P.sized⟩
  | coqGuardAdmittance P => exact ⟨ori5_laws P, P.guard⟩
  | bellantoniCookSplit P => exact ⟨ori5_laws P, ⟨P.safeNormalPositive⟩⟩
  | linearLogicTypingBarrier P => exact ⟨ori5_laws P, P.resourceDupBlocked⟩
  | ramifiedRecursionTypingBarrier P => exact ⟨ori5_laws P, no_ramifiedDupDerivation⟩
  | weightedTypeGraphEscape P => exact ⟨ori6_laws P, P.weightedGraphExact⟩
  | generalizedWeightedTypeGraphs P => exact ⟨ori6_laws P, P.generalizedWeightActive⟩
  | leftLinearMatchBounds P =>
      refine ⟨leftLinearDup_holds, ?_⟩
      intro a b n h
      exact P.countdownMatchBound.linear_bound h
  | infinitaryRewritingTermination P => exact ⟨ori5_laws P, P.infiniteControl⟩
  | piCalculusTerminationTranslation P => exact ⟨ori6_laws P, P.piFragmentWF⟩
  | lambdaMuSNViaCPS P => exact ⟨ori6_laws P, P.lambdaMuSimulation⟩
  | abstractInterpretationAdmittance P => exact P.abstractMethod.counterDescent
  | quasiInterpretationsSharingAware P => exact P.sharingQINonconstant

/-- Interpretation-dependent certificate.  The package laws and the row-specific
witness are both indexed by the exact stored interpretation value. -/
structure DependentNativeCertificate (f : RDRSMethodFamily) : Type 2 where
  interpretation : MissingNativeInterpretation f
  laws : NativeMethodLaws interpretation
  rowWitness : NativeRowWitness interpretation

/-- Canonical dependent certificate on exactly the sixty complementary rows. -/
noncomputable def dependentNativeCertificate :
    (f : RDRSMethodFamily) → Option (DependentNativeCertificate f) := fun f =>
  match missingNativeInterpretation f with
  | none => none
  | some i => some ⟨i, nativeMethodLaws_closed i, nativeRowWitness_closed i⟩

/-- Rows selected by the dependent-certificate layer. -/
noncomputable def dependentNativeRows : List RDRSMethodFamily :=
  allMethodFamilies.filter (fun f => (dependentNativeCertificate f).isSome)

/-- The dependent layer selects the same sixty row identities as the native
interpretation layer. -/
theorem dependentNativeRows_eq_missingNativeInterpretationRows :
    dependentNativeRows = missingNativeInterpretationRows := by
  decide

/-- Hence exactly sixty complementary rows carry interpretation-dependent
certificates. -/
theorem dependentNativeRows_count : dependentNativeRows.length = 60 := by
  rw [dependentNativeRows_eq_missingNativeInterpretationRows]
  exact missingNativeInterpretationRows_count

/-- Membership in the dependent row list produces a certificate whose laws are
about its own stored interpretation. -/
theorem dependentNativeRows_have_certificate
    (f : RDRSMethodFamily) (h : f ∈ dependentNativeRows) :
    Nonempty (DependentNativeCertificate f) := by
  simp only [dependentNativeRows, List.mem_filter] at h
  rcases h with ⟨_, hs⟩
  cases hc : dependentNativeCertificate f with
  | none =>
      rw [hc] at hs
      contradiction
  | some c => exact ⟨c⟩

end OperatorKO7.Methods.OrientationClosure.DependentMethodEvidence
