import OperatorKO7.Meta.BoundaryGeneral.VectorOrderRepair
import OperatorKO7.Meta.BoundaryGeneral.CheckedNonOrientationCertificate
import OperatorKO7.Meta.BoundaryGeneral.DeclaredMethodUniverse

/-!
# Reach test for the Tier 17 A-01/A-02 repair surface

This file checks that the public declarations are reachable through their
intended module imports. It adds no axioms or external trust.
-/

set_option autoImplicit false

namespace OperatorKO7.Test.PriorArtRepairOrientationReach

open OperatorKO7.StepDuplicating
open OperatorKO7.StepDuplicating.StepDuplicatingSchema
open OperatorKO7.Meta.BoundaryGeneral
open OperatorKO7.Meta.BoundaryGeneral.VectorGrammarClosure
open OperatorKO7.Meta.BoundaryGeneral.VectorOrderRepair

#check @PrimarySomeDecreaseLt
#check primarySomeDecrease_has_two_cycle
#check primaryFirstLt_fin3_two_cycle
#check not_wellFounded_primaryFirstLt_fin3
#check vecLexLt_transitive
#check vecLexLt_wellFounded
#check vecLexLt_dominatedByPrimary
#check vecLex_orients_implies_primary_payloadBlind
#check @PrimaryStrictWeakLt
#check primaryStrictWeakLt_wellFounded
#check fixedRow_orients_implies_payloadBlind
#check rowSum_orients_implies_payloadBlind
#check counterVector_orients_vecLexLt
#check counterVector_orients_primaryStrictWeakLt
#check counterVector_fixedRow_adapter_nonvacuous
#check counterVector_rowSum_adapter_nonvacuous

#check @DupStep
#check DeclaredDirectFamily
#check @CheckedNonOrientationCertificate
#check @CheckedNonOrientationCertificate.not_global_orients
#check @CheckedNonOrientationCertificate.not_system_global_orients
#check @CheckedSystemNonOrientationCertificate
#check @additive_checkedCertificate
#check @transparentCompositional_checkedCertificate
#check @affineWithPump_checkedCertificate
#check @restrictedQuadraticWithPump_checkedCertificate
#check @maxPlusWithPump_checkedCertificate
#check @matrixFunctionalWithProjectedAffinePump_checkedCertificate
#check @ko7Additive_checkedSystemCertificate
#check ko7SimpleSize_checkedSystemCertificate
#check ko7SimpleSize_checkedSystemCertificate_not_global_orients
#check @ko7TransparentCompositional_checkedSystemCertificate
#check @ko7AffineWithPump_checkedSystemCertificate
#check @ko7RestrictedQuadraticWithPump_checkedSystemCertificate
#check @ko7MaxPlusWithPump_checkedSystemCertificate
#check @ko7MatrixFunctionalWithProjectedAffinePump_checkedSystemCertificate

#check OutsideMethod
#check @ConstructionWitness
#check @ProjectionWitness
#check @ClassificationResult
#check @DeclaredDirectFamilyInput
#check @checkedCertificateFor
#check @DeclaredDirectMethod
#check @DeclaredMethod
#check @classifyDeclaredMethod
#check @declaredDirectMethod_not_orients
#check @declaredDirectMethod_not_system_global_orients
#check @declaredMethod_classification_exhaustive
#check atlasFamily_classifies_outside
#check tupleInterpretation_classifies_outside
#check semanticLabeling_classifies_outside

example :
    ∃ u v : Fin 3 → Nat,
      PrimaryFirstLt (0 : Fin 3) u v ∧
        PrimaryFirstLt (0 : Fin 3) v u :=
  primaryFirstLt_fin3_two_cycle

example (d : Nat) : WellFounded (@VecLexLt d) :=
  vecLexLt_wellFounded d

example (d : Nat) :
    VecOrients (counterVectorMeasure d) (@VecLexLt d) :=
  counterVector_orients_vecLexLt d

end OperatorKO7.Test.PriorArtRepairOrientationReach
