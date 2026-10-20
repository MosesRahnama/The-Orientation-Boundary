import OperatorKO7.Meta.GenericDPGrammar
import OperatorKO7.Meta.SemanticMethodGrammar

/-!
# Reach test for the generic-DP and semantic-method grammars (Lane D)

Confirms the public surface of the two grammar modules resolves under
`lake env lean --run`.

Exercises D.3, D.4, D.7 by name as required by Lane D acceptance gate 4.
-/

namespace GenericDPSemanticGrammarReach

open OperatorKO7.GenericDPMethodBoundary
open OperatorKO7.SemanticMethodBoundary
open OperatorKO7.GenericDPGrammar
open OperatorKO7.SemanticMethodGrammar

#check GenericDPMethod
#check allGenericDPMethods
#check allGenericDPMethods_length
#check allGenericDPMethods_nodup
#check allGenericDPMethods_complete
#check GenericDPMethodStatus
#check allGenericDPMethodStatuses
#check classifyGenericDPMethod
#check generic_dp_method_grammar_universal_coverage
#check generic_dp_method_classification_unconditional
#check pairExtraction_is_w0Blocked
#check scc_is_w0Blocked
#check argumentFiltering_is_w2LicensedEscape
#check usableRules_is_w2LicensedEscape
#check externalOrdering_is_w1LicensedEscape
#check certificateEngine_is_externallyCertified
#check boundaryClassToMethod
#check boundary_classification_via_grammar
#check boundaryClassToMethod_injective

#check SemanticMethod
#check allSemanticMethods
#check allSemanticMethods_length
#check allSemanticMethods_nodup
#check allSemanticMethods_complete
#check SemanticMethodStatus
#check allSemanticMethodStatuses
#check classifySemanticMethod
#check semantic_method_grammar_universal_coverage
#check semantic_method_classification_unconditional
#check modelImport_is_w1LicensedEscape
#check logicalRelation_is_w1LicensedEscape
#check reducibilityCandidate_is_w1LicensedEscape
#check generic_dp_and_semantic_method_grammar_unconditional
#check combined_grammar_size
#check combined_classification_total
#check semanticBoundaryClassToMethod
#check semantic_boundary_classification_via_grammar
#check semanticBoundaryClassToMethod_injective

/-- Sanity check: the canonical DP enumeration reproduces the six
constructor list in canonical order. -/
example : allGenericDPMethods =
    [ GenericDPMethod.pairExtraction
    , GenericDPMethod.scc
    , GenericDPMethod.argumentFiltering
    , GenericDPMethod.usableRules
    , GenericDPMethod.externalOrdering
    , GenericDPMethod.certificateEngine ] := rfl

/-- Sanity check: the canonical semantic enumeration reproduces the
three-constructor list in canonical order. -/
example : allSemanticMethods =
    [ SemanticMethod.modelImport
    , SemanticMethod.logicalRelation
    , SemanticMethod.reducibilityCandidate ] := rfl

/-- Sanity check: every DP-style method classifies into one of the four
canonical status values. -/
example (m : GenericDPMethod) :
    classifyGenericDPMethod m ∈ allGenericDPMethodStatuses :=
  generic_dp_method_classification_unconditional m

/-- Sanity check: every semantic-style method classifies into one of the
three canonical status values. -/
example (m : SemanticMethod) :
    classifySemanticMethod m ∈ allSemanticMethodStatuses :=
  semantic_method_classification_unconditional m

/-- Sanity check: D.3 (universal coverage on the DP grammar). -/
example (m : GenericDPMethod) : m ∈ allGenericDPMethods :=
  generic_dp_method_grammar_universal_coverage m

/-- Sanity check: D.4 (universal coverage on the semantic grammar). -/
example (m : SemanticMethod) : m ∈ allSemanticMethods :=
  semantic_method_grammar_universal_coverage m

/-- Sanity check: D.7 headline; full conjunction reduces. -/
example :
    (∀ d : GenericDPMethod, d ∈ allGenericDPMethods)
    ∧ (∀ s : SemanticMethod, s ∈ allSemanticMethods)
    ∧ (∀ d : GenericDPMethod,
        classifyGenericDPMethod d ∈ allGenericDPMethodStatuses)
    ∧ (∀ s : SemanticMethod,
        classifySemanticMethod s ∈ allSemanticMethodStatuses)
    ∧ allGenericDPMethods.length + allSemanticMethods.length = 9 :=
  generic_dp_and_semantic_method_grammar_unconditional

/-- Sanity check: the 4-row DP boundary catalog embeds into the 6-row
exact grammar with classification agreement. -/
example (cls : GenericDPMethodClass) :
    classifyGenericDPMethod (boundaryClassToMethod cls) =
      match cls with
      | .directPairExtraction => .w0Blocked
      | .transformedCallRoute => .w2LicensedEscape
      | .importedOrdering => .w1LicensedEscape
      | .certifiedEngine => .externallyCertified :=
  boundary_classification_via_grammar cls

/-- Sanity check: the 3-row semantic boundary catalog embeds into the 3-row
exact grammar; every embedded class lands in `w1LicensedEscape`. -/
example (cls : SemanticMethodClass) :
    classifySemanticMethod (semanticBoundaryClassToMethod cls)
      = .w1LicensedEscape :=
  semantic_boundary_classification_via_grammar cls

end GenericDPSemanticGrammarReach
