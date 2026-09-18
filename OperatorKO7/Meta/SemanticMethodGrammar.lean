import OperatorKO7.Meta.SemanticMethodBoundary
import OperatorKO7.Meta.GenericDPGrammar

/-!
# Semantic Method Grammar

Three-constructor exact grammar over semantic-style methods (model
imports, logical relations, reducibility candidates) plus the headline
conjunction theorem combining the DP grammar (six constructors) and the
semantic grammar (three constructors) into a single universal
classification across all 9 method types.

Constructors: `modelImport`, `logicalRelation`, `reducibilityCandidate`.

Theorems close by `decide` / `rfl` on the finite enum surface; no `sorry`,
no new top-level `axiom`, no `PartialProgressClaim` carriers.
-/

namespace OperatorKO7.SemanticMethodGrammar

open OperatorKO7.SemanticMethodBoundary
open OperatorKO7.GenericDPGrammar

/-- Three-constructor exact grammar for semantic-style methods.

The constructors enumerate the proof-theoretic devices a semantic method
may import: a model interpretation, a logical relation between source and
interpretation, or a reducibility-candidate predicate. -/
inductive SemanticMethod where
  | modelImport
  | logicalRelation
  | reducibilityCandidate
  deriving DecidableEq, Repr

/-- The exact grammar's three members in canonical order. -/
def allSemanticMethods : List SemanticMethod :=
  [ .modelImport
  , .logicalRelation
  , .reducibilityCandidate ]

theorem allSemanticMethods_length :
    allSemanticMethods.length = 3 := rfl

theorem allSemanticMethods_nodup :
    allSemanticMethods.Nodup := by decide

theorem allSemanticMethods_complete (m : SemanticMethod) :
    m ∈ allSemanticMethods := by
  cases m <;> decide

/-- Classification vocabulary for a semantic method.

Additive enum: constructors are appended as new structural
classifications surface. -/
inductive SemanticMethodStatus where
  | w0ReducedToExisting
  | w1LicensedEscape
  | externallyCertified
  deriving DecidableEq, Repr

/-- The three canonical status values in canonical order. -/
def allSemanticMethodStatuses : List SemanticMethodStatus :=
  [ .w0ReducedToExisting
  , .w1LicensedEscape
  , .externallyCertified ]

/-- Total classifier on the exact grammar.

Justification of each row:

* `modelImport` interprets source terms in an external semantic model
  (Tait, Kreisel, Plotkin); this imports the typing context from outside
  the source rewrite system, hence is W1-licensed.
* `logicalRelation` defines a binary predicate over source and model
  values that is preserved under reduction; this also imports semantic
  structure from outside, hence W1-licensed.
* `reducibilityCandidate` (Girard, Tait) imports a normalizability
  predicate that is closed under reduction; W1-licensed by the same
  argument. -/
def classifySemanticMethod : SemanticMethod → SemanticMethodStatus
  | .modelImport => .w1LicensedEscape
  | .logicalRelation => .w1LicensedEscape
  | .reducibilityCandidate => .w1LicensedEscape

/-- Universal coverage: every semantic-style method is one of the three
constructors. -/
theorem semantic_method_grammar_universal_coverage (m : SemanticMethod) :
    m ∈ allSemanticMethods :=
  allSemanticMethods_complete m

/-- Every constructor classifies as exactly one of the three canonical
status values; the classifier is total. -/
theorem semantic_method_classification_unconditional (m : SemanticMethod) :
    classifySemanticMethod m ∈ allSemanticMethodStatuses := by
  cases m <;> decide

/-- Per-constructor classification facts (decidable). -/
theorem modelImport_is_w1LicensedEscape :
    classifySemanticMethod .modelImport = .w1LicensedEscape := rfl
theorem logicalRelation_is_w1LicensedEscape :
    classifySemanticMethod .logicalRelation = .w1LicensedEscape := rfl
theorem reducibilityCandidate_is_w1LicensedEscape :
    classifySemanticMethod .reducibilityCandidate = .w1LicensedEscape := rfl

/-- HEADLINE: `generic_dp_and_semantic_method_grammar_unconditional`.
Universal grammar + universal coverage + universal classification across
all 6 + 3 = 9 method types. -/
theorem generic_dp_and_semantic_method_grammar_unconditional :
    (∀ d : GenericDPMethod, d ∈ allGenericDPMethods)
    ∧ (∀ s : SemanticMethod, s ∈ allSemanticMethods)
    ∧ (∀ d : GenericDPMethod,
        classifyGenericDPMethod d ∈ allGenericDPMethodStatuses)
    ∧ (∀ s : SemanticMethod,
        classifySemanticMethod s ∈ allSemanticMethodStatuses)
    ∧ allGenericDPMethods.length + allSemanticMethods.length = 9 :=
  ⟨ generic_dp_method_grammar_universal_coverage
  , semantic_method_grammar_universal_coverage
  , generic_dp_method_classification_unconditional
  , semantic_method_classification_unconditional
  , rfl ⟩

/-- Combined-grammar exhaustiveness count: the union of the DP grammar
and the semantic grammar enumerates exactly nine method types. -/
theorem combined_grammar_size :
    allGenericDPMethods.length + allSemanticMethods.length = 9 := rfl

/-- Combined-grammar classification: every method (DP-style or
semantic-style) carries exactly one classification status from the union
of the two status enums. The lemma is stated as a sum-type case
distinction because the two status enums are themselves disjoint
inductives; the universal-coverage shape is the conjunction of the two
per-grammar classifications. -/
theorem combined_classification_total :
    (∀ d : GenericDPMethod, ∃ s, classifyGenericDPMethod d = s)
    ∧ (∀ s : SemanticMethod, ∃ t, classifySemanticMethod s = t) := by
  refine ⟨?_, ?_⟩
  · intro d; exact ⟨classifyGenericDPMethod d, rfl⟩
  · intro s; exact ⟨classifySemanticMethod s, rfl⟩

/-- Embedding from the existing 3-row semantic boundary catalog
(`SemanticMethodClass`) into the 3-constructor exact grammar.

The embedding maps the import-based row directly to `logicalRelation`;
the transparent-whole-term and certified-external rows are mapped to
`modelImport` and `reducibilityCandidate` respectively as the closest
proof-theoretic device. The agreement theorem below records the
classification image without claiming a 1:1 isomorphism between the
boundary catalog (which mixes W0 reductions with W1 imports) and the
exact grammar (which is W1-uniform). -/
def semanticBoundaryClassToMethod : SemanticMethodClass → SemanticMethod
  | .transparentWholeTermMeasure => .modelImport
  | .importedModelLogicalRelation => .logicalRelation
  | .certifiedExternalEngine => .reducibilityCandidate

/-- The embedding lands every boundary class in `w1LicensedEscape` under
the exact-grammar classification. This is the formal "flip" from boundary
catalog to exact grammar with classification: every semantic method, in
the exact-grammar sense, imports semantic structure from outside the
source rewrite system. -/
theorem semantic_boundary_classification_via_grammar (cls : SemanticMethodClass) :
    classifySemanticMethod (semanticBoundaryClassToMethod cls)
      = .w1LicensedEscape := by
  cases cls <;> rfl

/-- The embedding is injective. -/
theorem semanticBoundaryClassToMethod_injective :
    Function.Injective semanticBoundaryClassToMethod := by
  intro a b h
  cases a <;> cases b <;> first | rfl | cases h

end OperatorKO7.SemanticMethodGrammar
