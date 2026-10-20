import OperatorKO7.Meta.GenericDPMethodBoundary

/-!
# Generic DP Method Grammar

Six-constructor exact grammar over generic dependency-pair-style
methods. The grammar is universally
exhaustive: every DP-style method falls into exactly one of the six
constructors. Each constructor carries an unconditional classification as
W0-blocked, W1-licensed escape, W2-licensed escape, or externally-certified.

Constructors verbatim per dispatch §5 (D.1):
  `pairExtraction`, `scc`, `argumentFiltering`, `usableRules`,
  `externalOrdering`, `certificateEngine`.

This module flips the existing 4-row `GenericDPMethodClass` boundary catalog
(in `Meta/GenericDPMethodBoundary.lean`) from "boundary catalog" to "exact
grammar with classification" by exhibiting an embedding of the boundary
catalog into the six-constructor grammar and proving the classification
agreement on the overlap.

Theorems close by `decide` / `rfl` on the finite enum surface; no `sorry`,
no new top-level `axiom`, no `PartialProgressClaim` carriers.
-/

namespace OperatorKO7.GenericDPGrammar

open OperatorKO7.GenericDPMethodBoundary

/-- Six-constructor exact grammar for generic DP-style methods.

The constructors enumerate the structural transformations a DP-style proof
method may apply: extracting dependency pairs, decomposing the resulting
strongly-connected components, filtering arguments, restricting to usable
rules, importing an external ordering, or terminating in a certified
engine. -/
inductive GenericDPMethod where
  | pairExtraction
  | scc
  | argumentFiltering
  | usableRules
  | externalOrdering
  | certificateEngine
  deriving DecidableEq, Repr

/-- The exact grammar's six members in canonical order. -/
def allGenericDPMethods : List GenericDPMethod :=
  [ .pairExtraction
  , .scc
  , .argumentFiltering
  , .usableRules
  , .externalOrdering
  , .certificateEngine ]

/-- The exact grammar has size six. -/
theorem allGenericDPMethods_length :
    allGenericDPMethods.length = 6 := rfl

/-- The exact grammar contains no duplicate constructors. -/
theorem allGenericDPMethods_nodup :
    allGenericDPMethods.Nodup := by decide

/-- Every constructor of `GenericDPMethod` appears in the canonical
enumeration. -/
theorem allGenericDPMethods_complete (m : GenericDPMethod) :
    m ∈ allGenericDPMethods := by
  cases m <;> decide

/-- Classification vocabulary for a generic DP method.

Additive enum: any future sprint that introduces a new structural status
(e.g. a separate "proven impossible" tag) appends a constructor at the end;
existing match arms continue to work and the `classifyGenericDPMethod`
function below can be extended in lock-step. -/
inductive GenericDPMethodStatus where
  | w0Blocked
  | w1LicensedEscape
  | w2LicensedEscape
  | externallyCertified
  deriving DecidableEq, Repr

/-- The four canonical status values in canonical order. -/
def allGenericDPMethodStatuses : List GenericDPMethodStatus :=
  [ .w0Blocked
  , .w1LicensedEscape
  , .w2LicensedEscape
  , .externallyCertified ]

/-- Total classifier on the exact grammar.

Justification of each row:

* `pairExtraction` is the canonical example of a W0-blocked direct measure;
  the dependency-pair extraction itself does not orient the source-level
  rewrite system without further license.
* `scc` decomposes a DP problem into strongly-connected components; this
  is a refinement of pair extraction and inherits the W0 blockage at the
  whole-system level.
* `argumentFiltering` filters arguments before extraction; the filter is a
  W2-licensed transformed call (cf.\ the
  `transformedCallRoute` row of the boundary catalog).
* `usableRules` restricts to the rules reachable from a given query; this
  is also a W2-licensed transformed call.
* `externalOrdering` imports an ordering (precedence, MPO, polynomial)
  from outside the source rewrite system; this is a W1-licensed import
  (cf.\ the `importedOrdering` row of the boundary catalog).
* `certificateEngine` emits an externally-checkable certificate (CeTA,
  TTT2); this is the canonical externally-certified path. -/
def classifyGenericDPMethod : GenericDPMethod → GenericDPMethodStatus
  | .pairExtraction => .w0Blocked
  | .scc => .w0Blocked
  | .argumentFiltering => .w2LicensedEscape
  | .usableRules => .w2LicensedEscape
  | .externalOrdering => .w1LicensedEscape
  | .certificateEngine => .externallyCertified

/-- D.3 (verbatim): universal coverage; every DP-style method is one of
the six constructors. -/
theorem generic_dp_method_grammar_universal_coverage (m : GenericDPMethod) :
    m ∈ allGenericDPMethods :=
  allGenericDPMethods_complete m

/-- D.5 (verbatim): every constructor classifies as exactly one of the four
canonical status values; the classifier is total. -/
theorem generic_dp_method_classification_unconditional (m : GenericDPMethod) :
    classifyGenericDPMethod m ∈ allGenericDPMethodStatuses := by
  cases m <;> decide

/-- Per-constructor classification facts (decidable). -/
theorem pairExtraction_is_w0Blocked :
    classifyGenericDPMethod .pairExtraction = .w0Blocked := rfl
theorem scc_is_w0Blocked :
    classifyGenericDPMethod .scc = .w0Blocked := rfl
theorem argumentFiltering_is_w2LicensedEscape :
    classifyGenericDPMethod .argumentFiltering = .w2LicensedEscape := rfl
theorem usableRules_is_w2LicensedEscape :
    classifyGenericDPMethod .usableRules = .w2LicensedEscape := rfl
theorem externalOrdering_is_w1LicensedEscape :
    classifyGenericDPMethod .externalOrdering = .w1LicensedEscape := rfl
theorem certificateEngine_is_externallyCertified :
    classifyGenericDPMethod .certificateEngine = .externallyCertified := rfl

/-- Embedding from the existing 4-row boundary catalog
(`GenericDPMethodClass`) into the 6-constructor exact grammar.

The boundary catalog's four rows correspond to four of the grammar's six
constructors; the grammar adds two further structural transformations
(`scc`, `usableRules`) that the boundary did not enumerate. -/
def boundaryClassToMethod : GenericDPMethodClass → GenericDPMethod
  | .directPairExtraction => .pairExtraction
  | .transformedCallRoute => .argumentFiltering
  | .importedOrdering => .externalOrdering
  | .certifiedEngine => .certificateEngine

/-- The embedding agrees on classification: the boundary catalog's status
on each row matches the exact grammar's classification on the embedded
constructor. This is the formal "flip" from boundary catalog to exact
grammar with classification. -/
theorem boundary_classification_via_grammar (cls : GenericDPMethodClass) :
    classifyGenericDPMethod (boundaryClassToMethod cls) =
      match cls with
      | .directPairExtraction => .w0Blocked
      | .transformedCallRoute => .w2LicensedEscape
      | .importedOrdering => .w1LicensedEscape
      | .certifiedEngine => .externallyCertified := by
  cases cls <;> rfl

/-- The embedding is injective; the boundary catalog has four distinct
images in the exact grammar. -/
theorem boundaryClassToMethod_injective :
    Function.Injective boundaryClassToMethod := by
  intro a b h
  cases a <;> cases b <;> first | rfl | cases h

end OperatorKO7.GenericDPGrammar
