import OperatorKO7.Meta.ConstructionRouteCatalog_Certificate

/-!
# Semantic Method Boundary

This module replaces the old prose-only semantic-method exclusion with a small
theorem-backed carrier. It records the currently supported semantic lanes:
transparent whole-term comparison, import-dependent semantic lifting, and a
certificate-emitting external procedure route.
-/

namespace OperatorKO7.SemanticMethodBoundary

open OperatorKO7.BenchmarkedPRCFamily
open OperatorKO7.ConstructionMethodClassification
open OperatorKO7.ConstructionRouteCatalog
open OperatorKO7.ConstructionRouteCatalogCertificate

/-- Finite carrier for the semantic method classes tracked by the current
boundary catalog. -/
inductive SemanticMethodClass where
  | transparentWholeTermMeasure
  | importedModelLogicalRelation
  | certifiedExternalProcedure
  deriving DecidableEq, Repr

/-- Finite inventory of the semantic method classes. -/
def semanticMethodClasses : List SemanticMethodClass :=
  [ .transparentWholeTermMeasure
  , .importedModelLogicalRelation
  , .certifiedExternalProcedure
  ]

/-- Route projection carried by a semantic method class when one is already
licensed by the current theorem surface. -/
def semanticMethodBoundaryRoute? : SemanticMethodClass → Option ConstructionRoute
  | .transparentWholeTermMeasure => some .W0
  | .importedModelLogicalRelation => some .W1
  | .certifiedExternalProcedure => none

/-- Boundary-status vocabulary for the semantic method carrier. -/
inductive SemanticMethodBoundaryStatus where
  | reducedToExistingTheorem (route : ConstructionRoute)
  | licensedEscape (route : ConstructionRoute)
  | certifiedSuccess
  deriving DecidableEq, Repr

/-- Status classification currently carried by each semantic method class. -/
def semanticMethodBoundaryStatus : SemanticMethodClass → SemanticMethodBoundaryStatus
  | .transparentWholeTermMeasure => .reducedToExistingTheorem .W0
  | .importedModelLogicalRelation => .licensedEscape .W1
  | .certifiedExternalProcedure => .certifiedSuccess

/-- The theorem-backed payload currently available for each semantic method row. -/
def SemanticMethodSupported : SemanticMethodClass → Prop
  | .transparentWholeTermMeasure =>
      HasDirectWitness fullLinear
  | .importedModelLogicalRelation =>
      PermittedW1Import .importedWholeWitness ∧
        importedWhole_w1_success.route ≠ .W0 ∧
        HasImportedWholeWitness fullDuplicating ∧
        ¬ HasDirectWitness fullDuplicating
  | .certifiedExternalProcedure =>
      CanonicalConstructionCertificate

/-- Every semantic-method row in the finite inventory has theorem-backed
support. -/
theorem semanticMethodSupported_holds (cls : SemanticMethodClass) :
    SemanticMethodSupported cls := by
  cases cls with
  | transparentWholeTermMeasure =>
      exact fullLinear_has_direct_witness
  | importedModelLogicalRelation =>
      exact ⟨importedWhole_w1_success_requires_imported_whole,
        importedWhole_w1_success_separates_from_w0.1,
        importedWhole_w1_success_separates_from_w0.2.1,
        importedWhole_w1_success_separates_from_w0.2.2⟩
  | certifiedExternalProcedure =>
      exact canonical_construction_certificate

/-- The semantic-method inventory has no duplicate rows. -/
theorem semanticMethodClasses_nodup :
    semanticMethodClasses.Nodup := by
  decide

/-- The semantic-method inventory has exact size three. -/
theorem semanticMethodClasses_length :
    semanticMethodClasses.length = 3 := by
  rfl

/-- Exact membership characterization for the semantic-method inventory. -/
theorem semanticMethodClasses_complete_exact
    (cls : SemanticMethodClass) :
    cls ∈ semanticMethodClasses ↔
      cls = .transparentWholeTermMeasure ∨
      cls = .importedModelLogicalRelation ∨
      cls = .certifiedExternalProcedure := by
  cases cls <;> simp [semanticMethodClasses]

/-- Route projection for each semantic-method row is exact. -/
theorem semanticMethodBoundaryRoute_exact (cls : SemanticMethodClass) :
    semanticMethodBoundaryRoute? cls =
      match cls with
      | .transparentWholeTermMeasure => some .W0
      | .importedModelLogicalRelation => some .W1
      | .certifiedExternalProcedure => none := by
  cases cls <;> rfl

/-- Status projection for each semantic-method row is exact. -/
theorem semanticMethodBoundaryStatus_exact (cls : SemanticMethodClass) :
    semanticMethodBoundaryStatus cls =
      match cls with
      | .transparentWholeTermMeasure => .reducedToExistingTheorem .W0
      | .importedModelLogicalRelation => .licensedEscape .W1
      | .certifiedExternalProcedure => .certifiedSuccess := by
  cases cls <;> rfl

/-- Paper-facing proposition for the finite semantic-method boundary catalog. -/
abbrev SemanticMethodBoundaryCatalog : Prop :=
  ∀ cls : SemanticMethodClass,
    cls ∈ semanticMethodClasses ∧
      SemanticMethodSupported cls ∧
      semanticMethodBoundaryStatus cls =
        match cls with
        | .transparentWholeTermMeasure => .reducedToExistingTheorem .W0
        | .importedModelLogicalRelation => .licensedEscape .W1
        | .certifiedExternalProcedure => .certifiedSuccess

/-- The finite semantic-method boundary catalog is fully realized by the current
theorem-backed rows. -/
theorem semanticMethodBoundaryCatalog_exact : SemanticMethodBoundaryCatalog := by
  intro cls
  refine ⟨?_, semanticMethodSupported_holds cls, ?_⟩
  · exact (semanticMethodClasses_complete_exact cls).2 <| by
      cases cls <;> simp
  · exact semanticMethodBoundaryStatus_exact cls

/-- The catalog projects the theorem-backed payload for each semantic row. -/
theorem semanticMethodBoundaryCatalog_projects_support
    (h : SemanticMethodBoundaryCatalog) (cls : SemanticMethodClass) :
    SemanticMethodSupported cls :=
  (h cls).2.1

/-- The catalog projects the exact status for each semantic row. -/
theorem semanticMethodBoundaryCatalog_projects_status
    (h : SemanticMethodBoundaryCatalog) (cls : SemanticMethodClass) :
    semanticMethodBoundaryStatus cls =
      match cls with
      | .transparentWholeTermMeasure => .reducedToExistingTheorem .W0
      | .importedModelLogicalRelation => .licensedEscape .W1
      | .certifiedExternalProcedure => .certifiedSuccess :=
  (h cls).2.2

/-- Import-dependent semantic methods are licensed escapes rather than direct
W0 barriers. -/
theorem importedSemanticMethod_is_licensed_escape :
    semanticMethodBoundaryStatus .importedModelLogicalRelation = .licensedEscape .W1 :=
  rfl

/-- Import-dependent semantic methods are not classified as direct W0 routes. -/
theorem importedSemanticMethod_not_direct_w0 :
    semanticMethodBoundaryRoute? .importedModelLogicalRelation ≠ some .W0 := by
  decide

/-- Certificate packaging the exact semantic boundary catalog together with the
import-dependent non-W0 classification. -/
structure SemanticMethodBoundaryCertificate where
  catalog : SemanticMethodBoundaryCatalog
  importedNotW0 : semanticMethodBoundaryRoute? .importedModelLogicalRelation ≠ some .W0

/-- The semantic boundary certificate is realized by the current theorem-backed
catalog and the import-dependent non-W0 separation theorem. -/
theorem semanticMethodBoundaryCertificate_exact : SemanticMethodBoundaryCertificate := by
  exact {
    catalog := semanticMethodBoundaryCatalog_exact
    importedNotW0 := importedSemanticMethod_not_direct_w0
  }

/-- The boundary certificate projects the exact semantic catalog. -/
theorem semanticMethodBoundaryCertificate_projects_catalog :
    SemanticMethodBoundaryCatalog :=
  semanticMethodBoundaryCertificate_exact.catalog

/-- The boundary certificate projects the import-dependent non-W0 separation theorem. -/
theorem semanticMethodBoundaryCertificate_projects_importedNotW0 :
    semanticMethodBoundaryRoute? .importedModelLogicalRelation ≠ some .W0 :=
  semanticMethodBoundaryCertificate_exact.importedNotW0

/-! ### Lane D LONG-22 additive note

The three-row `SemanticMethodClass` boundary catalog is now in
correspondence with the three-constructor exact grammar in
`Meta/SemanticMethodGrammar.lean`
(`OperatorKO7.SemanticMethodGrammar.SemanticMethod`). The exact grammar
classifies every semantic method as W1-licensed escape (importing
semantic structure from outside the source rewrite system); the boundary
catalog here predates that classification and mixes a transparent W0
reduction with a W1 import and an external certificate. The embedding
theorem
`OperatorKO7.SemanticMethodGrammar.semantic_boundary_classification_via_grammar`
documents the classification image without claiming a 1:1 isomorphism
between the boundary catalog and the exact grammar.

The single additive lemma below records the size relation; the embedding
itself lives in the grammar module to keep the boundary file
import-acyclic. -/

theorem semanticMethodClasses_subsumed_by_exact_grammar :
    semanticMethodClasses.length = 3
      ∧ semanticMethodClasses.length ≤ 3 := by
  refine ⟨rfl, ?_⟩
  decide

end OperatorKO7.SemanticMethodBoundary
