import OperatorKO7.Meta.ConstructionRouteCatalog_Certificate

/-!
This module defines a three-constructor method registry, assigns route and status metadata by
constructor, and packages imported support propositions. Catalog coverage ranges over this local
enum. The subsumption lemma establishes list-length arithmetic only.



-/

namespace OperatorKO7.SemanticMethodBoundary

open OperatorKO7.BenchmarkedPRCFamily
open OperatorKO7.ConstructionMethodClassification
open OperatorKO7.ConstructionRouteCatalog
open OperatorKO7.ConstructionRouteCatalogCertificate

/-- Carrier with the constructors displayed below.
-/
inductive SemanticMethodClass where
  | transparentWholeTermMeasure
  | importedModelLogicalRelation
  | certifiedExternalEngine
  deriving DecidableEq, Repr

/-- Definition with formal content given by the displayed type and body. -/
def semanticMethodClasses : List SemanticMethodClass :=
  [ .transparentWholeTermMeasure
  , .importedModelLogicalRelation
  , .certifiedExternalEngine
  ]

/-- Definition with formal content given by the displayed type and body.
-/
def semanticMethodBoundaryRoute? : SemanticMethodClass → Option ConstructionRoute
  | .transparentWholeTermMeasure => some .W0
  | .importedModelLogicalRelation => some .W1
  | .certifiedExternalEngine => none

/-- Carrier with the constructors displayed below. -/
inductive SemanticMethodBoundaryStatus where
  | reducedToExistingTheorem (route : ConstructionRoute)
  | licensedEscape (route : ConstructionRoute)
  | certifiedSuccess
  deriving DecidableEq, Repr

/-- Definition with formal content given by the displayed type and body. -/
def semanticMethodBoundaryStatus : SemanticMethodClass → SemanticMethodBoundaryStatus
  | .transparentWholeTermMeasure => .reducedToExistingTheorem .W0
  | .importedModelLogicalRelation => .licensedEscape .W1
  | .certifiedExternalEngine => .certifiedSuccess

/-- Definition with formal content given by the displayed type and body. -/
def SemanticMethodSupported : SemanticMethodClass → Prop
  | .transparentWholeTermMeasure =>
      HasDirectWitness fullLinear
  | .importedModelLogicalRelation =>
      PermittedW1Import .importedWholeWitness ∧
        importedWhole_w1_success.route ≠ .W0 ∧
        HasImportedWholeWitness fullDuplicating ∧
        ¬ HasDirectWitness fullDuplicating
  | .certifiedExternalEngine =>
      CanonicalConstructionCertificate

/-- The displayed proposition follows from the stated hypotheses.
-/
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
  | certifiedExternalEngine =>
      exact canonical_construction_certificate

/-- The displayed proposition follows from the stated hypotheses. -/
theorem semanticMethodClasses_nodup :
    semanticMethodClasses.Nodup := by
  decide

/-- The displayed proposition follows from the stated hypotheses. -/
theorem semanticMethodClasses_length :
    semanticMethodClasses.length = 3 := by
  rfl

/-- The displayed proposition follows from the stated hypotheses. -/
theorem semanticMethodClasses_complete_exact
    (cls : SemanticMethodClass) :
    cls ∈ semanticMethodClasses ↔
      cls = .transparentWholeTermMeasure ∨
      cls = .importedModelLogicalRelation ∨
      cls = .certifiedExternalEngine := by
  cases cls <;> simp [semanticMethodClasses]

/-- The displayed proposition follows from the stated hypotheses. -/
theorem semanticMethodBoundaryRoute_exact (cls : SemanticMethodClass) :
    semanticMethodBoundaryRoute? cls =
      match cls with
      | .transparentWholeTermMeasure => some .W0
      | .importedModelLogicalRelation => some .W1
      | .certifiedExternalEngine => none := by
  cases cls <;> rfl

/-- The displayed proposition follows from the stated hypotheses. -/
theorem semanticMethodBoundaryStatus_exact (cls : SemanticMethodClass) :
    semanticMethodBoundaryStatus cls =
      match cls with
      | .transparentWholeTermMeasure => .reducedToExistingTheorem .W0
      | .importedModelLogicalRelation => .licensedEscape .W1
      | .certifiedExternalEngine => .certifiedSuccess := by
  cases cls <;> rfl

/-- Abbreviation for the displayed type. -/
abbrev SemanticMethodBoundaryCatalog : Prop :=
  ∀ cls : SemanticMethodClass,
    cls ∈ semanticMethodClasses ∧
      SemanticMethodSupported cls ∧
      semanticMethodBoundaryStatus cls =
        match cls with
        | .transparentWholeTermMeasure => .reducedToExistingTheorem .W0
        | .importedModelLogicalRelation => .licensedEscape .W1
        | .certifiedExternalEngine => .certifiedSuccess

/-- The displayed proposition follows from the stated hypotheses.
-/
theorem semanticMethodBoundaryCatalog_exact : SemanticMethodBoundaryCatalog := by
  intro cls
  refine ⟨?_, semanticMethodSupported_holds cls, ?_⟩
  · exact (semanticMethodClasses_complete_exact cls).2 <| by
      cases cls <;> simp
  · exact semanticMethodBoundaryStatus_exact cls

/-- The displayed proposition follows from the stated hypotheses. -/
theorem semanticMethodBoundaryCatalog_projects_support
    (h : SemanticMethodBoundaryCatalog) (cls : SemanticMethodClass) :
    SemanticMethodSupported cls :=
  (h cls).2.1

/-- The displayed proposition follows from the stated hypotheses. -/
theorem semanticMethodBoundaryCatalog_projects_status
    (h : SemanticMethodBoundaryCatalog) (cls : SemanticMethodClass) :
    semanticMethodBoundaryStatus cls =
      match cls with
      | .transparentWholeTermMeasure => .reducedToExistingTheorem .W0
      | .importedModelLogicalRelation => .licensedEscape .W1
      | .certifiedExternalEngine => .certifiedSuccess :=
  (h cls).2.2

/-- The displayed proposition follows from the stated hypotheses.
-/
theorem importedSemanticMethod_is_licensed_escape :
    semanticMethodBoundaryStatus .importedModelLogicalRelation = .licensedEscape .W1 :=
  rfl

/-- The displayed proposition follows from the stated hypotheses. -/
theorem importedSemanticMethod_not_direct_w0 :
    semanticMethodBoundaryRoute? .importedModelLogicalRelation ≠ some .W0 := by
  decide

/-- Data record whose requirements are the fields displayed below.
-/
structure SemanticMethodBoundaryCertificate where
  catalog : SemanticMethodBoundaryCatalog
  importedNotW0 : semanticMethodBoundaryRoute? .importedModelLogicalRelation ≠ some .W0

/-- The displayed proposition follows from the stated hypotheses.
-/
theorem semanticMethodBoundaryCertificate_exact : SemanticMethodBoundaryCertificate := by
  exact {
    catalog := semanticMethodBoundaryCatalog_exact
    importedNotW0 := importedSemanticMethod_not_direct_w0
  }

/-- The displayed proposition follows from the stated hypotheses. -/
theorem semanticMethodBoundaryCertificate_projects_catalog :
    SemanticMethodBoundaryCatalog :=
  semanticMethodBoundaryCertificate_exact.catalog

/-- The displayed proposition follows from the stated hypotheses. -/
theorem semanticMethodBoundaryCertificate_projects_importedNotW0 :
    semanticMethodBoundaryRoute? .importedModelLogicalRelation ≠ some .W0 :=
  semanticMethodBoundaryCertificate_exact.importedNotW0

/-! Declarations for the section below.
















-/

theorem semanticMethodClasses_subsumed_by_exact_grammar :
    semanticMethodClasses.length = 3
      ∧ semanticMethodClasses.length ≤ 3 := by
  refine ⟨rfl, ?_⟩
  decide

end OperatorKO7.SemanticMethodBoundary
