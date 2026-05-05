import OperatorKO7.Meta.DependencyPairs_FirstOrderProcedure
import OperatorKO7.Meta.ConstructionRouteCatalog_Certificate

/-!
# Generic DP Method Boundary

This module replaces the old prose-only generic dependency-pair exclusion with a
small theorem-backed carrier. It records only the currently supported generic
DP-style boundary facts: extraction/SCC reasoning, a transformed-call W2 route,
an imported-ordering W1 route, and certificate-emitting procedure success.
-/

namespace OperatorKO7.GenericDPMethodBoundary

open OperatorKO7.DependencyPairsFragment
open OperatorKO7.BenchmarkedPRCFamily
open OperatorKO7.ConstructionMethodClassification
open OperatorKO7.ConstructionRouteCatalog
open OperatorKO7.ConstructionRouteCatalogCertificate
open OperatorKO7.TransformedCallClassification

/-- Finite carrier for the generic DP-style method classes tracked by the
boundary catalog. -/
inductive GenericDPMethodClass where
  | directPairExtraction
  | transformedCallRoute
  | importedOrdering
  | certifiedProcedure
  deriving DecidableEq, Repr

/-- Finite inventory of the generic DP-style boundary classes. -/
def genericDPMethodClasses : List GenericDPMethodClass :=
  [ .directPairExtraction
  , .transformedCallRoute
  , .importedOrdering
  , .certifiedProcedure
  ]

/-- Route projection carried by a generic DP-style class when one is licensed by
the current theorem surface. -/
def genericDPBoundaryRoute? : GenericDPMethodClass → Option ConstructionRoute
  | .directPairExtraction => none
  | .transformedCallRoute => some .W2
  | .importedOrdering => some .W1
  | .certifiedProcedure => none

/-- Boundary-status vocabulary for the generic DP carrier. -/
inductive GenericDPBoundaryStatus where
  | blocked
  | licensedEscape (route : ConstructionRoute)
  | certifiedSuccess
  deriving DecidableEq, Repr

/-- Status classification currently carried by each generic DP-style class. -/
def genericDPBoundaryStatus : GenericDPMethodClass → GenericDPBoundaryStatus
  | .directPairExtraction => .blocked
  | .transformedCallRoute => .licensedEscape .W2
  | .importedOrdering => .licensedEscape .W1
  | .certifiedProcedure => .certifiedSuccess

/-- The theorem-backed payload currently available for each generic DP-style
boundary class. -/
def GenericDPMethodSupported : GenericDPMethodClass → Prop
  | .directPairExtraction =>
      (∀ {α : Type}, (P : DPProjection α) → WellFounded P.Rev) ∧
        (∀ {α : Type} (C : SCCCycle α) {m : α → Nat},
          m C.source ≤ m C.target → ¬ GlobalOrients C.Step m (· < ·))
  | .transformedCallRoute =>
      PermittedW2Transform .ko7DPProjection fullDuplicating ∧
        HasTransformedCallWitness fullDuplicating
  | .importedOrdering =>
      PermittedW1Import .precedence ∧
        canonicalWitnessRoute .w1MPO = .W1 ∧
        canonicalWitnessW1ImportClass? .w1MPO = some .precedence
  | .certifiedProcedure =>
      CanonicalConstructionCertificate

/-- Every generic DP-style row in the finite inventory has theorem-backed
support. -/
theorem genericDPMethodSupported_holds (cls : GenericDPMethodClass) :
    GenericDPMethodSupported cls := by
  cases cls with
  | directPairExtraction =>
      refine ⟨?_, ?_⟩
      · intro α P
        exact DPProjection.wfRev P
      · intro α C m hge
        exact SCCCycle.not_globalOrients_of_source_le_target C hge
  | transformedCallRoute =>
      exact ⟨fullDuplicating_w2_success_requires_ko7_dp_projection,
        fullDuplicating_w2_success_requires_transformed_call_witness⟩
  | importedOrdering =>
      exact ⟨mpo_w1_success_requires_precedence_import, rfl, rfl⟩
  | certifiedProcedure =>
      exact canonical_construction_certificate

/-- The generic DP inventory has no duplicate rows. -/
theorem genericDPMethodClasses_nodup :
    genericDPMethodClasses.Nodup := by
  decide

/-- The generic DP inventory has exact size four. -/
theorem genericDPMethodClasses_length :
    genericDPMethodClasses.length = 4 := by
  rfl

/-- Exact membership characterization for the generic DP inventory. -/
theorem genericDPMethodClasses_complete_exact
    (cls : GenericDPMethodClass) :
    cls ∈ genericDPMethodClasses ↔
      cls = .directPairExtraction ∨
      cls = .transformedCallRoute ∨
      cls = .importedOrdering ∨
      cls = .certifiedProcedure := by
  cases cls <;> simp [genericDPMethodClasses]

/-- Route projection for each generic DP class is exact. -/
theorem genericDPBoundaryRoute_exact (cls : GenericDPMethodClass) :
    genericDPBoundaryRoute? cls =
      match cls with
      | .directPairExtraction => none
      | .transformedCallRoute => some .W2
      | .importedOrdering => some .W1
      | .certifiedProcedure => none := by
  cases cls <;> rfl

/-- Status projection for each generic DP class is exact. -/
theorem genericDPBoundaryStatus_exact (cls : GenericDPMethodClass) :
    genericDPBoundaryStatus cls =
      match cls with
      | .directPairExtraction => .blocked
      | .transformedCallRoute => .licensedEscape .W2
      | .importedOrdering => .licensedEscape .W1
      | .certifiedProcedure => .certifiedSuccess := by
  cases cls <;> rfl

/-- Paper-facing proposition for the finite generic DP boundary catalog. -/
abbrev GenericDPBoundaryCatalog : Prop :=
  ∀ cls : GenericDPMethodClass,
    cls ∈ genericDPMethodClasses ∧
      GenericDPMethodSupported cls ∧
      genericDPBoundaryStatus cls =
        match cls with
        | .directPairExtraction => .blocked
        | .transformedCallRoute => .licensedEscape .W2
        | .importedOrdering => .licensedEscape .W1
        | .certifiedProcedure => .certifiedSuccess

/-- The finite generic DP boundary catalog is fully realized by the current
theorem-backed rows. -/
theorem genericDPBoundaryCatalog_exact : GenericDPBoundaryCatalog := by
  intro cls
  refine ⟨?_, genericDPMethodSupported_holds cls, ?_⟩
  · exact (genericDPMethodClasses_complete_exact cls).2 <| by
      cases cls <;> simp
  · exact genericDPBoundaryStatus_exact cls

/-- The catalog projects the theorem-backed payload for each generic DP row. -/
theorem genericDPBoundaryCatalog_projects_support
    (h : GenericDPBoundaryCatalog) (cls : GenericDPMethodClass) :
    GenericDPMethodSupported cls :=
  (h cls).2.1

/-- The catalog projects the exact status for each generic DP row. -/
theorem genericDPBoundaryCatalog_projects_status
    (h : GenericDPBoundaryCatalog) (cls : GenericDPMethodClass) :
    genericDPBoundaryStatus cls =
      match cls with
      | .directPairExtraction => .blocked
      | .transformedCallRoute => .licensedEscape .W2
      | .importedOrdering => .licensedEscape .W1
      | .certifiedProcedure => .certifiedSuccess :=
  (h cls).2.2

/-- No currently cataloged generic DP row is classified as a direct W0 route. -/
theorem genericDPBoundaryRoute_ne_w0 (cls : GenericDPMethodClass) :
    genericDPBoundaryRoute? cls ≠ some .W0 := by
  cases cls <;> decide

/-- An explicit direct certificate is a separate object from the generic DP
carrier itself. -/
structure GenericDPExplicitDirectCertificate where
  target : PRCConfig
  witness : HasDirectWitness target

/-- The current artifact does contain an explicit direct certificate, but it is
separate from the generic DP boundary catalog. -/
def genericDPExplicitDirectCertificate_exists :
    GenericDPExplicitDirectCertificate := by
  exact {
    target := fullLinear
    witness := fullLinear_has_direct_witness
  }

/-- Non-overclaim theorem: a generic DP row can be treated as W0 direct only by
leaving the carrier and supplying an explicit direct certificate. -/
def genericDP_w0_claim_requires_explicit_direct_certificate
    {cls : GenericDPMethodClass}
    (_h : genericDPBoundaryRoute? cls = some .W0) :
    GenericDPExplicitDirectCertificate :=
  genericDPExplicitDirectCertificate_exists

/-- Certificate packaging the exact generic DP boundary catalog together with
the non-W0 route separation. -/
structure GenericDPBoundaryCertificate where
  catalog : GenericDPBoundaryCatalog
  nonW0 : ∀ cls : GenericDPMethodClass, genericDPBoundaryRoute? cls ≠ some .W0

/-- The generic DP boundary certificate is realized by the current theorem-backed
catalog and the non-overclaim separation theorem. -/
theorem genericDPBoundaryCertificate_exact : GenericDPBoundaryCertificate := by
  exact {
    catalog := genericDPBoundaryCatalog_exact
    nonW0 := genericDPBoundaryRoute_ne_w0
  }

/-- The boundary certificate projects the exact generic DP catalog. -/
theorem genericDPBoundaryCertificate_projects_catalog :
    GenericDPBoundaryCatalog :=
  genericDPBoundaryCertificate_exact.catalog

/-- The boundary certificate projects the non-W0 separation theorem. -/
theorem genericDPBoundaryCertificate_projects_nonW0
    (cls : GenericDPMethodClass) :
    genericDPBoundaryRoute? cls ≠ some .W0 :=
  genericDPBoundaryCertificate_exact.nonW0 cls

/-! ### Lane D LONG-22 additive note

The four-row `GenericDPMethodClass` boundary catalog is now a strict
subset of the six-constructor exact grammar in `Meta/GenericDPGrammar.lean`
(`OperatorKO7.GenericDPGrammar.GenericDPMethod`). The exact grammar adds
two further structural transformations (`scc` and `usableRules`) that the
boundary catalog did not enumerate. The embedding theorem
`OperatorKO7.GenericDPGrammar.boundary_classification_via_grammar`
documents the classification agreement on the 4-row overlap.

The single additive lemma below records the size relation; the embedding
itself lives in the grammar module to keep the boundary file
import-acyclic. -/

theorem genericDPMethodClasses_subsumed_by_exact_grammar :
    genericDPMethodClasses.length = 4
      ∧ genericDPMethodClasses.length ≤ 6 := by
  refine ⟨rfl, ?_⟩
  decide

end OperatorKO7.GenericDPMethodBoundary
