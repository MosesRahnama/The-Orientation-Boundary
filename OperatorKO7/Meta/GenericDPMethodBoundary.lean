import OperatorKO7.Meta.DependencyPairs_FirstOrderEngine
import OperatorKO7.Meta.ConstructionRouteCatalog_Certificate

/-!
# Generic DP Method Boundary

This module defines a four-constructor dependency-pair boundary carrier. Its
rows package extraction/SCC reasoning, a transformed-call W2 route, an
imported-ordering W1 route, and certificate-emitting engine success.
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
  | certifiedEngine
  deriving DecidableEq, Repr

/-- Finite inventory of the generic DP-style boundary classes. -/
def genericDPMethodClasses : List GenericDPMethodClass :=
  [ .directPairExtraction
  , .transformedCallRoute
  , .importedOrdering
  , .certifiedEngine
  ]

/-- Route projection carried by a generic DP-style class when the finite
classification assigns one. -/
def genericDPBoundaryRoute? : GenericDPMethodClass → Option ConstructionRoute
  | .directPairExtraction => none
  | .transformedCallRoute => some .W2
  | .importedOrdering => some .W1
  | .certifiedEngine => none

/-- Boundary-status vocabulary for the generic DP carrier. -/
inductive GenericDPBoundaryStatus where
  | blocked
  | licensedEscape (route : ConstructionRoute)
  | certifiedSuccess
  deriving DecidableEq, Repr

/-- Status classification assigned to each generic DP-style class. -/
def genericDPBoundaryStatus : GenericDPMethodClass → GenericDPBoundaryStatus
  | .directPairExtraction => .blocked
  | .transformedCallRoute => .licensedEscape .W2
  | .importedOrdering => .licensedEscape .W1
  | .certifiedEngine => .certifiedSuccess

/-- The theorem-backed payload assigned to each generic DP-style
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
  | .certifiedEngine =>
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
  | certifiedEngine =>
      exact canonical_construction_certificate

/-- The generic DP inventory is duplicate-free. -/
theorem genericDPMethodClasses_nodup :
    genericDPMethodClasses.Nodup := by
  decide

/-- The generic DP inventory has length four. -/
theorem genericDPMethodClasses_length :
    genericDPMethodClasses.length = 4 := by
  rfl

/-- Membership characterization for the generic DP inventory. -/
theorem genericDPMethodClasses_complete_exact
    (cls : GenericDPMethodClass) :
    cls ∈ genericDPMethodClasses ↔
      cls = .directPairExtraction ∨
      cls = .transformedCallRoute ∨
      cls = .importedOrdering ∨
      cls = .certifiedEngine := by
  cases cls <;> simp [genericDPMethodClasses]

/-- Route projection agrees with the displayed constructor match. -/
theorem genericDPBoundaryRoute_exact (cls : GenericDPMethodClass) :
    genericDPBoundaryRoute? cls =
      match cls with
      | .directPairExtraction => none
      | .transformedCallRoute => some .W2
      | .importedOrdering => some .W1
      | .certifiedEngine => none := by
  cases cls <;> rfl

/-- Status projection agrees with the displayed constructor match. -/
theorem genericDPBoundaryStatus_exact (cls : GenericDPMethodClass) :
    genericDPBoundaryStatus cls =
      match cls with
      | .directPairExtraction => .blocked
      | .transformedCallRoute => .licensedEscape .W2
      | .importedOrdering => .licensedEscape .W1
      | .certifiedEngine => .certifiedSuccess := by
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
        | .certifiedEngine => .certifiedSuccess

/-- Realization of the finite generic DP boundary catalog by its four
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

/-- The catalog projects the stated status for each generic DP row. -/
theorem genericDPBoundaryCatalog_projects_status
    (h : GenericDPBoundaryCatalog) (cls : GenericDPMethodClass) :
    genericDPBoundaryStatus cls =
      match cls with
      | .directPairExtraction => .blocked
      | .transformedCallRoute => .licensedEscape .W2
      | .importedOrdering => .licensedEscape .W1
      | .certifiedEngine => .certifiedSuccess :=
  (h cls).2.2

/-- Every cataloged generic DP row differs from the direct W0 route. -/
theorem genericDPBoundaryRoute_ne_w0 (cls : GenericDPMethodClass) :
    genericDPBoundaryRoute? cls ≠ some .W0 := by
  cases cls <;> decide

/-- An explicit direct certificate is a separate object from the generic DP
carrier itself. -/
structure GenericDPExplicitDirectCertificate where
  target : PRCConfig
  witness : HasDirectWitness target

/-- An explicit direct certificate for `fullLinear`, defined separately from
the generic DP boundary catalog. -/
def genericDPExplicitDirectCertificate_exists :
    GenericDPExplicitDirectCertificate := by
  exact {
    target := fullLinear
    witness := fullLinear_has_direct_witness
  }

/-- A catalog row assigned the direct W0 route contradicts its route-exclusion
theorem. -/
theorem genericDP_w0_route_impossible
    {cls : GenericDPMethodClass}
    (h : genericDPBoundaryRoute? cls = some .W0) :
    False :=
  genericDPBoundaryRoute_ne_w0 cls h

/-- Compatibility name for the direct W0 contradiction. -/
abbrev genericDP_w0_claim_requires_explicit_direct_certificate :=
  @genericDP_w0_route_impossible

/-- Certificate packaging the generic DP boundary catalog together with its W0
route exclusion. -/
structure GenericDPBoundaryCertificate where
  catalog : GenericDPBoundaryCatalog
  nonW0 : ∀ cls : GenericDPMethodClass, genericDPBoundaryRoute? cls ≠ some .W0

/-- The generic DP boundary certificate is realized by the theorem-backed
catalog and route-exclusion theorem. -/
theorem genericDPBoundaryCertificate_exact : GenericDPBoundaryCertificate := by
  exact {
    catalog := genericDPBoundaryCatalog_exact
    nonW0 := genericDPBoundaryRoute_ne_w0
  }

/-- The boundary certificate projects the generic DP catalog. -/
theorem genericDPBoundaryCertificate_projects_catalog :
    GenericDPBoundaryCatalog :=
  genericDPBoundaryCertificate_exact.catalog

/-- The boundary certificate projects the W0 route-exclusion theorem. -/
theorem genericDPBoundaryCertificate_projects_nonW0
    (cls : GenericDPMethodClass) :
    genericDPBoundaryRoute? cls ≠ some .W0 :=
  genericDPBoundaryCertificate_exact.nonW0 cls

/-! ### Relation to the six-constructor grammar

The four-row `GenericDPMethodClass` boundary catalog embeds into the
six-constructor grammar in `Meta/GenericDPGrammar.lean`
(`OperatorKO7.GenericDPGrammar.GenericDPMethod`). The larger grammar includes
two further structural transformations, `scc` and `usableRules`. The embedding theorem
`OperatorKO7.GenericDPGrammar.boundary_classification_via_grammar`
documents the classification agreement on the 4-row overlap.

The lemma below records the size relation; the embedding resides in the grammar
module to preserve an acyclic import graph. -/

theorem genericDPMethodClasses_subsumed_by_exact_grammar :
    genericDPMethodClasses.length = 4
      ∧ genericDPMethodClasses.length ≤ 6 := by
  refine ⟨rfl, ?_⟩
  decide

end OperatorKO7.GenericDPMethodBoundary
