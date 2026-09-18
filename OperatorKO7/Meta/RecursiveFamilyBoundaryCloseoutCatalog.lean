import OperatorKO7.Meta.RightDuplicatingRecursorSchema
import OperatorKO7.Meta.DuplicatingRecursiveFamily
import OperatorKO7.Meta.KO7RDRSAdapter
import OperatorKO7.Meta.CanonicalWitnessUniversality
import OperatorKO7.Meta.DirectBarrierScope
import OperatorKO7.Meta.DirectWholeTermObserver
import OperatorKO7.Meta.PayloadExposureMatrix
import OperatorKO7.Meta.TupleDecomposition
import OperatorKO7.Meta.MatrixOverPolynomialReduction
import OperatorKO7.Meta.FiniteGraphSCC
import OperatorKO7.Meta.ContextSCCTransport
import OperatorKO7.Meta.RecursiveFamilyEscapeCharacterization
import OperatorKO7.Meta.KO7EscapeRouteCharacterization
import OperatorKO7.Meta.DependencyPairs_Works
import OperatorKO7.Meta.DPSubtermCriterionExact
import OperatorKO7.Meta.RecursiveFamilyTypedPolicyRows
import OperatorKO7.Meta.ResidualMethodClosureCatalog

/-!
# Recursive Family Boundary Closeout Catalog (Phase G)

Phase G surface layer. The recursive-family boundary program (Phases A through
F+) consists of 11 substrate deliverables, each backed by a named theorem in a
dedicated module. Phase G catalogues those 11 deliverables as a single finite
row inventory and records, per row, a projection witness onto an existing
theorem-backed identifier from the substrate.

The eleven rows and their backing substrate identifiers:

* `phaseA_RDRS` ->
  `OperatorKO7.StepDuplicating.RightDuplicatingRecursorSchema.rhs_count_gt_lhs_count`.
* `phaseA_DuplicatingRecursiveFamily` ->
  `OperatorKO7.StepDuplicating.DuplicatingRecursiveFamily.distinguished_payload_count_strict`.
* `phaseA3_CanonicalWitnessUniversality` ->
  the four canonical witnesses in
  `OperatorKO7.StepDuplicating.CanonicalWitnessUniversality`.
* `phaseA5_DirectBarrierScope` ->
  `OperatorKO7.StepDuplicating.fullScope_InScope`.
* `phaseB_DirectWholeTermObserver` ->
  `OperatorKO7.StepDuplicating.no_additive_orients_dup_step_via_DWO`.
* `phaseC_VectorMatrixTuple` ->
  `OperatorKO7.StepDuplicating.phaseC_vector_matrix_tuple_closed`.
* `phaseD_FiniteSCCBoundaryBundle` ->
  `OperatorKO7.ContextSCCTransport.finite_scc_boundary_coexistence_bundle`.
* `phaseEprime_TypedPolicyRows` ->
  `OperatorKO7.StepDuplicating.RecursiveFamilyTypedPolicyRows.phaseEprime_typed_policy_rows_closed`.
* `phaseF_EscapeCatalog` ->
  `OperatorKO7.ResidualMethodClosureCatalog.residualMethodClosureCertificate`.
* `phaseF5_EscapeCharacterization` ->
  `OperatorKO7.StepDuplicating.phaseF5_escape_characterization_closed`.
* `phaseFplus_DPSubtermCriterion` ->
  `OperatorKO7.DPSubtermCriterionExactNS.phaseFplus_dp_subterm_closed`.

No proof placeholder is used, no top-level postulate is declared, and no
existing public name is touched. Inventory-only rows are not introduced; every
row's projection predicate is theorem-backed by an existing identifier from
the substrate.
-/

namespace OperatorKO7.StepDuplicating

open OperatorKO7
open RecursiveFamilyEscapeCharacterization
open KO7RDRSAdapter
open CanonicalWitnessUniversality
open RecursiveFamilyTypedPolicyRows
open OperatorKO7.ContextSCCTransport
open OperatorKO7.ContextClosedBarrier
open OperatorKO7.FiniteGraphSCC
open OperatorKO7.FiniteGraphReachability
open OperatorKO7.CompositionalImpossibility
open OperatorKO7.MetaDependencyPairs
open OperatorKO7.TTT2CertificateReplay
open OperatorKO7.DPSubtermCriterionExactNS
open OperatorKO7.ResidualMethodClosureCatalog

namespace RecursiveFamilyBoundaryCloseoutCatalog

/-- Finite identity tag for each Phase G recursive-family boundary closeout
row surfaced from the substrate. The eleven constructors match the eleven
phases of the recursive-family boundary program. -/
inductive RecursiveFamilyBoundaryCloseoutRow
  | phaseA_RDRS
  | phaseA_DuplicatingRecursiveFamily
  | phaseA3_CanonicalWitnessUniversality
  | phaseA5_DirectBarrierScope
  | phaseB_DirectWholeTermObserver
  | phaseC_VectorMatrixTuple
  | phaseD_FiniteSCCBoundaryBundle
  | phaseEprime_TypedPolicyRows
  | phaseF_EscapeCatalog
  | phaseF5_EscapeCharacterization
  | phaseFplus_DPSubtermCriterion
  deriving DecidableEq, Repr

namespace RecursiveFamilyBoundaryCloseoutRow

/-- Per-row status tag for Phase G. Every row currently surfaced is a
theorem-backed projection onto an existing substrate identifier, hence
`theoremBacked`. The constructor is retained for symmetry with the other
catalog surfaces (`RecursiveFamilyTypedPolicyRow.Status`,
`ResidualMethodClosureCatalogRowStatus`, etc.) while keeping this Phase G
surface entirely theorem-backed. -/
inductive Status
  | theoremBacked
  deriving DecidableEq, Repr

/-- Status assignment for every Phase G row. Every row is theorem-backed via
the projection lemma in
`recursiveFamily_boundary_closeout_row_projects_existing_surface_holds`. -/
def status : RecursiveFamilyBoundaryCloseoutRow → Status
  | _ => Status.theoremBacked

end RecursiveFamilyBoundaryCloseoutRow

/-- Finite catalog of Phase G recursive-family boundary closeout rows.

The order is fixed in phase-execution order: A (RDRS), A (DuplicatingRecursive
Family), A.3 (canonical witness), A.5 (scope record), B (direct whole-term
observer), C (vector/matrix/tuple), D (finite SCC and boundary coexistence),
E' (typed and policy rows), F (escape catalog), F.5 (escape-route
characterization), and F+ (DP subterm criterion plus independent CeTA support). -/
def recursiveFamily_boundary_closeout_catalog :
    List RecursiveFamilyBoundaryCloseoutRow :=
  [ .phaseA_RDRS
  , .phaseA_DuplicatingRecursiveFamily
  , .phaseA3_CanonicalWitnessUniversality
  , .phaseA5_DirectBarrierScope
  , .phaseB_DirectWholeTermObserver
  , .phaseC_VectorMatrixTuple
  , .phaseD_FiniteSCCBoundaryBundle
  , .phaseEprime_TypedPolicyRows
  , .phaseF_EscapeCatalog
  , .phaseF5_EscapeCharacterization
  , .phaseFplus_DPSubtermCriterion ]

/-- The Phase G row catalog has the expected length, is duplicate-free, and
covers every constructor of `RecursiveFamilyBoundaryCloseoutRow`. -/
theorem recursiveFamily_boundary_closeout_catalog_complete_exact :
    recursiveFamily_boundary_closeout_catalog.length = 11 ∧
      recursiveFamily_boundary_closeout_catalog.Nodup ∧
      (∀ row : RecursiveFamilyBoundaryCloseoutRow,
        row ∈ recursiveFamily_boundary_closeout_catalog) := by
  refine ⟨?_, ?_, ?_⟩
  · rfl
  · decide
  · intro row
    cases row <;> decide

/-- Projection of every Phase G row onto a concrete existing theorem
identifier from the substrate. Each branch returns a propositional witness
that the named substrate surface is reachable and theorem-backed. No new
content about the schema, the recursive-family carriers, or the escape-route
catalog is asserted; the projection reuses an existing theorem applied to
canonical arguments. -/
def recursiveFamily_boundary_closeout_row_projects_existing_surface :
    RecursiveFamilyBoundaryCloseoutRow → Prop
  | .phaseA_RDRS =>
      ∀ (S : RightDuplicatingRecursorSchema),
        S.payloadCount S.distinguishedPayload S.lhs <
          S.payloadCount S.distinguishedPayload S.rhs
  | .phaseA_DuplicatingRecursiveFamily =>
      ∀ (F : DuplicatingRecursiveFamily),
        F.schema.payloadCount F.distinguishedPayload F.schema.lhs <
          F.schema.payloadCount F.distinguishedPayload F.schema.rhs
  | .phaseA3_CanonicalWitnessUniversality =>
      canonicalWitnesses.length = 4 ∧
        nonKO7CanonicalWitnesses.length = 3 ∧
        ko7CanonicalWitness.declaredClosedFirability ∧
        textbookCanonicalWitness.declaredClosedFirability ∧
        taggedBinaryCanonicalWitness.declaredClosedFirability ∧
        depthCounterCanonicalWitness.declaredClosedFirability ∧
        ko7CanonicalWitness.schema = ko7RDRS
  | .phaseA5_DirectBarrierScope =>
      InScope fullScope
  | .phaseB_DirectWholeTermObserver =>
      ∀ (F : DuplicatingRecursiveFamily)
        (_hPump : F.HasUnboundedPayloadPump F.distinguishedPayload),
        ¬ F.GloballyOrients (payloadCountObserver F)
  | .phaseC_VectorMatrixTuple =>
      ∀ (F : DuplicatingRecursiveFamily)
        (_hPump : F.HasUnboundedPayloadPump F.distinguishedPayload),
        (∀ (i : F.schema.PayloadCoord) (t : F.schema.Term),
          (payloadExposureMatrix F).entry i t = F.schema.payloadCount i t)
          ∧ (∀ P : MatrixOverPolynomial F,
            ¬ F.GloballyOrients (payloadExposureMatrix_to_DWO P.matrix))
          ∧ (∀ (_D : TupleDecomposition F) (k : TupleDispositionKind),
            k = TupleDispositionKind.scalar
              ∨ k = TupleDispositionKind.matrix
              ∨ k = TupleDispositionKind.status)
  | .phaseD_FiniteSCCBoundaryBundle =>
      ∀ (C : FiniteSCCCertificate),
        SCCRoundTrip C
          ∧
          (∀ {α : Type} {m : Trace → α} {lt : α → α → Prop}
            (_h : GlobalOrientsStepCtxFull m lt),
              StepDuplicatingSchema.GlobalOrients ko7System m lt)
          ∧
          (∀ {F : DuplicatingRecursiveFamily}
            (O : DirectWholeTermObserver F)
            {i : F.schema.PayloadCoord}
            (_hPump : F.HasUnboundedPayloadPump i)
            (_hExposure : F.ExposesPayloadStrictly i)
            (_hVisible : O.visiblePayloadCoordinate i)
            (_hSensitive : O.carrierSensitive i),
              ¬ F.GloballyOrients O)
  | .phaseEprime_TypedPolicyRows =>
      (recursiveFamilyTypedPolicyRows.length = 7 ∧
        recursiveFamilyTypedPolicyRows.Nodup ∧
        (∀ row : RecursiveFamilyTypedPolicyRow,
          row ∈ recursiveFamilyTypedPolicyRows)) ∧
        (∀ row : RecursiveFamilyTypedPolicyRow,
          typed_policy_rows_project_existing_surfaces row)
  | .phaseF_EscapeCatalog =>
      ResidualMethodClosureCatalogSurface ∧
        (∀ row : ResidualMethodClosureCatalogRow,
          residualMethodClosureCatalogRowStatus row = .blocked ∨
            residualMethodClosureCatalogRowStatus row = .closedByLeanTheorem ∨
            residualMethodClosureCatalogRowStatus row = .reducedToExistingTheorem ∨
            residualMethodClosureCatalogRowStatus row = .licensedEscape ∨
            residualMethodClosureCatalogRowStatus row = .certifiedSuccess)
  | .phaseF5_EscapeCharacterization =>
      (∀ (F : DuplicatingRecursiveFamily),
        RecursiveFamilyEscapeCharacterization F) ∧
        KO7EscapeRouteCharacterization
  | .phaseFplus_DPSubtermCriterion =>
      (∀ {a b : Trace}, DPPair a b → dpRank b < dpRank a)
        ∧ ko7FastReplay.projectionProblem.Pair = DPPair
        ∧ ko7DPSubtermCriterionExact.projectionIndex_paper
            = ko7FastReplay.projectionIndexPaper
        ∧ WellFounded DPPairRev

/-- Every Phase G row's projection predicate is theorem-backed by an existing
substrate identifier. Each branch reuses the existing theorem name; where the
substrate surface is a closure marker conjunction, the relevant conjunct is
projected without restating its proof. -/
theorem recursiveFamily_boundary_closeout_row_projects_existing_surface_holds
    (row : RecursiveFamilyBoundaryCloseoutRow) :
    recursiveFamily_boundary_closeout_row_projects_existing_surface row := by
  cases row with
  | phaseA_RDRS =>
      show ∀ (S : RightDuplicatingRecursorSchema),
          S.payloadCount S.distinguishedPayload S.lhs <
            S.payloadCount S.distinguishedPayload S.rhs
      intro S
      exact S.rhs_count_gt_lhs_count
  | phaseA_DuplicatingRecursiveFamily =>
      show ∀ (F : DuplicatingRecursiveFamily),
          F.schema.payloadCount F.distinguishedPayload F.schema.lhs <
            F.schema.payloadCount F.distinguishedPayload F.schema.rhs
      intro F
      exact F.distinguished_payload_count_strict
  | phaseA3_CanonicalWitnessUniversality =>
      show canonicalWitnesses.length = 4 ∧
          nonKO7CanonicalWitnesses.length = 3 ∧
          ko7CanonicalWitness.declaredClosedFirability ∧
          textbookCanonicalWitness.declaredClosedFirability ∧
          taggedBinaryCanonicalWitness.declaredClosedFirability ∧
          depthCounterCanonicalWitness.declaredClosedFirability ∧
          ko7CanonicalWitness.schema = ko7RDRS
      exact ⟨canonicalWitnesses_length,
        nonKO7CanonicalWitnesses_length,
        ko7CanonicalWitness_declaredClosedFirability,
        textbookCanonicalWitness_declaredClosedFirability,
        taggedBinaryCanonicalWitness_declaredClosedFirability,
        depthCounterCanonicalWitness_declaredClosedFirability,
        ko7_as_canonical_recursiveFamily_witness⟩
  | phaseA5_DirectBarrierScope =>
      show InScope fullScope
      exact fullScope_InScope
  | phaseB_DirectWholeTermObserver =>
      show ∀ (F : DuplicatingRecursiveFamily)
            (_hPump : F.HasUnboundedPayloadPump F.distinguishedPayload),
          ¬ F.GloballyOrients (payloadCountObserver F)
      intro F hPump
      exact no_additive_orients_dup_step_via_DWO F hPump
  | phaseC_VectorMatrixTuple =>
      show ∀ (F : DuplicatingRecursiveFamily)
            (_hPump : F.HasUnboundedPayloadPump F.distinguishedPayload),
          (∀ (i : F.schema.PayloadCoord) (t : F.schema.Term),
            (payloadExposureMatrix F).entry i t = F.schema.payloadCount i t)
            ∧ (∀ P : MatrixOverPolynomial F,
              ¬ F.GloballyOrients (payloadExposureMatrix_to_DWO P.matrix))
            ∧ (∀ (_D : TupleDecomposition F) (k : TupleDispositionKind),
              k = TupleDispositionKind.scalar
                ∨ k = TupleDispositionKind.matrix
                ∨ k = TupleDispositionKind.status)
      intro F hPump
      exact phaseC_vector_matrix_tuple_closed F hPump
  | phaseD_FiniteSCCBoundaryBundle =>
      show ∀ (C : FiniteSCCCertificate),
          SCCRoundTrip C
            ∧
            (∀ {α : Type} {m : Trace → α} {lt : α → α → Prop}
              (_h : GlobalOrientsStepCtxFull m lt),
                StepDuplicatingSchema.GlobalOrients ko7System m lt)
            ∧
            (∀ {F : DuplicatingRecursiveFamily}
              (O : DirectWholeTermObserver F)
              {i : F.schema.PayloadCoord}
              (_hPump : F.HasUnboundedPayloadPump i)
              (_hExposure : F.ExposesPayloadStrictly i)
              (_hVisible : O.visiblePayloadCoordinate i)
              (_hSensitive : O.carrierSensitive i),
                ¬ F.GloballyOrients O)
      intro C
      exact finite_scc_boundary_coexistence_bundle C
  | phaseEprime_TypedPolicyRows =>
      show (recursiveFamilyTypedPolicyRows.length = 7 ∧
          recursiveFamilyTypedPolicyRows.Nodup ∧
          (∀ row : RecursiveFamilyTypedPolicyRow,
            row ∈ recursiveFamilyTypedPolicyRows)) ∧
          (∀ row : RecursiveFamilyTypedPolicyRow,
            typed_policy_rows_project_existing_surfaces row)
      exact phaseEprime_typed_policy_rows_closed
  | phaseF_EscapeCatalog =>
      show ResidualMethodClosureCatalogSurface ∧
          (∀ row : ResidualMethodClosureCatalogRow,
            residualMethodClosureCatalogRowStatus row = .blocked ∨
              residualMethodClosureCatalogRowStatus row = .closedByLeanTheorem ∨
              residualMethodClosureCatalogRowStatus row = .reducedToExistingTheorem ∨
              residualMethodClosureCatalogRowStatus row = .licensedEscape ∨
              residualMethodClosureCatalogRowStatus row = .certifiedSuccess)
      exact ⟨residualMethodClosureCertificate_projects_catalog,
        residualMethodClosureCertificate.allRowsTerminal⟩
  | phaseF5_EscapeCharacterization =>
      show (∀ (F : DuplicatingRecursiveFamily),
          RecursiveFamilyEscapeCharacterization F) ∧
          KO7EscapeRouteCharacterization
      exact phaseF5_escape_characterization_closed
  | phaseFplus_DPSubtermCriterion =>
      show (∀ {a b : Trace}, DPPair a b → dpRank b < dpRank a)
        ∧ ko7FastReplay.projectionProblem.Pair = DPPair
        ∧ ko7DPSubtermCriterionExact.projectionIndex_paper
            = ko7FastReplay.projectionIndexPaper
        ∧ WellFounded DPPairRev
      exact phaseFplus_dp_subterm_closed

/-- Phase G closeout marker. The catalog is complete and exact, and every
row projects onto an existing theorem-backed substrate identifier. This is
the single public name reviewers reach for to confirm Phase G closure.

No new manuscript or Lean claim is asserted beyond what the substrate modules
already establish; Phase G is intentionally a surfacing pass that catalogs
every prior phase's closure into one finite row inventory. -/
theorem phaseG_recursiveFamily_boundary_closeout_closed :
    (recursiveFamily_boundary_closeout_catalog.length = 11 ∧
        recursiveFamily_boundary_closeout_catalog.Nodup ∧
        (∀ row : RecursiveFamilyBoundaryCloseoutRow,
          row ∈ recursiveFamily_boundary_closeout_catalog)) ∧
      (∀ row : RecursiveFamilyBoundaryCloseoutRow,
        recursiveFamily_boundary_closeout_row_projects_existing_surface row) :=
  ⟨recursiveFamily_boundary_closeout_catalog_complete_exact,
   recursiveFamily_boundary_closeout_row_projects_existing_surface_holds⟩

end RecursiveFamilyBoundaryCloseoutCatalog
end OperatorKO7.StepDuplicating
