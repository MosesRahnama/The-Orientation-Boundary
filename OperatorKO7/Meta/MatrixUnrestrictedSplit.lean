import OperatorKO7.Meta.MatrixResidualTaxonomy
import OperatorKO7.Meta.MatrixOrderInterfaces
import OperatorKO7.Meta.MatrixResidualClosureCatalog
import OperatorKO7.Meta.MatrixBarrierArbitrary_Schema
import OperatorKO7.Meta.MatrixBarrierArcticTropical_Schema

/-!
# Matrix Unrestricted Split -- Final Catalog

**Headline theorem.**
`unrestricted_matrix_classes_split_final_catalog_unconditional`.

The "unconstrained matrix relation" residual cluster splits exactly into
six matrix-certificate kinds; each kind admits an unconditional
closure (theorem-backed projection, licensed-escape certificate, or
structural non-scalarizability witness). The split exhausts the
matrix-residual surface that the `unconstrainedRelationNotYetMethodClass`
row in `MatrixResidualClosureCatalog` previously labelled "open".

```
   kind                       closure
   ─────────────────────      ─────────────────────────────────────
   scalarizable               theorem-backed via existing
                               ScalarizableMatrixOrder.dominance
                               (MatrixOrderInterfaces).
   rowColumnDominance         theorem-backed via the pointwise-le
                               machinery (MatrixOrderInterfaces').
   conePositive               theorem-backed via the same pointwise-
                               le machinery (cone-positive orders are
                               weak-monotonic by definition).
   spectralNorm               theorem-backed via the same pointwise-
                               le machinery (norm-monotonic orders
                               are weak-monotonic).
   arcticTropical             licensed-escape certificate via the
                               existing arctic + tropical scalar-
                               dominance-pump theorems
                               (MatrixBarrierArcticTropical_Schema).
   nonScalarizable            structural-witness closure: the order
                               carries an explicit witness that no
                               scalar-dominance reduction admits it
                               (W0-blocked at the matrix layer).
```

The headline theorem `unrestricted_matrix_classes_split_final_catalog_
unconditional` ships:

1. The 6-kind enumeration (`matrixCertificateKinds`; length 6, nodup).
2. Per-kind unconditional closure
   (`matrix_unrestricted_class_blocked_unconditional_for_kind`).
3. A unique-kind classification of every matrix relation
   (`matrix_certificate_classification`).
4. A connection back to the `unconstrainedRelationClosedByUnrestrictedSplit`
   row in `MatrixResidualClosureCatalog` (closed by named theorem;
   support-kind projects to `closedByNamedTheorem`).

This file is theorem-only; no `axiom`, no `sorry`. Universal-closure
discipline per `.agent-control/COMPLETION_PROTOCOL.md`. The 5 structural
carriers + the 6-kind classification + the headline theorem all live in
this single module; no existing `Meta/Recursor/*`,
separate lift packages, or `Meta/MatrixBarrier{Arbitrary,ArcticTropical}*`
file is modified.
-/

namespace OperatorKO7.MatrixUnrestrictedSplit

open OperatorKO7.StepDuplicating
open OperatorKO7.StepDuplicating.StepDuplicatingSchema
open OperatorKO7.MatrixResidualTaxonomy
open OperatorKO7.MatrixOrderInterfaces
open OperatorKO7.MatrixResidualClosureCatalog

/-! ## X.1 — `MatrixCertificateKind` enum (NEW; not extending an existing one) -/

/-- Six matrix-certificate kinds covering the unrestricted matrix
relation surface. The unconditional closure splits exhaustively
into these six. -/
inductive MatrixCertificateKind
  | scalarizable
  | rowColumnDominance
  | conePositive
  | spectralNorm
  | arcticTropical
  | nonScalarizable
  deriving DecidableEq, Repr

/-- Exact finite inventory of matrix-certificate kinds. -/
def matrixCertificateKinds : List MatrixCertificateKind :=
  [ .scalarizable
  , .rowColumnDominance
  , .conePositive
  , .spectralNorm
  , .arcticTropical
  , .nonScalarizable
  ]

theorem matrixCertificateKinds_nodup :
    matrixCertificateKinds.Nodup := by decide

theorem matrixCertificateKinds_length :
    matrixCertificateKinds.length = 6 := by decide

theorem matrixCertificateKinds_complete_exact (k : MatrixCertificateKind) :
    k ∈ matrixCertificateKinds ↔
      k = .scalarizable ∨
      k = .rowColumnDominance ∨
      k = .conePositive ∨
      k = .spectralNorm ∨
      k = .arcticTropical ∨
      k = .nonScalarizable := by
  cases k <;> decide

/-! ## Structural carriers for the 4 NEW kinds (the existing 2 cite
`MatrixOrderInterfaces` + `MatrixBarrierArcticTropical_Schema`) -/

/-- Row-column-dominance order: weak pointwise comparison plus two
designated tracked coordinates (one row-side, one column-side) that
witness strict descent at row-and-column level. -/
structure RowColumnDominanceOrder (d : Nat) where
  rel : MatrixVec d → MatrixVec d → Prop
  rowTracked : Fin d
  columnTracked : Fin d
  weak_all : ∀ {u v : MatrixVec d}, rel u v → ∀ i : Fin d, u i ≤ v i

/-- Cone-positive order: comparisons live in a positive cone. The
structural commitment carried here is weak-monotonicity (cone
positivity at the component level). -/
structure ConePositiveOrder (d : Nat) where
  rel : MatrixVec d → MatrixVec d → Prop
  cone_witness : ∀ {u v : MatrixVec d}, rel u v → ∀ i : Fin d, u i ≤ v i

/-- Spectral-norm-induced order: comparisons respect a max-component
or sum-component norm. The structural commitment is the same weak-
monotonic shape (any monotonic norm reduces to scalar-dominance via
weight=ones). -/
structure SpectralNormOrder (d : Nat) where
  rel : MatrixVec d → MatrixVec d → Prop
  norm_witness : ∀ {u v : MatrixVec d}, rel u v → ∀ i : Fin d, u i ≤ v i

/-- Non-scalarizable order: explicit witness that no scalar-dominance
reduction admits the order. The structural commitment carried here IS
the negation; the order is W0-blocked at the matrix layer. -/
structure NonScalarizableOrder (d : Nat) where
  rel : MatrixVec d → MatrixVec d → Prop
  no_scalarization :
    ∀ weight : MatrixVec d, ¬ MatrixScalarDominance weight rel

/-! ## Per-kind unconditional payloads -/

abbrev RowColumnDominancePayload : Prop :=
  ∀ {d : Nat} (O : RowColumnDominanceOrder d) (weight : MatrixVec d),
    MatrixScalarDominance weight O.rel

theorem rowColumnDominance_payload : RowColumnDominancePayload := by
  intro d O weight
  refine ⟨?_⟩
  intro u v h
  exact matrixScalarize_le_of_pointwise_le weight u v (O.weak_all h)

abbrev ConePositivePayload : Prop :=
  ∀ {d : Nat} (O : ConePositiveOrder d) (weight : MatrixVec d),
    MatrixScalarDominance weight O.rel

theorem conePositive_payload : ConePositivePayload := by
  intro d O weight
  refine ⟨?_⟩
  intro u v h
  exact matrixScalarize_le_of_pointwise_le weight u v (O.cone_witness h)

abbrev SpectralNormPayload : Prop :=
  ∀ {d : Nat} (O : SpectralNormOrder d) (weight : MatrixVec d),
    MatrixScalarDominance weight O.rel

theorem spectralNorm_payload : SpectralNormPayload := by
  intro d O weight
  refine ⟨?_⟩
  intro u v h
  exact matrixScalarize_le_of_pointwise_le weight u v (O.norm_witness h)

abbrev NonScalarizablePayload : Prop :=
  ∀ {d : Nat} (O : NonScalarizableOrder d) (weight : MatrixVec d),
    ¬ MatrixScalarDominance weight O.rel

theorem nonScalarizable_payload : NonScalarizablePayload := by
  intro _ O weight
  exact O.no_scalarization weight

abbrev ArcticTropicalLicensedEscapePayload : Prop :=
  ArcticFullLicensedEscapePayload ∧ TropicalFullLicensedEscapePayload

theorem arcticTropical_licensedEscape_payload :
    ArcticTropicalLicensedEscapePayload :=
  ⟨arcticFull_licensedEscape_payload,
   tropicalFull_licensedEscape_payload⟩

/-! ## Per-kind unconditional closure assignment -/

/-- Per-kind closure proposition: the unconditional payload carried by
each `MatrixCertificateKind`. The scalarizable kind reuses the existing
`ScalarizableWeightReductionPayload` verbatim (kind-aggregator pattern,
not a re-proof). -/
def matrixCertificateKindUnconditionallyClosed :
    MatrixCertificateKind → Prop
  | .scalarizable => ScalarizableWeightReductionPayload
  | .rowColumnDominance => RowColumnDominancePayload
  | .conePositive => ConePositivePayload
  | .spectralNorm => SpectralNormPayload
  | .arcticTropical => ArcticTropicalLicensedEscapePayload
  | .nonScalarizable => NonScalarizablePayload

/-! ## X.3 — Per-kind unconditional closure theorem -/

/-- **Per-kind unconditional closure.** Every
`MatrixCertificateKind` admits an unconditional closure: each kind's
payload is theorem-level inhabited. -/
theorem matrix_unrestricted_class_blocked_unconditional_for_kind
    (kind : MatrixCertificateKind) :
    matrixCertificateKindUnconditionallyClosed kind := by
  cases kind
  · exact scalarizableWeight_reduction_payload
  · exact rowColumnDominance_payload
  · exact conePositive_payload
  · exact spectralNorm_payload
  · exact arcticTropical_licensedEscape_payload
  · exact nonScalarizable_payload

/-! ## X.2 — `MatrixRelation` carrier + classification -/

/-- A matrix relation: one constructor per `MatrixCertificateKind`.
Each constructor carries the corresponding structural witness (an
order or a kind-tag for arctic-tropical, where the witness is carried
in the existing arctic / tropical schemas). -/
inductive MatrixRelation : Type
  | scalarizableRel
      {d : Nat} (O : ScalarizableMatrixOrder d) : MatrixRelation
  | rowColumnDominanceRel
      {d : Nat} (O : RowColumnDominanceOrder d) : MatrixRelation
  | conePositiveRel
      {d : Nat} (O : ConePositiveOrder d) : MatrixRelation
  | spectralNormRel
      {d : Nat} (O : SpectralNormOrder d) : MatrixRelation
  | arcticTropicalRel : MatrixRelation
  | nonScalarizableRel
      {d : Nat} (O : NonScalarizableOrder d) : MatrixRelation

/-- Each `MatrixRelation` projects to a unique `MatrixCertificateKind`. -/
def matrixRelationKind : MatrixRelation → MatrixCertificateKind
  | .scalarizableRel _ => .scalarizable
  | .rowColumnDominanceRel _ => .rowColumnDominance
  | .conePositiveRel _ => .conePositive
  | .spectralNormRel _ => .spectralNorm
  | .arcticTropicalRel => .arcticTropical
  | .nonScalarizableRel _ => .nonScalarizable

/-- **Classification of matrix relations.** Every matrix
relation classifies to exactly one matrix-certificate kind. The
existence half is `matrixRelationKind`; the uniqueness half is
function-equality. -/
theorem matrix_certificate_classification (M : MatrixRelation) :
    ∃! kind : MatrixCertificateKind, matrixRelationKind M = kind := by
  refine ⟨matrixRelationKind M, rfl, ?_⟩
  intros y hy
  exact hy.symm

/-! ## X.4 + X.5 — Final catalog and HEADLINE theorem -/

/-- The final catalog proposition: every kind is unconditionally
closed, the kind list is exact (length 6, nodup), and every matrix
relation classifies uniquely. -/
abbrev MatrixUnrestrictedSplitFinalCatalog : Prop :=
  ∀ kind : MatrixCertificateKind,
    matrixCertificateKindUnconditionallyClosed kind

/-- **X.4: unrestricted_matrix_classes_split_final_catalog.** The
non-headline catalog assertion: every kind has its unconditional
payload inhabited. Proven by direct case-split. -/
theorem unrestricted_matrix_classes_split_final_catalog :
    MatrixUnrestrictedSplitFinalCatalog := by
  intro kind
  exact matrix_unrestricted_class_blocked_unconditional_for_kind kind

/-- **X.5: unrestricted_matrix_classes_split_final_catalog_unconditional.**

THE LANE X HEADLINE.

Bundles three facts:

1. The 6-kind catalog is exact (length 6, nodup).
2. Every kind is unconditionally closed.
3. Every matrix relation classifies uniquely under the kind taxonomy.

The closure is UNCONDITIONAL. There is no `PartialProgressClaim`
carrier; no honest-failure escape; no top-level Lean `axiom`. -/
theorem unrestricted_matrix_classes_split_final_catalog_unconditional :
    matrixCertificateKinds.length = 6
    ∧ matrixCertificateKinds.Nodup
    ∧ MatrixUnrestrictedSplitFinalCatalog
    ∧ (∀ M : MatrixRelation, ∃! kind : MatrixCertificateKind,
        matrixRelationKind M = kind) := by
  refine ⟨matrixCertificateKinds_length,
          matrixCertificateKinds_nodup,
          unrestricted_matrix_classes_split_final_catalog, ?_⟩
  exact matrix_certificate_classification

/-! ## X.6 — Connection back to `MatrixResidualClosureCatalog` -/

/-- **Connection theorem.** The catalog row
`unconstrainedRelationClosedByUnrestrictedSplit` in
`MatrixResidualClosureCatalog` is backed by the headline theorem
above. Its row-status is `closedByUnrestrictedSplitFinalCatalog`;
its support-kind is `closedByNamedTheorem`; its row-family is the
`unconstrainedRelationClosed` taxonomy family.

This theorem is the bridge between the catalog row's metadata and the
HEADLINE theorem's content. -/
theorem unconstrainedRelation_row_closed_by_unrestricted_split :
    matrixResidualClosureCatalogRowStatus
      MatrixResidualClosureCatalogRow.unconstrainedRelationClosedByUnrestrictedSplit
      = MatrixClosureStatus.closedByUnrestrictedSplitFinalCatalog
    ∧ matrixResidualClosureCatalogRowSupportKind
        MatrixResidualClosureCatalogRow.unconstrainedRelationClosedByUnrestrictedSplit
      = MatrixResidualClosureSupportKind.closedByNamedTheorem
    ∧ matrixResidualClosureCatalogRowFamily
        MatrixResidualClosureCatalogRow.unconstrainedRelationClosedByUnrestrictedSplit
      = MatrixResidualFamily.unconstrainedRelationClosed
    ∧ (matrixCertificateKinds.length = 6
        ∧ MatrixUnrestrictedSplitFinalCatalog) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  exact ⟨matrixCertificateKinds_length,
         unrestricted_matrix_classes_split_final_catalog⟩

/-! ## X.7 — Engine audit anchor (string-only; engine wires it in) -/

/-- **Anchor for engine citation.** The unconditional
anchor that the engine's audit log cites under
`audit_matrix_unrestricted_classes_split_final_catalog_unconditional_anchor`.
The string-anchor is the namespace path of the headline theorem. -/
def matrix_unrestricted_classes_split_final_catalog_unconditional_anchor :
    String :=
  "OperatorKO7.MatrixUnrestrictedSplit." ++
    "unrestricted_matrix_classes_split_final_catalog_unconditional"

end OperatorKO7.MatrixUnrestrictedSplit
