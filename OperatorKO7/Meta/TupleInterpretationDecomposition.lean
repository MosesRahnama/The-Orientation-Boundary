import OperatorKO7.Meta.RDRSAlgebraicInterpretationAtlas
import OperatorKO7.Meta.RDRSSemanticDirectMeasure

/-!
# Tuple Interpretation Decomposition (theory-expansion module)

Roadmap source: the tuple-interpretation row in
`OperatorKO7/Expansion/RDRS_Termination_Methods_Roadmap.md`, the
tuple-interpretation surface in `Meta/RDRSAlgebraicInterpretationAtlas.lean`,
the stable shim `Meta/RDRSTupleInterpretationBoundary.lean`, and the tuple
taxonomy disclaimers in Paper A.

This module does not claim a barrier against tuple interpretations as a whole.
The formal universe already records only two tuple rows, both conditional:

* `tupleInterpretationStrictS`
* `higherOrderTupleInterpretation`

The honest unconditional theorem here is therefore a decomposition theorem over
the existing row-hypothesis carriers. Each tuple row factors into a finite
family of component scalar direct-measure observations, together with a
designated strict coordinate. That factorization determines the row-local
classification consequence:

* first-order tuple strict-s factors through coordinate-AF conditional barrier;
* higher-order tuple strict-s factors through higher-order strict-s conditional
  barrier.

No universal subsumption claim is made for tuple interpretations as a whole,
generalized WPO, or co-rewrite variants.

## Audit slots

```text
Relation:  closed metadata carriers over the two tuple rows and their explicit
           row hypotheses; not a rewriting relation.
Closure:   not applicable.
Strategy:  not applicable.
Trust:     kernel-only. No forbidden trusted shortcuts.
Scope:     unconditional decomposition inside the existing formal RDRS universe,
           not a universal theorem about arbitrary tuple interpretations.
```
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.TupleInterpretationDecomposition

open OperatorKO7.RDRSTerminationMethodUniverse
open OperatorKO7.RDRSAlgebraicInterpretationAtlas
open OperatorKO7.RDRSSemanticDirectMeasure

/-- The two tuple-interpretation rows represented in the RDRS universe. -/
inductive TupleInterpretationRow where
  | tupleInterpretationStrictS
  | higherOrderTupleInterpretation
  deriving DecidableEq, Repr

/-- Closed inventory of the two tuple rows. -/
def tupleInterpretationRows : List TupleInterpretationRow :=
  [.tupleInterpretationStrictS, .higherOrderTupleInterpretation]

theorem tupleInterpretationRows_length :
    tupleInterpretationRows.length = 2 := by
  rfl

theorem tupleInterpretationRows_nodup :
    tupleInterpretationRows.Nodup := by
  decide

/-- Transport from the local row carrier to the global RDRS method universe. -/
def familyOf : TupleInterpretationRow → RDRSMethodFamily
  | .tupleInterpretationStrictS => .tupleInterpretationStrictS
  | .higherOrderTupleInterpretation => .higherOrderTupleInterpretation

/-- The row-local barrier consequence determined by the decomposition. -/
inductive TupleBoundaryClass where
  | coordinateAFConditionalBarrier
  | hoTupleStrictSConditionalBarrier
  deriving DecidableEq, Repr

/-- Classifier for the two tuple rows. -/
def boundaryClassOf : TupleInterpretationRow → TupleBoundaryClass
  | .tupleInterpretationStrictS => .coordinateAFConditionalBarrier
  | .higherOrderTupleInterpretation => .hoTupleStrictSConditionalBarrier

/-- Existing row-hypothesis carrier for each tuple row. -/
def RowHypothesis : TupleInterpretationRow → Type
  | .tupleInterpretationStrictS => TupleStrictSHyp
  | .higherOrderTupleInterpretation => HOTupleStrictSHyp

/-- Project arity from the row hypothesis. -/
def arityOf : {row : TupleInterpretationRow} → RowHypothesis row → Nat
  | .tupleInterpretationStrictS, h => h.arity
  | .higherOrderTupleInterpretation, h => h.arity

/-- Project the designated strict coordinate from the row hypothesis. -/
def strictIndexOf : {row : TupleInterpretationRow} → RowHypothesis row → Nat
  | .tupleInterpretationStrictS, h => h.strictIndex
  | .higherOrderTupleInterpretation, h => h.strictIndex

/-- Proof that the designated strict coordinate lies inside the tuple arity. -/
def strictIndex_lt_arity_of :
    {row : TupleInterpretationRow} → (h : RowHypothesis row) →
      strictIndexOf h < arityOf h
  | .tupleInterpretationStrictS, h => h.strictIndex_lt_arity
  | .higherOrderTupleInterpretation, h => h.strictIndex_lt_arity

/-- The higher-order argument-filter side condition, when present. -/
def higherOrderFlagOf? :
    {row : TupleInterpretationRow} → RowHypothesis row → Option Bool
  | .tupleInterpretationStrictS, _ => none
  | .higherOrderTupleInterpretation, h => some h.argumentFilterAdmissible

/-- Every tuple component is treated as a scalar direct observation. -/
def scalarComponentKind (arity : Nat) : Fin arity → DirectEvidenceKind :=
  fun _ => .scalarObservation

/--
Decomposition package for one tuple row. The package records the explicit
strict coordinate, the scalar direct-measure kind of every component, the
optional higher-order side condition, and the resulting row-local boundary
classification.
-/
structure TupleInterpretationDecomposition (row : TupleInterpretationRow) where
  arity : Nat
  strictIndex : Nat
  strictIndex_lt_arity : strictIndex < arity
  componentKind : Fin arity → DirectEvidenceKind
  components_are_scalar : ∀ i, componentKind i = .scalarObservation
  higherOrderFlag? : Option Bool
  boundaryClass : TupleBoundaryClass
  boundaryClass_eq : boundaryClass = boundaryClassOf row
  universeStatus_eq : statusOf (familyOf row) = .conditional_barrier

/-- Canonical decomposition for the first-order tuple strict-s row. -/
def tupleStrictSDecomposition (h : TupleStrictSHyp) :
    TupleInterpretationDecomposition .tupleInterpretationStrictS where
  arity := h.arity
  strictIndex := h.strictIndex
  strictIndex_lt_arity := h.strictIndex_lt_arity
  componentKind := scalarComponentKind h.arity
  components_are_scalar := by
    intro i
    rfl
  higherOrderFlag? := none
  boundaryClass := .coordinateAFConditionalBarrier
  boundaryClass_eq := rfl
  universeStatus_eq := rfl

/-- Canonical decomposition for the higher-order tuple strict-s row. -/
def higherOrderTupleDecomposition (h : HOTupleStrictSHyp) :
    TupleInterpretationDecomposition .higherOrderTupleInterpretation where
  arity := h.arity
  strictIndex := h.strictIndex
  strictIndex_lt_arity := h.strictIndex_lt_arity
  componentKind := scalarComponentKind h.arity
  components_are_scalar := by
    intro i
    rfl
  higherOrderFlag? := some h.argumentFilterAdmissible
  boundaryClass := .hoTupleStrictSConditionalBarrier
  boundaryClass_eq := rfl
  universeStatus_eq := rfl

/-- Uniform constructor for the tuple decomposition package. -/
def decompositionOf :
    {row : TupleInterpretationRow} → RowHypothesis row →
      TupleInterpretationDecomposition row
  | .tupleInterpretationStrictS, h => tupleStrictSDecomposition h
  | .higherOrderTupleInterpretation, h => higherOrderTupleDecomposition h

/-- Both tuple rows remain conditional-barrier rows in the global universe. -/
theorem tuple_rows_have_conditional_barrier_status
    (row : TupleInterpretationRow) :
    statusOf (familyOf row) = .conditional_barrier := by
  cases row <;> rfl

/--
Proves: every formal tuple-interpretation row in the RDRS universe decomposes
into finitely many component scalar direct-measure observations, together with
one designated strict coordinate and its row-local classification.
-/
theorem tuple_interpretation_decomposition_unconditional :
    ∀ (row : TupleInterpretationRow) (h : RowHypothesis row),
      ∃ D : TupleInterpretationDecomposition row,
        D.arity = arityOf h ∧
        D.strictIndex = strictIndexOf h ∧
        D.strictIndex < D.arity ∧
        D.higherOrderFlag? = higherOrderFlagOf? h ∧
        D.boundaryClass = boundaryClassOf row ∧
        (∀ i, D.componentKind i = .scalarObservation) ∧
        statusOf (familyOf row) = .conditional_barrier := by
  intro row h
  cases row with
  | tupleInterpretationStrictS =>
      refine ⟨tupleStrictSDecomposition h, ?_⟩
      refine ⟨rfl, rfl, h.strictIndex_lt_arity, rfl, rfl, ?_, rfl⟩
      intro i
      rfl
  | higherOrderTupleInterpretation =>
      refine ⟨higherOrderTupleDecomposition h, ?_⟩
      refine ⟨rfl, rfl, h.strictIndex_lt_arity, rfl, rfl, ?_, rfl⟩
      intro i
      rfl

/-- Stable placeholder anchor until Supervisor A flips audit-log status. -/
def audit_theory_expansion_tuple_interpretation_decomposition_module_anchor : String :=
  "OperatorKO7.Meta.TupleInterpretationDecomposition.tuple_interpretation_decomposition_unconditional"

end OperatorKO7.Meta.TupleInterpretationDecomposition
