import OperatorKO7.Meta.RDRSAlgebraicInterpretationAtlas

/-!
# RDRS Tuple-Interpretation Boundary (compatibility shim)

Archimedean-algebra and tuple-boundary row: the tuple-interpretation
strict-s conditional-barrier row.

This module exists as a stable import path for the historical file name.
The two tuple-interpretation rows landed inside the algebraic-interpretation
atlas:

  `tupleInterpretationStrictS`     conditional_barrier  TupleStrictSHyp
  `higherOrderTupleInterpretation` conditional_barrier  HOTupleStrictSHyp

Both rows are conditional under named hypothesis carriers. The shim re-exports the algebraic-interpretation
atlas so downstream code that wrote
`import OperatorKO7.Meta.RDRSTupleInterpretationBoundary` resolves.

No `sorry`, `axiom`, `native_decide`, `@[csimp]`, `unsafe`, `partial`, or
`opaque` is introduced.
-/

set_option autoImplicit false

namespace OperatorKO7.RDRSTupleInterpretationBoundary

def supersededBy : List String :=
  ["OperatorKO7.RDRSAlgebraicInterpretationAtlas"]

theorem rdrs_tuple_interpretation_boundary_shim_marker :
    supersededBy.length = 1 ∧ supersededBy.Nodup := by
  refine ⟨rfl, ?_⟩
  simp [supersededBy, List.Nodup]

end OperatorKO7.RDRSTupleInterpretationBoundary
