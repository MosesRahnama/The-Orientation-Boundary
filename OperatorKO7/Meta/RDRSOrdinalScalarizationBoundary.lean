import OperatorKO7.Meta.RDRSPathOrderDichotomy
import OperatorKO7.Meta.RDRSAlgebraicInterpretationAtlas

/-!
# RDRS Ordinal-Scalarization Boundary (T3 shim)

Roadmap row: `Expansion/RDRS_Termination_Methods_Roadmap.md` milestone T3,
"WPO And Ordinal Classification" -- the Cichon/Lepper ordinal-non-universality
caveat and the simple-termination order-type barrier framed as a positive
classification (not impossibility).

This module exists as a stable import path for the historical T3 file name.
The Cichon slow-growing caveat and the simple-termination order-type row are
both rows of the path-order dichotomy atlas; the polynomial-KBO ordinal-lift
row is a row of the algebraic-interpretation atlas. This shim re-exports
both modules.

Supersession map:

  Cichon slow-growing caveat            -> OperatorKO7.RDRSPathOrderDichotomy
                                           (`cichonSlowGrowing`)
  simple-termination order-type barrier
                                        -> OperatorKO7.RDRSPathOrderDichotomy
                                           (`simpleTerminationOrderType`)
  polynomial-KBO / WPO ordinal lift     -> OperatorKO7.RDRSAlgebraicInterpretationAtlas
                                           (`polynomialKBO`, `PolynomialKBOHyp`)

No `sorry`, `axiom`, `native_decide`, `@[csimp]`, `unsafe`, `partial`, or
`opaque` is introduced.
-/

set_option autoImplicit false

namespace OperatorKO7.RDRSOrdinalScalarizationBoundary

def supersededBy : List String :=
  ["OperatorKO7.RDRSPathOrderDichotomy",
   "OperatorKO7.RDRSAlgebraicInterpretationAtlas"]

theorem rdrs_ordinal_scalarization_boundary_shim_marker :
    supersededBy.length = 2 ∧ supersededBy.Nodup := by
  refine ⟨rfl, ?_⟩
  simp [supersededBy, List.Nodup]

end OperatorKO7.RDRSOrdinalScalarizationBoundary
