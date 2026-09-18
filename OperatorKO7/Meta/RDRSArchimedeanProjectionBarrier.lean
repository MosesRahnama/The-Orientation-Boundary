import OperatorKO7.Meta.RDRSAlgebraicInterpretationAtlas
import OperatorKO7.Meta.RDRSSemanticStructuralAtlas

/-!
# RDRS Archimedean-Projection Barrier (T4 shim)

Roadmap row: `Expansion/RDRS_Termination_Methods_Roadmap.md` milestone T4,
"Archimedean Algebra And Tuple Boundary" -- the polynomial / matrix / arctic /
tropical scalar-projection barrier package plus the strict-monotone-algebra
Archimedean barrier.

This module exists as a stable import path for the historical T4 file name.
The 11 algebraic-projection rows
(`linearPolyQ`, `linearPolyR`, `negativeCoefficientPolynomial`,
 `maxPolynomial`, `nonlinearHigherDegreePolynomial`, `multilinearInterpretation`,
 `matrixNScalarProjection`, `matrixQRScalarProjection`, `arcticScalarProjection`,
 `tropicalScalarProjection`, `triangularMatrix`)
landed inside the algebraic-interpretation atlas. The strict-monotone algebra
Archimedean barrier landed inside the semantic / structural atlas under the
`pumpSInfinity` mechanism.

Supersession map:

  polynomial / matrix / arctic / tropical scalar-projection barriers
                                        -> OperatorKO7.RDRSAlgebraicInterpretationAtlas
                                           (closure marker
                                            `rdrs_algebraic_interpretation_layer_closed`)
  strict-monotone algebra Archimedean barrier (pump-S infinity)
                                        -> OperatorKO7.RDRSSemanticStructuralAtlas
                                           (mechanism `pumpSInfinity`; closure
                                            marker
                                            `rdrs_semantic_structural_layer_closed`)

No `sorry`, `axiom`, `native_decide`, `@[csimp]`, `unsafe`, `partial`, or
`opaque` is introduced.
-/

set_option autoImplicit false

namespace OperatorKO7.RDRSArchimedeanProjectionBarrier

def supersededBy : List String :=
  ["OperatorKO7.RDRSAlgebraicInterpretationAtlas",
   "OperatorKO7.RDRSSemanticStructuralAtlas"]

theorem rdrs_archimedean_projection_barrier_shim_marker :
    supersededBy.length = 2 ∧ supersededBy.Nodup := by
  refine ⟨rfl, ?_⟩
  simp [supersededBy, List.Nodup]

end OperatorKO7.RDRSArchimedeanProjectionBarrier
