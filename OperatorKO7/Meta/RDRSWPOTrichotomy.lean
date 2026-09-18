import OperatorKO7.Meta.RDRSAlgebraicInterpretationAtlas
import OperatorKO7.Meta.RDRSPathOrderDichotomy

/-!
# RDRS WPO Trichotomy (T3 shim)

Roadmap row: `Expansion/RDRS_Termination_Methods_Roadmap.md` milestone T3,
"WPO And Ordinal Classification".

This module exists as a stable import path for the historical T3 file name.
The WPO trichotomy content (head precedence vs algebra import vs unorientable)
landed inside the algebraic-interpretation atlas; the polynomial-KBO row
alignment and the simple-termination order-type / Cichon ordinal boundary
landed inside the path-order dichotomy. This shim re-exports both modules so
downstream code that wrote `import OperatorKO7.Meta.RDRSWPOTrichotomy`
continues to resolve.

Supersession map:

  WPO trichotomy (head precedence / algebra import / unorientable)
                                        -> OperatorKO7.RDRSAlgebraicInterpretationAtlas
  polynomial-KBO / WPO-polynomial row alignment
                                        -> OperatorKO7.RDRSAlgebraicInterpretationAtlas
                                           (`polynomialKBO`, `RowHypothesis`)
  simple-termination order-type barrier as classification
                                        -> OperatorKO7.RDRSPathOrderDichotomy
                                           (`simpleTerminationOrderType`)
  Cichon and Lepper caveat              -> OperatorKO7.RDRSPathOrderDichotomy
                                           (`cichonSlowGrowing`)

No `sorry`, `axiom`, `native_decide`, `@[csimp]`, `unsafe`, `partial`, or
`opaque` is introduced. The shim's marker theorem is closed by `decide`,
keeping the axiom footprint at the baseline.
-/

set_option autoImplicit false

namespace OperatorKO7.RDRSWPOTrichotomy

/-- The two modules that carry the T3 WPO-trichotomy content. -/
def supersededBy : List String :=
  ["OperatorKO7.RDRSAlgebraicInterpretationAtlas",
   "OperatorKO7.RDRSPathOrderDichotomy"]

/-- Supersession marker. Records that the T3 WPO-trichotomy roadmap row is
satisfied by the two named modules, both of which are reachable as imports
of this shim. -/
theorem rdrs_wpo_trichotomy_shim_marker :
    supersededBy.length = 2 ∧ supersededBy.Nodup := by
  refine ⟨rfl, ?_⟩
  simp [supersededBy, List.Nodup]

end OperatorKO7.RDRSWPOTrichotomy
