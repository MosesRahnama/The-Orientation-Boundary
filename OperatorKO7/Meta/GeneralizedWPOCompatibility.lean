import OperatorKO7.Meta.RDRSWPOTrichotomy
import OperatorKO7.Meta.RDRSAlgebraicInterpretationAtlas
import OperatorKO7.Meta.RDRSNotesReconciliationAddendum
import OperatorKO7.Meta.DirectBarrierScope

/-!
# Generalized WPO Compatibility

This module packages the exact generalized-WPO compatibility statement already
justified by the live RDRS surface.

It does not formalize a new universal theorem about generalized WPO. The honest
compatibility split is narrower:

- the polynomial-KBO branch is already formalized inside the algebraic atlas as
  the conditional `polynomialKBO` row with named hypothesis carrier
  `PolynomialKBOHyp`, and
- the residual generalized-WPO note closes only by exiting the direct lane via
  the nonmonotone co-order sentinel.

This keeps later files from widening the scope of "WPO" or "gWPO" beyond the
already formalized algebraic-import branch.
-/

set_option autoImplicit false

namespace OperatorKO7.GeneralizedWPOCompatibility

open OperatorKO7.RDRSTerminationMethodUniverse
open OperatorKO7.RDRSAlgebraicInterpretationAtlas
open OperatorKO7.RDRSNotesReconciliationAddendum
open OperatorKO7.StepDuplicating

/-- The algebraic branch by which generalized-WPO language is allowed to enter
the RDRS story: the already-formalized `polynomialKBO` conditional row. -/
abbrev GeneralizedWPOAlgebraicBranch : Prop :=
  .polynomialKBO ∈ algebraicInterpretationRows ∧
  statusOf .polynomialKBO = .conditional_barrier ∧
  mechanismOf .polynomialKBO = .polynomialKBOLift ∧
  RowHypothesis .polynomialKBO = PolynomialKBOHyp

/-- Exact theorem-backed witness of the algebraic generalized-WPO branch. -/
theorem generalized_wpo_algebraic_branch :
    GeneralizedWPOAlgebraicBranch := by
  refine ⟨?_, rfl, rfl, rfl⟩
  simp [algebraicInterpretationRows]

/-- The residual generalized-WPO branch is closed only by leaving the direct
RDRS lane via the nonmonotone co-order sentinel. -/
abbrev GeneralizedWPOOutOfDirectLane : Prop := generalizedWPOBranchClosed

/-- Exact theorem-backed witness of the out-of-lane generalized-WPO branch. -/
theorem generalized_wpo_out_of_direct_lane :
    GeneralizedWPOOutOfDirectLane :=
  generalizedWPOBranchClosed_intro

/-- Packed compatibility certificate for the live generalized-WPO surface. -/
structure GeneralizedWPOCompatibility : Prop where
  /-- The historical T3 WPO shim resolves to the two live carrying modules. -/
  shimReachable :
    OperatorKO7.RDRSWPOTrichotomy.supersededBy.length = 2 ∧
      OperatorKO7.RDRSWPOTrichotomy.supersededBy.Nodup
  /-- The only live algebraic generalized-WPO branch is the existing
  `polynomialKBO` conditional row. -/
  algebraicBranch : GeneralizedWPOAlgebraicBranch
  /-- Any residual generalized-WPO branch closes only by leaving the direct
  lane. -/
  outOfDirectLane : GeneralizedWPOOutOfDirectLane
  /-- The co-order route is explicitly out of scope for the direct barrier. -/
  coOrderOutOfScope : ¬ InScope coOrderScope

/-- Exact compatibility statement for generalized-WPO references in the RDRS
tree: they are compatible only through the already-formalized algebraic branch,
or they sit outside the direct lane. -/
theorem generalized_wpo_compatibility_exact :
    GeneralizedWPOCompatibility where
  shimReachable := OperatorKO7.RDRSWPOTrichotomy.rdrs_wpo_trichotomy_shim_marker
  algebraicBranch := generalized_wpo_algebraic_branch
  outOfDirectLane := generalized_wpo_out_of_direct_lane
  coOrderOutOfScope := coOrderScope_not_InScope

/-- Stable audit anchor for the generalized-WPO compatibility module. -/
def audit_theory_expansion_generalized_wpo_compatibility_module_anchor : String :=
  "OperatorKO7.GeneralizedWPOCompatibility.generalized_wpo_compatibility_exact"

end OperatorKO7.GeneralizedWPOCompatibility
