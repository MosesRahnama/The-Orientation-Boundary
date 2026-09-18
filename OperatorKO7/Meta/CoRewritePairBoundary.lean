import OperatorKO7.Meta.RDRSNotesReconciliationAddendum
import OperatorKO7.Meta.DirectBarrierScope
import OperatorKO7.Meta.GeneralizedWPOCompatibility

/-!
# Co-Rewrite Pair Boundary

This module closes the co-rewrite / co-WPO note honestly.

It does not prove a new barrier theorem. It packages the already-landed scope
facts showing that these methods do not supply a loophole in the direct
orientation theorem:

- the residual notes row `coRewritePairCoWPO` is classified as a
  `nonconservative_escape`, and
- the co-order route needed by co-WPO is already theorem-backed as outside the
  direct barrier scope.

So the correct classification is scope escape, not direct-lane counterexample.
-/

set_option autoImplicit false

namespace OperatorKO7.CoRewritePairBoundary

open OperatorKO7.RDRSNotesReconciliationAddendum
open OperatorKO7.StepDuplicating
open OperatorKO7.GeneralizedWPOCompatibility

/-- The notes addendum already records the co-rewrite / co-WPO row as a
nonconservative escape. -/
theorem co_rewrite_pair_note_is_nonconservative_escape :
    notesStatus .coRewritePairCoWPO = .nonconservative_escape := by
  rfl

/-- The co-WPO route requires the co-order sentinel, which is out of the direct
barrier scope. -/
theorem co_wpo_requires_out_of_scope_co_order :
    ¬ InScope coOrderScope :=
  coOrderScope_not_InScope

/-- Packed boundary certificate for the co-rewrite / co-WPO note. -/
structure CoRewritePairBoundary : Prop where
  coRewritePairStatus :
    notesStatus .coRewritePairCoWPO = .nonconservative_escape
  coOrderOutOfScope :
    ¬ InScope coOrderScope
  generalizedWPOCompatibleOnlyOutsideLane :
    GeneralizedWPOCompatibility

/-- Final boundary theorem: co-rewrite pairs and co-WPO enter the current tree
only as scope escapes, not as loopholes in the direct barrier. -/
theorem co_rewrite_pair_boundary_closed :
    CoRewritePairBoundary where
  coRewritePairStatus := co_rewrite_pair_note_is_nonconservative_escape
  coOrderOutOfScope := co_wpo_requires_out_of_scope_co_order
  generalizedWPOCompatibleOnlyOutsideLane := generalized_wpo_compatibility_exact

/-- Stable audit anchor for the co-rewrite / co-WPO boundary module. -/
def audit_theory_expansion_co_rewrite_pair_boundary_module_anchor : String :=
  "OperatorKO7.CoRewritePairBoundary.co_rewrite_pair_boundary_closed"

end OperatorKO7.CoRewritePairBoundary
