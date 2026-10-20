import OperatorKO7.Meta.CoRewritePairBoundary

/-!
# Reach tests for `Meta/CoRewritePairBoundary.lean`
-/

set_option autoImplicit false

namespace OperatorKO7.Test.CoRewritePairBoundaryReach

open OperatorKO7.CoRewritePairBoundary

#check co_rewrite_pair_note_is_nonconservative_escape
#check co_wpo_requires_out_of_scope_co_order
#check CoRewritePairBoundary
#check co_rewrite_pair_boundary_closed
#check audit_theory_expansion_co_rewrite_pair_boundary_module_anchor

#print axioms co_rewrite_pair_boundary_closed

example :
    OperatorKO7.RDRSNotesReconciliationAddendum.notesStatus
      .coRewritePairCoWPO = .nonconservative_escape :=
  co_rewrite_pair_note_is_nonconservative_escape

end OperatorKO7.Test.CoRewritePairBoundaryReach
