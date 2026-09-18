import OperatorKO7.Meta.RDRSDirectBarrierScope

/-!
# Reach test for `OperatorKO7.Meta.RDRSDirectBarrierScope`

Forces elaboration of every public declaration of the theory-expansion
direct-barrier-scope module.
-/

set_option autoImplicit false

namespace OperatorKO7.RDRSDirectBarrierScopeReach

open OperatorKO7.RDRSDirectBarrierScope

-- types
#check (DirectBarrierFamily)
#check (DirectBarrierEscapeReason)
#check (RDRSDirectMethod)
#check (DirectBarrierScopeClass)

-- defs / classifiers
#check (directBarrierGrammarFamilies)
#check @barrierFamilyOf
#check @escapeReasonOf
#check @directBarrierScope
#check @escapeScopeWitness?
#check (audit_theory_expansion_direct_barrier_scope_module_anchor)

-- theorems
#check @directBarrierGrammarFamilies_card
#check @rdrs_direct_barrier_scope_unconditional
#check @rdrs_direct_barrier_scope_escape_total
#check @rdrs_scope_violation_escapes_not_in_scope
#check @rdrs_direct_barrier_scope_inside_nonvacuous
#check @rdrs_direct_barrier_scope_escape_nonvacuous

end OperatorKO7.RDRSDirectBarrierScopeReach
