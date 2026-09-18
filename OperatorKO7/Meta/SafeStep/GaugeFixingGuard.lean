import OperatorKO7.Kernel
import OperatorKO7.Meta.SafeStep_Core
import OperatorKO7.Meta.Confluence_Safe

universe u v

/-!
This module packages an off-diagonal disequality and re-exports the corresponding local-join
theorem. ExternalGaugeChoice stores a caller-supplied equality-or-disequality disjunction. Full
local confluence and runtime provenance require separate declarations.































-/

open OperatorKO7 Trace
open MetaSN_KO7

namespace OperatorKO7.Meta.SafeStep.GaugeFixingGuard

/-- Data record whose requirements are the fields displayed below.

-/
structure SafeStepGuard (a b : Trace) : Prop where
  disequality : a ≠ b

/-- Abbreviation for the displayed type.
-/
abbrev DistinctionLicense (a b : Trace) : Prop := a ≠ b

/-- The displayed proposition follows from the stated hypotheses. -/
theorem distinctionLicense_to_disequality {a b : Trace}
    (h : DistinctionLicense a b) : a ≠ b := h

/-- The displayed proposition follows from the stated hypotheses. -/
theorem distinctionLicense_diagonal_empty (a : Trace) :
    ¬ DistinctionLicense a a := fun h => h rfl

/-- The displayed proposition follows from the stated hypotheses. -/
theorem safeStepGuard_to_distinctionLicense {a b : Trace}
    (g : SafeStepGuard a b) : DistinctionLicense a b := g.disequality

/-- The displayed proposition follows from the stated hypotheses. -/
theorem distinctionLicense_to_safeStepGuard {a b : Trace}
    (h : DistinctionLicense a b) : SafeStepGuard a b := ⟨h⟩

/-- Data record whose requirements are the fields displayed below.








-/
structure ExternalGaugeChoice (a b : Trace) where
  decide : a ≠ b ∨ a = b

/-- The displayed proposition follows from the stated hypotheses.




-/
theorem safestep_guard_restores_local_confluence
    {a b : Trace} (g : SafeStepGuard a b) :
    LocalJoinSafe (eqW a b) :=
  localJoin_eqW_ne a b g.disequality

--
--
--

#print axioms distinctionLicense_diagonal_empty
#print axioms safeStepGuard_to_distinctionLicense
#print axioms distinctionLicense_to_safeStepGuard

end OperatorKO7.Meta.SafeStep.GaugeFixingGuard
