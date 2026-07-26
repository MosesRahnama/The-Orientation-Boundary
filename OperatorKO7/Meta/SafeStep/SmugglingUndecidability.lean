import OperatorKO7.Kernel
import OperatorKO7.Meta.Confluence_Safe
import OperatorKO7.Meta.RepShift_BottleneckPredicate
import OperatorKO7.Meta.SafeStep.EqWVoidAnomaly
import OperatorKO7.Meta.SafeStep.GaugeFixingGuard

/-!
# Critical-pair and guard projections

`GaugeAnomalyAsSmuggling` stores a critical-pair proof, a family of `ExternalGaugeChoice` values, and
an arbitrary proposition named `agent_instability`. The first theorem returns a three-part
conjunction: existence of the imported unjoinable fork, nonemptiness of each external-choice type,
and `0 < 1`. It does not construct `PreUndecidabilityFracture`, does not use the stored
`critical_pair`, does not use `agent_instability`, and does not prove absence of a depth-zero witness.
The second theorem projects the disequality already stored in `SafeStepGuard`; it does not prove the
origin or uniqueness of that evidence.
-/

open OperatorKO7 Trace
open OperatorKO7.Meta.SafeStep.EqWVoidAnomaly
open OperatorKO7.Meta.SafeStep.GaugeFixingGuard

namespace OperatorKO7.Meta.SafeStep.SmugglingUndecidability

universe u

/-- Package containing the displayed critical-pair proof, external-choice function, and an arbitrary
proposition. -/
structure GaugeAnomalyAsSmuggling where
  /-- A proof of the displayed critical pair. -/
  critical_pair : CriticalPairAt
    (eqW void void) void (integrate (merge void void))
  /-- One `ExternalGaugeChoice a b` for every pair of traces. -/
  external_observer_decision :
    ∀ a b : Trace, ExternalGaugeChoice a b
  /-- An arbitrary proposition; no inhabitant is required by the structure. -/
  agent_instability : Prop

/-- Combine the imported unjoinable fork, nonemptiness induced by
`G.external_observer_decision`, and `Nat.zero_lt_one`. Despite its historical name, the conclusion is
not a `PreUndecidabilityFracture` value. -/
theorem eqW_void_void_is_pre_undecidability_fracture
    (G : GaugeAnomalyAsSmuggling) :
    -- The imported overlap has two unjoinable reducts.
    (∃ (b1 b2 : Trace), Step (eqW void void) b1
                         ∧ Step (eqW void void) b2
                         ∧ ¬ ∃ d, StepStar b1 d ∧ StepStar b2 d)
    -- Each external-choice type is nonempty because `G` supplies a value.
    ∧ (∀ a b : Trace, Nonempty (ExternalGaugeChoice a b))
    -- The numeral one is positive.
    ∧ (0 < 1) := by
  refine ⟨⟨void, integrate (merge void void), ?_, ?_, ?_⟩, ?_, ?_⟩
  · exact eqW_void_void_admits_two_normal_forms.1
  · exact eqW_void_void_admits_two_normal_forms.2
  · exact eqW_void_void_normal_forms_are_unjoinable
  · exact fun a b => ⟨G.external_observer_decision a b⟩
  · exact Nat.zero_lt_one

/-- Project the disequality field of a `SafeStepGuard`. -/
theorem safestep_guard_smuggles_external_observer
    {a b : Trace} (g : SafeStepGuard a b) :
    -- The conclusion is exactly the stored field.
    a ≠ b :=
  g.disequality

#print axioms eqW_void_void_is_pre_undecidability_fracture
#print axioms safestep_guard_smuggles_external_observer

end OperatorKO7.Meta.SafeStep.SmugglingUndecidability
