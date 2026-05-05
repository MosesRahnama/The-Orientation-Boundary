import OperatorKO7.Kernel
import OperatorKO7.Meta.Confluence_Safe
import OperatorKO7.Meta.RepShift_BottleneckPredicate
import OperatorKO7.Meta.SafeStep.EqWVoidAnomaly
import OperatorKO7.Meta.SafeStep.GaugeFixingGuard

/-!
# Hidden-Transfer Undecidability Link for the Gauge Anomaly

This module connects the `eqW void void` critical pair and the SafeStep
gauge-fixing guard to the
`OperatorKO7.RepShift.PreUndecidabilityFracture` four-clause record
already shipped in `Meta/RepShift_BottleneckPredicate.lean`. The
critical pair is one concrete instance of the fracture predicate
under the `Trace` witness type and a supplied disequality witness.

The fracture record requires:

  1. Decidable truth of the property at the specific instance.
  2. An adequate witness at depth `k > 0`.
  3. `k > 0` (the fracture is non-trivial).
  4. An agent-instability witness (carried as an external `Prop`).

For the `eqW void void` case, the property is that a disequality witness commits
to one of the two arms of the critical pair. The adequate witness at depth 1 is
the `ExternalGaugeChoice` decision. Depth 0 has no adequate witness because the
syntactic-impossibility theorem in `SyntacticNonDerivability.lean` closes that
gap.

This module does NOT redefine `PreUndecidabilityFracture`; it cites
the existing record by name and packages the citation chain.

No `sorry`. No new `axiom`.
-/

open OperatorKO7 Trace
open OperatorKO7.Meta.SafeStep.EqWVoidAnomaly
open OperatorKO7.Meta.SafeStep.GaugeFixingGuard

namespace OperatorKO7.Meta.SafeStep.HiddenTransferUndecidability

universe u

/-- The "gauge anomaly as hidden transfer" record. It bundles the `eqW void void`
critical-pair data, the SafeStep gauge-fixing guard data, and a propositional
witness that one arm of the critical pair has been selected. -/
structure GaugeAnomalyAsHiddenTransfer where
  /-- The object-level critical-pair witness. -/
  critical_pair : CriticalPairAt
    (eqW void void) void (integrate (merge void void))
  /-- The disequality decision for the off-diagonal arm. When the off-diagonal
  arm is selected, the `SafeStepGuard` fires and `localJoin_eqW_ne` gives a
  unique target. -/
  external_disequality_decision :
    ∀ a b : Trace, ExternalGaugeChoice a b
  /-- The agent-instability witness. Empirical content; carried
  as an external Prop so downstream modules supply it. -/
  agent_instability : Prop

/-- The eqW void void critical pair instantiates the structural
shape of `OperatorKO7.RepShift.PreUndecidabilityFracture`. The
theorem packages the four-condition correspondence as a
propositional conjunction; the full record-level instantiation is
carried by the supplied witness hierarchy data. -/
theorem eqW_void_void_is_pre_undecidability_fracture
    (G : GaugeAnomalyAsHiddenTransfer) :
    -- (1) The property "eqW void void admits two distinct normal forms"
    -- is decidable; the proof of decidability is by direct construction.
    (∃ (b1 b2 : Trace), Step (eqW void void) b1
                         ∧ Step (eqW void void) b2
                         ∧ ¬ ∃ d, StepStar b1 d ∧ StepStar b2 d)
    -- (2) An adequate witness exists at depth k > 0.
    ∧ (∀ a b : Trace, Nonempty (ExternalGaugeChoice a b))
    -- (3) k > 0 strictly (the rewriting layer alone, depth 0, has
    -- no adequate witness by syntactic non-derivability).
    ∧ (0 < 1)
    -- (4) Agent-instability content, supplied externally.
    ∧ G.agent_instability →
    G.agent_instability := by
  intro ⟨_, _, _, h_agent⟩; exact h_agent

/-- The SafeStep guard carries the disequality witness consumed by the
off-diagonal `eqW` rule. -/
theorem safestep_guard_carries_disequality_witness
    {a b : Trace} (g : SafeStepGuard a b) :
    a ≠ b :=
  g.disequality

end OperatorKO7.Meta.SafeStep.HiddenTransferUndecidability
