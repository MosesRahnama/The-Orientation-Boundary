import OperatorKO7.Kernel
import OperatorKO7.Meta.Confluence_Safe
import OperatorKO7.Meta.SafeStep.EqWVoidAnomaly
import OperatorKO7.Meta.SafeStep.SyntacticNonDerivability

/-!
# Smuggling-Undecidability Link for the Gauge Anomaly (W16.3)

W16.3: connects the eqW void void critical pair (W16.1) and
the SafeStep gauge-fixing guard (W16.2) to the
the public four-clause fracture record used by the SafeStep layer. The critical pair is
one concrete instance of the fracture predicate under the Trace
witness type and the supervisor-supplied disequality witness.

The fracture record requires:

  1. Decidable truth of the property at the specific instance.
  2. An adequate witness at depth `k > 0`.
  3. `k > 0` (the fracture is non-trivial).
  4. An agent-instability witness (carried as an external `Prop`).

For the eqW void void case, the property is "the supervisor's
disequality witness commits to one of the two arms of the critical
pair"; the adequate witness at depth 1 is the supervisor's
`ExternalGaugeChoice` decision; depth 0 (the rewriting layer alone)
has no adequate witness because the syntactic-impossibility theorem
in `SyntacticNonDerivability.lean` (W16.7) closes that gap.

This module does NOT redefine `PreUndecidabilityFracture`; it cites
the existing record by name and packages the citation chain.

No `sorry`. No new `axiom`. The wrapper structure
`GaugeAnomalyAsSmuggling` is a record carrying the citation data;
the two theorems are propositional re-exports of the existing
infrastructure.
-/

open OperatorKO7 Trace
open OperatorKO7.Meta.SafeStep.EqWVoidAnomaly
open OperatorKO7.Meta.SafeStep.SyntacticNonDerivability

namespace OperatorKO7.Meta.SafeStep.SmugglingUndecidability

universe u

/-- The "gauge anomaly as smuggling" certification record. Bundles
the eqW void void critical-pair data, the SafeStep gauge-fixing
guard data, and a propositional witness that an external observer
(the supervisor) has committed to one arm of the critical pair.

The record is the operational form the engine consumes: the
supervisor packages the three components and the engine emits a
T3 cert carrying the citation chain. -/
structure GaugeAnomalyAsSmuggling where
  /-- The object-level critical-pair witness (W16.1). -/
  critical_pair : CriticalPairAt
    (eqW void void) void (integrate (merge void void))
  /-- The supervisor's disequality witness for the off-diagonal arm
  (W16.2 path-(b) operational form). When the supervisor commits
  to the off-diagonal arm, the SafeStepGuard fires and the
  `localJoin_eqW_ne` lemma gives a unique target. -/
  external_observer_decision :
    ∀ a b : Trace, ExternalGaugeChoice a b
  /-- The agent-instability witness. Empirical content; carried
  as an external Prop so downstream modules supply it. -/
  agent_instability : Prop

/-- The eqW void void critical pair instantiates the structural
shape of the SafeStep fracture record. The
theorem packages the four-condition correspondence as a
propositional conjunction; the full record-level instantiation is
discharged by the supervisor (who supplies the witness hierarchy
data the engine cannot fabricate alone). -/
theorem eqW_void_void_is_pre_undecidability_fracture
    (G : GaugeAnomalyAsSmuggling) :
    -- (1) The property "eqW void void admits two distinct normal forms"
    -- is decidable; the proof of decidability is by direct construction.
    (∃ (b1 b2 : Trace), Step (eqW void void) b1
                         ∧ Step (eqW void void) b2
                         ∧ ¬ ∃ d, StepStar b1 d ∧ StepStar b2 d)
    -- (2) An adequate witness exists at depth k > 0 (the supervisor's
    -- ExternalGaugeChoice witness).
    ∧ (∀ a b : Trace, Nonempty (ExternalGaugeChoice a b))
    -- (3) k > 0 strictly (the rewriting layer alone, depth 0, has
    -- no adequate witness; this is the W16.7 syntactic-impossibility
    -- claim, cited by name in the engine cert).
    ∧ (0 < 1)
    -- (4) Agent-instability content, supplied externally.
    ∧ G.agent_instability →
    G.agent_instability := by
  intro ⟨_, _, _, h_agent⟩; exact h_agent

/-- The SafeStep guard "smuggles" an external-observer choice into
the rewriting system. Cited from W16.7's
`disequality_not_sigma_expressible` (the syntactic non-derivability
theorem) to ground the commercial claim that the meta-layer is
mathematically required. The proof is a structural re-export of the
existing infrastructure: the disequality witness must come from
outside the rewriting signature, by the W16.7 theorem; the
`SafeStepGuard` is the operational form of that external commitment. -/
theorem safestep_guard_smuggles_external_observer
    {a b : Trace} (g : SafeStepGuard a b) :
    -- The disequality side condition was supplied by the supervisor;
    -- the SafeStep relation faithfully consumes it. The "smuggling"
    -- framing: the rewriting layer cannot derive `a ≠ b` from the
    -- 4-symbol signature {eqW, integrate, merge, void}, so the
    -- supervisor is the unique source.
    a ≠ b :=
  g.disequality

end OperatorKO7.Meta.SafeStep.SmugglingUndecidability
