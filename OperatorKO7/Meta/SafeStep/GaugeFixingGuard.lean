import OperatorKO7.Kernel
import OperatorKO7.Meta.SafeStep_Core
import OperatorKO7.Meta.Confluence_Safe

universe u v

/-!
# Meta-level Gauge-Fixing Guard for SafeStep (W16.2)

W16.2: the meta-level operational structure that "fixes the
gauge" at the eqW critical pair documented in `EqWVoidAnomaly.lean`.

The full kernel `Step` relation is not locally confluent at
`eqW void void` because the two rules `R_eq_refl` and `R_eq_diff`
overlap. `SafeStep` (already shipped in
`OperatorKO7/Meta/SafeStep_Core.lean`) attaches an explicit side
condition to each of the two `eqW` rules:

  * `SafeStep.R_eq_refl a (h0 : kappaM a = 0)` only fires at the
    diagonal AND only when the DM payload is zero.
  * `SafeStep.R_eq_diff a b (hne : a ≠ b)` only fires off-diagonal.

The two side conditions are mutually exclusive, so the eqW root
critical pair never re-emerges under SafeStep. The
`SafeStepGuard` record below packages the disequality side
condition under a name auditors can cite. The
`ExternalGaugeChoice` structure is the path-(b) structural twin
to the path-(a) syntactic-impossibility theorem of
`SyntacticNonDerivability.lean` (W16.7): the engine consumes a
runtime witness that decides which arm of the `eqW a a` vs `eqW a b`
disjunction to take.

The engine-facing meta-halt bridge `safestep_is_meta_halt` (re-exporting
`TypedRefusalCompleteness_engine_grade`) lives in the companion reviewer-NDA
module `GaugeFixingGuardMetaHalt.lean`, kept separate so this guard-core module
carries no boundary-operator / meta-halt dependency and stays publicly
self-contained.

No `sorry`. No new `axiom`. The only new structure is
`ExternalGaugeChoice`, which is a record (Prop / Type), not an
`axiom` declaration.
-/

open OperatorKO7 Trace
open MetaSN_KO7

namespace OperatorKO7.Meta.SafeStep.GaugeFixingGuard

/-- The SafeStep gauge-fixing guard at the eqW critical pair.
Records the disequality side condition that excludes the
`R_eq_refl` rule and forces `R_eq_diff` as the unique arm. -/
structure SafeStepGuard (a b : Trace) : Prop where
  disequality : a ≠ b

/-- A paper-facing name for the off-diagonal distinction license imported by
SafeStep. It is definitionally just the disequality proof object. -/
abbrev DistinctionLicense (a b : Trace) : Prop := a ≠ b

/-- A distinction license exposes the disequality it carries. -/
theorem distinctionLicense_to_disequality {a b : Trace}
    (h : DistinctionLicense a b) : a ≠ b := h

/-- The distinction license is uninhabited on the diagonal. -/
theorem distinctionLicense_diagonal_empty (a : Trace) :
    ¬ DistinctionLicense a a := fun h => h rfl

/-- The existing SafeStep guard is a distinction license. -/
theorem safeStepGuard_to_distinctionLicense {a b : Trace}
    (g : SafeStepGuard a b) : DistinctionLicense a b := g.disequality

/-- Conversely, a distinction license packages as the SafeStep guard. -/
theorem distinctionLicense_to_safeStepGuard {a b : Trace}
    (h : DistinctionLicense a b) : SafeStepGuard a b := ⟨h⟩

/-- The path-(b) structural twin to the
`disequality_not_sigma_expressible` theorem of
`SyntacticNonDerivability.lean` (W16.7). At runtime the engine
consumes an external observer's decision that supplies the
disequality witness. The supervisor is the source of truth; the
rewriting layer below is faithful to whatever decision the
supervisor commits.

This is a record, not an `axiom`: the carrier is constructed by
the supervisor at every fracture call. -/
structure ExternalGaugeChoice (a b : Trace) where
  decide : a ≠ b ∨ a = b

/-- The SafeStep guard restores local confluence at the eqW root
peak. Verbatim re-export of `MetaSN_KO7.localJoin_eqW_ne` under the
W16.2 wire name. The engine cites both names; supervisors auditing
the engine see the citation chain
`SafeStepGuard -> safestep_guard_restores_local_confluence ->
MetaSN_KO7.localJoin_eqW_ne` and can verify each link. -/
theorem safestep_guard_restores_local_confluence
    {a b : Trace} (g : SafeStepGuard a b) :
    LocalJoinSafe (eqW a b) :=
  localJoin_eqW_ne a b g.disequality

-- `safestep_is_meta_halt` (the engine-coupled meta-halt bridge) now lives in the
-- companion reviewer-NDA module `GaugeFixingGuardMetaHalt.lean`, so this guard-core
-- module imports no boundary-operator / meta-halt surface and is publicly self-contained.

#print axioms distinctionLicense_diagonal_empty
#print axioms safeStepGuard_to_distinctionLicense
#print axioms distinctionLicense_to_safeStepGuard

end OperatorKO7.Meta.SafeStep.GaugeFixingGuard
