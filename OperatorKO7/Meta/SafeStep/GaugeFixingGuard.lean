import OperatorKO7.Kernel
import OperatorKO7.Meta.SafeStep_Core
import OperatorKO7.Meta.Confluence_Safe
import OperatorKO7.Meta.BoundaryOperator.TypedRefusalCompleteness

/-!
# Meta-Level Gauge-Fixing Guard for SafeStep

This module records the operational structure that fixes the gauge at the
`eqW` critical pair documented in `EqWVoidAnomaly.lean`.

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
condition. The `ExternalGaugeChoice` structure packages a decision of which arm
of the `eqW a a` vs. `eqW a b` disjunction applies.

This module is the SafeStep-side bridge to
`OperatorKO7.Meta.BoundaryOperator.TypedRefusalCompleteness`: the
meta-halt theorem used by the typed-refusal partition. The bridge lemma
`safestep_is_meta_halt` re-exports the upstream theorem at the SafeStep
namespace level.

No `sorry`. No new `axiom`. The only new structure is
`ExternalGaugeChoice`, which is a record (Prop / Type), not an
`axiom` declaration.
-/

open OperatorKO7 Trace
open MetaSN_KO7
open OperatorKO7.Meta.BoundaryOperator

namespace OperatorKO7.Meta.SafeStep.GaugeFixingGuard

/-- The SafeStep gauge-fixing guard at the eqW critical pair.
Records the disequality side condition that excludes the
`R_eq_refl` rule and forces `R_eq_diff` as the unique arm. -/
structure SafeStepGuard (a b : Trace) : Prop where
  disequality : a ≠ b

/-- A packaged decision of whether the diagonal or off-diagonal `eqW` arm
applies. This is a record, not an `axiom`. -/
structure ExternalGaugeChoice (a b : Trace) where
  decide : a ≠ b ∨ a = b

/-- The SafeStep guard restores local confluence at the off-diagonal `eqW` root
peak. This re-exports `MetaSN_KO7.localJoin_eqW_ne` under a SafeStep-local
name. -/
theorem safestep_guard_restores_local_confluence
    {a b : Trace} (g : SafeStepGuard a b) :
    LocalJoinSafe (eqW a b) :=
  localJoin_eqW_ne a b g.disequality

/-- The SafeStep relation inherits the boundary-operator typed-refusal meta-halt
theorem. Given a boundary-operator carrier and a classification, the
typed-refusal completeness theorem is inherited verbatim. -/
theorem safestep_is_meta_halt
    {X : Type u} {Y : Type v}
    (B : BoundaryOperator X Y)
    (C : TypedRefusalClassification Y) :
    (∃ (Y_typed : Set Y) (refusal_classification : Y → RefusalType),
        Y_typed = Set.univ ∧
        ∀ y, refusal_classification y ∈ refusalTypeSupport)
    ∧
    (∀ y : Y, C.classify y = RefusalType.Y
              ∨ C.classify y = RefusalType.N
              ∨ C.classify y = RefusalType.U
              ∨ C.classify y = RefusalType.H) :=
  TypedRefusalCompleteness_procedure_grade B C

end OperatorKO7.Meta.SafeStep.GaugeFixingGuard
