import OperatorKO7.Meta.EqW_Guard_Barrier
import OperatorKO7.Meta.SafeStep.GaugeFixingGuard

set_option autoImplicit false

/-!
# Guard necessity at the `eqW` diagonal (WAVE2-D)

This file pairs a HARD no-go with its constructive repair, both for the `eqW`
critical pair of the KO7 kernel.

The two kernel rules that overlap at the diagonal are

  * `Step.R_eq_refl a : Step (eqW a a) void`
    -- the *reflexive verdict*: a self-comparison collapses to `void`.
  * `Step.R_eq_diff a b : Step (eqW a b) (integrate (merge a b))`
    -- the *non-null difference verdict*; **instantiated at the diagonal** `b := a`
       it also fires from `eqW a a`, producing `integrate (merge a a)`.

Both reducts are full-kernel normal forms and are distinct, so the diagonal
source `eqW a a` has two incompatible verdicts that never re-join. Keeping
`R_eq_refl` together with the *diagonal firing* of `R_eq_diff` is therefore
incompatible with local confluence at the diagonal. This is the no-go.

The repair is the `SafeStep` `a ≠ b` guard, which suppresses exactly the
diagonal diff branch (`R_eq_diff` cannot fire when `a = b`) and restores local
confluence. The discharged witness is re-exported from
`OperatorKO7.Meta.SafeStep.GaugeFixingGuard.safestep_guard_restores_local_confluence`.

No `sorry`, `admit`, `axiom`, `native_decide`, `@[csimp]`, `unsafe`, `partial`,
or `opaque`. The `RepairRoute` enumeration below only *organizes* the statement;
the `guard` route is the ONLY route claimed proven (it is discharged here). No
inhabitant, witness, or proof is asserted for `delete`, `inert`, `structuralize`,
or `quotient`.

Relation: Step (full unguarded kernel) for the no-go; SafeStep for the repair.
Closure:  root critical pair at the diagonal `eqW a a`.
Strategy: full (unguarded) for the no-go; guarded (`a ≠ b`) for the repair.
Trust:    kernel-only; subset of {propext, Classical.choice, Quot.sound}.
-/

open OperatorKO7 Trace
open MetaSN_KO7

namespace OperatorKO7.Meta.SafeStep.GuardNecessity

/-! ## 1. The diagonal emits both verdicts (full kernel `Step`) -/

/-- The reflexive verdict fires at the diagonal: `eqW a a ⇒ void`
(`Step.R_eq_refl`). -/
theorem diagonal_emits_refl_verdict (a : Trace) :
    Step (eqW a a) void :=
  Step.R_eq_refl a

/-- The non-null difference verdict, **instantiated at the diagonal**
`b := a`, also fires: `eqW a a ⇒ integrate (merge a a)` (`Step.R_eq_diff a a`).
This is the diagonal firing of `R_eq_diff` that the SafeStep `a ≠ b` guard
later suppresses. -/
theorem diagonal_emits_diff_verdict (a : Trace) :
    Step (eqW a a) (integrate (merge a a)) :=
  Step.R_eq_diff a a

/-! ## 2. The HARD no-go -/

/-- **No-go (HARD).** For the full kernel relation `Step`, keeping the reflexive
verdict `R_eq_refl` together with the diagonal firing of `R_eq_diff` is
incompatible with local confluence at the diagonal: for every `a`, the source
`eqW a a` is not locally joinable.

The two verdicts `Step.R_eq_refl a` and `Step.R_eq_diff a a` reduce `eqW a a`
to the two distinct normal forms `void` and `integrate (merge a a)`, which can
never re-join, so `LocalJoinStep (eqW a a)` is impossible.

Reuses `OperatorKO7.Meta.EqW_Guard_Barrier.not_localJoinStep_eqW_refl`.

Relation: Step.  Closure: root.  Strategy: full (unguarded).
Property: local_confluence (refuted at the diagonal). -/
theorem diagonal_emission_incompatible_with_local_confluence (a : Trace) :
    ¬ MetaSN_KO7.LocalJoinStep (eqW a a) :=
  OperatorKO7.Meta.EqW_Guard_Barrier.not_localJoinStep_eqW_refl a

/-- Spelled-out form of the no-go that exhibits the two incompatible verdicts
explicitly: from a (hypothetical) local join at `eqW a a` together with the
reflexive verdict and the diagonal diff verdict, one derives `False`. This makes
the obstruction's mechanism visible at the call site; it is logically the same
content as `diagonal_emission_incompatible_with_local_confluence`. -/
theorem both_diagonal_verdicts_block_local_join (a : Trace)
    (hjoin : MetaSN_KO7.LocalJoinStep (eqW a a)) : False :=
  diagonal_emission_incompatible_with_local_confluence a hjoin

/-! ## 3. Repair-route organizer (only `guard` is claimed proven) -/

/-- An organizing enumeration of conceivable repair routes for the diagonal
critical pair. **Only the `guard` route is claimed proven in this file** (it is
discharged by `guard_route_discharged` below). No inhabitant, witness, or proof
is asserted for `delete`, `inert`, `structuralize`, or `quotient`; they are
listed solely to fix the vocabulary of the statement. -/
inductive RepairRoute
  | guard
  | delete
  | inert
  | structuralize
  | quotient
deriving DecidableEq, Repr

/-! ## 4. The discharged guard repair (`SafeStep` `a ≠ b` guard) -/

/-- **Repair (constructive).** The `SafeStep` gauge-fixing guard suppresses
exactly the diagonal diff branch: `SafeStepGuard a b` carries `a ≠ b`, under
which `R_eq_diff` cannot fire at the diagonal, and local confluence is restored
at `eqW a b`.

Verbatim re-export of
`OperatorKO7.Meta.SafeStep.GaugeFixingGuard.safestep_guard_restores_local_confluence`.

Relation: SafeStep.  Closure: root.  Strategy: guarded (`a ≠ b`).
Property: local_confluence (restored). -/
theorem guard_route_discharged {a b : Trace}
    (g : OperatorKO7.Meta.SafeStep.GaugeFixingGuard.SafeStepGuard a b) :
    MetaSN_KO7.LocalJoinSafe (eqW a b) :=
  OperatorKO7.Meta.SafeStep.GaugeFixingGuard.safestep_guard_restores_local_confluence g

/-- The `guard` route is the satisfier: there is a constructive map from the
SafeStep disequality guard to restored local confluence at `eqW a b`. This is
the only `RepairRoute` arm with a discharged witness. -/
theorem guard_is_the_satisfier :
    ∀ {a b : Trace},
      OperatorKO7.Meta.SafeStep.GaugeFixingGuard.SafeStepGuard a b →
      MetaSN_KO7.LocalJoinSafe (eqW a b) :=
  fun g => guard_route_discharged g

/-! ## 5. No-go and repair side by side (the WAVE2-D deliverable)

Off the diagonal (`a ≠ b`) the guard yields local confluence
(`guard_route_discharged`); on the diagonal (`a = a`) the unguarded relation is
provably non-joinable (`diagonal_emission_incompatible_with_local_confluence`).
The guard is exactly what removes the diagonal diff firing, and nothing weaker
is asserted. -/

#print axioms diagonal_emission_incompatible_with_local_confluence
#print axioms both_diagonal_verdicts_block_local_join
#print axioms guard_route_discharged
#print axioms guard_is_the_satisfier

end OperatorKO7.Meta.SafeStep.GuardNecessity
