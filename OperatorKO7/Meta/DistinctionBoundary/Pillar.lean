import OperatorKO7.Meta.DistinctionBoundary.CriticalPairCompleteness
import OperatorKO7.Meta.DistinctionBoundary.GlobalConfluence
import OperatorKO7.Meta.SafeStep.EqWVoidAnomaly
import OperatorKO7.Meta.SafeStep.DistinctionControls
import OperatorKO7.Meta.SafeStep.SyntacticNonDerivability
import OperatorKO7.Meta.EqW_Guard_Barrier
import OperatorKO7.Meta.Confluence_Safe
import OperatorKO7.Meta.Newman_Safe
import OperatorKO7.Meta.SafeStepCtx_Confluence

set_option autoImplicit false

/-!
# The Distinction (confluence) Pillar — front door

This is the importable front door for the **distinction axis** of the boundary
framework: the confluence leg, co-equal to the orientation (termination) stack's
front door `OperatorKO7.OrientationBoundaryAPI`.

Importing this one module makes the whole confluence-axis surface available:

* **Substrate (existing, re-exported, not re-proved).**
  - `Meta/SafeStep/EqWVoidAnomaly.lean` — the `eqW void void` critical pair as an
    object-level record (`local_confluence_fails_at_eqW_void_void`).
  - `Meta/SafeStep/DistinctionControls.lean` — the benign `merge void void` control
    and the surgical "guard removes exactly the diagonal" statements.
  - `Meta/SafeStep/SyntacticNonDerivability.lean` — disequality is not
    Σ-expressible / not substitution-invariant; the guard needs an external observer.
  - `Meta/EqW_Guard_Barrier.lean` — the unguarded `eqW a a` overlap is never locally
    joinable; the `eqW` guards are confluence-necessary.
  - `Meta/Confluence_Safe.lean`, `Meta/Newman_Safe.lean`,
    `Meta/SafeStepCtx_Confluence.lean` — the local-join enumeration, Newman engine,
    and global confluence of `SafeStep` and `SafeStepCtx`.

* **Depth (new in this pillar).**
  - `Meta/DistinctionBoundary/CriticalPairCompleteness.lean` — completeness:
    the `eqW` reflexive diagonal is the **unique** root confluence obstruction of the
    full kernel `Step` (`eqW_diagonal_is_the_unique_root_obstruction`).
  - `Meta/DistinctionBoundary/GlobalConfluence.lean` — global confluence of
    `SafeStep`/`SafeStepCtx` packaged with explicit Newman (SN + local confluence)
    provenance, bridged to the completeness result
    (`safeStep_confluent_and_obstruction_complete`).

This file is a pure aggregation front door (imports plus a stable alias surface). It
adds no new mathematics; every aliased theorem is proved in the module cited next to
it. The aliases give downstream code one namespace,
`OperatorKO7.Meta.DistinctionBoundary.Pillar`, to depend on, so renames inside the
substrate are absorbed here rather than rippling outward.

## What this pillar does NOT claim

* It does not claim confluence of the full unguarded kernel `Step` — that relation is
  provably not even locally confluent at the `eqW` diagonal. The confluence result is
  for the guarded `SafeStep`/`SafeStepCtx`.
* It does not add an exact-order-type or complexity theorem; those live on the
  orientation axis.
-/

open OperatorKO7 Trace

namespace OperatorKO7.Meta.DistinctionBoundary.Pillar

/-! ## Headline aliases — the confluence axis surface

Each alias re-exports a load-bearing theorem under a pillar-stable name. Relation and
property are stated per alias; trust is kernel-only throughout (subset of
`{propext, Classical.choice, Quot.sound}`). -/

/-- **Pillar headline 1 — completeness.** The `eqW` reflexive diagonal is the unique
root confluence obstruction of the full kernel `Step`:
`¬ LocalJoinStep a ↔ a = eqW c c`.

Relation: full kernel `Step` (closure `StepStar`). Property: `local_confluence`
characterization. Source:
`CriticalPairCompleteness.eqW_diagonal_is_the_unique_root_obstruction`. -/
theorem eqW_diagonal_is_the_unique_root_obstruction (a : Trace) :
    ¬ MetaSN_KO7.LocalJoinStep a ↔
      OperatorKO7.Meta.DistinctionBoundary.CriticalPairCompleteness.IsEqWDiagonal a :=
  OperatorKO7.Meta.DistinctionBoundary.CriticalPairCompleteness.eqW_diagonal_is_the_unique_root_obstruction a

/-- **Pillar headline 2 — the canonical witness.** `eqW void void` is non-joinable,
and every non-joinable root source is a reflexive `eqW`. The precise sense in which
`eqW void void` is *the* confluence obstruction of KO7.

Relation: full kernel `Step`. Property: `local_confluence`. Source:
`CriticalPairCompleteness.eqW_void_void_is_canonical_root_obstruction`. -/
theorem eqW_void_void_is_canonical_root_obstruction :
    ¬ MetaSN_KO7.LocalJoinStep (eqW void void)
      ∧ (∀ a, ¬ MetaSN_KO7.LocalJoinStep a →
          OperatorKO7.Meta.DistinctionBoundary.CriticalPairCompleteness.IsEqWDiagonal a) :=
  OperatorKO7.Meta.DistinctionBoundary.CriticalPairCompleteness.eqW_void_void_is_canonical_root_obstruction

/-- **Pillar headline 3 — global confluence.** Church–Rosser for `SafeStepStar`,
the packaged Newman conclusion (SN + local confluence everywhere).

Relation: `SafeStep` (closure `SafeStepStar`). Property: `confluence`. Source:
`GlobalConfluence.safeStep_globally_confluent`. -/
theorem safeStep_globally_confluent : MetaSN_KO7.ConfluentSafe :=
  OperatorKO7.Meta.DistinctionBoundary.GlobalConfluence.safeStep_globally_confluent

/-- **Pillar headline 4 — context-closed global confluence.** Church–Rosser for the
context closure `SafeStepCtxStar`.

Relation: `SafeStepCtx` (closure `SafeStepCtxStar`). Property: `confluence`. Source:
`GlobalConfluence.safeStepCtx_globally_confluent`. -/
theorem safeStepCtx_globally_confluent : MetaSN_KO7.ConfluentSafeCtx :=
  OperatorKO7.Meta.DistinctionBoundary.GlobalConfluence.safeStepCtx_globally_confluent

/-- **Pillar headline 5 — axis end to end.** Global confluence of `SafeStep` together
with the completeness characterization of the full-kernel obstruction set. The guarded
relation is confluent, and what had to be guarded away is a single characterized
critical pair (the `eqW` diagonal).

Relation: `SafeStep` (first conjunct) and full kernel `Step` (obstruction
characterization). Property: `confluence` + `local_confluence` completeness. Source:
`GlobalConfluence.safeStep_confluent_and_obstruction_complete`. -/
theorem safeStep_confluent_and_obstruction_complete :
    MetaSN_KO7.ConfluentSafe ∧
      (∀ a, ¬ MetaSN_KO7.LocalJoinStep a ↔
        OperatorKO7.Meta.DistinctionBoundary.CriticalPairCompleteness.IsEqWDiagonal a) :=
  OperatorKO7.Meta.DistinctionBoundary.GlobalConfluence.safeStep_confluent_and_obstruction_complete

/-- **Pillar headline 6 — guard necessity.** In the unguarded kernel relation, every
`eqW a a` overlap is non-joinable; the `SafeStep` `eqW` guards are confluence-necessary.

Relation: full kernel `Step`. Property: `local_confluence` (its negation). Source:
`EqW_Guard_Barrier.eqW_guards_are_confluence_necessary`. -/
theorem eqW_guards_are_confluence_necessary :
    ∀ a : Trace, ¬ MetaSN_KO7.LocalJoinStep (eqW a a) :=
  OperatorKO7.Meta.EqW_Guard_Barrier.eqW_guards_are_confluence_necessary

/-- **Pillar headline 7 — the object-level critical pair.** `eqW void void` admits two
distinct normal forms that do not join, recorded as a `CriticalPairAt`.

Relation: full kernel `Step` (closure `StepStar`). Property: `local_confluence`
(failure, as a witnessed record). Source:
`SafeStep.EqWVoidAnomaly.local_confluence_fails_at_eqW_void_void`. -/
theorem local_confluence_fails_at_eqW_void_void :
    OperatorKO7.Meta.SafeStep.EqWVoidAnomaly.CriticalPairAt
      (eqW void void) void (integrate (merge void void)) :=
  OperatorKO7.Meta.SafeStep.EqWVoidAnomaly.local_confluence_fails_at_eqW_void_void

/-- **Pillar headline 8 — the honesty keystone.** Non-left-linearity is necessary but
not sufficient for the fork: on the full kernel `Step`, `merge void void` joins while
`eqW void void` does not.

Relation: full kernel `Step` (closure `StepStar`). Property: `local_confluence`
(joinability of the benign control; non-joinability of the breaker). Source:
`SafeStep.DistinctionControls.nonLeftLinearity_necessary_not_sufficient`. -/
theorem nonLeftLinearity_necessary_not_sufficient :
    MetaSN_KO7.LocalJoinStep (merge void void) ∧
      ¬ MetaSN_KO7.LocalJoinStep (eqW void void) :=
  OperatorKO7.Meta.SafeStep.DistinctionControls.nonLeftLinearity_necessary_not_sufficient

end OperatorKO7.Meta.DistinctionBoundary.Pillar
