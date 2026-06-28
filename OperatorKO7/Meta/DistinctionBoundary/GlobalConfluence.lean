import OperatorKO7.Meta.Newman_Safe
import OperatorKO7.Meta.SafeStepCtx_Confluence
import OperatorKO7.Meta.ComputableMeasure
import OperatorKO7.Meta.DistinctionBoundary.CriticalPairCompleteness

set_option autoImplicit false

/-!
# Global confluence of the KO7 safe relation (distinction axis)

## Inventory first

Global confluence of the guarded relation `SafeStep` is **already proved
unconditionally** in the published development, by Newman's lemma:

* Strong normalization of `SafeStep` is `MetaSN_KO7.wf_SafeStepRev_c`
  (`Meta/ComputableMeasure.lean`): `WellFounded SafeStepRev`, the reverse relation
  being well-founded is exactly SN.
* Local joinability everywhere is `MetaSN_KO7.locAll_safe`
  (`Meta/Confluence_Safe.lean` via `localJoin_all_safe`): `∀ a, LocalJoinAt a`.
* Newman combines them: `MetaSN_KO7.newman_safe` gives
  `MetaSN_KO7.confluentSafe : ConfluentSafe`, i.e. global Church–Rosser for
  `SafeStepStar` (`Meta/Newman_Safe.lean`).

The context-closed relation is likewise global-confluent unconditionally:
`MetaSN_KO7.confluentSafeCtx : ConfluentSafeCtx` (`Meta/SafeStepCtx_Confluence.lean`),
again SN (`acc_ctx_all`) + exhaustive local join (`localJoinAll_ctx`).

So there is **no local-only gap to close**: this module does not re-prove confluence.
Its content is to (1) package the existing global results under stable
distinction-axis names with explicit Newman provenance, and (2) connect them to the
completeness result of `CriticalPairCompleteness.lean`: the guard that makes
`SafeStep` confluent removes exactly the unique root obstruction characterized there
(the `eqW` reflexive diagonal), and nothing else.

## Relation / property (LASOT)

* Relation: `SafeStep` (closure `SafeStepStar`) for the root-level statements;
  `SafeStepCtx` (closure `SafeStepCtxStar`) for the context-closed statement; the
  full kernel `Step` only in the obstruction-contrast theorem (cited from
  `CriticalPairCompleteness`).
* Property: `confluence` (Church–Rosser of the reflexive-transitive closure), built
  from `SN` + `local_confluence` via Newman.
* Trust: kernel-only. No `sorry`, `admit`, `axiom`, `native_decide`, `bv_decide`,
  `@[csimp]`, `unsafe`, `partial`, or `opaque`. `#print axioms` on each headline is a
  subset of `{propext, Classical.choice, Quot.sound}`.
-/

open OperatorKO7 Trace

namespace OperatorKO7.Meta.DistinctionBoundary.GlobalConfluence

/-! ## SN component (Newman premise 1) -/

/-- **Strong normalization of `SafeStep`.** The reverse relation `SafeStepRev` is
well-founded; this is the termination premise consumed by Newman's lemma. Cited from
`Meta/ComputableMeasure.lean`.

Relation: `SafeStep`. Property: `SN`. -/
theorem safeStep_strongly_normalizing : WellFounded MetaSN_KO7.SafeStepRev :=
  OperatorKO7.MetaCM.wf_SafeStepRev_c

/-! ## Local-confluence component (Newman premise 2) -/

/-- **Local confluence of `SafeStep` everywhere.** Every root source is locally
joinable. Cited from `Meta/Confluence_Safe.lean` (`localJoin_all_safe`).

Relation: `SafeStep` (closure `SafeStepStar`). Property: `local_confluence`. -/
theorem safeStep_locally_confluent : ∀ a, MetaSN_KO7.LocalJoinAt a :=
  MetaSN_KO7.locAll_safe

/-! ## Global confluence (Newman conclusion) -/

/-- **Global confluence of `SafeStep` (root closure).** Church–Rosser for
`SafeStepStar`: any two reducts of a common source have a common reduct. This is the
packaged form of `MetaSN_KO7.confluentSafe`, obtained from SN + local confluence by
Newman's lemma (`MetaSN_KO7.newman_safe`).

Relation: `SafeStep` (closure `SafeStepStar`). Property: `confluence`. -/
theorem safeStep_globally_confluent : MetaSN_KO7.ConfluentSafe :=
  MetaSN_KO7.confluentSafe

/-- Newman provenance, stated explicitly: from any SN witness and any global
local-join witness for `SafeStep`, global confluence follows. This records that the
packaged `safeStep_globally_confluent` is genuinely the Newman conclusion and not an
independent assumption.

Relation: `SafeStep` (closure `SafeStepStar`). Property: `confluence` from
`SN ∧ local_confluence`. -/
theorem safeStep_confluent_via_newman
    (_hSN : WellFounded MetaSN_KO7.SafeStepRev)
    (hloc : ∀ a, MetaSN_KO7.LocalJoinAt a) : MetaSN_KO7.ConfluentSafe :=
  MetaSN_KO7.newman_safe hloc

/-- **Unique normal forms.** A direct consequence of global confluence: safe-normal
forms reachable from a common source coincide. Cited from `Meta/Newman_Safe.lean`.

Relation: `SafeStep` (closure `SafeStepStar`). Property: `confluence` (unique normal
forms). -/
theorem safeStep_unique_normal_forms
    {a n₁ n₂ : Trace}
    (h₁ : MetaSN_KO7.SafeStepStar a n₁) (h₂ : MetaSN_KO7.SafeStepStar a n₂)
    (hnf₁ : MetaSN_KO7.NormalFormSafe n₁) (hnf₂ : MetaSN_KO7.NormalFormSafe n₂) :
    n₁ = n₂ :=
  MetaSN_KO7.unique_normal_forms_safe h₁ h₂ hnf₁ hnf₂

/-! ## Context-closed global confluence -/

/-- **Global confluence of the context-closed safe relation `SafeStepCtx`.** Cited
from `Meta/SafeStepCtx_Confluence.lean`; again SN (`acc_ctx_all`) + exhaustive local
join (`localJoinAll_ctx`) via Newman.

Relation: `SafeStepCtx` (closure `SafeStepCtxStar`). Property: `confluence`. -/
theorem safeStepCtx_globally_confluent : MetaSN_KO7.ConfluentSafeCtx :=
  MetaSN_KO7.confluentSafeCtx

/-- The exact Newman equivalence for the context closure: since SN is already
available, confluence of `SafeStepCtx` is equivalent to the global local-join
obligation. Cited from `Meta/SafeStepCtx_Confluence.lean`.

Relation: `SafeStepCtx`. Property: `confluence ↔ local_confluence` (under ambient SN). -/
theorem safeStepCtx_confluent_iff_localJoin :
    MetaSN_KO7.ConfluentSafeCtx ↔ ∀ a, MetaSN_KO7.LocalJoinCtxAt a :=
  MetaSN_KO7.confluentSafeCtx_iff_localJoinAll

/-! ## Bridge: the guard removes exactly the unique obstruction

`SafeStep` is globally confluent; the full kernel `Step` is not even locally confluent.
By `CriticalPairCompleteness.eqW_diagonal_is_the_unique_root_obstruction`, the *only*
root source where `Step` fails is the reflexive `eqW` diagonal. The `SafeStep` guards
on the `eqW` rules neutralize precisely that diagonal (and the completeness result says
there is nothing else to neutralize). This theorem packages the two halves so the
"confluence is bought by guarding exactly the unique critical pair" reading is on one
statement. -/

/-- **The confluence axis, end to end.** Conjunction of:

* global confluence of `SafeStep` (`safeStep_globally_confluent`), and
* the completeness characterization of the full-kernel obstruction set as exactly the
  `eqW` reflexive diagonal
  (`CriticalPairCompleteness.eqW_diagonal_is_the_unique_root_obstruction`).

Reading: the guarded relation is confluent, and what had to be guarded away is a single
characterized critical pair — the `eqW` diagonal — not an open-ended family.

Relation: `SafeStep` (closure `SafeStepStar`) for the first conjunct; full kernel
`Step` (closure `StepStar`) for the obstruction characterization. Property:
`confluence` together with the `local_confluence` completeness `iff`. -/
theorem safeStep_confluent_and_obstruction_complete :
    MetaSN_KO7.ConfluentSafe ∧
      (∀ a, ¬ MetaSN_KO7.LocalJoinStep a ↔
        OperatorKO7.Meta.DistinctionBoundary.CriticalPairCompleteness.IsEqWDiagonal a) :=
  ⟨safeStep_globally_confluent,
   OperatorKO7.Meta.DistinctionBoundary.CriticalPairCompleteness.eqW_diagonal_is_the_unique_root_obstruction⟩

/-! ## Axiom audit -/

#print axioms safeStep_globally_confluent
#print axioms safeStepCtx_globally_confluent
#print axioms safeStep_confluent_via_newman
#print axioms safeStep_unique_normal_forms
#print axioms safeStep_confluent_and_obstruction_complete

end OperatorKO7.Meta.DistinctionBoundary.GlobalConfluence
