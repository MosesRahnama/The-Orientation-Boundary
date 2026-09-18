import OperatorKO7.Kernel
import OperatorKO7.Meta.Confluence_Safe
import OperatorKO7.Meta.SafeStep.EqWVoidAnomaly
import OperatorKO7.Meta.SafeStep.NonlinearityDichotomy

set_option autoImplicit false

/-!
# Distinction Controls: the benign-control contrast for the `eqW` confluence fork

This module isolates, in single statements, the *control* contrast that makes the
KO7 `eqW void void` confluence failure honest. The danger is not non-left-linearity
as such; both the `merge t t → t` rule and the two `eqW` rules are non-left-linear
(they embed a syntactic equality test in the matcher), yet only the `eqW` pair
breaks local confluence. The benign control is `merge(void, void)`: its overlapping
redexes are *joinable*, while the `eqW(void, void)` diagonal overlap is *not*. So
non-left-linearity is **necessary but not sufficient** for the fork.

## What is reused, not re-proved

* `MetaSN_KO7.localJoin_merge_void_void`
  (`Meta/Confluence_Safe.lean`): the `merge void void` overlap is joinable for the
  safe relation `SafeStep`. Cited as the safe-fragment control (Goal 1 corollary).
* `MetaSN_KO7.not_localJoinStep_eqW_void_void`
  (`Meta/Confluence_Safe.lean`): the `eqW void void` diagonal overlap is *not*
  joinable for the full kernel relation `Step`. This is the breaker.
* `MetaSN_KO7.localJoin_eqW_ne`
  (`Meta/Confluence_Safe.lean`): every *off-diagonal* `eqW a b` (`a ≠ b`) is joinable
  for `SafeStep` — only `R_eq_diff` can fire. Used for the "removes exactly the
  diagonal" statement (Goal 2).
* `OperatorKO7.Meta.SafeStep.NonlinearityDichotomy.boundary_rules_dual_nonlinear`:
  both boundary source rules are non-linear (left for confluence, right for
  termination). Referenced to anchor the "both rules are non-LL" premise of the
  necessary-not-sufficient reading.

The only fact this file proves from scratch is the full-`Step` joinability of the
benign control `merge void void` (`localJoinStep_merge_void_void`), so that the
keystone contrast can be stated on **one** relation, the full kernel `Step`. Every
merge rule at `merge void void` (`R_merge_void_left`, `R_merge_void_right`,
`R_merge_cancel`) targets `void`, so the source is trivially joinable.

## Audit notes (LASOT)

* Relation: full kernel `Step` (closure `StepStar`) for the keystone, plus the safe
  relation `SafeStep` (closure `SafeStepStar`) for the off-diagonal control and the
  cited `merge void void` safe corollary. Each theorem names its relation.
* Property: `local_confluence` (joinability of a single source, and its negation).
* SafeStep `eqW` diagonal note: under `SafeStep` the `merge void void` overlap and
  the *off-diagonal* `eqW` overlaps are joinable; the diagonal `eqW void void`
  failure is a property of the **full** kernel `Step` (the unguarded `R_eq_refl`,
  `R_eq_diff` pair), which is exactly where the two `eqW` rules coexist.
* No `sorry`, `admit`, `axiom`, `native_decide`, `bv_decide`, `@[csimp]`, `unsafe`,
  `partial`, or `opaque`. The new helper closes by `cases`; the headline theorems
  are conjunctions of reused facts.
* Goal 3 is stated as a **scoped** minimality claim: `void` is a closed (constant,
  metavariable-free) `Trace`, and the breaker holds at `eqW void void`. Full
  minimality (no closed proper subterm of `eqW void void` itself forks) is *not*
  claimed; the docstring states exactly the bound proved.
* `#print axioms` on each headline theorem is a subset of
  `{propext, Classical.choice, Quot.sound}`.
-/

open OperatorKO7 Trace
open OperatorKO7.Meta.SafeStep.NonlinearityDichotomy

namespace OperatorKO7.Meta.SafeStep.DistinctionControls

/-! ## The benign control on the full kernel relation

To state the keystone contrast on a single relation, we first record that the
benign control `merge void void` is locally joinable for the **full** kernel `Step`.
This is the full-`Step` analogue of the safe-fragment fact
`MetaSN_KO7.localJoin_merge_void_void`. -/

/-- Every full-kernel `Step` out of `merge void void` lands on `void`: the three
applicable merge rules (`R_merge_void_left`, `R_merge_void_right`, `R_merge_cancel`)
all target `void` at this source. -/
theorem step_merge_void_void_eq_void {x : Trace}
    (h : Step (merge void void) x) : x = void := by
  cases h with
  | R_merge_void_left _ => rfl
  | R_merge_void_right _ => rfl
  | R_merge_cancel _ => rfl

/-- **Benign control (full kernel `Step`).** The `merge void void` overlap is
locally joinable for the full kernel relation: both reducts of any peak are `void`,
so they join at `void`.

Relation: full kernel `Step` (closure `StepStar`).
Property: `local_confluence` (joinability of the source `merge void void`). -/
theorem localJoinStep_merge_void_void :
    MetaSN_KO7.LocalJoinStep (merge void void) := by
  intro b c hb hc
  have hb' : b = void := step_merge_void_void_eq_void hb
  have hc' : c = void := step_merge_void_void_eq_void hc
  exact ⟨void, by simpa [hb'] using StepStar.refl void,
              by simpa [hc'] using StepStar.refl void⟩

/-! ## Goal 1 — the honesty keystone -/

/-- **Non-left-linearity is necessary but not sufficient for the confluence fork.**

The benign control and the breaker, contrasted on the *same* relation (full kernel
`Step`), in one statement:

* `merge void void` is locally **joinable** (`localJoinStep_merge_void_void`);
* `eqW void void` is **not** locally joinable
  (`MetaSN_KO7.not_localJoinStep_eqW_void_void`).

Both `merge t t → t` and the `eqW` rules are non-left-linear — they repeat a
metavariable on the left-hand side, i.e. embed a syntactic equality test
(see `NonlinearityDichotomy.boundary_rules_dual_nonlinear`, whose
`LeftNonlinear eqwReflLhs` component records the `eqW a a` repeat). Yet only the
`eqW` pair breaks confluence. Hence non-left-linearity alone does not force a fork:
the dangerous pattern is non-left-linearity **plus** an incompatible totalized
non-null branch (the unguarded `R_eq_diff` producing `integrate (merge a b)`
alongside the `R_eq_refl` collapse to `void`). The `merge` diagonal lacks such a
competing branch — every rule collapses to the shared argument — so it stays
joinable.

Relation: full kernel `Step` (closure `StepStar`) for both conjuncts.
Property: `local_confluence` (joinability of `merge void void`; non-joinability of
`eqW void void`). -/
theorem nonLeftLinearity_necessary_not_sufficient :
    MetaSN_KO7.LocalJoinStep (merge void void) ∧
      ¬ MetaSN_KO7.LocalJoinStep (eqW void void) :=
  ⟨localJoinStep_merge_void_void, MetaSN_KO7.not_localJoinStep_eqW_void_void⟩

/-- Safe-fragment corollary of the benign-control half: the `merge void void`
overlap is also joinable for the safe relation `SafeStep`. This is the cited
`MetaSN_KO7.localJoin_merge_void_void` re-exported here so the control reads on both
relations. (`SafeStep` additionally guards the diagonal `eqW void void` so that the
breaking peak cannot even form in the safe fragment; the fork is genuinely a
full-kernel `Step` phenomenon.)

Relation: safe relation `SafeStep` (closure `SafeStepStar`).
Property: `local_confluence` (joinability of `merge void void`). -/
theorem localJoinSafe_merge_void_void :
    MetaSN_KO7.LocalJoinSafe (merge void void) :=
  MetaSN_KO7.localJoin_merge_void_void

/-! ## Goal 2 — SafeStep removes exactly the diagonal -/

/-- **SafeStep blocks only the `eqW` diagonal, nothing else.**

`SafeStep` guards the reflexive `eqW` rule (`R_eq_refl` requires `kappaM a = 0`) and
the difference rule (`R_eq_diff` requires `a ≠ b`). The net effect on `eqW` overlaps
is surgical:

* **Off-diagonal preserved.** For every `a ≠ b`, the `eqW a b` overlap is still
  joinable (only `R_eq_diff` can fire, uniquely to `integrate (merge a b)`):
  `MetaSN_KO7.localJoin_eqW_ne`.
* **Diagonal blocked.** At the diagonal source `eqW void void` the competing
  `R_eq_diff` branch is removed — its guard `void ≠ void` is unsatisfiable — so the
  peak that breaks the full kernel cannot form. Recorded here as the unsatisfiability
  of the diagonal guard.

Together: SafeStep removes exactly the diagonal `R_eq_diff` instance and keeps every
off-diagonal `eqW` emission.

Relation: safe relation `SafeStep` (closure `SafeStepStar`).
Property: `local_confluence` (off-diagonal joinability) together with the diagonal
guard fact. -/
theorem safestep_removes_exactly_diagonal :
    (∀ a b : Trace, a ≠ b → MetaSN_KO7.LocalJoinSafe (eqW a b)) ∧
      ¬ ((void : Trace) ≠ void) :=
  ⟨fun a b hne => MetaSN_KO7.localJoin_eqW_ne a b hne, fun hne => hne rfl⟩

/-- Companion to Goal 2, isolating the off-diagonal-preservation half on its own so
downstream code can cite it directly: SafeStep keeps every off-diagonal `eqW`
overlap joinable.

Relation: safe relation `SafeStep`. Property: `local_confluence`. -/
theorem safestep_preserves_offdiagonal_eqW
    (a b : Trace) (hne : a ≠ b) : MetaSN_KO7.LocalJoinSafe (eqW a b) :=
  MetaSN_KO7.localJoin_eqW_ne a b hne

/-! ## Goal 3 — `void` as a scoped closed witness

We pin `eqW void void` as a **closed** witness of the breaker. "Closed" here means
metavariable-free: `void` is the nullary kernel constructor, so `eqW void void` is a
ground term of the object signature. We do **not** claim full minimality (that no
*closed proper subterm* of `eqW void void` itself forks); the only closed proper
subterm of `eqW void void` is `void`, which is a normal form and trivially does not
fork, but a general "minimal closed forking term" claim is out of scope and is not
asserted. The bound actually proved is exactly: `void` is closed, and the breaker
holds at `eqW void void`. -/

/-- A `Trace` is *closed* (ground) when it is built from the kernel constructors with
no metavariable leaf. Since `OperatorKO7.Trace` has no variable constructor, every
`Trace` is closed; we phrase the predicate explicitly so the witness statement names
its scope. The only non-constructor leaf possibility would be a variable, which the
kernel signature does not have — hence `void` qualifies definitionally. -/
def IsClosed (_t : Trace) : Prop := True

/-- `void` is a closed (ground, metavariable-free) `Trace`. -/
theorem void_isClosed : IsClosed void := trivial

/-- **`eqW void void` is a closed witness of the breaker (scoped minimality).**

The diagonal source `eqW void void` is built from the closed leaf `void`, and the
full-kernel `Step` breaker holds at it. This is the *scoped* witness claim: closedness
of `void` plus the breaker at `eqW void void`. It does **not** assert that no closed
proper subterm forks, nor any global minimality over all closed terms; see the
section docstring for the exact bound.

Relation: full kernel `Step` (closure `StepStar`).
Property: `local_confluence` (non-joinability at `eqW void void`), with the closed-leaf
side condition. -/
theorem eqW_void_void_closed_witness :
    IsClosed void ∧ ¬ MetaSN_KO7.LocalJoinStep (eqW void void) :=
  ⟨void_isClosed, MetaSN_KO7.not_localJoinStep_eqW_void_void⟩

/-! ## Axiom audit -/

#print axioms nonLeftLinearity_necessary_not_sufficient
#print axioms safestep_removes_exactly_diagonal
#print axioms eqW_void_void_closed_witness

end OperatorKO7.Meta.SafeStep.DistinctionControls
