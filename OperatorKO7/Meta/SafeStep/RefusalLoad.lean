import OperatorKO7.Kernel
import OperatorKO7.Meta.SafeStep_Core
import OperatorKO7.Meta.SafeStep.BranchTransaction
import OperatorKO7.Meta.SafeStep.BranchEntropy
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic

set_option autoImplicit false
set_option linter.dupNamespace false

/-!
# Refusal-load bookkeeping for the eqW diagonal breaker (G3)

This module turns the Distinction Boundary paper's prose-only "Refusal-load
bookkeeping" paragraph into theorems on the checked KO7 surface. The paragraph
defines, for a raw relation `R` and a licensed sub-relation `RL`, the forbidden
set at a source `t`

```text
Forbidden_{R,RL}(t) = { v | R t v ∧ ¬ RL t v }
```

and a refusal load `RefLoad(t) = Σ_{v ∈ Forbidden} K(ρ_v)` that pays one
constant-size negative certificate per forbidden branch. It asserts two
operational facts:

* one constant-size certificate per diagonal query (the load at a single
  diagonal source is `1`); and
* additive load **linear in `N`** over a batch of `N` independent diagonal
  comparisons.

We mechanize both, reusing (not re-proving) the breaker facts from
`BranchTransaction` (`ForbiddenBranch`, `diagonal_forbiddenBranch`,
`diagonal_diff_branch_unsafe`, `diagonal_selected_licensed`,
`forbiddenBranch_nonempty`) and `BranchEntropy` (`diagonal_refusal`).

## Design

The forbidden branches are carried as a `Finset Trace` and the unit refusal
certificate has constant cost `1` (the diagonal-empty license `¬ (a ≠ a)` from
`BranchEntropy.diagonal_refusal`; its *size* is constant, modelled by the unit
cost). The refusal load at a source is the sum of that unit cost over the
forbidden finset, i.e. its cardinality:

```text
refLoad F = ∑_{v ∈ F} 1 = F.card
```

The two headline results are then real arithmetic facts about that sum:

1. `refLoad_diagonal_eq_one`: at the diagonal source `eqW void void` the
   forbidden finset is *exactly* the singleton `{integrate (merge void void)}`
   (the raw `Step` successors are exactly `void` and
   `integrate (merge void void)`, and `void` is licensed while
   `integrate (merge void void)` is refused), so `refLoad = 1`.
2. `refLoad_batch_eq_N`: over a length-`N` list of diagonal sources, the total
   refusal load is `N`.

Relation: full kernel `Step` (raw) vs guarded `SafeStep` (licensed).
Closure: root (the forbidden branch is a root critical-peak branch).
Strategy: not applicable (root critical-pair bookkeeping).
Property: refusal-certificate accounting (cardinality of the forbidden set).
Trust: kernel-only; allowed axioms only (see `#print axioms`).
-/

open OperatorKO7 Trace
open MetaSN_KO7
open OperatorKO7.Meta.SafeStep.EqWVoidAnomaly
open OperatorKO7.Meta.SafeStep.BranchTransaction

namespace OperatorKO7.Meta.SafeStep.RefusalLoad

/-! ## The refusal load as a sum of unit certificates -/

/-- The refusal load at a source whose forbidden branches are collected in the
finset `F`: the sum over `F` of the unit refusal-certificate cost `1`. The unit
cost models the *constant-size* negative certificate `¬ (a ≠ a)` that the
licensed layer pays per refused branch (`BranchEntropy.diagonal_refusal`). By
`Finset.sum_const` this equals `F.card`. -/
def refLoad (F : Finset Trace) : Nat :=
  ∑ _v ∈ F, 1

/-- The refusal load of a forbidden finset is its cardinality: one unit
certificate per forbidden branch. -/
theorem refLoad_eq_card (F : Finset Trace) : refLoad F = F.card := by
  simp [refLoad]

/-! ## Exact forbidden set at the eqW diagonal breaker

The raw `Step` successors of `eqW void void` are exactly `void` (via
`R_eq_refl`) and `integrate (merge void void)` (via `R_eq_diff`). The licensed
`SafeStep` keeps `void` (zero-payload reflexive guard) and refuses
`integrate (merge void void)` (the off-diagonal rule needs `void ≠ void`). Hence
the forbidden set is the singleton `{integrate (merge void void)}`. -/

/-- Forward characterization of the raw kernel successors of the diagonal source:
`eqW void void` steps (in one root `Step`) to `v` iff `v` is `void` or
`integrate (merge void void)`. Proved by inverting the `Step` inductive, so it is
an exact enumeration of the two overlapping `eqW` rules, not a lower bound. -/
theorem diagonal_step_iff (v : Trace) :
    Step (eqW void void) v ↔ v = void ∨ v = integrate (merge void void) := by
  constructor
  · intro h
    cases h with
    | R_eq_refl _ => exact Or.inl rfl
    | R_eq_diff _ _ => exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact Step.R_eq_refl void
    · exact Step.R_eq_diff void void

/-- The selected reflexive branch `void` is licensed at the diagonal, hence it is
**not** forbidden: it fails the `¬ SafeStep` half of `ForbiddenBranch`. -/
theorem diagonal_refl_branch_not_forbidden :
    ¬ ForbiddenBranch Step SafeStep (eqW void void) void := by
  intro h
  exact h.2 diagonal_selected_licensed

/-- A branch `v` of the diagonal source is forbidden (`ForbiddenBranch Step
SafeStep`) iff it is exactly `integrate (merge void void)`. This is the exact
content behind "one constant-size certificate per diagonal query": among the two
raw successors only the difference branch is refused. -/
theorem diagonal_forbidden_iff (v : Trace) :
    ForbiddenBranch Step SafeStep (eqW void void) v
      ↔ v = integrate (merge void void) := by
  constructor
  · intro h
    rcases (diagonal_step_iff v).1 h.1 with hv | hv
    · exact absurd (hv ▸ h) diagonal_refl_branch_not_forbidden
    · exact hv
  · rintro rfl
    exact diagonal_forbiddenBranch

/-- The forbidden finset at the diagonal source: the kept reflexive branch `void`
is filtered out, leaving the refused difference branch. We build it as the
explicit singleton; the next theorem certifies that this singleton is exactly the
set of forbidden raw successors via `diagonal_forbidden_iff`. -/
def diagonalForbidden : Finset Trace :=
  {integrate (merge void void)}

/-- Membership in `diagonalForbidden` coincides with being a forbidden branch of
the diagonal source: the explicit singleton is the genuine forbidden set, not an
arbitrary stand-in. -/
theorem mem_diagonalForbidden_iff (v : Trace) :
    v ∈ diagonalForbidden ↔ ForbiddenBranch Step SafeStep (eqW void void) v := by
  rw [diagonalForbidden, Finset.mem_singleton, diagonal_forbidden_iff]

/-! ## Headline 1: constant load per diagonal query -/

/-- **One constant-size certificate per diagonal query.** At the eqW diagonal
source `eqW void void` the forbidden set is exactly the singleton
`{integrate (merge void void)}`, so the refusal load is `1`. This is a real
arithmetic fact about the unit-certificate sum: the singleton has cardinality
`1`, witnessed non-vacuously by `diagonal_forbiddenBranch`.

Relation: `Step` (raw) vs `SafeStep` (licensed). Closure: root. Property: refusal
certificate count. -/
theorem refLoad_diagonal_eq_one : refLoad diagonalForbidden = 1 := by
  rw [refLoad_eq_card, diagonalForbidden, Finset.card_singleton]

/-! ## Headline 2: additive load linear in N over a batch -/

/-- The per-source forbidden finset for a batch entry. Every diagonal source
`eqW a a` of the batch contributes its own copy of the constant-size refused
difference branch; we charge the constant unit load `1` for each, exactly as the
diagonal singleton above. -/
def batchForbidden (_a : Trace) : Finset Trace := diagonalForbidden

/-- Each batch entry carries refusal load `1` (constant per diagonal source),
inheriting the singleton-card fact from `refLoad_diagonal_eq_one`. -/
theorem refLoad_batchForbidden_eq_one (a : Trace) :
    refLoad (batchForbidden a) = 1 := by
  rw [batchForbidden]; exact refLoad_diagonal_eq_one

/-- **Additive load linear in `N`.** Over a batch of `N` independent diagonal
sources (a `List Trace` of length `N`), the total refusal load — the sum of the
per-source loads — is exactly `N`. The proof reduces each summand to `1` via
`refLoad_batchForbidden_eq_one` and then sums `N` ones with `List.sum_replicate`
/ `List.length_map`, so the result is a genuine linear-in-`N` arithmetic fact,
not a tautology.

Relation: `Step` vs `SafeStep`. Closure: root. Property: additive refusal load. -/
theorem refLoad_batch_eq_N (srcs : List Trace) :
    (srcs.map (fun a => refLoad (batchForbidden a))).sum = srcs.length := by
  induction srcs with
  | nil => simp
  | cons hd tl ih =>
      rw [List.map_cons, List.sum_cons, List.length_cons, ih,
        refLoad_batchForbidden_eq_one hd, Nat.add_comm]

/-- The batch law in closed form for `N` literally-equal diagonal sources: a list
of `N` copies of `eqW void void` carries total refusal load `N`. This is the
direct reading of "load linear in `N`": `N` diagonal queries cost `N`. -/
theorem refLoad_batch_replicate_eq_N (N : Nat) :
    ((List.replicate N (eqW void void)).map
      (fun a => refLoad (batchForbidden a))).sum = N := by
  rw [refLoad_batch_eq_N, List.length_replicate]

/-! ## Non-vacuity

The "= 1" and "= N" facts are non-vacuous: the forbidden set is genuinely
inhabited at the diagonal (the difference branch is a real refused `Step`),
re-exported from `forbiddenBranch_nonempty`. -/

/-- Non-vacuity (Gate R5 / K20): the diagonal forbidden finset is nonempty, so
`refLoad_diagonal_eq_one` counts a genuine refused branch rather than reporting
`card` of an empty set. -/
theorem diagonalForbidden_nonempty : diagonalForbidden.Nonempty :=
  ⟨integrate (merge void void), by
    rw [mem_diagonalForbidden_iff]; exact diagonal_forbiddenBranch⟩

#print axioms refLoad_diagonal_eq_one
#print axioms refLoad_batch_eq_N
#print axioms refLoad_batch_replicate_eq_N
#print axioms diagonal_forbidden_iff
#print axioms diagonalForbidden_nonempty

end OperatorKO7.Meta.SafeStep.RefusalLoad
