import OperatorKO7.Kernel
import OperatorKO7.Meta.SafeStep_Core
import OperatorKO7.Meta.SafeStep.BranchTransaction
import OperatorKO7.Meta.SafeStep.BranchEntropy
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic

set_option autoImplicit false

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
2. `refLoad_batch_eq_N`: a batch entry `a` stands for the diagonal source
 `eqW a a` and carries the exact forbidden set of that source
 (`mem_batchForbidden_iff`); over a length-`N` list of entries without
 payload (`kappaM a = 0`) the total refusal load is `N`. An entry with payload
 refuses both raw branches and carries load `2`
 (`refLoad_batchForbidden_recDelta_eq_two`), and `refLoad_batch_eq_sum` gives
 the total for an arbitrary list.

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

/-! ## Exact forbidden set at every diagonal source

At `eqW a a` the raw successors are again `void` and `integrate (merge a a)`.
The difference branch is always refused, since its guard needs `a ≠ a`. The
reflexive branch is licensed exactly when `a` carries no payload
(`kappaM a = 0`), so a source with payload refuses both raw branches. -/

/-- The raw kernel successors of the diagonal source `eqW a a` are exactly `void`
and `integrate (merge a a)`. -/
theorem diagonal_step_iff_at (a v : Trace) :
    Step (eqW a a) v ↔ v = void ∨ v = integrate (merge a a) := by
  constructor
  · intro h
    cases h with
    | R_eq_refl _ => exact Or.inl rfl
    | R_eq_diff _ _ => exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact Step.R_eq_refl a
    · exact Step.R_eq_diff a a

/-- The reflexive branch of `eqW a a` is licensed exactly when `a` carries no
payload. -/
theorem diagonal_refl_safe_iff (a : Trace) :
    SafeStep (eqW a a) void ↔ MetaSN_DM.kappaM a = 0 := by
  constructor
  · intro h
    cases h with
    | R_eq_refl _ h0 => exact h0
  · intro h0
    exact SafeStep.R_eq_refl a h0

/-- The difference branch of `eqW a a` is never licensed. -/
theorem diagonal_diff_not_safe (a : Trace) :
    ¬ SafeStep (eqW a a) (integrate (merge a a)) := by
  intro h
  cases h with
  | R_eq_diff _ _ hne => exact hne rfl

/-- The forbidden finset of the diagonal source `eqW a a`: the difference branch,
together with the reflexive branch `void` when `a` carries payload. -/
def diagonalForbiddenAt (a : Trace) : Finset Trace :=
  if MetaSN_DM.kappaM a = 0 then {integrate (merge a a)}
  else {void, integrate (merge a a)}

/-- Membership in `diagonalForbiddenAt a` coincides with being a forbidden branch
of the diagonal source `eqW a a`. -/
theorem mem_diagonalForbiddenAt_iff (a v : Trace) :
    v ∈ diagonalForbiddenAt a ↔ ForbiddenBranch Step SafeStep (eqW a a) v := by
  simp only [ForbiddenBranch, diagonal_step_iff_at]
  by_cases h0 : MetaSN_DM.kappaM a = 0
  · simp only [diagonalForbiddenAt, h0, if_true, Finset.mem_singleton]
    constructor
    · rintro rfl
      exact ⟨Or.inr rfl, diagonal_diff_not_safe a⟩
    · rintro ⟨hv | hv, hns⟩
      · subst hv
        exact absurd ((diagonal_refl_safe_iff a).2 h0) hns
      · exact hv
  · simp only [diagonalForbiddenAt, h0, if_false, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (rfl | rfl)
      · exact ⟨Or.inl rfl, fun hs => h0 ((diagonal_refl_safe_iff a).1 hs)⟩
      · exact ⟨Or.inr rfl, diagonal_diff_not_safe a⟩
    · rintro ⟨hv, _⟩
      exact hv

/-- At the payload-free source `eqW void void` the general forbidden set is the
singleton of the first headline. -/
theorem diagonalForbiddenAt_void : diagonalForbiddenAt void = diagonalForbidden := by
  simp [diagonalForbiddenAt, diagonalForbidden]

/-- The refusal load of the diagonal source `eqW a a` is `1` without payload and
`2` with payload. -/
theorem refLoad_diagonalForbiddenAt (a : Trace) :
    refLoad (diagonalForbiddenAt a) = if MetaSN_DM.kappaM a = 0 then 1 else 2 := by
  rw [refLoad_eq_card]
  by_cases h0 : MetaSN_DM.kappaM a = 0
  · simp [diagonalForbiddenAt, h0]
  · simp [diagonalForbiddenAt, h0]

/-! ## Headline 2: additive load over a batch

STATEMENT CHANGE (2026-10-26, Lean audit of the observation-principle stack).
Old: `batchForbidden (_a : Trace) := diagonalForbidden`, so every entry, whatever
its term, was charged the singleton of `eqW void void`, and `refLoad_batch_eq_N`
stated load `N` for an arbitrary list. The audit exhibited the entry
`recΔ void void void`: its diagonal source refuses both raw branches, while the
stored set had one element. New: an entry `a` carries the exact forbidden set of
`eqW a a`; the linear law holds for payload-free entries, and
`refLoad_batch_eq_sum` gives the total of an arbitrary list. -/

/-- The forbidden finset of a batch entry `a`, which stands for the diagonal
source `eqW a a`: the exact forbidden set of that source. -/
def batchForbidden (a : Trace) : Finset Trace := diagonalForbiddenAt a

/-- A batch entry carries exactly the forbidden branches of its diagonal source. -/
theorem mem_batchForbidden_iff (a v : Trace) :
    v ∈ batchForbidden a ↔ ForbiddenBranch Step SafeStep (eqW a a) v :=
  mem_diagonalForbiddenAt_iff a v

/-- A payload-free batch entry carries refusal load `1`. -/
theorem refLoad_batchForbidden_eq_one (a : Trace) (h0 : MetaSN_DM.kappaM a = 0) :
    refLoad (batchForbidden a) = 1 := by
  rw [batchForbidden, refLoad_diagonalForbiddenAt, if_pos h0]

/-- The entry `recΔ void void void` carries payload, so its diagonal source
refuses both raw branches and its refusal load is `2`: the load per diagonal
query is not constant across sources. -/
theorem refLoad_batchForbidden_recDelta_eq_two :
    refLoad (batchForbidden (recΔ void void void)) = 2 := by
  rw [batchForbidden, refLoad_diagonalForbiddenAt, if_neg (by simp)]

/-- The total refusal load of an arbitrary batch: each entry contributes `1`
without payload and `2` with payload. -/
theorem refLoad_batch_eq_sum (srcs : List Trace) :
    (srcs.map (fun a => refLoad (batchForbidden a))).sum
      = (srcs.map (fun a => if MetaSN_DM.kappaM a = 0 then 1 else 2)).sum := by
  simp only [batchForbidden, refLoad_diagonalForbiddenAt]

/-- **Additive load linear in `N`.** Over a batch of `N` payload-free diagonal
comparisons, the total refusal load is exactly `N`.

Relation: `Step` vs `SafeStep`. Closure: root. Property: additive refusal load. -/
theorem refLoad_batch_eq_N (srcs : List Trace)
    (h0 : ∀ a ∈ srcs, MetaSN_DM.kappaM a = 0) :
    (srcs.map (fun a => refLoad (batchForbidden a))).sum = srcs.length := by
  induction srcs with
  | nil => simp
  | cons hd tl ih =>
      rw [List.map_cons, List.sum_cons, List.length_cons,
        ih (fun a ha => h0 a (by simp [ha])),
        refLoad_batchForbidden_eq_one hd (h0 hd (by simp)), Nat.add_comm]

/-- The batch law in closed form for `N` copies of the diagonal source
`eqW void void`, given by the entry `void`: total refusal load `N`. -/
theorem refLoad_batch_replicate_eq_N (N : Nat) :
    ((List.replicate N void).map
      (fun a => refLoad (batchForbidden a))).sum = N := by
  rw [refLoad_batch_eq_N _ (fun a ha => by simp [List.eq_of_mem_replicate ha]),
    List.length_replicate]

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
#print axioms mem_diagonalForbiddenAt_iff
#print axioms refLoad_diagonalForbiddenAt
#print axioms mem_batchForbidden_iff
#print axioms refLoad_batchForbidden_recDelta_eq_two
#print axioms refLoad_batch_eq_sum

end OperatorKO7.Meta.SafeStep.RefusalLoad
