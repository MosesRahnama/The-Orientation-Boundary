import OperatorKO7.Meta.RDRSDescentLens
import OperatorKO7.Meta.RDRSBoundaryBottleneck

set_option autoImplicit false

/-!
# RDRS Search-Budget Invariance Inside Fixed W0 (Milestone U5, file 2/2)

Roadmap source: `OperatorKO7/Expansion/Universal_Payload_Sensitive_Direct_Measures_Roadmap.md`
Milestone U5 -- search-budget invariance inside fixed W0.

## Audit slots (Lean Development Bible W8 / R4)

```
Relation:  N/A. The invariance is about a function
           `search : Nat -> RDRSLayeredWitness R` and its boundary
           admissibility tag, not about rewriting steps.
Closure:   N/A.
Strategy:  N/A. The "search" abstraction is intentionally opaque; no
           assumption about its implementation or termination is made.
Trust:     kernel-only.
Scope:     invariance is asserted ONLY inside the fixed W0 layer
           (via the `IsW0Bounded` precondition). No claim about W1 or
           cross-layer searches. No claim about full DP / MSPO / WPO.
```

A search procedure inside the W0 (direct payload-sensitive grammar)
layer is, at this layer of generality, a `Nat`-indexed enumeration of
candidate W0 witnesses: each budget value produces one candidate
witness, all tagged at layer W0. The roadmap's "search inside fixed
W0 cannot cross the boundary" line is recorded structurally as the
invariance of `κ_boundary` under the search budget.

## Theorem-name adequacy note

* `search_budget_invariance` -- "invariance" here means the boundary
  admissibility tag does not vary with the budget; **not** a claim
  that the search procedure terminates or that its output is in any
  semantic sense invariant.
* `boundary_invariant_under_W0_budget` -- the boundary admissibility
  tag is invariant across budgets; again, structural-tag-level only.
* `W0_budget_invariance_does_not_block_W2` -- documents that the W0
  search-budget invariance and a separately exhibited W2 witness's
  admissibility are independent verdicts.

## Non-vacuity status

* `W0Search R` is an `abbrev` for `Nat -> RDRSLayeredWitness R`. Under
  `Nonempty (RDRSLayeredWitness R)` (which holds unconditionally via
  `W1_construction`), `W0Search R` is inhabited by the constant
  function. The constant function does **not** satisfy `IsW0Bounded`
  unless its output is tagged W0; the constant-W0-direct witness with
  the `abstain` certificate satisfies `IsW0Bounded`.
* `IsW0Bounded` non-emptiness is shipped below.

Scope: no `sorry`, `admit`, `axiom`, or production `example :`.
-/

namespace OperatorKO7.RDRSSearchBudgetInvariance

open OperatorKO7.RDRSDescentLens
open OperatorKO7.RDRSBoundaryBottleneck
open OperatorKO7.RDRSMethodCertificate

variable {B S N T : Type} {R : RDRSStep B S N T}

/-- A search procedure inside W0: a `Nat`-indexed enumeration of
candidate W0 witnesses. The budget `Nat` is the search depth or
resource bound.

Declared as `abbrev` so that `search budget` reduces to a function
application of the underlying `Nat → RDRSLayeredWitness R` at use
sites. -/
abbrev W0Search {B S N T : Type} (R : RDRSStep B S N T) :=
  Nat → RDRSLayeredWitness R

/-- A search is W0-bounded if every witness it produces, at every
budget, is tagged W0.

**Audit slots.**

* **Proves:** N/A (definition).
* **Does not prove:** that any concrete search implementation
  satisfies this property; the caller must establish it.
* **Trust:** kernel-only. -/
def IsW0Bounded {B S N T : Type} {R : RDRSStep B S N T}
    (search : W0Search R) : Prop :=
  ∀ budget, (search budget).layer = WitnessLayer.W0

/-- Canonical W0-bounded search: the constant function returning the
W0-tagged `abstain` certificate for every budget. Inhabitation
witness for `{search : W0Search R // IsW0Bounded search}`. -/
def W0Search.constantAbstain : W0Search R :=
  fun _ =>
    RDRSLayeredWitness.W0_direct NormalizedDescentCertificate.abstain

/-- The canonical constant search is W0-bounded. -/
theorem W0Search.constantAbstain_isW0Bounded :
    IsW0Bounded (W0Search.constantAbstain (R := R)) :=
  fun _ => rfl

/-- **Non-vacuity (unconditional):** there is at least one W0-bounded
search procedure. Witnessed by the constant `abstain` search. -/
theorem W0Search_W0Bounded_nonempty :
    ∃ search : W0Search R, IsW0Bounded search :=
  ⟨W0Search.constantAbstain,
    W0Search.constantAbstain_isW0Bounded (R := R)⟩

/-- **Search-budget invariance inside fixed W0.**

A W0-bounded search procedure never produces a boundary-admissible
witness, regardless of the budget. The boundary cannot be crossed by
enlarging the search budget within W0.

This is the structural content of the roadmap's "search inside fixed
W0 cannot cross the boundary" line: `κ_boundary` is uniformly `false`
on a W0-bounded search, with no dependence on the budget.

**Audit slots.**

* **Proves:** `kappa_boundary (search budget) = false` for any
  budget, under `IsW0Bounded search`.
* **Does not prove:** termination of `search`, or anything about W1
  / cross-layer searches; does not prove `R` terminates.
* **Trust:** kernel-only (extraction). -/
theorem search_budget_invariance
    (search : W0Search R) (h : IsW0Bounded search) (budget : Nat) :
    kappa_boundary (search budget) = false :=
  W0_not_boundary_admissible (search budget) (h budget)

/-- **Boundary verdict is invariant under the W0 search budget.**

For any two budgets, a W0-bounded search produces witnesses with the
same boundary-admissibility verdict (both `false`). The boundary is
indifferent to the W0 search budget.

**Audit slots.**

* **Proves:** `kappa_boundary (search b1) = kappa_boundary (search b2)`.
* **Does not prove:** that the witnesses themselves are equal across
  budgets; only their boundary tag agrees.
* **Trust:** kernel-only. -/
theorem boundary_invariant_under_W0_budget
    (search : W0Search R) (h : IsW0Bounded search)
    (budget1 budget2 : Nat) :
    kappa_boundary (search budget1) = kappa_boundary (search budget2) := by
  rw [search_budget_invariance search h budget1,
      search_budget_invariance search h budget2]

/-- **W0 budget invariance does not block the W2 layer.**

The W0 search-budget invariance is consistent with a separately
exhibited W2 witness succeeding at the boundary. The two verdicts
are independent: W0 budget search remains blocked at every budget,
and the W2 projection-transaction witness remains admissible.

This is the precise sense in which the boundary is "boundary-
relative": admissibility is determined by the layer of the witness,
not by the budget of any W0-bounded search procedure.

**Audit slots.**

* **Proves:** the conjunction of W0-search blocked and a
  separately-supplied W2 witness admissible.
* **Does not prove:** that the W2 witness was produced by the search;
  the two are independent.
* **Trust:** kernel-only. -/
theorem W0_budget_invariance_does_not_block_W2
    (search : W0Search R) (hSearch : IsW0Bounded search)
    (BB : BoundaryBottleneck R) (budget : Nat) :
    kappa_boundary (search budget) = false ∧
    kappa_boundary BB.w2_witness = true := by
  refine ⟨search_budget_invariance search hSearch budget, ?_⟩
  exact W2_boundary_admissible BB.w2_witness BB.w2_at_W2

/-- Audit anchor for the U5 search-budget-invariance surface. -/
def rdrs_search_budget_invariance_anchor : String :=
  "OperatorKO7.RDRSSearchBudgetInvariance.search_budget_invariance"

end OperatorKO7.RDRSSearchBudgetInvariance
