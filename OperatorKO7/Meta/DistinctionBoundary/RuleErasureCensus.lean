import OperatorKO7.Kernel

set_option autoImplicit false

/-!
# Rule erasure census: which kernel rules write, which record, and which erase

Manuscript anchor: the composite-of-fragments section of
`Rahnama_The_Distinction_Boundary`, and Weld 4 ("the tape is free; the bill is at
erasure") of `ROADMAP-09-six-welds-boundary-object.md`.

## What this module does

It classifies each of the eight root rules of the full kernel relation `Step` by
the **signed node delta** it induces, and it computes every delta rather than
asserting it. `nodeCount` counts constructors; `nodeDelta before after` is
`nodeCount after - nodeCount before` taken in `Int`, so erasure is negative and
growth is positive with no truncation.

The eight computed rows are:

| rule | signed node delta |
|---|---|
| `R_int_delta` | `-(nodeCount t + 1)` |
| `R_merge_void_left` | `-2` |
| `R_merge_void_right` | `-2` |
| `R_merge_cancel` | `-(nodeCount t + 1)` |
| `R_rec_zero` | `-(nodeCount s + 2)` |
| `R_eq_refl` | `-(2 * nodeCount a)` |
| `R_rec_succ` | `+ nodeCount s` |
| `R_eq_diff` | `+1` |

Six rules erase. Exactly two grow. Of the two that grow, `R_eq_diff` grows by
the constant one on every instance (`record_growth_constant_one`), and
`R_rec_succ` grows by an amount that is unbounded across its instances
(`duplicator_growth_unbounded`). `censusOf` records that three-way table, and
`census_erasing_iff`, `census_recordForming_iff`, and `census_writing_iff` prove
each row is exactly characterised by the computed deltas, so the classification
is forced by the arithmetic and not by the rule's name.

## The observation this mirrors, typed as an observation

At the node level this reproduces the program's two-loads shape: one load grows
without bound in the size of what is duplicated, and the other is a constant
per-event record. That is an **observation** about the census, an ANALOGY in the
project's claim typing, not a theorem about any cost model. Nothing here proves
a Landauer reading, a thermodynamic bound, or a complexity separation. The
physical reading stays behind the existing engine note on the irreversibility
floor, which is cited elsewhere and not restated here.

## Duplication fence (LASOT)

`nodeCount` is **not** a termination measure and is used as none. The
`R_rec_succ` row is stated as growth (`0 < nodeDelta`, and unbounded), and no
declaration in this module feeds it into an orientation, a well-founded
relation, a measure decrease, or any `Step` termination argument. The
duplication-stress obstruction is exactly what the row records.

## Claim boundaries

* Relation: `Step` (the full kernel relation, all eight unconditional rules).
* Closure: root only. Nothing here is closed under contexts, and nothing here
  is about `StepStar`, `SafeStep`, or any guarded subrelation.
* Strategy: not applicable; these are root-rule schemas, not a reduction order.
* Property: `metadata` (a census of the rule set), plus the two headline growth
  facts. No `SN`, `WN`, confluence, or normal-form claim is made or used.
* Trust: kernel-only. No axioms beyond Lean's baseline, no external artifact.

## Reported divergence from the roadmap sketch

The roadmap sketch reads the three classes as a partition of the rules by sign.
Sign alone gives only two classes, because `R_eq_diff` and `R_rec_succ` are both
positive. Worse, the two growing rules are **not** separated at the level of an
individual step: `R_rec_succ` with `s = void` writes exactly one node, which is
the record rule's constant. That is proved as
`instance_level_sign_does_not_separate`. The three-class census is therefore a
partition of rule **families** (each class characterised by a property holding of
all instances of a family), which is what `census_writing_iff` and
`census_recordForming_iff` state. The roadmap sketch also gave no number for the
`R_int_delta` row; the computed value is `-(nodeCount t + 1)`.
-/

namespace OperatorKO7.Meta.DistinctionBoundary.RuleErasureCensus

open Trace

/-! ## The counter and the signed delta -/

/-- Total constructor count of a trace: every node of the term tree counts one. -/
def nodeCount : Trace → Nat
  | void => 1
  | delta t => nodeCount t + 1
  | integrate t => nodeCount t + 1
  | merge a b => nodeCount a + nodeCount b + 1
  | app a b => nodeCount a + nodeCount b + 1
  | recΔ b s n => nodeCount b + nodeCount s + nodeCount n + 1
  | eqW a b => nodeCount a + nodeCount b + 1

/-- Every trace has at least one node. Used to sign the erasing rows. -/
theorem nodeCount_pos (t : Trace) : 0 < nodeCount t := by
  cases t <;> simp [nodeCount]

/-- The signed node delta of a rewrite, `after - before`, computed in `Int` so that
erasure is genuinely negative. `Nat` subtraction is deliberately avoided here: it
truncates, and truncation would hide exactly the erasing rows this census is about. -/
def nodeDelta (before after : Trace) : Int :=
  (nodeCount after : Int) - (nodeCount before : Int)

/-! ## The eight computed rows

One lemma per root rule, each stating the computed signed delta. These are the
R5 non-vacuity witnesses of the census: every row is a closed-form value, not an
inequality that could hold vacuously. -/

/-- Row 1, `R_int_delta`. Erases the whole redex; the erasure is unbounded in `t`. -/
theorem delta_R_int_delta (t : Trace) :
    nodeDelta (integrate (delta t)) void = -((nodeCount t : Int) + 1) := by
  simp only [nodeDelta, nodeCount]
  omega

/-- Row 2, `R_merge_void_left`. Erases the two unit nodes. -/
theorem delta_R_merge_void_left (t : Trace) :
    nodeDelta (merge void t) t = -2 := by
  simp only [nodeDelta, nodeCount]
  omega

/-- Row 3, `R_merge_void_right`. Erases the two unit nodes. -/
theorem delta_R_merge_void_right (t : Trace) :
    nodeDelta (merge t void) t = -2 := by
  simp only [nodeDelta, nodeCount]
  omega

/-- Row 4, `R_merge_cancel`. Erases one whole copy plus the `merge` node. -/
theorem delta_R_merge_cancel (t : Trace) :
    nodeDelta (merge t t) t = -((nodeCount t : Int) + 1) := by
  simp only [nodeDelta, nodeCount]
  omega

/-- Row 5, `R_rec_zero`. Erases the step argument, the `recΔ` node, and the `void` fuel. -/
theorem delta_R_rec_zero (b s : Trace) :
    nodeDelta (recΔ b s void) b = -((nodeCount s : Int) + 2) := by
  simp only [nodeDelta, nodeCount]
  omega

/-- Row 6, `R_eq_refl`. Erases both arguments; the erasure is unbounded in `a`. -/
theorem delta_R_eq_refl (a : Trace) :
    nodeDelta (eqW a a) void = -(2 * (nodeCount a : Int)) := by
  simp only [nodeDelta, nodeCount]
  omega

/-- Row 7, `R_rec_succ`. The duplicator. It **grows** the node count by exactly the
size of the duplicated step argument. Stated as growth only: see the duplication
fence in the module docstring. -/
theorem delta_R_rec_succ (b s n : Trace) :
    nodeDelta (recΔ b s (delta n)) (app s (recΔ b s n)) = (nodeCount s : Int) := by
  simp only [nodeDelta, nodeCount]
  omega

/-- Row 8, `R_eq_diff`. The record former. It grows the node count by exactly one,
for every pair of arguments. -/
theorem delta_R_eq_diff (a b : Trace) :
    nodeDelta (eqW a b) (integrate (merge a b)) = 1 := by
  simp only [nodeDelta, nodeCount]
  omega

/-! ## The sign of each row

Each row's sign, read off its computed delta. These are the statements the census
table is checked against; nothing below re-derives an arithmetic fact. -/

/-- `R_int_delta` erases. -/
theorem neg_R_int_delta (t : Trace) : nodeDelta (integrate (delta t)) void < 0 := by
  rw [delta_R_int_delta]
  have := nodeCount_pos t
  omega

/-- `R_merge_void_left` erases. -/
theorem neg_R_merge_void_left (t : Trace) : nodeDelta (merge void t) t < 0 := by
  rw [delta_R_merge_void_left]
  omega

/-- `R_merge_void_right` erases. -/
theorem neg_R_merge_void_right (t : Trace) : nodeDelta (merge t void) t < 0 := by
  rw [delta_R_merge_void_right]
  omega

/-- `R_merge_cancel` erases. -/
theorem neg_R_merge_cancel (t : Trace) : nodeDelta (merge t t) t < 0 := by
  rw [delta_R_merge_cancel]
  have := nodeCount_pos t
  omega

/-- `R_rec_zero` erases. -/
theorem neg_R_rec_zero (b s : Trace) : nodeDelta (recΔ b s void) b < 0 := by
  rw [delta_R_rec_zero]
  have := nodeCount_pos s
  omega

/-- `R_eq_refl` erases. -/
theorem neg_R_eq_refl (a : Trace) : nodeDelta (eqW a a) void < 0 := by
  rw [delta_R_eq_refl]
  have := nodeCount_pos a
  omega

/-- `R_rec_succ` grows, on every instance. Growth only: see the duplication fence. -/
theorem pos_R_rec_succ (b s n : Trace) :
    0 < nodeDelta (recΔ b s (delta n)) (app s (recΔ b s n)) := by
  rw [delta_R_rec_succ]
  have := nodeCount_pos s
  omega

/-- `R_eq_diff` grows, on every instance. -/
theorem pos_R_eq_diff (a b : Trace) :
    0 < nodeDelta (eqW a b) (integrate (merge a b)) := by
  rw [delta_R_eq_diff]
  omega

/-! ## The two headline theorems -/

/-- `delta`-towers, the witness family for unbounded duplication. -/
def deltaTower : Nat → Trace
  | 0 => void
  | n + 1 => delta (deltaTower n)

/-- A `delta`-tower of height `n` has exactly `n + 1` nodes. -/
theorem nodeCount_deltaTower (n : Nat) : nodeCount (deltaTower n) = n + 1 := by
  induction n with
  | zero => rfl
  | succ m ih => simp [deltaTower, nodeCount, ih]

/-- **Headline 1.** The duplicator's write is unbounded: for every `k` there is a step
argument `s` such that every `R_rec_succ` instance using `s` grows the node count by
more than `k`. Relation: `Step`, root, rule `R_rec_succ`. Property: growth only. -/
theorem duplicator_growth_unbounded (k : Nat) :
    ∃ s : Trace, ∀ b n : Trace,
      (k : Int) < nodeDelta (recΔ b s (delta n)) (app s (recΔ b s n)) := by
  refine ⟨deltaTower k, fun b n => ?_⟩
  rw [delta_R_rec_succ, nodeCount_deltaTower]
  omega

/-- **Headline 2.** The record rule's growth is the constant one, for **all** arguments,
equal or not. Relation: `Step`, root, rule `R_eq_diff`. Property: growth only. -/
theorem record_growth_constant_one (a b : Trace) :
    nodeDelta (eqW a b) (integrate (merge a b)) = 1 :=
  delta_R_eq_diff a b

/-! ## Naming the eight rules and tying the names to the live relation -/

/-- Names for the eight root rules of `Step`. -/
inductive RuleName : Type
  | R_int_delta
  | R_merge_void_left
  | R_merge_void_right
  | R_merge_cancel
  | R_rec_zero
  | R_rec_succ
  | R_eq_refl
  | R_eq_diff

/-- `RuleInstance r t u` says the pair `(t, u)` is an instance of the schema of the
named rule `r`. Each clause is the literal left- and right-hand side of the matching
`Step` constructor in `OperatorKO7/Kernel.lean`. -/
def RuleInstance : RuleName → Trace → Trace → Prop
  | .R_int_delta, t, u => ∃ x, t = integrate (delta x) ∧ u = void
  | .R_merge_void_left, t, u => ∃ x, t = merge void x ∧ u = x
  | .R_merge_void_right, t, u => ∃ x, t = merge x void ∧ u = x
  | .R_merge_cancel, t, u => ∃ x, t = merge x x ∧ u = x
  | .R_rec_zero, t, u => ∃ b s, t = recΔ b s void ∧ u = b
  | .R_rec_succ, t, u => ∃ b s n, t = recΔ b s (delta n) ∧ u = app s (recΔ b s n)
  | .R_eq_refl, t, u => ∃ a, t = eqW a a ∧ u = void
  | .R_eq_diff, t, u => ∃ a b, t = eqW a b ∧ u = integrate (merge a b)

/-- Every named row is inhabited, so no census row is vacuous. -/
theorem ruleInstance_nonempty (r : RuleName) : ∃ t u, RuleInstance r t u := by
  cases r
  · exact ⟨integrate (delta void), void, void, rfl, rfl⟩
  · exact ⟨merge void void, void, void, rfl, rfl⟩
  · exact ⟨merge void void, void, void, rfl, rfl⟩
  · exact ⟨merge void void, void, void, rfl, rfl⟩
  · exact ⟨recΔ void void void, void, void, void, rfl, rfl⟩
  · exact ⟨recΔ void void (delta void), app void (recΔ void void void),
      void, void, void, rfl, rfl⟩
  · exact ⟨eqW void void, void, void, rfl, rfl⟩
  · exact ⟨eqW void void, integrate (merge void void), void, void, rfl, rfl⟩

/-- Operational completeness (LASOT K21): the eight named schemas are **exactly** the
live root relation `Step`, in both directions. The census therefore classifies the
kernel's own rules and not a hand-written proxy list. -/
theorem step_iff_exists_rule (t u : Trace) : Step t u ↔ ∃ r : RuleName, RuleInstance r t u := by
  constructor
  · intro h
    cases h
    · exact ⟨.R_int_delta, _, rfl, rfl⟩
    · exact ⟨.R_merge_void_left, _, rfl, rfl⟩
    · exact ⟨.R_merge_void_right, _, rfl, rfl⟩
    · exact ⟨.R_merge_cancel, _, rfl, rfl⟩
    · exact ⟨.R_rec_zero, _, _, rfl, rfl⟩
    · exact ⟨.R_rec_succ, _, _, _, rfl, rfl⟩
    · exact ⟨.R_eq_refl, _, rfl, rfl⟩
    · exact ⟨.R_eq_diff, _, _, rfl, rfl⟩
  · rintro ⟨r, hr⟩
    cases r
    · obtain ⟨_, rfl, rfl⟩ := hr; exact Step.R_int_delta _
    · obtain ⟨_, rfl, rfl⟩ := hr; exact Step.R_merge_void_left _
    · obtain ⟨_, rfl, rfl⟩ := hr; exact Step.R_merge_void_right _
    · obtain ⟨_, rfl, rfl⟩ := hr; exact Step.R_merge_cancel _
    · obtain ⟨_, _, rfl, rfl⟩ := hr; exact Step.R_rec_zero _ _
    · obtain ⟨_, _, _, rfl, rfl⟩ := hr; exact Step.R_rec_succ _ _ _
    · obtain ⟨_, rfl, rfl⟩ := hr; exact Step.R_eq_refl _
    · obtain ⟨_, _, rfl, rfl⟩ := hr; exact Step.R_eq_diff _ _

/-! ## The census table and its exactness -/

/-- The census classes, read at the level of rule families. -/
inductive Census : Type
  /-- Every instance strictly decreases the node count. -/
  | erasing
  /-- Every instance increases the node count by exactly one. -/
  | recordForming
  /-- Every instance increases the node count, and the increase is unbounded. -/
  | writing

/-- The census table. Every entry is the class forced by the computed delta of that
row; see `census_erasing_iff`, `census_recordForming_iff`, and `census_writing_iff`. -/
def censusOf : RuleName → Census
  | .R_int_delta => .erasing
  | .R_merge_void_left => .erasing
  | .R_merge_void_right => .erasing
  | .R_merge_cancel => .erasing
  | .R_rec_zero => .erasing
  | .R_rec_succ => .writing
  | .R_eq_refl => .erasing
  | .R_eq_diff => .recordForming

/-- Table soundness for the erasing rows: an `erasing` entry really erases, on every
instance of that row. -/
theorem ruleInstance_erasing_neg {r : RuleName} {t u : Trace} (hi : RuleInstance r t u)
    (h : censusOf r = Census.erasing) : nodeDelta t u < 0 := by
  cases r
  · obtain ⟨_, rfl, rfl⟩ := hi; exact neg_R_int_delta _
  · obtain ⟨_, rfl, rfl⟩ := hi; exact neg_R_merge_void_left _
  · obtain ⟨_, rfl, rfl⟩ := hi; exact neg_R_merge_void_right _
  · obtain ⟨_, rfl, rfl⟩ := hi; exact neg_R_merge_cancel _
  · obtain ⟨_, _, rfl, rfl⟩ := hi; exact neg_R_rec_zero _ _
  · simp [censusOf] at h
  · obtain ⟨_, rfl, rfl⟩ := hi; exact neg_R_eq_refl _
  · simp [censusOf] at h

/-- Table soundness for the growing rows: a non-`erasing` entry really grows, on every
instance of that row. -/
theorem ruleInstance_growing_pos {r : RuleName} {t u : Trace} (hi : RuleInstance r t u)
    (h : censusOf r ≠ Census.erasing) : 0 < nodeDelta t u := by
  cases r
  · exact absurd rfl h
  · exact absurd rfl h
  · exact absurd rfl h
  · exact absurd rfl h
  · exact absurd rfl h
  · obtain ⟨_, _, _, rfl, rfl⟩ := hi; exact pos_R_rec_succ _ _ _
  · exact absurd rfl h
  · obtain ⟨_, _, rfl, rfl⟩ := hi; exact pos_R_eq_diff _ _

/-- A concrete `R_rec_succ` instance whose write is exactly one node. -/
theorem recSucc_unit_instance :
    RuleInstance .R_rec_succ (recΔ void void (delta void)) (app void (recΔ void void void)) :=
  ⟨void, void, void, rfl, rfl⟩

/-- That instance's delta: exactly one, which is the record rule's constant. -/
theorem recSucc_unit_delta_one :
    nodeDelta (recΔ void void (delta void)) (app void (recΔ void void void)) = 1 := by
  rw [delta_R_rec_succ]
  rfl

/-- A concrete `R_eq_diff` instance, used to refute the erasing and writing rows. -/
theorem eqDiff_unit_instance :
    RuleInstance RuleName.R_eq_diff (eqW void void) (integrate (merge void void)) :=
  ⟨void, void, rfl, rfl⟩

/-- A concrete `R_rec_succ` instance whose write is two nodes. -/
theorem recSucc_two_instance :
    RuleInstance .R_rec_succ (recΔ void (delta void) (delta void))
      (app (delta void) (recΔ void (delta void) void)) :=
  ⟨void, delta void, void, rfl, rfl⟩

/-- That instance's delta: exactly two, so the duplicator's delta is not constant. -/
theorem recSucc_two_delta_two :
    nodeDelta (recΔ void (delta void) (delta void))
      (app (delta void) (recΔ void (delta void) void)) = 2 := by
  rw [delta_R_rec_succ]
  rfl

/-- Exactness of the erasing rows: a row is marked `erasing` exactly when every instance
of that row strictly decreases the node count. -/
theorem census_erasing_iff (r : RuleName) :
    censusOf r = Census.erasing ↔ ∀ t u, RuleInstance r t u → nodeDelta t u < 0 := by
  constructor
  · intro h t u hi
    exact ruleInstance_erasing_neg hi h
  · intro h
    cases r
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · have hlt := h _ _ recSucc_unit_instance
      rw [recSucc_unit_delta_one] at hlt
      exact absurd hlt (by omega)
    · rfl
    · have hlt := h _ _ eqDiff_unit_instance
      rw [delta_R_eq_diff] at hlt
      exact absurd hlt (by omega)

/-- Exactness of the record row: a row is marked `recordForming` exactly when every
instance of that row grows the node count by exactly one. `R_rec_succ` fails this at
`s = delta void`, which is why the duplicator is not a record former. -/
theorem census_recordForming_iff (r : RuleName) :
    censusOf r = Census.recordForming ↔ ∀ t u, RuleInstance r t u → nodeDelta t u = 1 := by
  constructor
  · intro h t u hi
    cases r
    · simp [censusOf] at h
    · simp [censusOf] at h
    · simp [censusOf] at h
    · simp [censusOf] at h
    · simp [censusOf] at h
    · simp [censusOf] at h
    · simp [censusOf] at h
    · obtain ⟨a, b, rfl, rfl⟩ := hi
      exact delta_R_eq_diff a b
  · intro h
    cases r
    case R_rec_succ =>
      have heq := h _ _ recSucc_two_instance
      rw [recSucc_two_delta_two] at heq
      exact absurd heq (by omega)
    case R_eq_diff => rfl
    all_goals
      obtain ⟨tw, uw, hi⟩ := ruleInstance_nonempty _
      have heq := h tw uw hi
      have hneg : nodeDelta tw uw < 0 := ruleInstance_erasing_neg hi rfl
      exact absurd heq (by omega)

/-- Exactness of the writing row: a row is marked `writing` exactly when its growth is
unbounded across its instances. This is the sense in which `R_rec_succ` is the unbounded
writer, and it is a statement about the family, not about any single step. -/
theorem census_writing_iff (r : RuleName) :
    censusOf r = Census.writing ↔
      ∀ k : Nat, ∃ t u, RuleInstance r t u ∧ (k : Int) < nodeDelta t u := by
  constructor
  · intro h k
    cases r
    · simp [censusOf] at h
    · simp [censusOf] at h
    · simp [censusOf] at h
    · simp [censusOf] at h
    · simp [censusOf] at h
    · refine ⟨recΔ void (deltaTower k) (delta void),
        app (deltaTower k) (recΔ void (deltaTower k) void),
        ⟨void, deltaTower k, void, rfl, rfl⟩, ?_⟩
      rw [delta_R_rec_succ, nodeCount_deltaTower]
      omega
    · simp [censusOf] at h
    · simp [censusOf] at h
  · intro h
    cases r
    case R_rec_succ => rfl
    case R_eq_diff =>
      obtain ⟨tw, uw, hi, hlt⟩ := h 1
      obtain ⟨a, b, rfl, rfl⟩ := hi
      rw [delta_R_eq_diff] at hlt
      exact absurd hlt (by omega)
    all_goals
      obtain ⟨tw, uw, hi, hlt⟩ := h 0
      have hneg : nodeDelta tw uw < 0 := ruleInstance_erasing_neg hi rfl
      exact absurd hlt (by omega)

/-- `R_rec_succ` is the unique row of the census table marked `writing`. -/
theorem writing_row_unique (r : RuleName) :
    censusOf r = Census.writing ↔ r = RuleName.R_rec_succ := by
  cases r <;> simp [censusOf]

/-- `R_eq_diff` is the unique row of the census table marked `recordForming`. -/
theorem recordForming_row_unique (r : RuleName) :
    censusOf r = Census.recordForming ↔ r = RuleName.R_eq_diff := by
  cases r <;> simp [censusOf]

/-! ## The partition, read back onto the live relation -/

/-- **Census partition.** Every step of the full kernel relation is an instance of a named
row, and that row's census class already determines the sign of the step's node delta.
Relation: `Step`. Closure: root. Property: metadata. -/
theorem step_census_partition {t u : Trace} (h : Step t u) :
    ∃ r : RuleName, RuleInstance r t u ∧
      ((censusOf r = Census.erasing ∧ nodeDelta t u < 0) ∨
        (censusOf r ≠ Census.erasing ∧ 0 < nodeDelta t u)) := by
  obtain ⟨r, hr⟩ := (step_iff_exists_rule t u).mp h
  refine ⟨r, hr, ?_⟩
  by_cases he : censusOf r = Census.erasing
  · exact Or.inl ⟨he, ruleInstance_erasing_neg hr he⟩
  · exact Or.inr ⟨he, ruleInstance_growing_pos hr he⟩

/-- No kernel root rule is node-count neutral: every step either erases or writes. -/
theorem step_nodeDelta_ne_zero {t u : Trace} (h : Step t u) : nodeDelta t u ≠ 0 := by
  obtain ⟨_, _, hcase⟩ := step_census_partition h
  rcases hcase with ⟨_, hneg⟩ | ⟨_, hpos⟩
  · omega
  · omega

/-- The growing steps are exactly the duplicator instances and the record instances.
The reverse direction needs no step hypothesis: both shapes grow by computation. -/
theorem step_writes_iff_recSucc_or_eqDiff {t u : Trace} (h : Step t u) :
    0 < nodeDelta t u ↔
      RuleInstance RuleName.R_rec_succ t u ∨ RuleInstance RuleName.R_eq_diff t u := by
  constructor
  · intro hpos
    obtain ⟨r, hr⟩ := (step_iff_exists_rule t u).mp h
    cases r
    · exact absurd (ruleInstance_erasing_neg hr rfl) (by omega)
    · exact absurd (ruleInstance_erasing_neg hr rfl) (by omega)
    · exact absurd (ruleInstance_erasing_neg hr rfl) (by omega)
    · exact absurd (ruleInstance_erasing_neg hr rfl) (by omega)
    · exact absurd (ruleInstance_erasing_neg hr rfl) (by omega)
    · exact Or.inl hr
    · exact absurd (ruleInstance_erasing_neg hr rfl) (by omega)
    · exact Or.inr hr
  · rintro (hr | hr)
    · exact ruleInstance_growing_pos hr (by simp [censusOf])
    · exact ruleInstance_growing_pos hr (by simp [censusOf])

/-! ## Non-triviality and the reported divergence -/

/-- Non-triviality: the census separates at least two classes with named live steps, one
erasing and one writing. -/
theorem census_separation_witnesses :
    (∃ t u, Step t u ∧ nodeDelta t u < 0) ∧ (∃ t u, Step t u ∧ 0 < nodeDelta t u) := by
  constructor
  · refine ⟨merge void void, void, Step.R_merge_void_left void, ?_⟩
    rw [delta_R_merge_void_left]
    omega
  · refine ⟨eqW void void, integrate (merge void void), Step.R_eq_diff void void, ?_⟩
    rw [delta_R_eq_diff]
    omega

/-- **Reported divergence.** The three census classes partition rule families, not single
steps. The duplicator at `s = void` writes exactly one node, the record rule's constant,
so no predicate on the delta of one step can separate the writer from the record former.
The separation lives at the family level, in `census_writing_iff` and
`census_recordForming_iff`. -/
theorem instance_level_sign_does_not_separate :
    RuleInstance RuleName.R_rec_succ (recΔ void void (delta void))
        (app void (recΔ void void void)) ∧
      nodeDelta (recΔ void void (delta void)) (app void (recΔ void void void)) = 1 ∧
      nodeDelta (eqW void void) (integrate (merge void void)) = 1 :=
  ⟨recSucc_unit_instance, recSucc_unit_delta_one, delta_R_eq_diff void void⟩

end OperatorKO7.Meta.DistinctionBoundary.RuleErasureCensus
