import OperatorKO7.Meta.RecordEmissionNecessity

/-!
# Record emission along the canonical rewrite sequence

`Meta/RecordEmissionNecessity.lean` proves the positional theorem: a right-hand side that
emits a record frame and preserves the recursive generator carries two distinct generator
occurrences. The manuscript states a *dynamic* definition of generator preservation, over
maximal rewrite sequences from `F(x, y, S^k(0))`, and then proves the positional theorem
instead, leaving the dynamic definition unused.

This module supplies the missing link. It defines the canonical rewrite sequence of the
record-emitting schema, proves consecutive stages are related by the step rule, and proves
that every positive stage simultaneously carries a frame-slot generator occurrence and an
active-site generator occurrence at distinct positions. That is the manuscript's dynamic
condition, discharged from the positional theorem.

Relation: `RecordStep`, the step rule of the record-emitting schema, closed under the
frame context.
Closure: one-step for `recordStep_canonicalStage_succ`; stage-indexed for the trace results.
Strategy: leftmost-innermost is forced, since each stage has one redex.
Trust: kernel-only. No `sorry`, no `admit`, no new `axiom`, no native reduction.
-/

set_option autoImplicit false

open OperatorKO7.StepDuplicating.StepDuplicatingSchema
open OperatorKO7.StepDuplicating.StepDuplicatingSchema.RecordTerm

namespace OperatorKO7.Meta.RecordEmissionDynamic

/-! ### The canonical rewrite sequence -/

/-- The counter term of height `n`. -/
def natToCounter : Nat → RecordCounter
  | 0 => .zero
  | n + 1 => .succ (natToCounter n)

/-- Wrap a term in `i` emitted record frames. -/
def frameStack : Nat → RecordTerm → RecordTerm
  | 0, t => t
  | i + 1, t => .frame .gen (frameStack i t)

/-- The canonical stage after `i` firings from counter height `k`: `i` accumulated record
frames wrapped around the live active site whose counter has dropped to `k - i`. -/
def canonicalStage (i k : Nat) : RecordTerm :=
  frameStack i (.active .base .gen (natToCounter (k - i)))

/--
The step rule of the record-emitting schema, closed under the frame context: firing at the
active site consumes one counter layer and emits one record frame.
-/
inductive RecordStep : RecordTerm → RecordTerm → Prop
  | fire : ∀ (t : RecordTerm) (c : RecordCounter),
      RecordStep (.active t .gen (.succ c)) (.frame .gen (.active t .gen c))
  | underFrame : ∀ u v : RecordTerm,
      RecordStep u v → RecordStep (.frame .gen u) (.frame .gen v)

/-- Pushing one frame through a frame stack. -/
theorem frameStack_frame (i : Nat) (t : RecordTerm) :
    frameStack i (.frame .gen t) = frameStack (i + 1) t := by
  induction i with
  | zero => rfl
  | succ k ih =>
      show RecordTerm.frame .gen (frameStack k (.frame .gen t))
        = RecordTerm.frame .gen (frameStack (k + 1) t)
      rw [ih]

/-- The step rule fires under any number of accumulated frames. -/
theorem recordStep_frameStack (i : Nat) (u v : RecordTerm) (h : RecordStep u v) :
    RecordStep (frameStack i u) (frameStack i v) := by
  induction i with
  | zero => exact h
  | succ j ih => exact RecordStep.underFrame _ _ ih

/--
Proves: consecutive canonical stages are related by the step rule, for every stage below
the starting counter height.
-/
theorem recordStep_canonicalStage_succ (i k : Nat) (hik : i < k) :
    RecordStep (canonicalStage i k) (canonicalStage (i + 1) k) := by
  have hcounter : natToCounter (k - i) = .succ (natToCounter (k - (i + 1))) := by
    have h : k - i = (k - (i + 1)) + 1 := by omega
    rw [h]
    rfl
  simp only [canonicalStage, hcounter]
  rw [← frameStack_frame i (.active .base .gen (natToCounter (k - (i + 1))))]
  exact recordStep_frameStack i _ _ (RecordStep.fire _ _)

/-! ### Every positive stage carries both generator occurrences -/

/--
Proves: from stage one onward the canonical state contains an emitted record frame.
-/
theorem canonicalStage_emitsNewRecordFrame (i k : Nat) (hi : 1 ≤ i) :
    emitsNewRecordFrame (canonicalStage i k) := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  show emitsNewRecordFrame (frameStack (j + 1) _)
  exact trivial

/--
Proves: every canonical state preserves the recursive generator, since the live active site
survives under the accumulated frames.
-/
theorem preservesRecursiveGenerator_frameStack
    (i : Nat) (t : RecordTerm) (h : preservesRecursiveGenerator t) :
    preservesRecursiveGenerator (frameStack i t) := by
  induction i with
  | zero => exact h
  | succ j ih => exact ih

theorem canonicalStage_preservesRecursiveGenerator (i k : Nat) :
    preservesRecursiveGenerator (canonicalStage i k) :=
  preservesRecursiveGenerator_frameStack i _ trivial

/--
Intent: **the dynamic record-emission theorem**. Along the canonical rewrite sequence from
counter height `k`, every stage from the first firing onward carries the generator
simultaneously in a frame slot and at an active-site generator position, at two distinct
positions.

This is the manuscript's dynamic definition of generator preservation, discharged from the
positional theorem of `Meta/RecordEmissionNecessity.lean` rather than assumed.

Relation: `RecordStep`.
Closure: stage-indexed along the canonical sequence.
Trust: kernel-only.
-/
theorem canonicalStage_carries_frame_and_active_generator_positions
    (i k : Nat) (hi : 1 ≤ i) :
    ∃ p q,
      p ≠ q ∧
      p ∈ generatorPositions (canonicalStage i k) ∧
      q ∈ generatorPositions (canonicalStage i k) ∧
      p.isFrameGeneratorPos ∧
      q.isActiveGeneratorPos :=
  architectural_necessity_of_payload_duplication
    (canonicalStage_emitsNewRecordFrame i k hi)
    (canonicalStage_preservesRecursiveGenerator i k)

/--
Proves: the dynamic condition holds at every stage of every canonical sequence of positive
counter height, which is the universally quantified form the manuscript's definition uses.
-/
theorem every_positive_stage_duplicates_the_generator (k : Nat) :
    ∀ i, 1 ≤ i → i ≤ k →
      ∃ p q,
        p ≠ q ∧
        p ∈ generatorPositions (canonicalStage i k) ∧
        q ∈ generatorPositions (canonicalStage i k) := by
  intro i hi _
  obtain ⟨p, q, hpq, hp, hq, _, _⟩ :=
    canonicalStage_carries_frame_and_active_generator_positions i k hi
  exact ⟨p, q, hpq, hp, hq⟩

/--
Proves: the canonical sequence of height `k` really runs for `k` firings, so the dynamic
statement quantifies over a non-empty stage range (Gate R5).
-/
theorem canonicalStage_sequence_is_inhabited (k : Nat) (hk : 1 ≤ k) :
    RecordStep (canonicalStage 0 k) (canonicalStage 1 k) :=
  recordStep_canonicalStage_succ 0 k (by omega)

end OperatorKO7.Meta.RecordEmissionDynamic
