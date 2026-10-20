import OperatorKO7.Meta.OperationalInexpressibility.RepeatDepthLicense
import OperatorKO7.Meta.DistinctionBoundary.ObservationalDiagonalFork

set_option autoImplicit false

/-!
# Comparison and recurrence have the same finite record cost

Proof graph: `Audit/ledgers/operational-inexpressibility/TWO-VOIDS-PROOF-GRAPH.md`, V4.
The same side channel is sufficient for correct comparison of every pair exactly when it
licenses repeat depth. The existing rank channel therefore attains both minima.
This composes the comparison theorem with the existing capacity theorem; it does not reprove
fiber capacity or the Church-family results of the Higher Order manuscript.
Relation: observer factorization on `Fin N`; no rewriting relation.
Trust: kernel-only. Empty horizons and zero-symbol alphabets are included.
-/

namespace OperatorKO7.Meta.OperationalInexpressibility.ComparisonRecurrencePrice

open OperatorKO7.Meta.OperationalInexpressibility.DirectGrammarBoundary
open OperatorKO7.Meta.OperationalInexpressibility.ObserverKernel
open OperatorKO7.Meta.OperationalInexpressibility.FiberDeficit
open OperatorKO7.Meta.OperationalInexpressibility.RepeatDepthLicense
open OperatorKO7.Meta.DistinctionBoundary.ObservationalDiagonalFork

#check @joint_decoder_exists_iff_injective
#check @repeatDepth_injective_on_fiber
#check @repeatDepth_lt_maxFiberCard
#check @additional_channel_card_lower_bound

/-- For the same channel, correct pair comparison is equivalent to recording exact repeat
 depth. A channel adequate only for the Boolean repeat-status target need not suffice. -/
theorem comparison_iff_repeatDepth {N : ℕ} {Q R : Type*} [DecidableEq Q]
    (obs : Fin N → Q) (r : Fin N → R) :
    (∃ decoder, ObservedDecoderCorrect (fun i => (obs i, r i)) decoder) ↔
      FactorsThrough (fun i => (obs i, r i)) (repeatDepth obs) := by
  rw [joint_decoder_exists_iff_injective]
  constructor
  · intro hinj i j hij
    exact congrArg (repeatDepth obs) (hinj hij)
  · intro h i j hij
    exact repeatDepth_injective_on_fiber obs (congrArg Prod.fst hij) (h hij)

/-- The exact rank channel supports correct comparison as well as exact repeat depth. -/
theorem rank_channel_supports_comparison {N : ℕ} {Q : Type*} [DecidableEq Q]
    (obs : Fin N → Q) :
    ∃ decoder, ObservedDecoderCorrect (fun i => (obs i, fiberRankChannel obs i)) decoder :=
  (comparison_iff_repeatDepth obs (fiberRankChannel obs)).mpr
    (fiberRank_channel_licenses_repeatDepth obs)

/-- Every comparison channel has at least as many symbols as the largest observation fiber. -/
theorem comparison_channel_card_lower {N : ℕ} {Q R : Type*} [DecidableEq Q] [Fintype R]
    (obs : Fin N → Q) (r : Fin N → R)
    (h : ∃ decoder, ObservedDecoderCorrect (fun i => (obs i, r i)) decoder) :
    maxFiberCard obs ≤ Fintype.card R := by
  have hbound := additional_channel_card_lower_bound obs (repeatDepth obs) r
    ((comparison_iff_repeatDepth obs r).mp h)
  rwa [repeatDepth_fiberMultiplicity_eq_maxFiberCard] at hbound

/-- Every alphabet at least as large as the maximum fiber supports exact repeat depth. -/
theorem repeatDepth_channel_of_capacity {N : ℕ} {Q : Type*} [DecidableEq Q]
    (obs : Fin N → Q) (k : ℕ) (hk : maxFiberCard obs ≤ k) :
    ∃ r : Fin N → Fin k, FactorsThrough (fun i => (obs i, r i)) (repeatDepth obs) := by
  let r : Fin N → Fin k := fun i =>
    ⟨repeatDepth obs i, (repeatDepth_lt_maxFiberCard obs i).trans_le hk⟩
  refine ⟨r, ?_⟩
  intro i j hij
  exact congrArg (fun z : Q × Fin k => z.2.val) hij

/-- Two-sided capacity, for an arbitrary finite horizon and any observation codomain. -/
theorem comparison_channel_exists_iff {N : ℕ} {Q : Type*} [DecidableEq Q]
    (obs : Fin N → Q) (k : ℕ) :
    (∃ r : Fin N → Fin k, ∃ decoder,
      ObservedDecoderCorrect (fun i => (obs i, r i)) decoder) ↔ maxFiberCard obs ≤ k := by
  constructor
  · rintro ⟨r, hr⟩
    simpa using comparison_channel_card_lower obs r hr
  · intro hk
    obtain ⟨r, hr⟩ := repeatDepth_channel_of_capacity obs k hk
    exact ⟨r, (comparison_iff_repeatDepth obs r).mpr hr⟩

/-- The feasible alphabet sizes for comparison and exact recurrence recording coincide. -/
theorem comparison_and_recurrence_same_alphabets {N : ℕ} {Q : Type*} [DecidableEq Q]
    (obs : Fin N → Q) (k : ℕ) :
    (∃ r : Fin N → Fin k, ∃ decoder,
      ObservedDecoderCorrect (fun i => (obs i, r i)) decoder) ↔
    (∃ r : Fin N → Fin k,
      FactorsThrough (fun i => (obs i, r i)) (repeatDepth obs)) := by
  constructor
  · rintro ⟨r, hr⟩
    exact ⟨r, (comparison_iff_repeatDepth obs r).mp hr⟩
  · rintro ⟨r, hr⟩
    exact ⟨r, (comparison_iff_repeatDepth obs r).mpr hr⟩

/-- V4: both tasks have the same least symbol count, with an attained minimum. -/
theorem comparison_minimum_eq_recurrence {N : ℕ} {Q : Type*} [DecidableEq Q]
    (obs : Fin N → Q) :
    IsLeast {k : ℕ | ∃ r : Fin N → Fin k, ∃ decoder,
      ObservedDecoderCorrect (fun i => (obs i, r i)) decoder} (maxFiberCard obs) := by
  constructor
  · exact (comparison_channel_exists_iff obs _).mpr le_rfl
  · intro k hk
    exact (comparison_channel_exists_iff obs k).mp hk

end OperatorKO7.Meta.OperationalInexpressibility.ComparisonRecurrencePrice
