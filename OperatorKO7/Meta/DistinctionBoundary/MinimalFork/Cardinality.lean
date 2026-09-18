import OperatorKO7.Meta.DistinctionBoundary.MinimalFork.Core

/-!
# Absolute cardinality lower bound for a nonjoinable peak

The results in this file are ARS-generic. They assume neither a comparator nor a
TRS signature. They prove only the state-cardinality minimum of a nonjoinable
one-step peak; syntactic symbol/rule minimality is proved separately.

Relation: arbitrary caller-supplied one-step relation `R`.
Closure: `Quantitative.Reach R` through `Joinable`.
Property: pairwise distinctness and finite carrier lower bound.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.DistinctionBoundary.MinimalFork

open OperatorKO7.Meta.DistinctionBoundary.Quantitative

universe u

/-- Any nonjoinable one-step peak contains three pairwise distinct states. -/
theorem nonjoinable_peak_has_three_distinct_states
    {T : Type u} {R : T → T → Prop} {s l r : T}
    (hsl : R s l) (hsr : R s r) (hnj : ¬ Joinable R l r) :
    s ≠ l ∧ s ≠ r ∧ l ≠ r := by
  have hlr : l ≠ r := by
    intro h
    apply hnj
    subst r
    exact ⟨l, reach_refl l, reach_refl l⟩
  have hsl_ne : s ≠ l := by
    intro h
    apply hnj
    subst l
    exact ⟨r, reach_step hsr, reach_refl r⟩
  have hsr_ne : s ≠ r := by
    intro h
    apply hnj
    subst r
    exact ⟨l, reach_refl l, reach_step hsl⟩
  exact ⟨hsl_ne, hsr_ne, hlr⟩

/-- On a finite carrier, a nonjoinable one-step peak forces at least three states. -/
theorem nonjoinable_peak_card_ge_three
    {T : Type u} [Fintype T] [DecidableEq T]
    {R : T → T → Prop} {s l r : T}
    (hsl : R s l) (hsr : R s r) (hnj : ¬ Joinable R l r) :
    3 ≤ Fintype.card T := by
  rcases nonjoinable_peak_has_three_distinct_states hsl hsr hnj with
    ⟨hsl_ne, hsr_ne, hlr⟩
  have hcard : ({s, l, r} : Finset T).card = 3 := by
    simp [hsl_ne, hsr_ne, hlr]
  calc
    3 = ({s, l, r} : Finset T).card := hcard.symm
    _ ≤ (Finset.univ : Finset T).card :=
      Finset.card_le_card (Finset.subset_univ _)
    _ = Fintype.card T := Finset.card_univ

/-- `Fork3` attains the universal finite-carrier lower bound. -/
theorem fork3_attains_nonjoinable_peak_lower_bound :
    Fintype.card Fork3 = 3 ∧
      Fork3Step .source .equal ∧
      Fork3Step .source .different ∧
      ¬ Joinable Fork3Step .equal .different :=
  ⟨fork3_card_eq_three, Fork3Step.toEqual, Fork3Step.toDifferent,
    fork3_verdicts_unjoinable⟩

/-- Roadmap-stable name: a nonjoinable one-step peak necessarily has two distinct targets. -/
theorem nonjoinable_peak_two_distinct_targets
    {T : Type u} {R : T → T → Prop} {s l r : T}
    (hsl : R s l) (hsr : R s r) (hnj : ¬ Joinable R l r) : l ≠ r :=
  (nonjoinable_peak_has_three_distinct_states hsl hsr hnj).2.2

/-- Exact outgoing-target set of the canonical source. -/
theorem fork3_outgoing_targets_exact :
    {t : Fork3 | Fork3Step .source t} = {.equal, .different} := by
  ext t
  cases t with
  | source =>
      constructor
      · intro h; cases h
      · simp
  | equal =>
      constructor
      · intro _; simp
      · intro _; exact Fork3Step.toEqual
  | different =>
      constructor
      · intro _; simp
      · intro _; exact Fork3Step.toDifferent

/-- A nonjoinable one-step peak necessarily has two distinct one-step targets.
This is an edge-target minimum, not a global syntactic TRS rule-count theorem. -/
theorem nonjoinable_peak_targets_distinct
    {T : Type u} {R : T → T → Prop} {s l r : T}
    (hsl : R s l) (hsr : R s r) (hnj : ¬ Joinable R l r) : l ≠ r :=
  (nonjoinable_peak_has_three_distinct_states hsl hsr hnj).2.2

end OperatorKO7.Meta.DistinctionBoundary.MinimalFork
