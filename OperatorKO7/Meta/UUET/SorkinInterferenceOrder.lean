import Mathlib
import OperatorKO7.Meta.UUET.FiniteInterferenceBorn
import OperatorKO7.Meta.UUET.ActionQuantum
import OperatorKO7.Meta.SchemaCanonicalTrace

set_option autoImplicit false

/-!
# UUET interference order from duplicator arity (Section 60.8a, 60.9)

Section 60.8 as written asserts that the complex assignment is forced by offset
conservation and gauge covariance. That derivation does not close: the pair
`(1, n)` is a definition (Definition 60.7), not a consequence, and nothing in it
selects a field. This module proves the part that IS a theorem, and states the
part that is a definition as a definition.

What is a theorem here: the ORDER of the interference hierarchy is fixed by the
arity of the duplicating step. The Sorkin functionals of inclusion-exclusion
vanish above order two on any quadratic intensity, and a cubic intensity has a
non-vanishing third-order functional. The step-duplicating recursor produces one
new payload copy per event, so its intensity is quadratic and its interference
hierarchy stops at order two. A measured third-order interference term would
refute that reading, which is the written falsifier.

What is a definition here: `duplicatorArity`. The identification of interference
poses with payload copies per event is the structural model of Section 58.5; the
vanishing theorems below are theorems about the resulting exponent.

Relation: real-valued intensity functionals over finite amplitude sums.
Property: identity, vanishing, and non-vanishing witnesses.
Trust: kernel-only real algebra.
Scope: the finite `CAmp` real-pair carrier and the real power model. No Hilbert
space, no quantum measure theory, no physical interference experiment.
-/

namespace OperatorKO7.Meta.UUET.SorkinInterferenceOrder

open OperatorKO7.Meta.UUET

noncomputable section

/-! ## Intensities of summed amplitude paths -/

/-- Intensity of a single amplitude path. -/
def P1 (a : CAmp) : ℝ := a.normSq

/-- Intensity of two coherently summed amplitude paths. -/
def P2 (a b : CAmp) : ℝ := (a.add b).normSq

/-- Intensity of three coherently summed amplitude paths. -/
def P3 (a b c : CAmp) : ℝ := ((a.add b).add c).normSq

/-- Intensity of four coherently summed amplitude paths. -/
def P4 (a b c d : CAmp) : ℝ := (((a.add b).add c).add d).normSq

/-! ## The Sorkin inclusion-exclusion functionals -/

/-- The second-order Sorkin functional: the two-path intensity minus the two
single-path intensities. -/
def sorkinI2 (a b : CAmp) : ℝ := P2 a b - P1 a - P1 b

/-- The third-order Sorkin functional by inclusion-exclusion on three paths. -/
def sorkinI3 (a b c : CAmp) : ℝ :=
  P3 a b c - P2 a b - P2 a c - P2 b c + P1 a + P1 b + P1 c

/-- The fourth-order Sorkin functional by inclusion-exclusion on four paths. -/
def sorkinI4 (a b c d : CAmp) : ℝ :=
  P4 a b c d
    - P3 a b c - P3 a b d - P3 a c d - P3 b c d
    + P2 a b + P2 a c + P2 a d + P2 b c + P2 b d + P2 c d
    - P1 a - P1 b - P1 c - P1 d

/--
Proves: the second-order Sorkin functional is exactly twice the real-pair dot
product of the two amplitudes, that is, exactly the interference cross term of
`FiniteInterferenceBorn.interferenceTerm_eq`.

Does not prove: that any physical two-path experiment realizes this value.

Relation: real algebra on the finite amplitude carrier.
Trust: kernel-only.
Scope: `CAmp` real pairs.
-/
theorem sorkinI2_eq_two_dot (a b : CAmp) : sorkinI2 a b = 2 * a.dot b := by
  simp only [sorkinI2, P2, P1, CAmp.add, CAmp.normSq, CAmp.dot]
  ring

/--
Proves: level two of the hierarchy is present, with an explicit witness. Two
copies of the unit real amplitude have second-order Sorkin functional `2`.

Relation: real algebra on the finite amplitude carrier.
Trust: kernel-only.
Scope: one concrete pair.
-/
theorem sorkinI2_nonzero_witness :
    sorkinI2 (CAmp.mk 1 0) (CAmp.mk 1 0) = 2 := by
  simp only [sorkinI2, P2, P1, CAmp.add, CAmp.normSq]
  norm_num

/--
Proves: the third-order Sorkin functional vanishes identically on the finite
complex amplitude carrier. The squared modulus of a sum is a quadratic form, and
inclusion-exclusion at order three annihilates every quadratic form.

Does not prove: that physical quantum mechanics has no third-order interference.
That is an experimental question; the standard reading is that the Born rule
makes it vanish and multi-slit experiments bound it.

Relation: real algebra on the finite amplitude carrier.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: all `CAmp` triples.
-/
theorem sorkinI3_eq_zero (a b c : CAmp) : sorkinI3 a b c = 0 := by
  simp only [sorkinI3, P3, P2, P1, CAmp.add, CAmp.normSq]
  ring

/--
Proves: the fourth-order Sorkin functional vanishes identically on the finite
complex amplitude carrier, for the same quadratic reason.

Relation: real algebra on the finite amplitude carrier.
Trust: kernel-only.
Scope: all `CAmp` quadruples.
-/
theorem sorkinI4_eq_zero (a b c d : CAmp) : sorkinI4 a b c d = 0 := by
  simp only [sorkinI4, P4, P3, P2, P1, CAmp.add, CAmp.normSq]
  ring

/-! ## The arity model: intensity as a power of the summed weight -/

/--
Proves: nothing on its own. The arity model: an event whose intensity is the
`d`-th power of the summed pose weight. `d = 2` is the squared modulus of a
two-pose event; `d = 3` is a genuinely cubic three-pose measure.

Relation: real powers.
Trust: kernel-only.
Scope: real arguments; `d` a natural exponent.
-/
def poseMeasure (d : ℕ) (x : ℝ) : ℝ := x ^ d

/-- The second-order real Sorkin functional at exponent `d`. -/
def sorkinI2Real (d : ℕ) (a b : ℝ) : ℝ :=
  poseMeasure d (a + b) - poseMeasure d a - poseMeasure d b

/-- The third-order real Sorkin functional at exponent `d`. -/
def sorkinI3Real (d : ℕ) (a b c : ℝ) : ℝ :=
  poseMeasure d (a + b + c)
    - poseMeasure d (a + b) - poseMeasure d (a + c) - poseMeasure d (b + c)
    + poseMeasure d a + poseMeasure d b + poseMeasure d c

/-- The fourth-order real Sorkin functional at exponent `d`. -/
def sorkinI4Real (d : ℕ) (a b c e : ℝ) : ℝ :=
  poseMeasure d (a + b + c + e)
    - poseMeasure d (a + b + c) - poseMeasure d (a + b + e)
    - poseMeasure d (a + c + e) - poseMeasure d (b + c + e)
    + poseMeasure d (a + b) + poseMeasure d (a + c) + poseMeasure d (a + e)
    + poseMeasure d (b + c) + poseMeasure d (b + e) + poseMeasure d (c + e)
    - poseMeasure d a - poseMeasure d b - poseMeasure d c - poseMeasure d e

/--
Proves: at exponent two the third-order real Sorkin functional vanishes for all
arguments. An arity-two event has interference of order at most two.

Relation: real algebra.
Trust: kernel-only.
Scope: exponent exactly two.
-/
theorem arity_two_third_order_vanishes (a b c : ℝ) :
    sorkinI3Real 2 a b c = 0 := by
  simp only [sorkinI3Real, poseMeasure]
  ring

/--
Proves: at exponent two the second-order real Sorkin functional is not
identically zero: at `a = b = 1` it equals `2`. Level two is genuinely present.

Relation: real algebra.
Trust: kernel-only.
Scope: exponent two at one concrete point.
-/
theorem arity_two_second_order_witness : sorkinI2Real 2 1 1 = 2 := by
  simp only [sorkinI2Real, poseMeasure]
  norm_num

/--
Proves: THE WRITTEN FALSIFIER. At exponent three the third-order real Sorkin
functional is not identically zero: at `a = b = c = 1` it equals `6`. An event
with three poses per step exhibits third-order interference.

This is the falsifier for the Section 60.8a reading: a measured non-zero
third-order interference term refutes the identification of the duplicating step
with an arity-two event.

Relation: real algebra.
Trust: kernel-only.
Scope: exponent three at one concrete point.
-/
theorem arity_three_third_order_witness : sorkinI3Real 3 1 1 1 = 6 := by
  simp only [sorkinI3Real, poseMeasure]
  norm_num

/--
Proves: at exponent three the FOURTH-order real Sorkin functional still vanishes
identically. The hierarchy stops one level higher, exactly at the arity. This is
the general shape: exponent `d` kills order `d + 1`.

Relation: real algebra.
Trust: kernel-only.
Scope: exponent exactly three.
-/
theorem arity_three_fourth_order_vanishes (a b c e : ℝ) :
    sorkinI4Real 3 a b c e = 0 := by
  simp only [sorkinI4Real, poseMeasure]
  ring

/-! ## The general hierarchy: inclusion-exclusion above order two -/

/-- The alternating sign of a subset, taken by the size of its complement. This
is the inclusion-exclusion weight of the Sorkin hierarchy at order `n`. -/
def powersetSign {n : ℕ} (S : Finset (Fin n)) : ℝ :=
  (-1) ^ ((Finset.univ \ S).card)

/-- The alternating powerset sum of the constant one, over the reals. Mathlib
carries this only over the integers, so it is transported here. -/
theorem sum_powerset_neg_one_pow_card_real {α : Type} [DecidableEq α]
    {x : Finset α} (h : x.Nonempty) :
    ∑ m ∈ x.powerset, ((-1 : ℝ)) ^ m.card = 0 := by
  have hz : (∑ m ∈ x.powerset, ((-1 : ℤ)) ^ m.card) = 0 :=
    Finset.sum_powerset_neg_one_pow_card_of_nonempty h
  have hcast : ((∑ m ∈ x.powerset, ((-1 : ℤ)) ^ m.card : ℤ) : ℝ) = ((0 : ℤ) : ℝ) := by
    exact_mod_cast congrArg (fun z : ℤ => z) hz
  push_cast at hcast
  simpa using hcast

/--
Proves: the alternating sum of the inclusion-exclusion weight over every
superset of a fixed set `R` vanishes whenever `R` misses at least one index.

Does not prove: anything when `R` is the whole index set, where the sum is one.

Relation: alternating sums over a finite powerset.
Trust: kernel-only.
Scope: `Fin n`; real-valued weights.
-/
theorem alternating_sum_over_supersets_eq_zero {n : ℕ}
    (R : Finset (Fin n)) (hR : R ≠ Finset.univ) :
    ∑ S ∈ Finset.univ.powerset.filter (fun S => R ⊆ S), powersetSign (n := n) S = 0 := by
  classical
  have hne : (Finset.univ \ R).Nonempty := by
    rw [Finset.sdiff_nonempty]
    intro hsub
    exact hR (Finset.Subset.antisymm (Finset.subset_univ _) hsub)
  have hbij :
      ∑ S ∈ Finset.univ.powerset.filter (fun S => R ⊆ S), powersetSign (n := n) S
        = ∑ U ∈ (Finset.univ \ R).powerset, ((-1 : ℝ)) ^ U.card := by
    refine Finset.sum_bij'
      (i := fun S _ => Finset.univ \ S) (j := fun U _ => Finset.univ \ U)
      ?hi ?hj ?left ?right ?val
    case hi =>
      intro S hS
      simp only [Finset.mem_filter, Finset.mem_powerset] at hS
      simp only [Finset.mem_powerset]
      exact Finset.sdiff_subset_sdiff (Finset.Subset.refl _) hS.2
    case hj =>
      intro U hU
      simp only [Finset.mem_powerset] at hU
      simp only [Finset.mem_filter, Finset.mem_powerset]
      refine ⟨Finset.subset_univ _, ?_⟩
      intro x hx
      simp only [Finset.mem_sdiff]
      refine ⟨Finset.mem_univ _, ?_⟩
      intro hxU
      have hmem := hU hxU
      simp only [Finset.mem_sdiff] at hmem
      exact hmem.2 hx
    case left =>
      intro S hS
      simp only [Finset.mem_filter, Finset.mem_powerset] at hS
      exact Finset.sdiff_sdiff_eq_self hS.1
    case right =>
      intro U hU
      simp only [Finset.mem_powerset] at hU
      exact Finset.sdiff_sdiff_eq_self (hU.trans Finset.sdiff_subset)
    case val =>
      intro S _
      rfl
  rw [hbij]
  exact sum_powerset_neg_one_pow_card_real hne

/--
Proves: THE GENERAL VANISHING. For any symmetric or asymmetric pair form `g`,
the alternating powerset sum of the double sum of `g` over each subset vanishes
once the index set carries at least three points. Every summand of a quadratic
intensity is a pair term, and inclusion-exclusion at order three or higher
annihilates every pair term.

Does not prove: vanishing at order two. Order two survives, witnessed by
`sorkinI2_nonzero_witness` and `arity_two_second_order_witness`.

Relation: alternating sums over a finite powerset of a pair form.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: `Fin n` with `3 ≤ n`; real-valued pair forms.
-/
theorem alternating_pair_form_eq_zero {n : ℕ} (hn : 3 ≤ n) (g : Fin n → Fin n → ℝ) :
    ∑ S ∈ Finset.univ.powerset,
      powersetSign (n := n) S * (∑ i ∈ S, ∑ j ∈ S, g i j) = 0 := by
  classical
  have hind : ∀ (S : Finset (Fin n)) (F : Fin n → ℝ),
      ∑ i ∈ Finset.univ, (if i ∈ S then F i else 0) = ∑ i ∈ S, F i := by
    intro S F
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  have hexp : ∀ S : Finset (Fin n),
      powersetSign (n := n) S * (∑ i ∈ S, ∑ j ∈ S, g i j)
        = ∑ i : Fin n, ∑ j : Fin n,
            (if ({i, j} : Finset (Fin n)) ⊆ S then powersetSign (n := n) S * g i j else 0) := by
    intro S
    have step : ∀ i : Fin n,
        (if i ∈ S then ∑ j ∈ S, powersetSign (n := n) S * g i j else 0)
          = ∑ j : Fin n,
              (if ({i, j} : Finset (Fin n)) ⊆ S then powersetSign (n := n) S * g i j else 0) := by
      intro i
      rw [← hind S (fun j => powersetSign (n := n) S * g i j)]
      by_cases hi : i ∈ S
      · simp only [hi, if_true]
        refine Finset.sum_congr rfl ?_
        intro j _
        by_cases hj : j ∈ S
        · simp [hj, Finset.insert_subset_iff, hi]
        · simp [hj, Finset.insert_subset_iff, hi]
      · simp only [hi, if_false]
        refine (Finset.sum_eq_zero ?_).symm
        intro j _
        have hns : ¬ (({i, j} : Finset (Fin n)) ⊆ S) := by
          simp [Finset.insert_subset_iff, hi]
        simp [hns]
    calc powersetSign (n := n) S * (∑ i ∈ S, ∑ j ∈ S, g i j)
        = ∑ i ∈ S, ∑ j ∈ S, powersetSign (n := n) S * g i j := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun i _ => Finset.mul_sum _ _ _)
      _ = ∑ i : Fin n, (if i ∈ S then ∑ j ∈ S, powersetSign (n := n) S * g i j else 0) := by
          rw [hind S (fun i => ∑ j ∈ S, powersetSign (n := n) S * g i j)]
      _ = ∑ i : Fin n, ∑ j : Fin n,
            (if ({i, j} : Finset (Fin n)) ⊆ S then powersetSign (n := n) S * g i j else 0) :=
          Finset.sum_congr rfl (fun i _ => step i)
  rw [Finset.sum_congr rfl (fun S _ => hexp S)]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero ?_
  intro i _
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero ?_
  intro j _
  have hcard : ({i, j} : Finset (Fin n)).card ≠ (Finset.univ : Finset (Fin n)).card := by
    have h2 : ({i, j} : Finset (Fin n)).card ≤ 2 :=
      (Finset.card_insert_le _ _).trans (by simp)
    have hu : (Finset.univ : Finset (Fin n)).card = n := by simp
    omega
  have hne : ({i, j} : Finset (Fin n)) ≠ Finset.univ := fun h => hcard (by rw [h])
  have key := alternating_sum_over_supersets_eq_zero ({i, j} : Finset (Fin n)) hne
  calc (∑ S ∈ Finset.univ.powerset,
          (if ({i, j} : Finset (Fin n)) ⊆ S then powersetSign (n := n) S * g i j else 0))
      = ∑ S ∈ Finset.univ.powerset.filter (fun S => ({i, j} : Finset (Fin n)) ⊆ S),
          powersetSign (n := n) S * g i j := (Finset.sum_filter _ _).symm
    _ = (∑ S ∈ Finset.univ.powerset.filter (fun S => ({i, j} : Finset (Fin n)) ⊆ S),
          powersetSign (n := n) S) * g i j := by rw [Finset.sum_mul]
    _ = 0 := by rw [key, zero_mul]

/-- The componentwise sum of a finite family of amplitudes. -/
def campSum {n : ℕ} (S : Finset (Fin n)) (a : Fin n → CAmp) : CAmp :=
  CAmp.mk (∑ i ∈ S, (a i).re) (∑ i ∈ S, (a i).im)

/--
Proves: the squared modulus of a finite amplitude sum is the double sum of the
pairwise dot products. This is the statement that the intensity is a quadratic
form, in the shape the general vanishing theorem consumes.

Relation: real algebra on the finite amplitude carrier.
Trust: kernel-only.
Scope: any finite index subset.
-/
theorem normSq_campSum {n : ℕ} (S : Finset (Fin n)) (a : Fin n → CAmp) :
    (campSum S a).normSq = ∑ i ∈ S, ∑ j ∈ S, (a i).dot (a j) := by
  classical
  simp only [campSum, CAmp.normSq, CAmp.dot, sq]
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [← Finset.sum_add_distrib]

/-- The Sorkin functional at order `n` on the finite amplitude carrier. -/
def sorkinOrder {n : ℕ} (a : Fin n → CAmp) : ℝ :=
  ∑ S ∈ Finset.univ.powerset, powersetSign (n := n) S * (campSum S a).normSq

/--
Proves: Sorkin level `n` vanishes on the finite complex amplitude carrier for
every `n` at least three. This is the general form of `sorkinI3_eq_zero` and
`sorkinI4_eq_zero`: the squared modulus of a sum is a quadratic form, and
inclusion-exclusion above order two annihilates every quadratic form.

Does not prove: vanishing at order two. Level two is present, witnessed by
`sorkinI2_nonzero_witness`.

Relation: alternating powerset sums of the finite intensity.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: `Fin n` with `3 ≤ n`; the `CAmp` real-pair carrier.
-/
theorem sorkinI_eq_zero_of_three_le {n : ℕ} (hn : 3 ≤ n) (a : Fin n → CAmp) :
    sorkinOrder a = 0 := by
  classical
  have hrw : ∀ S : Finset (Fin n),
      powersetSign (n := n) S * (campSum S a).normSq
        = powersetSign (n := n) S * (∑ i ∈ S, ∑ j ∈ S, (a i).dot (a j)) := by
    intro S
    rw [normSq_campSum]
  rw [sorkinOrder, Finset.sum_congr rfl (fun S _ => hrw S)]
  exact alternating_pair_form_eq_zero hn (fun i j => (a i).dot (a j))

/-! ## The recursor's arity -/

open OperatorKO7.StepDuplicating.StepDuplicatingSchema.BaseDuplicatingSystem in
/--
Proves: nothing on its own. THIS IS A DEFINITION, not a theorem. The
step-duplicating recursor is declared to be an arity-two event, meaning two
interference poses per step.

Does not prove: that interference poses ARE payload copies. That identification
is the structural model of Section 58.5. What is tied to the mechanized trace is
the number: `duplicatorArity_eq_payload_increment_succ` shows the declared value
equals one plus the payload increment per step of the canonical trace, and the
payload increment is `trace_pay 1 - trace_pay 0 = 1`.

Relation: a natural-number constant.
Trust: kernel-only.
Scope: a declared constant with a proved tie to the trace payload increment.
-/
def duplicatorArity : ℕ := 2

open OperatorKO7.StepDuplicating.StepDuplicatingSchema.BaseDuplicatingSystem in
/--
Proves: the declared duplicator arity equals one plus the payload increment of
one canonical-trace step. The recursor adds exactly one payload copy per event,
so the arity is two.

Does not prove: that poses and payload copies are the same thing.

Relation: natural-number arithmetic on the canonical trace payload coordinate.
Trust: kernel-only.
Scope: the first trace step.
-/
theorem duplicatorArity_eq_payload_increment_succ :
    duplicatorArity = (trace_pay 1 - trace_pay 0) + 1 := by
  simp [duplicatorArity, trace_pay]

/--
Proves: Section 60.8a. At the duplicator's arity the interference hierarchy has
level two present and level three absent: the third-order Sorkin functional
vanishes for all arguments, and the second-order one is non-zero at a witness.

Does not prove: that the field of amplitudes is the complex numbers. Order two
is compatible with the reals, the complexes and the quaternions alike; the field
is selected by a different axiom, treated in
`OperatorKO7.Meta.UUET.Quantum.LocalTomographyDimension`.

Relation: real algebra at a fixed exponent.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: the declared arity `duplicatorArity = 2`.
-/
theorem recursor_interference_order_two :
    (∀ a b c : ℝ, sorkinI3Real duplicatorArity a b c = 0)
      ∧ sorkinI2Real duplicatorArity 1 1 = 2 := by
  exact ⟨fun a b c => arity_two_third_order_vanishes a b c,
    arity_two_second_order_witness⟩

/-! ## Section 60.9: the per-step phase is the zero-point ratio -/

/--
Proves: Definition 60.9's value as a ratio of two ALREADY MECHANIZED
quantities, not as a fresh literal. The zero-point confession
`OperatorKO7.Meta.UUET.zeroPointConfession b = b / 2` divided by the action
quantum `OperatorKO7.Meta.UUET.proofSystemPlanck b = b` equals `1 / 2` for every
non-zero burden parameter.

Does not prove: that this ratio is a phase in radians, or that any physical
process advances by it. The radian reading is the structural model of Section
60.9.

Relation: rational division.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: non-zero rational burden parameter.
-/
theorem per_step_phase_eq_zero_point_ratio (b : ℚ) (hb : b ≠ 0) :
    zeroPointConfession b / proofSystemPlanck b = 1 / 2 := by
  simp only [zeroPointConfession, proofSystemPlanck]
  field_simp
  ring

/-! ## Non-vacuity -/

/--
Proves: the interference-order carriers are non-vacuous and the two levels are
genuinely separated. Level two is non-zero on the amplitude carrier and on the
arity-two power model; level three vanishes at arity two and is non-zero at
arity three; the per-step phase ratio is one half at the witness burden `4`.

Relation: finite fixtures.
Trust: kernel-only.
Scope: the concrete witnesses named.
-/
theorem sorkinInterferenceOrder_nonvacuous :
    sorkinI2 (CAmp.mk 1 0) (CAmp.mk 1 0) = 2
      ∧ sorkinI3 (CAmp.mk 1 0) (CAmp.mk 1 0) (CAmp.mk 1 0) = 0
      ∧ sorkinI3Real 2 1 1 1 = 0
      ∧ sorkinI3Real 3 1 1 1 = 6
      ∧ zeroPointConfession (4 : ℚ) / proofSystemPlanck (4 : ℚ) = 1 / 2 := by
  refine ⟨sorkinI2_nonzero_witness, sorkinI3_eq_zero _ _ _,
    arity_two_third_order_vanishes 1 1 1, arity_three_third_order_witness, ?_⟩
  exact per_step_phase_eq_zero_point_ratio 4 (by norm_num)

end

/-! Imported NameGate and TypeGate. -/
#check @CAmp.normSq
#check @CAmp.add
#check @CAmp.dot
#check @CAmp.normSq_add
#check @OperatorKO7.Meta.UUET.zeroPointConfession
#check @OperatorKO7.Meta.UUET.proofSystemPlanck
#check @OperatorKO7.StepDuplicating.StepDuplicatingSchema.BaseDuplicatingSystem.trace_pay

#check @P1
#check @P2
#check @P3
#check @P4
#check @sorkinI2
#check @sorkinI3
#check @sorkinI4
#check @sorkinI2_eq_two_dot
#check @sorkinI2_nonzero_witness
#check @sorkinI3_eq_zero
#check @sorkinI4_eq_zero
#check @poseMeasure
#check @sorkinI2Real
#check @sorkinI3Real
#check @sorkinI4Real
#check @arity_two_third_order_vanishes
#check @arity_two_second_order_witness
#check @arity_three_third_order_witness
#check @arity_three_fourth_order_vanishes
#check @duplicatorArity
#check @duplicatorArity_eq_payload_increment_succ
#check @recursor_interference_order_two
#check @per_step_phase_eq_zero_point_ratio
#check @powersetSign
#check @sum_powerset_neg_one_pow_card_real
#check @alternating_sum_over_supersets_eq_zero
#check @alternating_pair_form_eq_zero
#check @campSum
#check @normSq_campSum
#check @sorkinOrder
#check @sorkinI_eq_zero_of_three_le
#check @sorkinInterferenceOrder_nonvacuous

#print axioms sorkinI2_eq_two_dot
#print axioms sorkinI2_nonzero_witness
#print axioms sorkinI3_eq_zero
#print axioms sorkinI4_eq_zero
#print axioms arity_two_third_order_vanishes
#print axioms arity_two_second_order_witness
#print axioms arity_three_third_order_witness
#print axioms arity_three_fourth_order_vanishes
#print axioms duplicatorArity_eq_payload_increment_succ
#print axioms recursor_interference_order_two
#print axioms per_step_phase_eq_zero_point_ratio
#print axioms sum_powerset_neg_one_pow_card_real
#print axioms alternating_sum_over_supersets_eq_zero
#print axioms alternating_pair_form_eq_zero
#print axioms normSq_campSum
#print axioms sorkinI_eq_zero_of_three_le
#print axioms sorkinInterferenceOrder_nonvacuous

end OperatorKO7.Meta.UUET.SorkinInterferenceOrder
