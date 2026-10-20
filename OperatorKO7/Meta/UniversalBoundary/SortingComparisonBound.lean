import OperatorKO7.Meta.HigherOrderRewriting_SystemTSyntax
import OperatorKO7.Meta.UniversalBoundary.BoundaryPrimitive
import OperatorKO7.Meta.OperationalInexpressibility.LiftOrRefuse
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Vector.Basic

/-!
# Comparison Sorting as an Additional-Channel Boundary

The classical comparison-sorting lower bound is ESTABLISHED. This module proves
that its finite counting step is an instance of the framework's
additional-channel cardinality lower bound.

Relation: equality on Boolean comparison transcripts.
Closure: not applicable; no rewriting closure is claimed.
Strategy: fixed non-adaptive deterministic comparisons.
Trust: kernel-only; finite arithmetic examples use decide.
Scope: fixed question lists with no randomness; adaptive and randomized algorithms
       are outside this module.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniversalBoundary.SortingComparisonBound

open scoped Nat
open OperatorKO7.Meta.UniversalBoundary.BoundaryPrimitive
open OperatorKO7.Meta.OperationalInexpressibility.DirectGrammarBoundary
open OperatorKO7.Meta.OperationalInexpressibility.ObserverKernel
open OperatorKO7.Meta.OperationalInexpressibility.FiberDeficit
open OperatorKO7.Meta.OperationalInexpressibility.LicenseCriterion
open OperatorKO7.Meta.OperationalInexpressibility.LiftOrRefuse

/-- Inputs are permutations of n distinct keys. -/
abbrev Input (n : Nat) := Equiv.Perm (Fin n)

/-- The verdict required to sort a permutation is the permutation itself. -/
def sortingVerdict {n : Nat} : Input n -> Equiv.Perm (Fin n) := id

/-- A fixed non-adaptive list of comparisons and its determined Boolean transcript. -/
structure Algorithm (n k : Nat) where
  ask : Fin k -> Fin n × Fin n
  transcript : Input n -> Fin k -> Bool
  transcript_def :
    forall p i, transcript p i = decide (p (ask i).1 < p (ask i).2)

/-- Correctness means that the transcript licenses the required sorting permutation.

An algorithm that ends with the same transcript on two inputs performs the same
rearrangement on both, so it can sort both only when they require the same
permutation.
-/
def Sorts {n k : Nat} (A : Algorithm n k) : Prop :=
  Licensed A.transcript sortingVerdict

/--
Proves: every sorting transcript with k Boolean entries has capacity at least n factorial.
Does not prove: an adaptive or randomized comparison lower bound.
Relation: additional-channel capacity for the constant observer and transcript channel.
Closure: not applicable.
Strategy: fixed non-adaptive deterministic comparisons.
Trust: kernel-only; uses the imported finite fiber-capacity theorem.
Scope: every A : Algorithm n k satisfying Sorts A.
-/
theorem comparison_count_lower_bound {n k : Nat} (A : Algorithm n k)
    (h : Sorts A) : (Fintype.card (Fin n))! <= 2 ^ k := by
  have hjoint :
      FactorsThrough (fun p : Input n => ((), A.transcript p)) sortingVerdict := by
    intro p q hpq
    exact h p q (congrArg Prod.snd hpq)
  have hcapacity :
      fiberMultiplicity (fun _ : Input n => ()) sortingVerdict <=
        Fintype.card (Fin k -> Bool) :=
    additional_channel_card_lower_bound
      (fun _ : Input n => ()) sortingVerdict A.transcript hjoint
  have hfiber :
      fiberMultiplicity (fun _ : Input n => ()) sortingVerdict =
        Fintype.card (Input n) := by
    rw [fiberMultiplicity_const]
    simp [sortingVerdict]
  calc
    (Fintype.card (Fin n))! = Fintype.card (Input n) := by
      symm
      exact Fintype.card_perm
    _ = fiberMultiplicity (fun _ : Input n => ()) sortingVerdict := hfiber.symm
    _ <= Fintype.card (Fin k -> Bool) := hcapacity
    _ = 2 ^ k := by simp

/--
Proves: a transcript alphabet smaller than n factorial contains a collision with distinct verdicts.
Does not prove: where a particular implementation first encounters that collision.
Relation: OperationallyInexpressibleAt for the transcript and sorting verdict.
Closure: not applicable.
Strategy: fixed non-adaptive deterministic comparisons.
Trust: kernel-only; classical collision normalization is imported.
Scope: every A : Algorithm n k under the stated strict cardinal inequality.
-/
theorem sorting_transcript_too_short_collides {n k : Nat} (A : Algorithm n k)
    (h : 2 ^ k < (Fintype.card (Fin n))!) :
    Exists fun p => Exists fun q =>
      OperationallyInexpressibleAt A.transcript sortingVerdict p q := by
  apply (not_factorsThrough_iff_exists_collision A.transcript sortingVerdict).1
  intro hfactor
  have hsorts : Sorts A :=
    (licensed_iff_factorsThrough A.transcript sortingVerdict).2 hfactor
  exact (Nat.not_le_of_gt h) (comparison_count_lower_bound A hsorts)

/--
Proves: fewer than n-factorial transcript values preclude correctness.
Does not prove: an upper bound or existence of an optimal sorting algorithm.
Relation: negation of Licensed for the transcript and sorting verdict.
Closure: not applicable.
Strategy: fixed non-adaptive deterministic comparisons.
Trust: kernel-only; applies the collision theorem.
Scope: every A : Algorithm n k under the stated strict cardinal inequality.
-/
theorem sorting_transcript_too_short_not_sorts {n k : Nat} (A : Algorithm n k)
    (h : 2 ^ k < (Fintype.card (Fin n))!) : Not (Sorts A) := by
  intro hsorts
  cases sorting_transcript_too_short_collides A h with
  | intro p hp =>
    cases hp with
    | intro q hpq =>
      exact hpq.2 (hsorts p q hpq.1)

/--
Proves: nothing by itself; the transcript collision packaged as the framework's typed boundary,
with the two colliding inputs chosen classically from `sorting_transcript_too_short_collides`.
Does not prove: a canonical choice of the colliding inputs.
Relation: equal transcripts with distinct sorting verdicts.
Closure: not applicable.
Strategy: fixed non-adaptive deterministic comparisons.
Trust: kernel-only; `Classical.choose` on the collision proof.
Scope: every A : Algorithm n k under the strict transcript-capacity inequality.
-/
noncomputable def sortingBoundary (n k : Nat) (A : Algorithm n k)
    (h : 2 ^ k < (Fintype.card (Fin n))!) : TypedBoundary :=
  let hc := sorting_transcript_too_short_collides A h
  let p := Classical.choose hc
  let q := Classical.choose (Classical.choose_spec hc)
  { State := Input n
    Obs := Fin k -> Bool
    Verdict := Equiv.Perm (Fin n)
    observe := A.transcript
    verdict := sortingVerdict
    s₁ := p
    s₂ := q
    obs_eq := (Classical.choose_spec (Classical.choose_spec hc)).1
    verdict_ne := (Classical.choose_spec (Classical.choose_spec hc)).2 }

/--
Proves: no function of the transcript returns the sorting verdict on every input; this is the
universal no-observation-only-verdict law at `sortingBoundary`.
Does not prove: a stronger adaptive, randomized, or expected-comparison result.
Relation: TypedBoundary.verdict_not_observation_function.
Closure: not applicable.
Strategy: fixed non-adaptive deterministic comparisons.
Trust: kernel-only; one application of the imported universal boundary law.
Scope: every A : Algorithm n k under the strict transcript-capacity inequality.
-/
theorem sortingBoundary_obeys_law (n k : Nat) (A : Algorithm n k)
    (h : 2 ^ k < (Fintype.card (Fin n))!) :
    ¬ ∃ f : (Fin k -> Bool) -> Equiv.Perm (Fin n),
      ∀ p : Input n, sortingVerdict p = f (A.transcript p) := by
  simpa [sortingBoundary] using
    TypedBoundary.verdict_not_observation_function (sortingBoundary n k A h)

/--
Proves: the sorting-verdict count for three keys is exactly six.
Does not prove: a general symbolic factorial identity.
Relation: concrete cardinality of Input 3.
Closure: not applicable.
Strategy: finite normalization.
Trust: kernel-only; discharged by decide.
Scope: the finite case n = 3.
-/
theorem fin_three_factorial_card : (Fintype.card (Fin 3))! = 6 := by
  decide

/--
Proves: two Boolean comparisons provide fewer than six transcripts.
Does not prove: failure of any adaptive or randomized two-query procedure.
Relation: strict capacity inequality used by the collision theorem.
Closure: not applicable.
Strategy: finite normalization.
Trust: kernel-only; discharged by decide.
Scope: the finite case n = 3 and k = 2.
-/
theorem two_comparisons_lt_three_factorial :
    2 ^ 2 < (Fintype.card (Fin 3))! := by
  decide

/--
Proves: three Boolean comparisons have raw cardinality at least six.
Does not prove: that the fixed three-comparison model contains a sorting algorithm.
Relation: the converse numerical side of the capacity lower bound.
Closure: not applicable.
Strategy: finite normalization.
Trust: kernel-only; discharged by decide.
Scope: the finite case n = 3 and k = 3.
-/
theorem three_comparisons_meet_three_factorial :
    (Fintype.card (Fin 3))! <= 2 ^ 3 := by
  decide

/-- An explicit two-comparison algorithm on three positions. -/
def threeTwoAlgorithm : Algorithm 3 2 := by
  let ask : Fin 2 -> Fin 3 × Fin 3 := fun i =>
    if i = 0 then (0, 1) else (1, 2)
  exact
    { ask := ask
      transcript := fun p i => decide (p (ask i).1 < p (ask i).2)
      transcript_def := by
        intro p i
        rfl }

/--
Proves: the explicit two-comparison algorithm cannot sort all three-key inputs.
Does not prove: which input pair is operationally most significant.
Relation: the finite instance of sorting_transcript_too_short_not_sorts.
Closure: not applicable.
Strategy: instantiate the strict transcript-capacity theorem.
Trust: kernel-only; combines a proved theorem with decidable arithmetic.
Scope: threeTwoAlgorithm only.
-/
theorem threeTwoAlgorithm_not_sorts : Not (Sorts threeTwoAlgorithm) :=
  sorting_transcript_too_short_not_sorts
    threeTwoAlgorithm two_comparisons_lt_three_factorial

end OperatorKO7.Meta.UniversalBoundary.SortingComparisonBound