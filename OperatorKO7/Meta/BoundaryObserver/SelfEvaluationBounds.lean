import OperatorKO7.Meta.BoundaryObserver.PartialSelfEvaluation
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false

/-!
# Two obstructions under one contract, approximate self-evaluation, and coverage

Subsection "Two obstructions under one contract" of Section 13 of the two-copies manuscript. An
observation succeeds when a readout from the permitted family returns the target from the record.
Two obstructions share that contract: a collision (two states with one record and two target
values) blocks every family, and a missing readout blocks the full-record observer, as Theorem 13.3
shows. The evaluator `c xor x` separates the two: its code observer has an empty boundary and its
diagonal is represented by no code. Adding a record never creates a merged pair.

The negation-preserving readouts of the three-valued completion of Theorem 13.4 are classified: no
total Boolean readout exists, and a readout into the rationals preserves negation in law if and
only if it reads the unresolved value as a fair coin.

The exact self-evaluation obstruction has an approximate form: an approximate self-evaluator and
an approximate negation code miss by at least the uniform displacement of the negation, and the
displacement hypothesis is needed, as the map `v + 1 / (1 + |v|)` shows.

Test accuracy and coverage are separated by two families of codes: every finite set of inputs is
passed by some code, the mean error under a geometric law tends to zero, and no code represents
the complemented diagonal.

Proof graph: `Audit/ledgers/operational-inexpressibility/SELF-EVALUATION-BOUNDS-PROOF-GRAPH.md`,
nodes B1 to B4.

Relation: none; the statements are about maps between arbitrary types, Boolean tables, and real
numbers. Trust: kernel-only. No `sorry`, `admit`, `axiom`, `native_decide`.
-/

namespace OperatorKO7.Meta.BoundaryObserver.SelfEvaluationBounds

open OperatorKO7.Meta.BoundaryObserver.MergedPair
open OperatorKO7.Meta.BoundaryObserver.DiagonalObservation
open OperatorKO7.Meta.BoundaryObserver.PartialSelfEvaluation
open scoped BigOperators

/-! ## B1: one contract, two obstructions -/

/-- The observation contract: some readout in the permitted family `F` returns the target `T`
from the record `O x` at every state. -/
def Solvable {X Y V : Type*} (O : X → Y) (T : X → V) (F : Set (Y → V)) : Prop :=
  ∃ f ∈ F, ∀ x, f (O x) = T x

/-- A collision blocks every family of readouts: lost information is the first obstruction. -/
theorem collision_blocks_every_family {X Y V : Type*} (O : X → Y) (T : X → V) (F : Set (Y → V))
    {x y : X} (hO : O x = O y) (hT : T x ≠ T y) : ¬ Solvable O T F := by
  rintro ⟨f, -, hf⟩
  exact hT ((hf x).symm.trans ((congrArg f hO).trans (hf y)))

/-- With every readout permitted and a nonempty value type, the contract is the determination of
Definition 2.1: the record determines the target. -/
theorem solvable_univ_iff_determines {X Y V : Type*} [Nonempty V] (O : X → Y) (T : X → V) :
    Solvable O T Set.univ ↔ Determines O T := by
  constructor
  · rintro ⟨f, -, hf⟩ x y hxy
    exact (hf x).symm.trans ((congrArg f hxy).trans (hf y))
  · intro h
    classical
    exact ⟨fun y => if hy : ∃ x, O x = y then T (Classical.choose hy) else Classical.arbitrary V,
      Set.mem_univ _, fun x => by
        have hx : ∃ x', O x' = O x := ⟨x, rfl⟩
        show (if hy : ∃ x', O x' = O x then T (Classical.choose hy) else Classical.arbitrary V) = T x
        rw [dif_pos hx]
        exact h _ _ (Classical.choose_spec hx)⟩

/-- Adding a record removes merged pairs and creates none: the boundary of `(q, s)` lies inside
the boundary of `q`. -/
theorem boundary_pair_subset {X Q S : Type*} (q : X → Q) (s : X → S) :
    boundary (fun x => (q x, s x)) ⊆ boundary q := by
  rintro ⟨x, y⟩ ⟨hne, hqs⟩
  exact ⟨hne, (Prod.mk.inj hqs).1⟩

/-- A record that separates every merged pair of `q` empties the boundary. -/
theorem boundary_pair_eq_empty {X Q S : Type*} (q : X → Q) (s : X → S)
    (h : ∀ x y, IsMergedPair q x y → s x ≠ s y) : boundary (fun x => (q x, s x)) = ∅ := by
  ext ⟨x, y⟩
  constructor
  · rintro ⟨hne, hqs⟩
    exact (h x y ⟨hne, (Prod.mk.inj hqs).1⟩ (Prod.mk.inj hqs).2).elim
  · intro hp
    exact hp.elim

/-- The evaluator `E c x = c xor x` on one bit of code and one bit of input. -/
def xorEval : Bool → Bool → Bool := fun c x => xor c x

/-- Its diagonal is constantly false. -/
theorem xorEval_self (c : Bool) : xorEval c c = false := by
  cases c <;> rfl

/-- The diagonal is represented by no code: a code returning false everywhere would have to equal
every input. -/
theorem xorEval_diagonal_not_represented : ¬ Represented xorEval (fun c => xorEval c c) := by
  rintro ⟨d, hd⟩
  have h1 : xorEval d true = xorEval true true := congrFun hd true
  have h2 : xorEval d false = xorEval false false := congrFun hd false
  cases d <;> simp [xorEval] at h1 h2

/-- The code observer reads each code exactly: its boundary is empty. -/
theorem code_observer_boundary_empty : boundary (fun c : Bool => c) = ∅ :=
  (boundary_eq_empty_iff_injective _).mpr fun _ _ h => h

/-- The second obstruction without the first: with the identity record and the represented family
as the permitted readouts, the diagonal is not solvable, and the observer has no merged pair. -/
theorem representation_failure_without_merged_pair :
    boundary (fun c : Bool => c) = ∅ ∧
      ¬ Solvable (fun c : Bool => c) (fun c => xorEval c c) (Set.range xorEval) := by
  constructor
  · exact code_observer_boundary_empty
  · rintro ⟨f, ⟨d, rfl⟩, hf⟩
    exact xorEval_diagonal_not_represented ⟨d, funext hf⟩

/-! ## B2: the readouts of the three-valued completion -/

/-- The fair readout: definite values read as themselves, the unresolved value as a fair coin. -/
def fairReadout : Option Bool → ℚ
  | none => 1 / 2
  | some true => 1
  | some false => 0

/-- The fair readout preserves negation in law. -/
theorem fairReadout_preserves_negation (v : Option Bool) :
    fairReadout (negate v) = 1 - fairReadout v := by
  cases v with
  | none => norm_num [fairReadout, negate]
  | some b => cases b <;> norm_num [fairReadout, negate]

/-- A probability fixed by complement is one half; no Boolean value is fixed by negation. -/
theorem complement_fixed_iff_half (p : ℚ) : p = 1 - p ↔ p = 1 / 2 := by
  constructor <;> intro h <;> linarith

/-- Any readout into the rationals that preserves negation at the unresolved value reads it as a
fair coin. -/
theorem stochastic_readout_forces_half (p : Option Bool → ℚ) (h : ∀ v, p (negate v) = 1 - p v) :
    p none = 1 / 2 :=
  (complement_fixed_iff_half _).mp (h none)

/-- A readout into the rationals preserves negation at every value if and only if it reads the
unresolved value as one half and the two definite values as complements. -/
theorem stochastic_readout_iff (p : Option Bool → ℚ) :
    (∀ v, p (negate v) = 1 - p v) ↔ p none = 1 / 2 ∧ p (some true) = 1 - p (some false) := by
  constructor
  · intro h
    constructor
    · exact stochastic_readout_forces_half p h
    · have := h (some false)
      rwa [negate_some, Bool.not_false] at this
  · rintro ⟨h0, h1⟩ v
    cases v with
    | none =>
      rw [negate_none]
      linarith
    | some b =>
      cases b
      · rw [negate_some, Bool.not_false]
        exact h1
      · rw [negate_some, Bool.not_true]
        linarith

/-- No total Boolean readout preserves negation, and the fair readout preserves it in law. -/
theorem no_deterministic_readout_fair_law :
    (¬ ∃ h : Option Bool → Bool, ∀ v, h (negate v) = !(h v)) ∧
      ∀ v, fairReadout (negate v) = 1 - fairReadout v :=
  ⟨no_total_boolean_readout, fairReadout_preserves_negation⟩

/-! ## Full real-probability readout and normalized Boolean output laws -/

/-- The probability interval [0,1], not the unrestricted rational codomain. -/
abbrev ReadoutProbability := {r : ℝ // r ∈ Set.Icc (0 : ℝ) 1}

/-- Among genuine real probabilities, the unique fixed point of complement is one half. -/
theorem real_probability_complement_fixed_iff_half (p : ReadoutProbability) :
    (p : ℝ) = 1 - (p : ℝ) ↔ (p : ℝ) = 1 / 2 := by
  constructor <;> intro h <;> linarith

/-- Exact real interval classification in the manuscript's readout proposition. -/
theorem real_probability_readout_iff (p : Option Bool → ReadoutProbability) :
    (∀ v, (p (negate v) : ℝ) = 1 - (p v : ℝ)) ↔
      (p none : ℝ) = 1 / 2 ∧
        (p (some true) : ℝ) = 1 - (p (some false) : ℝ) := by
  constructor
  · intro h
    constructor
    · have h0 := h none
      rw [negate_none] at h0
      linarith
    · simpa [negate_some] using h (some false)
  · rintro ⟨h0, hpair⟩ v
    cases v with
    | none =>
      rw [negate_none]
      linarith
    | some b =>
      cases b with
      | false =>
        simpa [negate_some] using hpair
      | true =>
        rw [negate_some, Bool.not_true]
        linarith

/-- Definite states are read without error, and the unresolved state gives a fair coin. -/
noncomputable def realFairReadout : Option Bool → ReadoutProbability
  | none => ⟨1 / 2, by constructor <;> norm_num⟩
  | some false => ⟨0, by constructor <;> norm_num⟩
  | some true => ⟨1, by constructor <;> norm_num⟩

/-- The fair real readout preserves negation in law. -/
theorem realFairReadout_law (v : Option Bool) :
    (realFairReadout (negate v) : ℝ) =
      1 - (realFairReadout v : ℝ) := by
  cases v with
  | none => norm_num [realFairReadout, negate]
  | some b => cases b <;> norm_num [realFairReadout, negate]

/-- Both output masses of one stochastic readout, not just an algebraic equality. -/
def realReadoutBernoulli (p : Option Bool → ReadoutProbability)
    (v : Option Bool) (b : Bool) : ℝ :=
  if b then (p v : ℝ) else 1 - (p v : ℝ)

/-- Both actual output masses are nonnegative, including endpoints. -/
theorem realReadoutBernoulli_nonneg (p : Option Bool → ReadoutProbability)
    (v : Option Bool) (b : Bool) :
    0 ≤ realReadoutBernoulli p v b := by
  rcases (p v).property with ⟨h0, h1⟩
  cases b with
  | false =>
    change 0 ≤ 1 - (p v : ℝ)
    linarith
  | true =>
    change 0 ≤ (p v : ℝ)
    exact h0

/-- Every output mass is also at most one. -/
theorem realReadoutBernoulli_le_one (p : Option Bool → ReadoutProbability)
    (v : Option Bool) (b : Bool) :
    realReadoutBernoulli p v b ≤ 1 := by
  rcases (p v).property with ⟨h0, h1⟩
  cases b with
  | false =>
    change 1 - (p v : ℝ) ≤ 1
    linarith
  | true =>
    change (p v : ℝ) ≤ 1
    exact h1

/-- Every input gives a normalized probability distribution over the two outputs. -/
theorem realReadoutBernoulli_total (p : Option Bool → ReadoutProbability)
    (v : Option Bool) :
    (∑ b : Bool, realReadoutBernoulli p v b) = 1 := by
  rw [Fintype.sum_bool]
  simp [realReadoutBernoulli]

/-- A genuine stochastic kernel from unresolved/definite values to Boolean reports. -/
structure RealBooleanReadoutKernel where
  mass : Option Bool → Bool → ℝ
  nonnegative : ∀ v b, 0 ≤ mass v b
  normalized : ∀ v, (∑ b : Bool, mass v b) = 1

/-- A real interval readout produces an actual normalized Boolean kernel. -/
def realReadoutKernel (p : Option Bool → ReadoutProbability) : RealBooleanReadoutKernel where
  mass := realReadoutBernoulli p
  nonnegative := realReadoutBernoulli_nonneg p
  normalized := realReadoutBernoulli_total p

/-- Every normalized Boolean kernel determines an interval-valued chance of true. -/
def realReadoutProbabilityOfKernel (K : RealBooleanReadoutKernel) :
    Option Bool → ReadoutProbability :=
  fun v => ⟨K.mass v true, by
    constructor
    · exact K.nonnegative v true
    · have hsum := K.normalized v
      rw [Fintype.sum_bool] at hsum
      have hfalse := K.nonnegative v false
      linarith⟩

/-- Boolean output laws are recovered exactly, including at the endpoints. -/
theorem realReadoutKernel_recovers (K : RealBooleanReadoutKernel)
    (v : Option Bool) (b : Bool) :
    (realReadoutKernel (realReadoutProbabilityOfKernel K)).mass v b = K.mass v b := by
  cases b with
  | false =>
    have hsum := K.normalized v
    rw [Fintype.sum_bool] at hsum
    change 1 - K.mass v true = K.mass v false
    linarith
  | true => rfl

/-- The reverse map preserves every original interval-valued probability. -/
theorem realReadoutProbabilityOfKernel_recovers
    (p : Option Bool → ReadoutProbability) :
    realReadoutProbabilityOfKernel (realReadoutKernel p) = p := by
  funext v
  apply Subtype.ext
  rfl

/-- Negating the input and complementing the output preserves the Bernoulli
law exactly when the real probability readout obeys complement symmetry. -/
theorem realReadoutBernoulli_negation_iff
    (p : Option Bool → ReadoutProbability) :
    (∀ v b, realReadoutBernoulli p (negate v) (!b) =
      realReadoutBernoulli p v b) ↔
      ∀ v, (p (negate v) : ℝ) = 1 - (p v : ℝ) := by
  constructor
  · intro h v
    simpa [realReadoutBernoulli] using h v false
  · intro h v b
    cases b with
    | false =>
      change (p (negate v) : ℝ) = 1 - (p v : ℝ)
      exact h v
    | true =>
      change 1 - (p (negate v) : ℝ) = (p v : ℝ)
      linarith [h v]

/-- Full iff for genuine normalized Boolean stochastic channels, not just
unbounded real or rational coordinate maps. -/
theorem realReadoutKernel_law_iff (p : Option Bool → ReadoutProbability) :
    (∀ v b, (realReadoutKernel p).mass (negate v) (!b) =
      (realReadoutKernel p).mass v b) ↔
    (p none : ℝ) = 1 / 2 ∧
      (p (some true) : ℝ) = 1 - (p (some false) : ℝ) := by
  change (∀ v b, realReadoutBernoulli p (negate v) (!b) =
    realReadoutBernoulli p v b) ↔ _
  exact (realReadoutBernoulli_negation_iff p).trans (real_probability_readout_iff p)

/-- The real fair readout is an actual symmetry-preserving normalized channel. -/
theorem realFairReadout_kernel_law :
    ∀ v b, (realReadoutKernel realFairReadout).mass (negate v) (!b) =
      (realReadoutKernel realFairReadout).mass v b :=
  (realReadoutBernoulli_negation_iff realFairReadout).2 realFairReadout_law

/-- An unresolved input has both output reports with probability one half. -/
theorem realFairReadout_unresolved (b : Bool) :
    (realReadoutKernel realFairReadout).mass none b = 1 / 2 := by
  cases b <;> norm_num [realReadoutKernel, realReadoutBernoulli, realFairReadout]

/-- A definite input gives the matching Boolean output with probability one. -/
theorem realFairReadout_definite (b : Bool) :
    (realReadoutKernel realFairReadout).mass (some b) b = 1 := by
  cases b <;> norm_num [realReadoutKernel, realReadoutBernoulli, realFairReadout]

/-- Stochastic completion does not produce a negation-preserving deterministic map. -/
theorem realReadout_no_total_Boolean_negating :
    ¬ ∃ h : Option Bool → Bool, ∀ v, h (negate v) = !(h v) :=
  no_total_boolean_readout

/-- No Boolean value is fixed by Boolean complement. -/
theorem Boolean_complement_not_fixed (b : Bool) : b ≠ !b := by
  cases b <;> decide

/-- Complement covariance alone does not require accurate definite readings:
an always-fair coin is a different normalized solution. -/
noncomputable def constantHalfRealReadout : Option Bool → ReadoutProbability :=
  fun _ => ⟨1 / 2, by constructor <;> norm_num⟩

theorem constantHalfRealReadout_law (v : Option Bool) :
    (constantHalfRealReadout (negate v) : ℝ) =
      1 - (constantHalfRealReadout v : ℝ) := by
  norm_num [constantHalfRealReadout]

theorem constantHalf_ne_realFairReadout :
    constantHalfRealReadout ≠ realFairReadout := by
  intro heq
  have h := congrArg (fun p : Option Bool → ReadoutProbability =>
      (p (some false) : ℝ)) heq
  norm_num [constantHalfRealReadout, realFairReadout] at h

/-- Accurate definite inputs make the fair randomized readout unique. -/
theorem realFairReadout_unique_of_definite_and_negation
    (p : Option Bool → ReadoutProbability)
    (hlaw : ∀ v, (p (negate v) : ℝ) = 1 - (p v : ℝ))
    (hdef : ∀ b : Bool, (p (some b) : ℝ) = if b then 1 else 0) :
    p = realFairReadout := by
  funext v
  apply Subtype.ext
  cases v with
  | none =>
    have hnone := ((real_probability_readout_iff p).mp hlaw).1
    simpa [realFairReadout] using hnone
  | some b =>
    cases b with
    | false => simpa [realFairReadout] using hdef false
    | true => simpa [realFairReadout] using hdef true

/-- The complete real-probability and stochastic-law Proposition on unresolved readouts:
the unique complement fixed probability, the iff classification of all normalized
laws, a fair law attaining it, and the Boolean deterministic impossibility. -/
theorem real_readouts_full :
    (∀ p : ReadoutProbability, (p : ℝ) = 1 - (p : ℝ) ↔ (p : ℝ) = 1 / 2) ∧
    (∀ p : Option Bool → ReadoutProbability,
      (∀ v b, (realReadoutKernel p).mass (negate v) (!b) =
        (realReadoutKernel p).mass v b) ↔
      (p none : ℝ) = 1 / 2 ∧
        (p (some true) : ℝ) = 1 - (p (some false) : ℝ)) ∧
    (∀ v b, (realReadoutKernel realFairReadout).mass (negate v) (!b) =
      (realReadoutKernel realFairReadout).mass v b) ∧
    (¬ ∃ h : Option Bool → Bool, ∀ v, h (negate v) = !(h v)) := by
  exact ⟨real_probability_complement_fixed_iff_half, realReadoutKernel_law_iff,
    realFairReadout_kernel_law, no_total_boolean_readout⟩

/-! ## B3: approximate self-evaluation -/

/--
Approximate self-evaluation. The code `d` is within `εd` of the diagonal at every input, the code
transformation `n` is within `εr` of the value map `g` at every input, and `g` moves every value by
at least `δ`. Then `δ ≤ εd + εr`.

Proves: the inequality, by the triangle inequality at the input `n d`.
Does not prove: anything when `g` has no uniform displacement; `shiftMap` below shows the
hypothesis is needed.
Relation: none. Trust: kernel-only.
-/
theorem approx_self_evaluation_bound {C V : Type*} [PseudoMetricSpace V] (E : C → C → V)
    (g : V → V) (n : C → C) (d : C) {εd εr δ : ℝ}
    (hdiag : ∀ c, dist (E d c) (E c c) ≤ εd)
    (hrep : ∀ c x, dist (E (n c) x) (g (E c x)) ≤ εr)
    (hdisp : ∀ v, δ ≤ dist v (g v)) : δ ≤ εd + εr := by
  have h1 := hdiag (n d)
  have h2 := hrep d (n d)
  have h3 := dist_triangle (E d (n d)) (E (n d) (n d)) (g (E d (n d)))
  have h4 := hdisp (E d (n d))
  linarith

/-- Non-vacuity, and the bound is attained: the constant evaluator `0` on one code, the identity
code transformation and the shift `g v = v + 1` satisfy the hypotheses with `εd = 0`, `εr = 1`,
`δ = 1`. -/
theorem approx_bound_attained :
    ∃ (E : Unit → Unit → ℝ) (g : ℝ → ℝ) (n : Unit → Unit) (d : Unit),
      (∀ c, dist (E d c) (E c c) ≤ (0 : ℝ)) ∧ (∀ c x, dist (E (n c) x) (g (E c x)) ≤ (1 : ℝ)) ∧
        ∀ v, (1 : ℝ) ≤ dist v (g v) := by
  exact ⟨fun _ _ => 0, fun v => v + 1, id, (), fun _ => by simp,
    fun _ _ => by norm_num [Real.dist_eq],
    fun v => by rw [Real.dist_eq, show v - (v + 1) = -1 by ring, abs_neg, abs_one]⟩

/-- Two states with one record: the distance of their targets is at most the sum of the two errors
of any readout. -/
theorem collision_error_sum {X Y V : Type*} [PseudoMetricSpace V] (O : X → Y) (T : X → V)
    (f : Y → V) {x y : X} (h : O x = O y) :
    dist (T x) (T y) ≤ dist (f (O x)) (T x) + dist (f (O y)) (T y) := by
  have ht := dist_triangle (T x) (f (O x)) (T y)
  have hc : dist (T x) (f (O x)) = dist (f (O x)) (T x) := dist_comm _ _
  have he : dist (f (O x)) (T y) = dist (f (O y)) (T y) := by rw [congrArg f h]
  linarith

/-- Two states with one record and targets at least `δ` apart force an error of at least `δ / 2`
on one of them, for every readout. -/
theorem collision_error_half {X Y V : Type*} [PseudoMetricSpace V] (O : X → Y) (T : X → V)
    (f : Y → V) {x y : X} (h : O x = O y) {δ : ℝ} (hδ : δ ≤ dist (T x) (T y)) :
    δ / 2 ≤ max (dist (f (O x)) (T x)) (dist (f (O y)) (T y)) := by
  have hs := collision_error_sum O T f h
  have h1 := le_max_left (dist (f (O x)) (T x)) (dist (f (O y)) (T y))
  have h2 := le_max_right (dist (f (O x)) (T x)) (dist (f (O y)) (T y))
  linarith

/-- A fixed-point-free map of the line with no uniform displacement. -/
noncomputable def shiftMap (v : ℝ) : ℝ := v + 1 / (1 + |v|)

/-- The displacement of `shiftMap` at `v` is `1 / (1 + |v|)`. -/
theorem shiftMap_displacement (v : ℝ) : dist v (shiftMap v) = 1 / (1 + |v|) := by
  have hpos : 0 < 1 / (1 + |v|) := by positivity
  rw [Real.dist_eq, shiftMap, show v - (v + 1 / (1 + |v|)) = -(1 / (1 + |v|)) by ring, abs_neg,
    abs_of_pos hpos]

/-- `shiftMap` has no fixed point. -/
theorem shiftMap_ne_self (v : ℝ) : shiftMap v ≠ v := by
  intro h
  have hpos : 0 < 1 / (1 + |v|) := by positivity
  have h' : v + 1 / (1 + |v|) = v := h
  linarith

/-- `shiftMap` has no uniform displacement: below every positive `δ` some value moves by less. -/
theorem shiftMap_no_uniform_displacement : ∀ δ : ℝ, 0 < δ → ∃ v, dist v (shiftMap v) < δ := by
  intro δ hδ
  have hδ' : δ ≠ 0 := ne_of_gt hδ
  have heq : (1 : ℝ) / (1 + 1 / δ) = δ / (δ + 1) := by
    field_simp
  exact ⟨1 / δ, by
    rw [shiftMap_displacement, abs_of_pos (by positivity), heq]
    exact div_lt_self hδ (by linarith)⟩

/-! ## B4: accuracy against coverage -/

/-- Code `a` answers true exactly on the inputs below `a`. -/
def thresholdEval (a x : ℕ) : Bool := decide (x < a)

/-- The complemented diagonal of the threshold family: constantly true. -/
def constTrue : ℕ → Bool := fun _ => true

/-- The diagonal of the threshold family is constantly false. -/
theorem thresholdEval_self (a : ℕ) : thresholdEval a a = false := by
  simp [thresholdEval]

/-- Every code fails the target at its own index. -/
theorem threshold_fails_at_self (a : ℕ) : thresholdEval a a ≠ constTrue a := by
  simp [thresholdEval, constTrue]

/-- Every finite set of inputs is passed by some code: take the index above the largest input. -/
theorem threshold_passes_finite (S : Finset ℕ) :
    ∃ a, ∀ x ∈ S, thresholdEval a x = constTrue x := by
  exact ⟨S.sup id + 1, fun x hx => by
    have hle : x ≤ S.sup id := Finset.le_sup (f := id) hx
    simp only [thresholdEval, constTrue, decide_eq_true_eq]
    omega⟩

/-- No code represents the target. -/
theorem threshold_not_represented : ¬ Represented thresholdEval constTrue := by
  rintro ⟨a, ha⟩
  exact threshold_fails_at_self a (congrFun ha a)

/-- Code `a` errs exactly at the inputs from `a` on. -/
theorem threshold_error_iff (a x : ℕ) : thresholdEval a x ≠ constTrue x ↔ a ≤ x := by
  simp [thresholdEval, constTrue]

/-- The error set of code `a` is enumerated by `k ↦ a + k`. -/
theorem threshold_error_enumerated (a x : ℕ) :
    thresholdEval a x ≠ constTrue x ↔ ∃ k, x = a + k := by
  rw [threshold_error_iff]
  constructor
  · intro h
    exact ⟨x - a, by omega⟩
  · rintro ⟨k, rfl⟩
    omega

/-- The geometric law on the inputs: input `x` has mass `2^-(x+1)`. -/
noncomputable def geometricLaw (x : ℕ) : ℝ := (1 / 2) ^ (x + 1)

/-- The geometric law has total mass one. -/
theorem geometricLaw_hasSum : HasSum geometricLaw 1 := by
  have h := hasSum_geometric_two.mul_left (1 / 2)
  have hf : (fun n : ℕ => (1 : ℝ) / 2 * (1 / 2) ^ n) = geometricLaw := by
    funext n
    rw [geometricLaw, pow_succ]
    ring
  rw [hf] at h
  norm_num at h
  exact h

/-- The mass of the geometric law on the error set of code `a`: the inputs `a, a + 1, …`. -/
noncomputable def thresholdErrorMass (a : ℕ) : ℝ := ∑' k : ℕ, geometricLaw (a + k)

/-- The error mass of code `a` sums to `2^-a`. -/
theorem thresholdErrorMass_hasSum (a : ℕ) :
    HasSum (fun k => geometricLaw (a + k)) ((1 / 2 : ℝ) ^ a) := by
  have h := geometricLaw_hasSum.mul_left ((1 / 2 : ℝ) ^ a)
  have hf : (fun k : ℕ => (1 / 2 : ℝ) ^ a * geometricLaw k) = fun k => geometricLaw (a + k) := by
    funext k
    simp only [geometricLaw]
    rw [← pow_add, Nat.add_assoc]
  rw [hf] at h
  simpa using h

/-- The mean error of code `a` under the geometric law is `2^-a`. -/
theorem thresholdErrorMass_eq (a : ℕ) : thresholdErrorMass a = (1 / 2) ^ a :=
  (thresholdErrorMass_hasSum a).tsum_eq

/-- The mean error tends to zero along the codes while every code fails at its own index. -/
theorem thresholdErrorMass_tendsto_zero :
    Filter.Tendsto thresholdErrorMass Filter.atTop (nhds 0) := by
  have hf : thresholdErrorMass = fun a : ℕ => (1 / 2 : ℝ) ^ a := funext thresholdErrorMass_eq
  rw [hf]
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

/-- The paired family: a code is an index and a bit, an input is an index and a bit, and the code
`(a, b)` answers `(c ∨ [k = a]) xor b` at the input `(k, c)`. -/
def pairedEval (code x : ℕ × Bool) : Bool := xor (x.2 || decide (x.1 = code.1)) code.2

/-- The complemented diagonal of the paired family: the bit of the input. -/
def pairedTarget (x : ℕ × Bool) : Bool := x.2

/-- The self-evaluation of the paired family is the complement of the bit. -/
theorem pairedEval_self (x : ℕ × Bool) : pairedEval x x = !x.2 := by
  obtain ⟨k, c⟩ := x
  cases c <;> simp [pairedEval]

/-- The target is the complement of the self-evaluation. -/
theorem pairedTarget_eq_not_self (x : ℕ × Bool) : pairedTarget x = !(pairedEval x x) := by
  rw [pairedEval_self, Bool.not_not]
  rfl

/-- The family is closed under negation: the second component of the code complements the row. -/
theorem pairedEval_negation_closed (a : ℕ) (b : Bool) (x : ℕ × Bool) :
    pairedEval (a, !b) x = !(pairedEval (a, b) x) := by
  obtain ⟨k, c⟩ := x
  cases b <;> cases c <;> simp [pairedEval]

/-- The row `(a, false)` errs on the target at the input `(a, false)` and nowhere else. -/
theorem pairedEval_error_iff (a : ℕ) (x : ℕ × Bool) :
    pairedEval (a, false) x ≠ pairedTarget x ↔ x = (a, false) := by
  obtain ⟨k, c⟩ := x
  cases c <;> simp [pairedEval, pairedTarget]

/-- The error set of the selected row is one point. -/
theorem paired_row_error_set (a : ℕ) :
    {x | pairedEval (a, false) x ≠ pairedTarget x} = {(a, false)} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, pairedEval_error_iff]

/-- Every code errs on the target at an input carrying its own index. -/
theorem paired_every_code_errs (code : ℕ × Bool) :
    ∃ x : ℕ × Bool, x.1 = code.1 ∧ pairedEval code x ≠ pairedTarget x := by
  obtain ⟨a, b⟩ := code
  cases b
  · exact ⟨(a, false), rfl, (pairedEval_error_iff a _).mpr rfl⟩
  · exact ⟨(a, true), rfl, by simp [pairedEval, pairedTarget]⟩

/-- No code represents the complemented diagonal. -/
theorem paired_not_represented : ¬ Represented pairedEval pairedTarget := by
  rintro ⟨code, hcode⟩
  obtain ⟨x, -, hx⟩ := paired_every_code_errs code
  exact hx (congrFun hcode x)

/-- No code represents the self-evaluation either. -/
theorem paired_self_evaluation_not_represented :
    ¬ Represented pairedEval (fun x => pairedEval x x) := by
  rintro ⟨⟨a, b⟩, h⟩
  have h1 := congrFun h (a, false)
  have h2 := congrFun h (a + 1, false)
  rw [pairedEval_self] at h1 h2
  cases b <;> simp [pairedEval] at h1 h2

/-- The restriction of the paired family to indices below `n`. -/
def pairedEvalFin (n : ℕ) (code x : Fin n × Bool) : Bool :=
  xor (x.2 || decide (x.1 = code.1)) code.2

/-- The complemented diagonal on the restriction. -/
def pairedTargetFin (n : ℕ) (x : Fin n × Bool) : Bool := x.2

/-- The restriction has `2n` codes and `2n` inputs. -/
theorem pairedFin_card (n : ℕ) : Fintype.card (Fin n × Bool) = 2 * n := by
  simp [mul_comm]

/-- On the restriction the selected row errs at its own index with the false bit and nowhere else. -/
theorem pairedFin_error_iff (n : ℕ) (a : Fin n) (x : Fin n × Bool) :
    pairedEvalFin n (a, false) x ≠ pairedTargetFin n x ↔ x = (a, false) := by
  obtain ⟨k, c⟩ := x
  cases c <;> simp [pairedEvalFin, pairedTargetFin]

/-- The selected row errs on exactly one of the `2n` inputs. -/
theorem pairedFin_selected_errors_once (n : ℕ) (a : Fin n) :
    (Finset.univ.filter (fun x => pairedEvalFin n (a, false) x ≠ pairedTargetFin n x)).card = 1 := by
  rw [Finset.card_eq_one]
  exact ⟨(a, false), by
    ext x
    simp [pairedFin_error_iff]⟩

/-- Every code errs on at least one of the `2n` inputs. -/
theorem pairedFin_every_code_errs (n : ℕ) (code : Fin n × Bool) :
    0 < (Finset.univ.filter (fun x => pairedEvalFin n code x ≠ pairedTargetFin n x)).card := by
  rw [Finset.card_pos]
  obtain ⟨a, b⟩ := code
  cases b
  · exact ⟨(a, false), by simp [pairedEvalFin, pairedTargetFin]⟩
  · exact ⟨(a, true), by simp [pairedEvalFin, pairedTargetFin]⟩

/-- Error set on inputs below the finite cutoff, with codes still drawn from all natural numbers. -/
def pairedBlockErrors (n : ℕ) (code : ℕ × Bool) : Finset (Fin n × Bool) :=
  Finset.univ.filter (fun x =>
    pairedEval code (x.1.val, x.2) ≠ pairedTarget (x.1.val, x.2))

/-- Number of wrong answers on the full finite test block. -/
def pairedBlockErrorCount (n : ℕ) (code : ℕ × Bool) : ℕ :=
  (pairedBlockErrors n code).card

/-- An in-block index with a false flip makes only the one error at (a, false). -/
theorem pairedBlock_false_errors_in (n a : ℕ) (ha : a < n) :
    pairedBlockErrors n (a, false) = {((⟨a, ha⟩ : Fin n), false)} := by
  classical
  ext x
  simp only [pairedBlockErrors, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_singleton]
  rw [pairedEval_error_iff]
  rcases x with ⟨i, b⟩
  simp only [Prod.mk.injEq, Fin.ext_iff]

/-- A false-flip code indexed beyond the tested block gives no wrong answer. -/
theorem pairedBlock_false_errors_out (n a : ℕ) (ha : n ≤ a) :
    pairedBlockErrors n (a, false) = ∅ := by
  classical
  ext x
  have hx : x.1.val ≠ a := by
    intro heq
    have hlt : a < n := by simpa [heq] using x.1.isLt
    exact (Nat.not_lt_of_ge ha) hlt
  simp [pairedBlockErrors, pairedEval_error_iff, Prod.mk.injEq, hx]

theorem pairedBlock_false_count_in (n a : ℕ) (ha : a < n) :
    pairedBlockErrorCount n (a, false) = 1 := by
  rw [pairedBlockErrorCount, pairedBlock_false_errors_in n a ha]
  simp

theorem pairedBlock_false_count_out (n a : ℕ) (ha : n ≤ a) :
    pairedBlockErrorCount n (a, false) = 0 := by
  rw [pairedBlockErrorCount, pairedBlock_false_errors_out n a ha]
  rfl

/-- Flipping the code bit complements each pointwise answer, so the two error counts
sum to the size of the test block, including the empty block. -/
theorem pairedBlock_complement_counts (n a : ℕ) :
    pairedBlockErrorCount n (a, false) +
      pairedBlockErrorCount n (a, true) = 2 * n := by
  classical
  let P : Fin n × Bool → Prop := fun x =>
    pairedEval (a, false) (x.1.val, x.2) ≠ pairedTarget (x.1.val, x.2)
  have hflip (x : Fin n × Bool) :
      (pairedEval (a, true) (x.1.val, x.2) ≠
        pairedTarget (x.1.val, x.2)) ↔ ¬ P x := by
    rcases x with ⟨i, b⟩
    cases b <;> by_cases h : i.val = a <;>
      simp [P, pairedEval, pairedTarget, h]
  have htrue :
      pairedBlockErrors n (a, true) =
        Finset.univ.filter (fun x : Fin n × Bool => ¬ P x) := by
    ext x
    simpa [pairedBlockErrors] using hflip x
  calc
    pairedBlockErrorCount n (a, false) + pairedBlockErrorCount n (a, true) =
        (Finset.univ.filter P).card +
          (Finset.univ.filter (fun x : Fin n × Bool => ¬ P x)).card := by
          change (pairedBlockErrors n (a, false)).card +
            (pairedBlockErrors n (a, true)).card = _
          rw [htrue]
          rfl
    _ = (Finset.univ : Finset (Fin n × Bool)).card :=
      Finset.filter_card_add_filter_neg_card_eq_card
        (s := Finset.univ) P
    _ = 2 * n := by
      rw [Finset.card_univ]
      exact pairedFin_card n

/-- Full finite-block error classification: an in-block false flip misses one input
and a true flip misses 2*n-1; outside the block these counts are zero and 2*n. -/
theorem pairedBlock_error_count_exact (n a : ℕ) (b : Bool) :
    pairedBlockErrorCount n (a, b) =
      if a < n then (if b = true then 2 * n - 1 else 1)
      else (if b = true then 2 * n else 0) := by
  by_cases ha : a < n
  · have hf := pairedBlock_false_count_in n a ha
    have hs := pairedBlock_complement_counts n a
    rw [hf] at hs
    cases b with
    | false => simpa [ha] using hf
    | true =>
      have ht : pairedBlockErrorCount n (a, true) = 2 * n - 1 := by omega
      simpa [ha] using ht
  · have hge : n ≤ a := Nat.le_of_not_gt ha
    have hf := pairedBlock_false_count_out n a hge
    have hs := pairedBlock_complement_counts n a
    rw [hf, Nat.zero_add] at hs
    cases b with
    | false => simpa [ha] using hf
    | true => simpa [ha] using hs

/-- On a nonempty test block zero error requires a false-flip code outside the block. -/
theorem pairedBlock_zero_iff_outside (n a : ℕ) (b : Bool) (hn : 0 < n) :
    pairedBlockErrorCount n (a, b) = 0 ↔ n ≤ a ∧ b = false := by
  constructor
  · intro hz
    by_cases ha : a < n
    · have hc := pairedBlock_error_count_exact n a b
      cases b with
      | false =>
        simp [ha] at hc
        omega
      | true =>
        simp [ha] at hc
        omega
    · have hge : n ≤ a := Nat.le_of_not_gt ha
      refine ⟨hge, ?_⟩
      cases b with
      | false => rfl
      | true =>
        have hc := pairedBlock_error_count_exact n a true
        simp [ha] at hc
        omega
  · rintro ⟨hge, rfl⟩
    exact pairedBlock_false_count_out n a hge

/-- With unrestricted code indices, every finite block has a zero-error code at index n. -/
theorem pairedBlock_unrestricted_minimum_zero (n : ℕ) :
    (∃ code : ℕ × Bool, pairedBlockErrorCount n code = 0) ∧
      ∀ code : ℕ × Bool, 0 ≤ pairedBlockErrorCount n code := by
  refine ⟨⟨(n, false), pairedBlock_false_count_out n n (Nat.le_refl n)⟩, ?_⟩
  intro code
  exact Nat.zero_le _

/-- A code whose index lies in the test block makes at least one error there. -/
theorem pairedBlock_bounded_count_positive (n : ℕ) (code : Fin n × Bool) :
    0 < pairedBlockErrorCount n (code.1.val, code.2) := by
  rcases code with ⟨a, b⟩
  have ha : a.val < n := a.isLt
  have hc := pairedBlock_error_count_exact n a.val b
  rw [if_pos ha] at hc
  show 0 < pairedBlockErrorCount n (a.val, b)
  rw [hc]
  cases b with
  | false => simp
  | true =>
    rw [if_pos rfl]
    omega

/-- Uniform mean error of a code on a positive-size finite test block. -/
noncomputable def pairedBlockMeanError (n : ℕ) (code : ℕ × Bool) : ℝ :=
  (pairedBlockErrorCount n code : ℝ) / (2 * (n : ℝ))

/-- For n > 0 the bounded-index minimum is exactly 1/(2*n), and a false flip attains it. -/
theorem pairedBlock_bounded_minimum_mean (n : ℕ) (hn : 0 < n) :
    (∃ code : Fin n × Bool,
      pairedBlockMeanError n (code.1.val, code.2) = 1 / (2 * (n : ℝ))) ∧
    (∀ code : Fin n × Bool,
      1 / (2 * (n : ℝ)) ≤ pairedBlockMeanError n (code.1.val, code.2)) := by
  constructor
  · refine ⟨(⟨0, hn⟩, false), ?_⟩
    have hc := pairedBlock_false_count_in n 0 hn
    simp [pairedBlockMeanError, hc]
  · intro code
    have hc : 1 ≤ pairedBlockErrorCount n (code.1.val, code.2) :=
      pairedBlock_bounded_count_positive n code
    unfold pairedBlockMeanError
    exact div_le_div_of_nonneg_right
      (by exact_mod_cast hc : (1 : ℝ) ≤
        (pairedBlockErrorCount n (code.1.val, code.2) : ℝ)) (by positivity)

/-- For n = 0 all unrestricted errors are zero and the bounded code carrier is empty. -/
theorem pairedBlock_empty_control :
    (∀ code : ℕ × Bool, pairedBlockErrorCount 0 code = 0) ∧
      ¬ ∃ _ : Fin 0 × Bool, True := by
  constructor
  · intro code
    simp [pairedBlockErrorCount, pairedBlockErrors]
  · rintro ⟨code, _⟩
    exact (Nat.not_lt_zero _) code.1.isLt

/-- A full-domain code has worst-case deterministic error one even when it fits
a finite block exactly. -/
def pairedPointError (code x : ℕ × Bool) : ℕ :=
  if pairedEval code x = pairedTarget x then 0 else 1

theorem pairedGlobal_worst_case_one (code : ℕ × Bool) :
    (∃ x : ℕ × Bool, pairedPointError code x = 1) ∧
      ∀ x : ℕ × Bool, pairedPointError code x ≤ 1 := by
  obtain ⟨x, -, hx⟩ := paired_every_code_errs code
  constructor
  · exact ⟨x, by simp [pairedPointError, hx]⟩
  · intro y
    by_cases heq : pairedEval code y = pairedTarget y <;>
      simp [pairedPointError, heq]

end OperatorKO7.Meta.BoundaryObserver.SelfEvaluationBounds
