import OperatorKO7.Meta.UUET.FiniteAmplitudeEntanglement
import OperatorKO7.Meta.ReverseBridge.BinEntropySharpBound

set_option autoImplicit false

/-!
# Four tests across two parties

Section 11 of the observation-principle manuscript. A table gives, for each of two tests of one
party and each of two tests of the other, the rate at which the two reports differ.

* Theorem 11.2(i): a table with an observer satisfies the eight cycle inequalities for the
  rates, and its score is at most `2` in absolute value.
* Proposition 11.3: the score is `4 - 4 (ρ₀ + ρ₁)` for the refused weights of the two
  questions answered from one symbol; one symbol about two hidden bits leaves at least two
  errors among the four states; with an observer `ρ₀ + ρ₁ ≥ 1/2`.
* Theorem 11.4: a table has vectors if and only if the angles `arccos (1 - 2 d)` satisfy the
  cycle inequalities with bound `π`; a table with an observer has vectors; with vectors the
  squares of the two excesses add to at most `1`, the score is at most `2 √2`, and the two
  answers hold at most one bit together.
* Proposition 11.5: kept weight, refused weight and the transposition; the label test and the
  transposition as matrices.
* Proposition 11.6(ii) in matrix form: vectors exist if and only if the four correlations have
  a positive semidefinite completion with unit diagonal.
* Example 11.7: the table with score `4` has no vectors.

Theorem 11.2(ii), the theorem of Fine, is the converse of Theorem 11.2(i) for tables with rates
in `[0, 1]`, and two modules that import this one prove it.
`ObserverRealization.observer_of_cycle` builds the observer by gluing two binary laws, and
`ObserverRealization.hasObserver_iff_cycle` states both directions.
`PitowskyPolytope.fine_theorem` derives it from the half-space description of the hull
(`PitowskyPolytope.mem_correlationPolytope_iff`), and `PitowskyPolytope.hasObserver_iff_cycleIneq`
states both directions. Proposition 11.6(i) is the central limit theorem and is not stated here.

Proof graph: `Audit/ledgers/operational-inexpressibility/TWO-VOIDS-PROOF-GRAPH.md`, node M9.

Relation: none; finite tables with real entries and vectors in Euclidean spaces.
Trust: kernel-only. No `sorry`, `admit`, `axiom`, `native_decide`. The inequality of
Theorem 11.4(iv) is `BinEntropySharpBound.binEntropy_ge_four_mul_log_two`.
-/

namespace OperatorKO7.Meta.BoundaryObserver.FourTestTables

open OperatorKO7.Meta.ReverseBridge.BinEntropySharpBound

/-! ## Tables, observers, vectors -/

/-- A table: the rate at which the reports of the tests `a x` and `b y` differ. -/
abbrev Table := Bool → Bool → ℝ

/-- The correlation of a pair of tests. -/
def corr (d : Table) (x y : Bool) : ℝ := 1 - 2 * d x y

/-- The score: three correlations added and the fourth subtracted. -/
def score (d : Table) : ℝ :=
  corr d false false + corr d false true + corr d true false - corr d true true

/-- The cycle inequalities with bound `l` for four numbers: each is at most the sum of the three
others, and that sum exceeds it by at most `2 * l`. -/
def CycleIneq (z : Bool → Bool → ℝ) (l : ℝ) : Prop :=
  ∀ x y : Bool,
    z x y ≤ (z false false + z false true + z true false + z true true) - z x y ∧
      (z false false + z false true + z true false + z true true) - 2 * z x y ≤ 2 * l

/-- The table has an observer: finitely many shared records with weights, and for each record a
report of every test. -/
def HasObserver (d : Table) : Prop :=
  ∃ (n : ℕ) (w : Fin n → ℝ) (A B : Bool → Fin n → Bool),
    (∀ l, 0 ≤ w l) ∧ ∑ l, w l = 1 ∧
      ∀ x y, d x y = ∑ l, if A x l ≠ B y l then w l else 0

/-- The table has vectors: four unit vectors whose inner products are the correlations. -/
def HasVectors (d : Table) : Prop :=
  ∃ (n : ℕ) (u v : Bool → EuclideanSpace ℝ (Fin n)),
    (∀ x, ‖u x‖ = 1) ∧ (∀ y, ‖v y‖ = 1) ∧ ∀ x y, @inner ℝ _ _ (u x) (v y) = corr d x y

/-- The refused weight of the first question. -/
noncomputable def refused0 (d : Table) : ℝ := (d false false + d true false) / 2

/-- The refused weight of the second question. -/
noncomputable def refused1 (d : Table) : ℝ := (d false true + 1 - d true true) / 2

/-- The indicator that two reports differ. -/
def disagree (a b : Bool) : ℝ := if a ≠ b then 1 else 0

/-- The sign of a report. -/
def boolSign (b : Bool) : ℝ := if b then 1 else -1

/-- The square of a sign is one. -/
theorem boolSign_sq (b : Bool) : boolSign b ^ 2 = 1 := by
  cases b <;> norm_num [boolSign]

/-- The product of two signs is `1 - 2 * disagree`. -/
theorem boolSign_mul (a b : Bool) : boolSign a * boolSign b = 1 - 2 * disagree a b := by
  cases a <;> cases b <;> norm_num [boolSign, disagree]

/-- Non-vacuity of `HasObserver`: the table in which no two reports differ has an observer with
one record. -/
theorem zeroTable_hasObserver : HasObserver (fun _ _ => 0) := by
  refine ⟨1, fun _ => 1, fun _ _ => true, fun _ _ => true, fun _ => zero_le_one, ?_, ?_⟩
  · simp
  · intro x y
    simp

/-! ## Theorem 11.2(i): tables with an observer -/

/-- Along the closed chain `a₀, b₀, a₁, b₁, a₀` the report changes an even number of times. -/
theorem cycle_parity (a0 a1 b0 b1 : Bool) :
    Even ((xor a0 b0).toNat + (xor a0 b1).toNat + (xor a1 b0).toNat + (xor a1 b1).toNat) := by
  cases a0 <;> cases a1 <;> cases b0 <;> cases b1 <;> decide

/-- For one record, the four indicators of disagreement satisfy the cycle inequalities with
bound `1`. -/
theorem disagree_cycle (a b : Bool → Bool) (x y : Bool) :
    disagree (a x) (b y) ≤
        (disagree (a false) (b false) + disagree (a false) (b true) +
          disagree (a true) (b false) + disagree (a true) (b true)) - disagree (a x) (b y) ∧
      (disagree (a false) (b false) + disagree (a false) (b true) +
          disagree (a true) (b false) + disagree (a true) (b true)) -
          2 * disagree (a x) (b y) ≤ 2 := by
  cases x <;> cases y <;>
    cases ha0 : a false <;> cases ha1 : a true <;> cases hb0 : b false <;> cases hb1 : b true <;>
    norm_num [disagree]

/--
Theorem 11.2(i), the inequalities.

Proves: a table with an observer satisfies the eight cycle inequalities for its rates, with
bound `1`.
Does not prove: the converse, the theorem of Fine. Two importing modules prove the converse for
tables with rates in `[0, 1]`: `ObserverRealization.observer_of_cycle` and
`PitowskyPolytope.fine_theorem`. The equivalence is `ObserverRealization.hasObserver_iff_cycle`
and `PitowskyPolytope.hasObserver_iff_cycleIneq`, the second through
`PitowskyPolytope.mem_correlationPolytope_iff`.
Relation: none. Trust: kernel-only.
-/
theorem observer_cycleIneq {d : Table} (h : HasObserver d) : CycleIneq d 1 := by
  obtain ⟨n, w, A, B, hw, hsum, hd⟩ := h
  have hd' : ∀ x y, d x y = ∑ l, w l * disagree (A x l) (B y l) := by
    intro x y
    rw [hd x y]
    refine Finset.sum_congr rfl fun l _ => ?_
    unfold disagree
    split_ifs <;> ring
  intro x y
  have hkey : (d false false + d false true + d true false + d true true) - 2 * d x y =
      ∑ l, w l * ((disagree (A false l) (B false l) + disagree (A false l) (B true l) +
        disagree (A true l) (B false l) + disagree (A true l) (B true l)) -
          2 * disagree (A x l) (B y l)) := by
    rw [hd' false false, hd' false true, hd' true false, hd' true true, hd' x y, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  have hnonneg : 0 ≤ (d false false + d false true + d true false + d true true) - 2 * d x y := by
    rw [hkey]
    refine Finset.sum_nonneg fun l _ => mul_nonneg (hw l) ?_
    have hl := (disagree_cycle (fun z => A z l) (fun z => B z l) x y).1
    linarith
  have hle : (d false false + d false true + d true false + d true true) - 2 * d x y ≤ 2 := by
    rw [hkey]
    calc ∑ l, w l * ((disagree (A false l) (B false l) + disagree (A false l) (B true l) +
          disagree (A true l) (B false l) + disagree (A true l) (B true l)) -
            2 * disagree (A x l) (B y l))
        ≤ ∑ l, w l * 2 := Finset.sum_le_sum fun l _ =>
          mul_le_mul_of_nonneg_left
            (disagree_cycle (fun z => A z l) (fun z => B z l) x y).2 (hw l)
      _ = 2 := by rw [← Finset.sum_mul, hsum, one_mul]
  constructor <;> linarith

/-- Theorem 11.2(i), the bound: a table with an observer has score at most `2` in absolute
value. -/
theorem observer_abs_score_le_two {d : Table} (h : HasObserver d) : |score d| ≤ 2 := by
  obtain ⟨h1, h2⟩ := observer_cycleIneq h true true
  unfold score corr
  rw [abs_le]
  constructor <;> linarith

/-! ## Proposition 11.3: the bound as the cost of a symbol -/

/-- Proposition 11.3(i): the score is `4 - 4 (ρ₀ + ρ₁)`. -/
theorem score_eq_refused (d : Table) : score d = 4 - 4 * (refused0 d + refused1 d) := by
  unfold score corr refused0 refused1
  ring

/--
Proposition 11.3(ii), the count.

Proves: for a symbol `m` with two values about a pair of bits and answers `g0`, `g1` read off
the symbol, the numbers of states at which the first answer is wrong and at which the second
answer is wrong add to at least two of the four states.
Does not prove: any statement about answers that read more than the symbol.
Relation: none. Trust: kernel-only.
-/
theorem one_symbol_two_bits (m : Bool × Bool → Bool) (g0 g1 : Bool → Bool) :
    2 ≤ (Finset.univ.filter (fun ξ : Bool × Bool => g0 (m ξ) ≠ ξ.1)).card +
        (Finset.univ.filter (fun ξ : Bool × Bool => g1 (m ξ) ≠ ξ.2)).card := by
  have hsub : (Finset.univ : Finset (Bool × Bool)) \
      {(g0 false, g1 false), (g0 true, g1 true)} ⊆
        Finset.univ.filter (fun ξ : Bool × Bool => g0 (m ξ) ≠ ξ.1) ∪
          Finset.univ.filter (fun ξ : Bool × Bool => g1 (m ξ) ≠ ξ.2) := by
    intro ξ hξ
    rw [Finset.mem_sdiff] at hξ
    by_contra hnot
    rw [Finset.mem_union, not_or] at hnot
    have h0 : g0 (m ξ) = ξ.1 := by
      by_contra hne
      exact hnot.1 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩)
    have h1 : g1 (m ξ) = ξ.2 := by
      by_contra hne
      exact hnot.2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩)
    apply hξ.2
    have hξeq : ξ = (g0 (m ξ), g1 (m ξ)) := Prod.ext h0.symm h1.symm
    rw [hξeq]
    cases m ξ
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hfour : (Finset.univ : Finset (Bool × Bool)).card = 4 := by decide
  have htwo : ({(g0 false, g1 false), (g0 true, g1 true)} : Finset (Bool × Bool)).card ≤ 2 :=
    Finset.card_le_two
  have hsd := Finset.le_card_sdiff
    ({(g0 false, g1 false), (g0 true, g1 true)} : Finset (Bool × Bool)) Finset.univ
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  omega

/-- Proposition 11.3(ii): with an observer the two refused weights add to at least one half. -/
theorem observer_refused_ge_half {d : Table} (h : HasObserver d) :
    1 / 2 ≤ refused0 d + refused1 d := by
  have hs := (abs_le.mp (observer_abs_score_le_two h)).2
  rw [score_eq_refused] at hs
  linarith

/-! ## Theorem 11.4: tables with vectors -/

/-- A vector of the Euclidean plane with coordinates of square sum one has norm one. -/
theorem norm_vec2 (a b : ℝ) (h : a ^ 2 + b ^ 2 = 1) :
    ‖(!₂[a, b] : EuclideanSpace ℝ (Fin 2))‖ = 1 := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  show Real.sqrt (‖a‖ ^ 2 + ‖b‖ ^ 2) = 1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs, h, Real.sqrt_one]

/-- The inner product of two vectors of the Euclidean plane. -/
theorem inner_vec2 (a b c e : ℝ) :
    @inner ℝ _ _ (!₂[a, b] : EuclideanSpace ℝ (Fin 2)) !₂[c, e] = a * c + b * e := by
  rw [PiLp.inner_apply, Fin.sum_univ_two]
  show @inner ℝ ℝ _ a c + @inner ℝ ℝ _ b e = a * c + b * e
  rw [RCLike.inner_apply, RCLike.inner_apply, conj_trivial, conj_trivial]
  ring

/-- A vector of Euclidean three-space with coordinates of square sum one has norm one. -/
theorem norm_vec3 (a b c : ℝ) (h : a ^ 2 + b ^ 2 + c ^ 2 = 1) :
    ‖(!₂[a, b, c] : EuclideanSpace ℝ (Fin 3))‖ = 1 := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_three]
  show Real.sqrt (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2) = 1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs, sq_abs, h,
    Real.sqrt_one]

/-- The inner product of two vectors of Euclidean three-space. -/
theorem inner_vec3 (a b c a' b' c' : ℝ) :
    @inner ℝ _ _ (!₂[a, b, c] : EuclideanSpace ℝ (Fin 3)) !₂[a', b', c'] =
      a * a' + b * b' + c * c' := by
  rw [PiLp.inner_apply, Fin.sum_univ_three]
  show @inner ℝ ℝ _ a a' + @inner ℝ ℝ _ b b' + @inner ℝ ℝ _ c c' = a * a' + b * b' + c * c'
  rw [RCLike.inner_apply, RCLike.inner_apply, RCLike.inner_apply, conj_trivial, conj_trivial,
    conj_trivial]
  ring

/--
Theorem 11.4(ii).

Proves: a table with an observer has vectors; the vectors are the reports as functions of the
record, weighted by the square roots of the weights.
Does not prove: the converse, which fails for the table of `extremeTable_not_observer`.
Relation: none. Trust: kernel-only.
-/
theorem observer_hasVectors {d : Table} (h : HasObserver d) : HasVectors d := by
  obtain ⟨n, w, A, B, hw, hsum, hd⟩ := h
  have hnorm : ∀ (C : Fin n → Bool),
      ‖(WithLp.toLp 2 (fun l => Real.sqrt (w l) * boolSign (C l)) : EuclideanSpace ℝ (Fin n))‖ =
        1 := by
    intro C
    rw [EuclideanSpace.norm_eq]
    have hs : ∑ l : Fin n, ‖(WithLp.toLp 2 (fun l => Real.sqrt (w l) * boolSign (C l)) :
        EuclideanSpace ℝ (Fin n)) l‖ ^ 2 = 1 := by
      rw [← hsum]
      refine Finset.sum_congr rfl fun l _ => ?_
      show ‖Real.sqrt (w l) * boolSign (C l)‖ ^ 2 = w l
      rw [Real.norm_eq_abs, sq_abs, mul_pow, Real.sq_sqrt (hw l), boolSign_sq, mul_one]
    rw [hs, Real.sqrt_one]
  refine ⟨n, fun x => WithLp.toLp 2 (fun l => Real.sqrt (w l) * boolSign (A x l)),
    fun y => WithLp.toLp 2 (fun l => Real.sqrt (w l) * boolSign (B y l)),
    fun x => hnorm (A x), fun y => hnorm (B y), ?_⟩
  intro x y
  rw [PiLp.inner_apply]
  have hterm : ∀ l : Fin n,
      @inner ℝ ℝ _ (Real.sqrt (w l) * boolSign (A x l)) (Real.sqrt (w l) * boolSign (B y l)) =
        w l - 2 * (if A x l ≠ B y l then w l else 0) := by
    intro l
    have hsq : Real.sqrt (w l) * Real.sqrt (w l) = w l := Real.mul_self_sqrt (hw l)
    have hprod : Real.sqrt (w l) * boolSign (B y l) * (Real.sqrt (w l) * boolSign (A x l)) =
        Real.sqrt (w l) * Real.sqrt (w l) * (boolSign (A x l) * boolSign (B y l)) := by ring
    rw [RCLike.inner_apply, conj_trivial, hprod, hsq, boolSign_mul]
    unfold disagree
    split_ifs <;> ring
  show ∑ l : Fin n,
      @inner ℝ ℝ _ (Real.sqrt (w l) * boolSign (A x l)) (Real.sqrt (w l) * boolSign (B y l)) =
        corr d x y
  rw [Finset.sum_congr rfl fun l _ => hterm l, Finset.sum_sub_distrib, hsum, ← Finset.mul_sum,
    ← hd x y]
  rfl

/-- The triangle inequality for the angles of three unit vectors of a real inner product
space. -/
theorem arccos_inner_triangle {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {a b c : E} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) :
    Real.arccos (@inner ℝ _ _ a c) ≤
      Real.arccos (@inner ℝ _ _ a b) + Real.arccos (@inner ℝ _ _ b c) := by
  have hp1 : |@inner ℝ _ _ a b| ≤ 1 := by
    have h := abs_real_inner_le_norm a b
    rwa [ha, hb, mul_one] at h
  have hr1 : |@inner ℝ _ _ b c| ≤ 1 := by
    have h := abs_real_inner_le_norm b c
    rwa [hb, hc, mul_one] at h
  obtain ⟨hpl, hpu⟩ := abs_le.mp hp1
  obtain ⟨hrl, hru⟩ := abs_le.mp hr1
  by_cases hsum : Real.arccos (@inner ℝ _ _ a b) + Real.arccos (@inner ℝ _ _ b c) ≤ Real.pi
  · have hperp : @inner ℝ _ _ (a - @inner ℝ _ _ a b • b) (c - @inner ℝ _ _ b c • b) =
        @inner ℝ _ _ a c - @inner ℝ _ _ a b * @inner ℝ _ _ b c := by
      rw [inner_sub_left, inner_sub_right, inner_sub_right, real_inner_smul_left,
        real_inner_smul_left, real_inner_smul_right, real_inner_smul_right,
        real_inner_self_eq_norm_sq, hb]
      ring
    have hna : ‖a - @inner ℝ _ _ a b • b‖ ^ 2 = 1 - @inner ℝ _ _ a b ^ 2 := by
      rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, ha, hb, Real.norm_eq_abs, mul_one,
        sq_abs]
      ring
    have hnc : ‖c - @inner ℝ _ _ b c • b‖ ^ 2 = 1 - @inner ℝ _ _ b c ^ 2 := by
      rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, hc, hb, Real.norm_eq_abs, mul_one,
        sq_abs, real_inner_comm b c]
      ring
    have hsa : ‖a - @inner ℝ _ _ a b • b‖ = Real.sqrt (1 - @inner ℝ _ _ a b ^ 2) := by
      rw [← hna, Real.sqrt_sq (norm_nonneg _)]
    have hsc : ‖c - @inner ℝ _ _ b c • b‖ = Real.sqrt (1 - @inner ℝ _ _ b c ^ 2) := by
      rw [← hnc, Real.sqrt_sq (norm_nonneg _)]
    have hcs := abs_real_inner_le_norm (a - @inner ℝ _ _ a b • b) (c - @inner ℝ _ _ b c • b)
    rw [hperp, hsa, hsc] at hcs
    have hcos : Real.cos (Real.arccos (@inner ℝ _ _ a b) + Real.arccos (@inner ℝ _ _ b c)) ≤
        @inner ℝ _ _ a c := by
      rw [Real.cos_add, Real.cos_arccos hpl hpu, Real.cos_arccos hrl hru, Real.sin_arccos,
        Real.sin_arccos]
      linarith [(abs_le.mp hcs).1]
    calc Real.arccos (@inner ℝ _ _ a c)
        ≤ Real.arccos (Real.cos (Real.arccos (@inner ℝ _ _ a b) +
            Real.arccos (@inner ℝ _ _ b c))) := Real.arccos_le_arccos hcos
      _ = Real.arccos (@inner ℝ _ _ a b) + Real.arccos (@inner ℝ _ _ b c) :=
          Real.arccos_cos (add_nonneg (Real.arccos_nonneg _) (Real.arccos_nonneg _)) hsum
  · push_neg at hsum
    linarith [Real.arccos_le_pi (@inner ℝ _ _ a c)]

/-- The angle between two of four unit vectors is at most the sum of the three other angles of
the closed chain `u, v', u', v, u`. -/
theorem arccos_inner_four_cycle {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {u u' v v' : E} (hu : ‖u‖ = 1) (hu' : ‖u'‖ = 1) (hv : ‖v‖ = 1) (hv' : ‖v'‖ = 1) :
    Real.arccos (@inner ℝ _ _ u v) ≤
      Real.arccos (@inner ℝ _ _ u v') + Real.arccos (@inner ℝ _ _ u' v') +
        Real.arccos (@inner ℝ _ _ u' v) := by
  have h1 := arccos_inner_triangle hu hv' hv
  have h2 := arccos_inner_triangle hv' hu' hv
  rw [real_inner_comm u' v'] at h2
  linarith

/-- A unit vector with prescribed angles `s` and `t` to two unit vectors at angle `β` exists
when `|s - t| ≤ β ≤ s + t` and `β + s + t ≤ 2π`; the statement is in coordinates. -/
theorem exists_third_vector {β s t : ℝ} (hβ0 : 0 ≤ β) (hβπ : β ≤ Real.pi) (hs0 : 0 ≤ s)
    (hsπ : s ≤ Real.pi) (ht0 : 0 ≤ t) (htπ : t ≤ Real.pi) (h1 : |s - t| ≤ β) (h2 : β ≤ s + t)
    (h3 : β + s + t ≤ 2 * Real.pi) :
    ∃ a b c : ℝ, a ^ 2 + b ^ 2 + c ^ 2 = 1 ∧ a = Real.cos s ∧
      a * Real.cos β + b * Real.sin β = Real.cos t := by
  obtain ⟨h1l, h1u⟩ := abs_le.mp h1
  have hcs : Real.cos s ^ 2 + Real.sin s ^ 2 = 1 := Real.cos_sq_add_sin_sq s
  rcases hβ0.eq_or_lt with hβ | hβpos
  · -- β = 0
    have hst : s = t := by linarith
    refine ⟨Real.cos s, 0, Real.sin s, by linarith, rfl, ?_⟩
    rw [← hβ, Real.cos_zero, Real.sin_zero, ← hst]
    ring
  rcases hβπ.eq_or_lt with hβ | hβlt
  · -- β = π
    have hst : t = Real.pi - s := by linarith
    refine ⟨Real.cos s, 0, Real.sin s, by linarith, rfl, ?_⟩
    rw [hβ, Real.cos_pi, Real.sin_pi, hst, Real.cos_pi_sub]
    ring
  · -- 0 < β < π
    have hsinβ : 0 < Real.sin β := Real.sin_pos_of_pos_of_lt_pi hβpos hβlt
    have hsins : 0 ≤ Real.sin s := Real.sin_nonneg_of_nonneg_of_le_pi hs0 hsπ
    have hupper : Real.cos t ≤ Real.cos s * Real.cos β + Real.sin s * Real.sin β := by
      rw [← Real.cos_sub, ← Real.cos_abs (s - β)]
      exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) htπ
        (abs_le.mpr ⟨by linarith, by linarith⟩)
    have hlower : Real.cos s * Real.cos β - Real.sin s * Real.sin β ≤ Real.cos t := by
      rw [← Real.cos_add]
      by_cases hsβ : s + β ≤ Real.pi
      · exact Real.cos_le_cos_of_nonneg_of_le_pi ht0 hsβ (by linarith)
      · push_neg at hsβ
        rw [← Real.cos_two_pi_sub]
        exact Real.cos_le_cos_of_nonneg_of_le_pi ht0 (by linarith) (by linarith)
    have hnum : (Real.cos t - Real.cos s * Real.cos β) ^ 2 ≤ (Real.sin s * Real.sin β) ^ 2 :=
      sq_le_sq' (by linarith) (by linarith)
    have hb2 : ((Real.cos t - Real.cos s * Real.cos β) / Real.sin β) ^ 2 ≤ Real.sin s ^ 2 := by
      rw [div_pow, div_le_iff₀ (by positivity)]
      calc (Real.cos t - Real.cos s * Real.cos β) ^ 2 ≤ (Real.sin s * Real.sin β) ^ 2 := hnum
        _ = Real.sin s ^ 2 * Real.sin β ^ 2 := by ring
    have hrest : 0 ≤ 1 - Real.cos s ^ 2 -
        ((Real.cos t - Real.cos s * Real.cos β) / Real.sin β) ^ 2 := by linarith
    refine ⟨Real.cos s, (Real.cos t - Real.cos s * Real.cos β) / Real.sin β,
      Real.sqrt (1 - Real.cos s ^ 2 -
        ((Real.cos t - Real.cos s * Real.cos β) / Real.sin β) ^ 2), ?_, rfl, ?_⟩
    · rw [Real.sq_sqrt hrest]
      ring
    · field_simp

/--
Theorem 11.4(i).

Proves: for a table with rates in `[0, 1]`, vectors exist if and only if the angles
`arccos (1 - 2 d)` satisfy the eight cycle inequalities with bound `π`.
Does not prove: uniqueness of the vectors.
Relation: none. Trust: kernel-only. The direction from vectors to inequalities is the triangle
inequality for angles, applied also after one vector is negated; the other direction places the
four vectors in Euclidean three-space.
-/
theorem hasVectors_iff_angle_cycle (d : Table) (hd : ∀ x y, 0 ≤ d x y ∧ d x y ≤ 1) :
    HasVectors d ↔ CycleIneq (fun x y => Real.arccos (corr d x y)) Real.pi := by
  constructor
  · rintro ⟨n, u, v, hu, hv, hin⟩
    have hneg : ∀ x, ‖-u x‖ = 1 := fun x => by rw [norm_neg, hu]
    have hθneg : ∀ x y, Real.arccos (@inner ℝ _ _ (-u x) (v y)) =
        Real.pi - Real.arccos (corr d x y) := fun x y => by
      rw [inner_neg_left, hin, Real.arccos_neg]
    have f00 := arccos_inner_four_cycle (hu false) (hu true) (hv false) (hv true)
    have f01 := arccos_inner_four_cycle (hu false) (hu true) (hv true) (hv false)
    have f10 := arccos_inner_four_cycle (hu true) (hu false) (hv false) (hv true)
    have f11 := arccos_inner_four_cycle (hu true) (hu false) (hv true) (hv false)
    have g11 := arccos_inner_four_cycle (hu true) (hneg false) (hv false) (hv true)
    have g10 := arccos_inner_four_cycle (hu true) (hneg false) (hv true) (hv false)
    have g00 := arccos_inner_four_cycle (hu false) (hneg true) (hv true) (hv false)
    have g01 := arccos_inner_four_cycle (hu false) (hneg true) (hv false) (hv true)
    rw [hθneg, hθneg] at g11 g10 g00 g01
    simp only [hin] at f00 f01 f10 f11 g11 g10 g00 g01
    intro x y
    cases x <;> cases y <;> dsimp only <;> constructor <;> linarith
  · intro hc
    have hcorr : ∀ x y, -1 ≤ corr d x y ∧ corr d x y ≤ 1 := by
      intro x y
      unfold corr
      constructor <;> linarith [(hd x y).1, (hd x y).2]
    have hcos : ∀ x y, Real.cos (Real.arccos (corr d x y)) = corr d x y := fun x y =>
      Real.cos_arccos (hcorr x y).1 (hcorr x y).2
    have h0 : ∀ x y, 0 ≤ Real.arccos (corr d x y) := fun x y => Real.arccos_nonneg _
    have hπ : ∀ x y, Real.arccos (corr d x y) ≤ Real.pi := fun x y => Real.arccos_le_pi _
    obtain ⟨a00, b00⟩ := hc false false
    obtain ⟨a01, b01⟩ := hc false true
    obtain ⟨a10, b10⟩ := hc true false
    obtain ⟨a11, b11⟩ := hc true true
    dsimp only at a00 b00 a01 b01 a10 b10 a11 b11
    have h000 := h0 false false
    have h001 := h0 false true
    have h010 := h0 true false
    have h011 := h0 true true
    have hπ00 := hπ false false
    have hπ01 := hπ false true
    have hπ10 := hπ true false
    have hπ11 := hπ true true
    -- the angle between the two vectors of the second party
    obtain ⟨β, hβdef⟩ : ∃ β, β = max
        |Real.arccos (corr d false false) - Real.arccos (corr d false true)|
        |Real.arccos (corr d true false) - Real.arccos (corr d true true)| := ⟨_, rfl⟩
    have hL0 : |Real.arccos (corr d false false) - Real.arccos (corr d false true)| ≤ β := by
      rw [hβdef]
      exact le_max_left _ _
    have hL1 : |Real.arccos (corr d true false) - Real.arccos (corr d true true)| ≤ β := by
      rw [hβdef]
      exact le_max_right _ _
    have hβ0 : 0 ≤ β := (abs_nonneg _).trans hL0
    have hβπ : β ≤ Real.pi := by
      rw [hβdef]
      exact max_le (abs_le.mpr ⟨by linarith, by linarith⟩) (abs_le.mpr ⟨by linarith, by linarith⟩)
    have hU0 : β ≤ Real.arccos (corr d false false) + Real.arccos (corr d false true) := by
      rw [hβdef]
      exact max_le (abs_le.mpr ⟨by linarith, by linarith⟩) (abs_le.mpr ⟨by linarith, by linarith⟩)
    have hU1 : β ≤ Real.arccos (corr d true false) + Real.arccos (corr d true true) := by
      rw [hβdef]
      exact max_le (abs_le.mpr ⟨by linarith, by linarith⟩) (abs_le.mpr ⟨by linarith, by linarith⟩)
    have hP0 : β + Real.arccos (corr d false false) + Real.arccos (corr d false true) ≤
        2 * Real.pi := by
      have hmax : β ≤ 2 * Real.pi - Real.arccos (corr d false false) -
          Real.arccos (corr d false true) := by
        rw [hβdef]
        exact max_le (abs_le.mpr ⟨by linarith, by linarith⟩)
          (abs_le.mpr ⟨by linarith, by linarith⟩)
      linarith
    have hP1 : β + Real.arccos (corr d true false) + Real.arccos (corr d true true) ≤
        2 * Real.pi := by
      have hmax : β ≤ 2 * Real.pi - Real.arccos (corr d true false) -
          Real.arccos (corr d true true) := by
        rw [hβdef]
        exact max_le (abs_le.mpr ⟨by linarith, by linarith⟩)
          (abs_le.mpr ⟨by linarith, by linarith⟩)
      linarith
    obtain ⟨a0, b0, c0, hn0, ha0, hi0⟩ :=
      exists_third_vector hβ0 hβπ h000 hπ00 h001 hπ01 hL0 hU0 hP0
    obtain ⟨a1, b1, c1, hn1, ha1, hi1⟩ :=
      exists_third_vector hβ0 hβπ h010 hπ10 h011 hπ11 hL1 hU1 hP1
    rw [hcos] at ha0 hi0 ha1 hi1
    refine ⟨3, fun x => cond x !₂[a1, b1, c1] !₂[a0, b0, c0],
      fun y => cond y !₂[Real.cos β, Real.sin β, 0] !₂[1, 0, 0], ?_, ?_, ?_⟩
    · intro x
      cases x
      · exact norm_vec3 a0 b0 c0 hn0
      · exact norm_vec3 a1 b1 c1 hn1
    · intro y
      cases y
      · exact norm_vec3 1 0 0 (by norm_num)
      · exact norm_vec3 (Real.cos β) (Real.sin β) 0 (by
          have := Real.cos_sq_add_sin_sq β
          linarith)
    · intro x y
      cases x <;> cases y
      · show @inner ℝ _ _ (!₂[a0, b0, c0] : EuclideanSpace ℝ (Fin 3)) !₂[1, 0, 0] = _
        rw [inner_vec3]
        linarith
      · show @inner ℝ _ _ (!₂[a0, b0, c0] : EuclideanSpace ℝ (Fin 3))
          !₂[Real.cos β, Real.sin β, 0] = _
        rw [inner_vec3]
        linarith
      · show @inner ℝ _ _ (!₂[a1, b1, c1] : EuclideanSpace ℝ (Fin 3)) !₂[1, 0, 0] = _
        rw [inner_vec3]
        linarith
      · show @inner ℝ _ _ (!₂[a1, b1, c1] : EuclideanSpace ℝ (Fin 3))
          !₂[Real.cos β, Real.sin β, 0] = _
        rw [inner_vec3]
        linarith

/--
Theorem 11.4(iii), the quadratic bound.

Proves: for a table with vectors, the squares of the excesses `1 - 2 ρ₀` and `1 - 2 ρ₁` of kept
over refused weight add to at most `1`.
Does not prove: the same for tables without vectors; `cornerTable` is a counterexample.
Relation: none. Trust: kernel-only. The proof is the inequality of Cauchy and Schwarz for the
sum and the difference of the two vectors of the first party.
-/
theorem vectors_quadratic {d : Table} (h : HasVectors d) :
    (1 - 2 * refused0 d) ^ 2 + (1 - 2 * refused1 d) ^ 2 ≤ 1 := by
  obtain ⟨n, u, v, hu, hv, hin⟩ := h
  have h1 : @inner ℝ _ _ (u false + u true) (v false) =
      corr d false false + corr d true false := by
    rw [inner_add_left, hin, hin]
  have h2 : @inner ℝ _ _ (u false - u true) (v true) =
      corr d false true - corr d true true := by
    rw [inner_sub_left, hin, hin]
  have hb1 := abs_real_inner_le_norm (u false + u true) (v false)
  have hb2 := abs_real_inner_le_norm (u false - u true) (v true)
  rw [h1, hv, mul_one] at hb1
  rw [h2, hv, mul_one] at hb2
  have hsq1 : (corr d false false + corr d true false) ^ 2 ≤ ‖u false + u true‖ ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hb1 2
  have hsq2 : (corr d false true - corr d true true) ^ 2 ≤ ‖u false - u true‖ ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hb2 2
  have hpar : ‖u false + u true‖ ^ 2 + ‖u false - u true‖ ^ 2 = 4 := by
    rw [norm_add_sq_real, norm_sub_sq_real, hu, hu]
    ring
  unfold corr at hsq1 hsq2
  unfold refused0 refused1
  nlinarith [hsq1, hsq2, hpar]

/-- Theorem 11.4(iii): with vectors the products of kept and refused weight add to at least one
quarter. -/
theorem vectors_kept_refused {d : Table} (h : HasVectors d) :
    1 / 4 ≤ (1 - refused0 d) * refused0 d + (1 - refused1 d) * refused1 d := by
  nlinarith [vectors_quadratic h]

/-- With vectors the sum of the two excesses is at most `√2` in absolute value. -/
theorem vectors_abs_excess_le {d : Table} (h : HasVectors d) :
    |(1 - 2 * refused0 d) + (1 - 2 * refused1 d)| ≤ Real.sqrt 2 := by
  refine abs_le_of_sq_le_sq ?_ (Real.sqrt_nonneg 2)
  rw [Real.sq_sqrt (by norm_num)]
  nlinarith [vectors_quadratic h,
    sq_nonneg ((1 - 2 * refused0 d) - (1 - 2 * refused1 d))]

/-- Theorem 11.4(iii): with vectors the two refused weights add to at least `1 - 1/√2`. -/
theorem vectors_refused_ge {d : Table} (h : HasVectors d) :
    1 - 1 / Real.sqrt 2 ≤ refused0 d + refused1 d := by
  have hs := (abs_le.mp (vectors_abs_excess_le h)).2
  have hsqrt : 1 / Real.sqrt 2 = Real.sqrt 2 / 2 := by
    have hpos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    field_simp
  rw [hsqrt]
  linarith

/-- Theorem 11.4(iii): a table with vectors has score at most `2 √2` in absolute value. -/
theorem vectors_abs_score_le {d : Table} (h : HasVectors d) :
    |score d| ≤ 2 * Real.sqrt 2 := by
  have hs := vectors_abs_excess_le h
  have hscore : score d = 2 * ((1 - 2 * refused0 d) + (1 - 2 * refused1 d)) := by
    rw [score_eq_refused]
    ring
  rw [hscore, abs_mul, abs_two]
  linarith

/-- The information of a reading with excess `y` of right over wrong answers, in bits, is at
most `y²`. This is the bound `h(p) ≥ 4 p (1 - p)` of `BinEntropySharpBound`. -/
theorem one_sub_binEntropy_le_sq (y : ℝ) (hy : |y| ≤ 1) :
    1 - Real.binEntropy ((1 + y) / 2) / Real.log 2 ≤ y ^ 2 := by
  obtain ⟨hyl, hyu⟩ := abs_le.mp hy
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hb := binEntropy_ge_four_mul_log_two (p := (1 + y) / 2) (by linarith) (by linarith)
  have hmul : (1 - y ^ 2) * Real.log 2 ≤ Real.binEntropy ((1 + y) / 2) := by
    have he : 4 * Real.log 2 * ((1 + y) / 2 * (1 - (1 + y) / 2)) = (1 - y ^ 2) * Real.log 2 := by
      ring
    rw [he] at hb
    exact hb
  have hdiv : 1 - y ^ 2 ≤ Real.binEntropy ((1 + y) / 2) / Real.log 2 := by
    rw [le_div_iff₀ hlog]
    exact hmul
  linarith

/--
Theorem 11.4(iv).

Proves: for a table with vectors, the information of the answer to the first question and the
information of the answer to the second, in bits, add to at most one.
Does not prove: the same for tables without vectors.
Relation: none. Trust: kernel-only.
-/
theorem vectors_bits_le_one {d : Table} (h : HasVectors d) :
    (1 - Real.binEntropy (refused0 d) / Real.log 2) +
        (1 - Real.binEntropy (refused1 d) / Real.log 2) ≤ 1 := by
  have hq := vectors_quadratic h
  have h0sq : (1 - 2 * refused0 d) ^ 2 ≤ 1 := by nlinarith [sq_nonneg (1 - 2 * refused1 d)]
  have h1sq : (1 - 2 * refused1 d) ^ 2 ≤ 1 := by nlinarith [sq_nonneg (1 - 2 * refused0 d)]
  have hb0 := one_sub_binEntropy_le_sq (1 - 2 * refused0 d)
    ((sq_le_one_iff_abs_le_one _).mp h0sq)
  have hb1 := one_sub_binEntropy_le_sq (1 - 2 * refused1 d)
    ((sq_le_one_iff_abs_le_one _).mp h1sq)
  have e0 : (1 + (1 - 2 * refused0 d)) / 2 = 1 - refused0 d := by ring
  have e1 : (1 + (1 - 2 * refused1 d)) / 2 = 1 - refused1 d := by ring
  rw [e0, Real.binEntropy_one_sub] at hb0
  rw [e1, Real.binEntropy_one_sub] at hb1
  linarith

/-! ## The extreme table and the table with score four -/

/-- The table with three angles `π / 4` and one angle `3 π / 4`. -/
noncomputable def extremeTable : Table := fun x y =>
  if x && y then (1 + 1 / Real.sqrt 2) / 2 else (1 - 1 / Real.sqrt 2) / 2

/-- The square of `1 / √2` is one half. -/
theorem inv_sqrt_two_sq : (1 / Real.sqrt 2) ^ 2 = 1 / 2 := by
  rw [div_pow, one_pow, Real.sq_sqrt (by norm_num)]

/-- Theorem 11.4(iii): the extreme table has vectors. -/
theorem extremeTable_hasVectors : HasVectors extremeTable := by
  have hs := inv_sqrt_two_sq
  refine ⟨2, fun x => cond x !₂[0, 1] !₂[1, 0],
    fun y => cond y !₂[1 / Real.sqrt 2, -(1 / Real.sqrt 2)] !₂[1 / Real.sqrt 2, 1 / Real.sqrt 2],
    ?_, ?_, ?_⟩
  · intro x
    cases x
    · exact norm_vec2 1 0 (by norm_num)
    · exact norm_vec2 0 1 (by norm_num)
  · intro y
    cases y
    · exact norm_vec2 _ _ (by linarith)
    · exact norm_vec2 _ _ (by nlinarith)
  · intro x y
    cases x <;> cases y
    · show @inner ℝ _ _ (!₂[1, 0] : EuclideanSpace ℝ (Fin 2))
        !₂[1 / Real.sqrt 2, 1 / Real.sqrt 2] = corr extremeTable false false
      rw [inner_vec2]
      simp [corr, extremeTable]
      ring
    · show @inner ℝ _ _ (!₂[1, 0] : EuclideanSpace ℝ (Fin 2))
        !₂[1 / Real.sqrt 2, -(1 / Real.sqrt 2)] = corr extremeTable false true
      rw [inner_vec2]
      simp [corr, extremeTable]
      ring
    · show @inner ℝ _ _ (!₂[0, 1] : EuclideanSpace ℝ (Fin 2))
        !₂[1 / Real.sqrt 2, 1 / Real.sqrt 2] = corr extremeTable true false
      rw [inner_vec2]
      simp [corr, extremeTable]
      ring
    · show @inner ℝ _ _ (!₂[0, 1] : EuclideanSpace ℝ (Fin 2))
        !₂[1 / Real.sqrt 2, -(1 / Real.sqrt 2)] = corr extremeTable true true
      rw [inner_vec2]
      simp [corr, extremeTable]
      ring

/-- Theorem 11.4(iii): the extreme table has score `2 √2`. -/
theorem extremeTable_score : score extremeTable = 2 * Real.sqrt 2 := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hpos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  simp only [score, corr, extremeTable, Bool.and_false, Bool.and_true,
    Bool.false_eq_true, if_false, if_true]
  field_simp
  nlinarith

/-- Theorem 11.4(iii): the refused weights of the extreme table add to `1 - 1/√2`. -/
theorem extremeTable_refused :
    refused0 extremeTable + refused1 extremeTable = 1 - 1 / Real.sqrt 2 := by
  simp only [refused0, refused1, extremeTable, Bool.and_false, Bool.and_true,
    Bool.false_eq_true, if_false, if_true]
  ring

/-- The extreme table has no observer of its single rounds. -/
theorem extremeTable_not_observer : ¬ HasObserver extremeTable := by
  intro h
  have hs := (abs_le.mp (observer_abs_score_le_two h)).2
  rw [extremeTable_score] at hs
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  nlinarith [Real.sqrt_nonneg 2]

/-- The table with three rates `0` and one rate `1`. -/
def cornerTable : Table := fun x y => if x && y then 1 else 0

/-- Example 11.7: the corner table has score `4`. -/
theorem cornerTable_score : score cornerTable = 4 := by
  simp only [score, corr, cornerTable, Bool.and_false, Bool.and_true,
    Bool.false_eq_true, if_false, if_true]
  norm_num

/-- Example 11.7: the corner table has no vectors. -/
theorem cornerTable_not_vectors : ¬ HasVectors cornerTable := by
  intro h
  have hs := (abs_le.mp (vectors_abs_score_le h)).2
  rw [cornerTable_score] at hs
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  nlinarith [Real.sqrt_nonneg 2]

/-! ## Proposition 11.5: kept weight, refused weight and the transposition -/

/-- Proposition 11.5(i): for two weights that add to one, the square of their difference and four
times their product add to one. -/
theorem kept_refused_identity (k r : ℝ) (h : k + r = 1) : (k - r) ^ 2 + 4 * (k * r) = 1 := by
  linear_combination (k + r + 1) * h

/-- Proposition 11.5(i) on the two-branch weights of the UUET development: four times the
product named `amplitudeEntanglement` there is the complement of the squared excess. -/
theorem kept_refused_eq_amplitude (w : OperatorKO7.Meta.UUET.TwoBranchWeight) :
    (w.p - w.q) ^ 2 + 4 * OperatorKO7.Meta.UUET.amplitudeEntanglement w = 1 := by
  unfold OperatorKO7.Meta.UUET.amplitudeEntanglement OperatorKO7.Meta.UUET.TwoBranchWeight.q
  ring

/-- The label test of a pair as a map on its real functions. -/
def labelMat : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]

/-- The transposition of a pair as a map on its real functions. -/
def swapMat : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

/-- Proposition 11.5(ii): the label test is an involution. -/
theorem labelMat_mul_self : labelMat * labelMat = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [labelMat, Matrix.mul_apply, Fin.sum_univ_two]

/-- Proposition 11.5(ii): the transposition is an involution. -/
theorem swapMat_mul_self : swapMat * swapMat = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swapMat, Matrix.mul_apply, Fin.sum_univ_two]

/-- Proposition 11.5(ii): the label test and the transposition anticommute. -/
theorem label_swap_anticommute : labelMat * swapMat = -(swapMat * labelMat) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [labelMat, swapMat, Matrix.mul_apply, Fin.sum_univ_two]

/-- Proposition 11.5(iii): the label test and the transposition are orthogonal for the trace
inner product. -/
theorem label_swap_trace : (labelMat * swapMat).trace = 0 := by
  simp [labelMat, swapMat, Matrix.trace, Fin.sum_univ_two]

/-- Proposition 11.5(iii): every unit combination of the label test and the transposition is an
involution, hence a test with the two values `1` and `-1`. -/
theorem unit_combination_mul_self (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) :
    (c • labelMat + s • swapMat) * (c • labelMat + s • swapMat) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [labelMat, swapMat, Matrix.mul_apply, Fin.sum_univ_two] <;> nlinarith [h]

/-! ## Proposition 11.6(ii) in matrix form -/

/--
Proposition 11.6(ii), as a statement about the covariance.

Proves: a table has vectors if and only if a positive semidefinite 4 by 4 real matrix with unit
diagonal has the four correlations at the places of the pairs of tests of different parties.
Does not prove: the statement about normal laws of totals; that part stays in the manuscript.
Relation: none. Trust: kernel-only.
-/
theorem hasVectors_iff_psd_completion (d : Table) :
    HasVectors d ↔
      ∃ G : Matrix (Fin 4) (Fin 4) ℝ, G.PosSemidef ∧ (∀ i, G i i = 1) ∧
        G 0 2 = corr d false false ∧ G 0 3 = corr d false true ∧
          G 1 2 = corr d true false ∧ G 1 3 = corr d true true := by
  constructor
  · rintro ⟨n, u, v, hu, hv, hin⟩
    obtain ⟨w, hw0, hw1, hw2, hw3, hnorm⟩ : ∃ w : Fin 4 → EuclideanSpace ℝ (Fin n),
        w 0 = u false ∧ w 1 = u true ∧ w 2 = v false ∧ w 3 = v true ∧ ∀ i, ‖w i‖ = 1 := by
      refine ⟨![u false, u true, v false, v true], rfl, rfl, rfl, rfl, ?_⟩
      intro i
      fin_cases i
      · exact hu false
      · exact hu true
      · exact hv false
      · exact hv true
    obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin n) (Fin 4) ℝ, ∀ l i, M l i = (w i) l :=
      ⟨Matrix.of fun l i => (w i) l, fun _ _ => rfl⟩
    have hentry : ∀ i j, (Matrix.conjTranspose M * M) i j = @inner ℝ _ _ (w i) (w j) := by
      intro i j
      rw [PiLp.inner_apply, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [RCLike.inner_apply, conj_trivial, Matrix.conjTranspose_apply, hM, hM, star_trivial,
        mul_comm]
    refine ⟨Matrix.conjTranspose M * M, Matrix.posSemidef_conjTranspose_mul_self M, ?_, ?_, ?_,
      ?_, ?_⟩
    · intro i
      rw [hentry, real_inner_self_eq_norm_sq, hnorm, one_pow]
    · rw [hentry, hw0, hw2]
      exact hin false false
    · rw [hentry, hw0, hw3]
      exact hin false true
    · rw [hentry, hw1, hw2]
      exact hin true false
    · rw [hentry, hw1, hw3]
      exact hin true true
  · rintro ⟨G, hG, hdiag, h02, h03, h12, h13⟩
    obtain ⟨B, hB⟩ := Matrix.posSemidef_iff_eq_conjTranspose_mul_self.mp hG
    have hinner : ∀ i j : Fin 4,
        @inner ℝ _ _ (WithLp.toLp 2 (fun l => B l i) : EuclideanSpace ℝ (Fin 4))
          (WithLp.toLp 2 (fun l => B l j)) = G i j := by
      intro i j
      rw [hB, PiLp.inner_apply, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun l _ => ?_
      show @inner ℝ ℝ _ (B l i) (B l j) = Matrix.conjTranspose B i l * B l j
      rw [RCLike.inner_apply, conj_trivial, Matrix.conjTranspose_apply, star_trivial, mul_comm]
    have hnorm : ∀ i : Fin 4,
        ‖(WithLp.toLp 2 (fun l => B l i) : EuclideanSpace ℝ (Fin 4))‖ = 1 := by
      intro i
      have hsq : ‖(WithLp.toLp 2 (fun l => B l i) : EuclideanSpace ℝ (Fin 4))‖ ^ 2 = 1 := by
        rw [← real_inner_self_eq_norm_sq, hinner, hdiag]
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp hsq
    refine ⟨4, fun x => cond x (WithLp.toLp 2 (fun l => B l 1)) (WithLp.toLp 2 (fun l => B l 0)),
      fun y => cond y (WithLp.toLp 2 (fun l => B l 3)) (WithLp.toLp 2 (fun l => B l 2)),
      ?_, ?_, ?_⟩
    · intro x
      cases x
      · exact hnorm 0
      · exact hnorm 1
    · intro y
      cases y
      · exact hnorm 2
      · exact hnorm 3
    · intro x y
      cases x <;> cases y
      · exact (hinner 0 2).trans h02
      · exact (hinner 0 3).trans h03
      · exact (hinner 1 2).trans h12
      · exact (hinner 1 3).trans h13

end OperatorKO7.Meta.BoundaryObserver.FourTestTables
