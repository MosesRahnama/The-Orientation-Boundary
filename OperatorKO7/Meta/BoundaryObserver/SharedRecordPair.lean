import OperatorKO7.Meta.UUET.PreEntanglement

set_option autoImplicit false

/-!
# A pair between its copy and its record

Section 10 of the observation-principle manuscript at the merged pair. The two members of a pair
carry opposite labels, and the label of the first member is drawn at equal chances. The joint law
of the two labels is `pairJoint`. It is the shared-record model of `PreEntanglement.lean` with one
report negated; it is not the product of its marginals; given the record it is a product; it is
the mixture of the two labellings of the pair; and in the shared-record model with arbitrary
report maps the law of one party's report does not depend on the other party's setting.

Proof graph: `Audit/ledgers/operational-inexpressibility/TWO-VOIDS-PROOF-GRAPH.md`, node M7.

Relation: none; finite laws with rational weights on `Bool`.
Trust: kernel-only. No `sorry`, `admit`, `axiom`, `native_decide`.
-/

namespace OperatorKO7.Meta.BoundaryObserver.SharedRecordPair

open OperatorKO7.Meta.UUET.PreEntanglement

/-- The joint law of the labels of the two members of a merged pair: the labels are opposite,
and each of the two assignments has weight one half. -/
def pairJoint (a b : Bool) : ℚ := if b = !a then 1 / 2 else 0

/-- The joint law of the two labels once the record `r` of the first label is given. -/
def pairPostRecord (r a b : Bool) : ℚ := (if a = r then 1 else 0) * (if b = !r then 1 else 0)

/-- The pair is the shared-record model at weight one half with the second report negated. -/
theorem pairJoint_eq_shared_flip (a b : Bool) : pairJoint a b = sharedJoint (1 / 2) a (!b) := by
  cases a <;> cases b <;> norm_num [pairJoint, sharedJoint]

/-- Proposition 10.2(i) at the pair: before the record, the joint law is not the product of its
marginals, at the cell where the first label is `true` and the second is `false`. -/
theorem pairJoint_not_product :
    pairJoint true false ≠
      (pairJoint true true + pairJoint true false) *
        (pairJoint true false + pairJoint false false) := by
  norm_num [pairJoint]

/-- Proposition 10.2(ii) at the pair: given the record, the joint law is the product of its
marginals. -/
theorem pairPostRecord_product (r a b : Bool) :
    pairPostRecord r a b =
      (pairPostRecord r a true + pairPostRecord r a false) *
        (pairPostRecord r true b + pairPostRecord r false b) := by
  cases r <;> cases a <;> cases b <;> norm_num [pairPostRecord]

/-- The law before the record is the equal mixture of the two laws after it. -/
theorem pairJoint_mixture (a b : Bool) :
    pairJoint a b = (1 / 2) * pairPostRecord true a b + (1 / 2) * pairPostRecord false a b := by
  cases a <;> cases b <;> norm_num [pairJoint, pairPostRecord]

/-- A permutation of `Bool` is the identity or the transposition. -/
theorem perm_bool_eq (e : Equiv.Perm Bool) : e = 1 ∨ e = Equiv.swap false true := by
  cases hf : e false
  · left
    refine Equiv.ext fun x => ?_
    cases x
    · exact hf
    · cases ht : e true
      · exact absurd (e.injective (hf.trans ht.symm)) Bool.false_ne_true
      · rfl
  · right
    refine Equiv.ext fun x => ?_
    cases x
    · rw [hf, Equiv.swap_apply_left]
    · cases ht : e true
      · rw [Equiv.swap_apply_right]
      · exact absurd (e.injective (hf.trans ht.symm)) Bool.false_ne_true

/--
The pair as the mixture of its two labellings.

Proves: the joint law of the two labels is the law of `(e false, e true)` when the labelling `e`
is drawn from the two permutations of `Bool` at equal chances.
Does not prove: any statement about labellings of sets with more than two elements.
Relation: none. Trust: kernel-only.
-/
theorem pairJoint_from_labellings (a b : Bool) :
    pairJoint a b =
      ∑ e : Equiv.Perm Bool, (1 / 2 : ℚ) * (if (e false, e true) = (a, b) then 1 else 0) := by
  have huniv : (Finset.univ : Finset (Equiv.Perm Bool)) = {1, Equiv.swap false true} := by
    ext e
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact perm_bool_eq e
  have hne : (1 : Equiv.Perm Bool) ≠ Equiv.swap false true := by
    intro h
    have h' := congrArg (fun e : Equiv.Perm Bool => e false) h
    simp at h'
  rw [huniv, Finset.sum_pair hne]
  cases a <;> cases b <;> norm_num [pairJoint]

/-- For a proposition `P` and a Boolean value `c`, the indicators of `P ∧ c = b` add over `b` to
the indicator of `P`. -/
theorem indicator_sum_bool (P : Prop) [Decidable P] (c : Bool) :
    (∑ b : Bool, (if P ∧ c = b then (1 : ℚ) else 0)) = if P then 1 else 0 := by
  rw [Fintype.sum_bool]
  by_cases hP : P <;> cases c <;> simp [hP]

/--
Proposition 10.2(iii) for arbitrary report maps.

Proves: in the shared-record model with record weight `w` and report maps `A`, `B`, the weight
of the report `a` of the first party under the setting `x` is the same for the settings `y` and
`y'` of the second party.
Does not prove: the same for models in which a report depends on the other party's setting.
Relation: none. Trust: kernel-only.
-/
theorem left_marginal_setting_free (w : ℚ) (A B : Bool → Bool → Bool) (x y y' a : Bool) :
    (∑ b : Bool, ∑ r : Bool,
        (if r then w else 1 - w) * (if A x r = a ∧ B y r = b then 1 else 0)) =
      ∑ b : Bool, ∑ r : Bool,
        (if r then w else 1 - w) * (if A x r = a ∧ B y' r = b then 1 else 0) := by
  have key : ∀ z : Bool,
      (∑ b : Bool, ∑ r : Bool,
          (if r then w else 1 - w) * (if A x r = a ∧ B z r = b then 1 else 0)) =
        ∑ r : Bool, (if r then w else 1 - w) * (if A x r = a then 1 else 0) := by
    intro z
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [← Finset.mul_sum, indicator_sum_bool]
  rw [key y, key y']


/-! ## Real shared-bit priors and all deterministic local report maps -/

/-- The original common bit is true with real weight w. The two raw labels
coincide. The expression is a probability law only for 0 ≤ w ≤ 1. -/
def realSharedJoint (w : ℝ) (a b : Bool) : ℝ :=
  if a = b then (if a then w else 1 - w) else 0

def realSharedLeftMarginal (w : ℝ) (a : Bool) : ℝ :=
  ∑ b : Bool, realSharedJoint w a b

def realSharedRightMarginal (w : ℝ) (b : Bool) : ℝ :=
  ∑ a : Bool, realSharedJoint w a b

/-- The raw two-party law has total mass one for every real parameter. -/
theorem realSharedJoint_normalized (w : ℝ) :
    (∑ a : Bool, ∑ b : Bool, realSharedJoint w a b) = 1 := by
  simp [realSharedJoint]

/-- Each joint cell has nonnegative mass for every real prior in [0,1]. -/
theorem realSharedJoint_nonnegative (w : ℝ) (h0 : 0 ≤ w) (h1 : w ≤ 1)
    (a b : Bool) : 0 ≤ realSharedJoint w a b := by
  cases a <;> cases b <;> simp [realSharedJoint] <;> linarith

/-- The exact two raw marginal laws are both the prior Bernoulli law. -/
theorem realSharedJoint_marginals (w : ℝ) :
    (∀ a : Bool, realSharedLeftMarginal w a = if a then w else 1 - w) ∧
      (∀ b : Bool, realSharedRightMarginal w b = if b then w else 1 - w) := by
  constructor
  · intro a
    cases a <;> simp [realSharedLeftMarginal, realSharedJoint]
  · intro b
    cases b <;> simp [realSharedRightMarginal, realSharedJoint]

/-- Independence at the (true,true) cell already forces one endpoint prior. -/
theorem realSharedJoint_product_cell_iff_endpoint (w : ℝ) :
    realSharedJoint w true true =
        realSharedLeftMarginal w true * realSharedRightMarginal w true ↔
      w = 0 ∨ w = 1 := by
  have hj : realSharedJoint w true true = w := by simp [realSharedJoint]
  have hl : realSharedLeftMarginal w true = w := by
    simp [realSharedLeftMarginal, realSharedJoint]
  have hr : realSharedRightMarginal w true = w := by
    simp [realSharedRightMarginal, realSharedJoint]
  rw [hj, hl, hr]
  constructor
  · intro heq
    have hm : w * (1 - w) = 0 := by nlinarith [heq]
    rcases mul_eq_zero.mp hm with hz | ho
    · exact Or.inl hz
    · exact Or.inr (by linarith)
  · rintro (hz | ho)
    · simp [hz]
    · simp [ho]

/-- The entire raw shared-label law factors exactly at the degenerate priors. -/
theorem realSharedJoint_product_iff_endpoints (w : ℝ) :
    (∀ a b : Bool, realSharedJoint w a b =
      realSharedLeftMarginal w a * realSharedRightMarginal w b) ↔
      w = 0 ∨ w = 1 := by
  constructor
  · intro h
    exact (realSharedJoint_product_cell_iff_endpoint w).mp (h true true)
  · intro h
    rcases h with h0 | h1
    · rw [h0]
      intro a b
      cases a <;> cases b <;>
        norm_num [realSharedJoint, realSharedLeftMarginal,
          realSharedRightMarginal, Fintype.sum_bool]
    · rw [h1]
      intro a b
      cases a <;> cases b <;>
        norm_num [realSharedJoint, realSharedLeftMarginal,
          realSharedRightMarginal, Fintype.sum_bool]

/-- Under admissible real priors, raw shared labels are nonproduct precisely
if the common bit has two positive possibilities. -/
theorem realSharedJoint_nonproduct_iff_interior (w : ℝ)
    (h0 : 0 ≤ w) (h1 : w ≤ 1) :
    (¬ ∀ a b : Bool, realSharedJoint w a b =
      realSharedLeftMarginal w a * realSharedRightMarginal w b) ↔
      0 < w ∧ w < 1 := by
  rw [realSharedJoint_product_iff_endpoints]
  constructor
  · intro h
    have hn0 : w ≠ 0 := fun hw => h (Or.inl hw)
    have hn1 : w ≠ 1 := fun hw => h (Or.inr hw)
    exact ⟨lt_of_le_of_ne h0 (Ne.symm hn0), lt_of_le_of_ne h1 hn1⟩
  · rintro ⟨hw0, hw1⟩ (hzero | hone)
    · exact (ne_of_gt hw0) hzero
    · exact (ne_of_lt hw1) hone

/-- Given the shared record r, arbitrary local deterministic maps A(x,r) and
B(y,r) produce a point-mass joint law. At an endpoint prior the kernel for a
zero-probability record is a formal definition, not a conditional probability. -/
def realConditionalJoint (A B : Bool → Bool → Bool)
    (x y r a b : Bool) : ℝ :=
  if A x r = a ∧ B y r = b then 1 else 0

theorem realConditionalJoint_nonnegative (A B : Bool → Bool → Bool)
    (x y r a b : Bool) : 0 ≤ realConditionalJoint A B x y r a b := by
  unfold realConditionalJoint
  split_ifs <;> norm_num

theorem realConditionalJoint_normalized (A B : Bool → Bool → Bool)
    (x y r : Bool) :
    (∑ a : Bool, ∑ b : Bool, realConditionalJoint A B x y r a b) = 1 := by
  cases hA : A x r <;> cases hB : B y r <;>
    simp only [realConditionalJoint, Fintype.sum_bool, hA, hB] <;> norm_num

theorem realConditionalJoint_leftMarginal (A B : Bool → Bool → Bool)
    (x y r a : Bool) :
    (∑ b : Bool, realConditionalJoint A B x y r a b) =
      if A x r = a then 1 else 0 := by
  cases hA : A x r <;> cases hB : B y r <;> cases a <;>
    norm_num [realConditionalJoint, Fintype.sum_bool, hA, hB]

theorem realConditionalJoint_rightMarginal (A B : Bool → Bool → Bool)
    (x y r b : Bool) :
    (∑ a : Bool, realConditionalJoint A B x y r a b) =
      if B y r = b then 1 else 0 := by
  cases hA : A x r <;> cases hB : B y r <;> cases b <;>
    norm_num [realConditionalJoint, Fintype.sum_bool, hA, hB]

/-- Given the record, the actual joint probability is the product of its
two true marginals for every settings pair. -/
theorem realConditionalJoint_product (A B : Bool → Bool → Bool)
    (x y r a b : Bool) :
    realConditionalJoint A B x y r a b =
      (∑ b' : Bool, realConditionalJoint A B x y r a b') *
      (∑ a' : Bool, realConditionalJoint A B x y r a' b) := by
  rw [realConditionalJoint_leftMarginal, realConditionalJoint_rightMarginal]
  by_cases hA : A x r = a <;> by_cases hB : B y r = b <;>
    simp [realConditionalJoint, hA, hB]

/-- The actual two-party law under local maps mixes the two conditional
record kernels with weights w and 1-w. -/
def realLocalJoint (w : ℝ) (A B : Bool → Bool → Bool)
    (x y a b : Bool) : ℝ :=
  w * realConditionalJoint A B x y true a b +
    (1 - w) * realConditionalJoint A B x y false a b

/-- Nonnegative real local laws follow under the admissible prior bounds. -/
theorem realLocalJoint_nonnegative (w : ℝ) (h0 : 0 ≤ w) (h1 : w ≤ 1)
    (A B : Bool → Bool → Bool) (x y a b : Bool) :
    0 ≤ realLocalJoint w A B x y a b := by
  unfold realLocalJoint
  exact add_nonneg
    (mul_nonneg h0 (realConditionalJoint_nonnegative A B x y true a b))
    (mul_nonneg (sub_nonneg.mpr h1)
      (realConditionalJoint_nonnegative A B x y false a b))

/-- The source law remains normalized under all deterministic local readouts. -/
theorem realLocalJoint_normalized (w : ℝ) (A B : Bool → Bool → Bool)
    (x y : Bool) :
    (∑ a : Bool, ∑ b : Bool, realLocalJoint w A B x y a b) = 1 := by
  calc
    (∑ a : Bool, ∑ b : Bool, realLocalJoint w A B x y a b) =
        w * (∑ a : Bool, ∑ b : Bool, realConditionalJoint A B x y true a b) +
          (1 - w) * (∑ a : Bool, ∑ b : Bool, realConditionalJoint A B x y false a b) := by
            simp only [realLocalJoint, Finset.sum_add_distrib, ← Finset.mul_sum]
    _ = w * 1 + (1 - w) * 1 := by
      rw [realConditionalJoint_normalized, realConditionalJoint_normalized]
    _ = 1 := by ring

/-- The first marginal is independent of the second setting and strategy. -/
theorem realLocalJoint_leftMarginal (w : ℝ) (A B : Bool → Bool → Bool)
    (x y a : Bool) :
    (∑ b : Bool, realLocalJoint w A B x y a b) =
      w * (if A x true = a then (1 : ℝ) else 0) +
        (1 - w) * (if A x false = a then (1 : ℝ) else 0) := by
  calc
    (∑ b : Bool, realLocalJoint w A B x y a b) =
        w * (∑ b : Bool, realConditionalJoint A B x y true a b) +
          (1 - w) * (∑ b : Bool, realConditionalJoint A B x y false a b) := by
            simp only [realLocalJoint, Finset.sum_add_distrib, ← Finset.mul_sum]
    _ = _ := by
      rw [realConditionalJoint_leftMarginal, realConditionalJoint_leftMarginal]

/-- The second marginal is independent of the first setting and strategy. -/
theorem realLocalJoint_rightMarginal (w : ℝ) (A B : Bool → Bool → Bool)
    (x y b : Bool) :
    (∑ a : Bool, realLocalJoint w A B x y a b) =
      w * (if B y true = b then (1 : ℝ) else 0) +
        (1 - w) * (if B y false = b then (1 : ℝ) else 0) := by
  calc
    (∑ a : Bool, realLocalJoint w A B x y a b) =
        w * (∑ a : Bool, realConditionalJoint A B x y true a b) +
          (1 - w) * (∑ a : Bool, realConditionalJoint A B x y false a b) := by
            simp only [realLocalJoint, Finset.sum_add_distrib, ← Finset.mul_sum]
    _ = _ := by
      rw [realConditionalJoint_rightMarginal, realConditionalJoint_rightMarginal]

/-- Both no-signalling identities hold for arbitrary local report maps,
including the endpoint priors. -/
theorem realLocalJoint_no_signalling (w : ℝ) (A B : Bool → Bool → Bool)
    (x x' y y' a b : Bool) :
    (∑ v : Bool, realLocalJoint w A B x y a v) =
        (∑ v : Bool, realLocalJoint w A B x y' a v) ∧
      (∑ u : Bool, realLocalJoint w A B x y u b) =
        (∑ u : Bool, realLocalJoint w A B x' y u b) := by
  constructor
  · rw [realLocalJoint_leftMarginal, realLocalJoint_leftMarginal]
  · rw [realLocalJoint_rightMarginal, realLocalJoint_rightMarginal]

/-- Identity local reports recover the raw real shared-bit law. -/
theorem realSharedJoint_eq_local_identity (w : ℝ) (a b : Bool) :
    realSharedJoint w a b =
      realLocalJoint w (fun _ r => r) (fun _ r => r) false false a b := by
  cases a <;> cases b <;>
    norm_num [realSharedJoint, realLocalJoint, realConditionalJoint]

/-- The original uniform opposite-labelled pair is this real law with the
second party's report negated. -/
theorem realShared_uniform_pair_compat (a b : Bool) :
    (pairJoint a b : ℝ) = realSharedJoint (1 / 2 : ℝ) a (!b) := by
  cases a <;> cases b <;> norm_num [pairJoint, realSharedJoint]

/-- Constant local reports can be independent even at an interior prior.
The nonproduct characterization concerns raw labels, not arbitrary reports. -/
theorem realLocalJoint_constant_reports (w : ℝ) (x y a b : Bool) :
    realLocalJoint w (fun _ _ => false) (fun _ _ => false) x y a b =
      (if a = false then (1 : ℝ) else 0) *
        (if b = false then (1 : ℝ) else 0) := by
  cases a <;> cases b <;>
    norm_num [realLocalJoint, realConditionalJoint]

/-! ## CHSH under every real shared-bit prior

Audit graph A7. The expectation is computed from realLocalJoint. The bound
includes endpoint priors and is attained by constant local outputs.
-/

/-- The signed value of a Boolean report. -/
def realReportSign (b : Bool) : ℝ := if b then 1 else -1

/-- Correlation computed from the normalized two-party report law. -/
noncomputable def realLocalCorrelation (w : ℝ) (A B : Bool → Bool → Bool)
    (x y : Bool) : ℝ :=
  ∑ a : Bool, ∑ b : Bool,
    realLocalJoint w A B x y a b * realReportSign a * realReportSign b

/-- The correlation at a given shared record is the product of its two reports. -/
theorem realConditionalJoint_correlation (A B : Bool → Bool → Bool)
    (x y r : Bool) :
    (∑ a : Bool, ∑ b : Bool,
      realConditionalJoint A B x y r a b * realReportSign a * realReportSign b) =
      realReportSign (A x r) * realReportSign (B y r) := by
  cases hA : A x r <;> cases hB : B y r <;>
    norm_num [realConditionalJoint, realReportSign, Fintype.sum_bool, hA, hB]

/-- The correlation is the prior-weighted sum of the conditional correlations. -/
theorem realLocalCorrelation_eq_weighted (w : ℝ) (A B : Bool → Bool → Bool)
    (x y : Bool) :
    realLocalCorrelation w A B x y =
      w * (realReportSign (A x true) * realReportSign (B y true)) +
        (1 - w) * (realReportSign (A x false) * realReportSign (B y false)) := by
  unfold realLocalCorrelation realLocalJoint
  calc
    _ = w * (∑ a : Bool, ∑ b : Bool,
          realConditionalJoint A B x y true a b * realReportSign a * realReportSign b) +
        (1 - w) * (∑ a : Bool, ∑ b : Bool,
          realConditionalJoint A B x y false a b * realReportSign a * realReportSign b) := by
      simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
    _ = _ := by
      rw [realConditionalJoint_correlation, realConditionalJoint_correlation]

/-- The CHSH expression on the actual real-valued report law. -/
noncomputable def realLocalCHSH (w : ℝ) (A B : Bool → Bool → Bool) : ℝ :=
  realLocalCorrelation w A B false false + realLocalCorrelation w A B false true +
    realLocalCorrelation w A B true false - realLocalCorrelation w A B true true

/-- A deterministic setting table has signed CHSH value two or minus two. -/
theorem realReportSign_chsh (a₀ a₁ b₀ b₁ : Bool) :
    realReportSign a₀ * realReportSign b₀ + realReportSign a₀ * realReportSign b₁ +
      realReportSign a₁ * realReportSign b₀ - realReportSign a₁ * realReportSign b₁ = 2 ∨
    realReportSign a₀ * realReportSign b₀ + realReportSign a₀ * realReportSign b₁ +
      realReportSign a₁ * realReportSign b₀ - realReportSign a₁ * realReportSign b₁ = -2 := by
  cases a₀ <;> cases a₁ <;> cases b₀ <;> cases b₁ <;> norm_num [realReportSign]

/-- Every real shared-bit distribution obeys the classical CHSH bound. -/
theorem realLocalCHSH_bound (w : ℝ) (h0 : 0 ≤ w) (h1 : w ≤ 1)
    (A B : Bool → Bool → Bool) : |realLocalCHSH w A B| ≤ 2 := by
  let score : Bool → ℝ := fun r =>
    realReportSign (A false r) * realReportSign (B false r) +
    realReportSign (A false r) * realReportSign (B true r) +
    realReportSign (A true r) * realReportSign (B false r) -
    realReportSign (A true r) * realReportSign (B true r)
  have hs (r : Bool) : -2 ≤ score r ∧ score r ≤ 2 := by
    rcases realReportSign_chsh (A false r) (A true r) (B false r) (B true r) with h | h
    · dsimp [score]
      rw [h]
      norm_num
    · dsimp [score]
      rw [h]
      norm_num
  have heq : realLocalCHSH w A B = w * score true + (1 - w) * score false := by
    unfold realLocalCHSH
    simp_rw [realLocalCorrelation_eq_weighted]
    dsimp [score]
    ring
  rw [heq, abs_le]
  have ht := hs true
  have hf := hs false
  constructor
  · have hleft := mul_le_mul_of_nonneg_left ht.1 h0
    have hright := mul_le_mul_of_nonneg_left hf.1 (sub_nonneg.mpr h1)
    nlinarith
  · have hleft := mul_le_mul_of_nonneg_left ht.2 h0
    have hright := mul_le_mul_of_nonneg_left hf.2 (sub_nonneg.mpr h1)
    nlinarith

/-- Constant local outputs attain the bound at every real prior. -/
theorem realLocalCHSH_attained (w : ℝ) :
    realLocalCHSH w (fun _ _ => true) (fun _ _ => true) = 2 := by
  unfold realLocalCHSH
  simp_rw [realLocalCorrelation_eq_weighted]
  norm_num [realReportSign]

end OperatorKO7.Meta.BoundaryObserver.SharedRecordPair
