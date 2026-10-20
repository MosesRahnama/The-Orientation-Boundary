import OperatorKO7.Meta.BoundaryObserver.ObserverRealization
import OperatorKO7.Meta.BoundaryObserver.FourTestTables

set_option autoImplicit false

/-!
# Four-test correlation polytope

Four correlations admit a common finite observer exactly for points in the deterministic hull.
The hull is the 16-cell: the vectors of the cube `[-1, 1]^4` that satisfy the eight cycle
inequalities (`mem_correlationPolytope_iff`). Each of the sixteen inequalities is a facet
(`sixteen_facets`), the hull is full-dimensional (`correlationPolytope_fullDim`), and Fine's
theorem follows (`fine_theorem`). The control table `cycleControl` satisfies the cycle
inequalities for its rates and lies outside the hull, so the eight bounds are needed.
Relation: none. Trust: kernel-only. No `sorry`, `admit`, `axiom`, `native_decide`.
-/

namespace OperatorKO7.Meta.BoundaryObserver.PitowskyPolytope

open FourTestTables ObserverRealization

/-- The four signed correlations of a deterministic pair of Boolean test reports. -/
def deterministicCorrelation (a b : Bool → Bool) : Bool × Bool → ℝ :=
  fun xy => boolSign (a xy.1) * boolSign (b xy.2)

/-- The four signed correlations associated with a table of disagreement rates. -/
def correlation (d : Table) : Bool × Bool → ℝ :=
  fun xy => 1 - 2 * d xy.1 xy.2

/-- A weighted deterministic correlation is one minus twice its weighted disagreement rate. -/
private theorem weighted_deterministicCorrelation_apply {L : Type*} [Fintype L]
    (w : L → ℝ) (A B : Bool → L → Bool) (x y : Bool) :
    (∑ l, w l • deterministicCorrelation (fun z => A z l) (fun z => B z l)) (x, y) =
      (∑ l, w l) - 2 * ∑ l, if A x l ≠ B y l then w l else 0 := by
  classical
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, deterministicCorrelation]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro l _
  rw [boolSign_mul]
  simp only [disagree]
  split_ifs <;> ring

/-- A four-test table has a finite common observer exactly when its correlation vector
belongs to the convex hull of deterministic correlation vectors. The equivalence holds for
all real tables, without a separate assumption that their rates lie in the unit interval. -/
theorem hasObserver_iff_mem_correlationPolytope (d : Table) :
    HasObserver d ↔
      correlation d ∈ convexHull ℝ
        (Set.range (fun ab : (Bool → Bool) × (Bool → Bool) =>
          deterministicCorrelation ab.1 ab.2)) := by
  classical
  let v : ((Bool → Bool) × (Bool → Bool)) → Bool × Bool → ℝ :=
    fun ab => deterministicCorrelation ab.1 ab.2
  change HasObserver d ↔ correlation d ∈ convexHull ℝ (Set.range v)
  rw [← realizable_iff_mem_convexHull v (correlation d)]
  constructor
  · rintro ⟨n, w, A, B, hw, hs, hreal⟩
    refine realizable_of_hidden v (correlation d)
      (fun l : Fin n => (fun x => A x l, fun y => B y l)) w hw hs ?_
    funext ⟨x, y⟩
    change (∑ l, w l • deterministicCorrelation (fun z => A z l) (fun z => B z l))
      (x, y) = 1 - 2 * d x y
    rw [weighted_deterministicCorrelation_apply, hs, hreal x y]
  · rintro ⟨w, hw, hs, hrep⟩
    refine hasObserver_of_fintype w (fun x ab => ab.1 x) (fun y ab => ab.2 y)
      hw hs ?_
    intro x y
    have he := congrFun hrep (x, y)
    change (∑ ab, w ab • deterministicCorrelation (fun z => ab.1 z)
      (fun z => ab.2 z)) (x, y) = 1 - 2 * d x y at he
    rw [weighted_deterministicCorrelation_apply, hs] at he
    linarith

/-- A canonical deterministic strategy fixes the second party's first output to false.
Its remaining three Boolean choices index the distinct correlation vectors. -/
private def canonicalCorrelation (t : Bool × Bool × Bool) : Bool × Bool → ℝ :=
  deterministicCorrelation (fun x => if x then t.2.1 else t.1)
    (fun y => if y then t.2.2 else false)

/-- Distinct canonical strategies give distinct signed correlation vectors. -/
private theorem canonicalCorrelation_injective : Function.Injective canonicalCorrelation := by
  intro ⟨a0, a1, b1⟩ ⟨a0', a1', b1'⟩ h
  have h00 := congrFun h (false, false)
  have h10 := congrFun h (true, false)
  have h01 := congrFun h (false, true)
  cases a0 <;> cases a1 <;> cases b1 <;>
    cases a0' <;> cases a1' <;> cases b1' <;>
    norm_num [canonicalCorrelation, deterministicCorrelation, boolSign] at h00 h10 h01 ⊢

/-- Every deterministic vector has exactly one canonical three-bit description. -/
private theorem deterministicCorrelation_range_eq_canonical :
    Set.range (fun ab : (Bool → Bool) × (Bool → Bool) =>
      deterministicCorrelation ab.1 ab.2) = Set.range canonicalCorrelation := by
  ext e
  constructor
  · rintro ⟨⟨a, b⟩, rfl⟩
    refine ⟨(Bool.xor (a false) (b false), Bool.xor (a true) (b false),
      Bool.xor (b true) (b false)), ?_⟩
    funext ⟨x, y⟩
    cases x <;> cases y <;>
      cases ha0 : a false <;> cases ha1 : a true <;>
      cases hb0 : b false <;> cases hb1 : b true <;>
      norm_num [canonicalCorrelation, deterministicCorrelation, boolSign,
        Bool.xor, ha0, ha1, hb0, hb1]
  · rintro ⟨⟨a0, a1, b1⟩, rfl⟩
    exact ⟨((fun x => if x then a1 else a0),
      (fun y => if y then b1 else false)), rfl⟩

/-- The sixteen deterministic pairs produce exactly eight distinct correlation vectors. -/
theorem correlationPolytope_card :
    (Set.range (fun ab : (Bool → Bool) × (Bool → Bool) =>
      deterministicCorrelation ab.1 ab.2)).ncard = 8 := by
  rw [deterministicCorrelation_range_eq_canonical, ← Set.image_univ]
  rw [Set.ncard_image_of_injective _ canonicalCorrelation_injective]
  norm_num [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_prod]

/-! ## The sixteen inequalities of the hull (Fine's theorem) -/

/-- The four correlations lie in the cube `[-1, 1]^4`: the eight bounds `|E xy| ≤ 1`. -/
def InBox (E : Bool × Bool → ℝ) : Prop := ∀ xy, |E xy| ≤ 1

/-- The eight cycle inequalities of Clauser, Horne, Shimony and Holt in correlation form: for
each index `e`, the sum of the three other correlations exceeds `E e` by at most `2`, and `E e`
exceeds that sum by at most `2`. -/
def CycleIneqE (E : Bool × Bool → ℝ) : Prop :=
  ∀ e : Bool × Bool,
    (∑ f ∈ Finset.univ.erase e, E f) - E e ≤ 2 ∧ E e - ∑ f ∈ Finset.univ.erase e, E f ≤ 2

/-- The sum of the three entries other than `e` is the total minus `E e`. -/
theorem sum_erase_eq (E : Bool × Bool → ℝ) (e : Bool × Bool) :
    ∑ f ∈ Finset.univ.erase e, E f =
      E (false, false) + E (false, true) + E (true, false) + E (true, true) - E e := by
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ e), Fintype.sum_prod_type, Fintype.sum_bool,
    Fintype.sum_bool, Fintype.sum_bool]
  ring

/-- The cycle inequalities with bound `1` for the rates are the cycle inequalities with bound `2`
for the correlations `E = 1 - 2 d`. -/
theorem cycleIneq_correlation_iff (d : Table) :
    CycleIneq d 1 ↔ CycleIneqE (correlation d) := by
  constructor
  · rintro h ⟨x, y⟩
    obtain ⟨h1, h2⟩ := h x y
    rw [sum_erase_eq]
    simp only [correlation]
    constructor <;> linarith
  · intro h x y
    have h' := h (x, y)
    rw [sum_erase_eq] at h'
    simp only [correlation] at h'
    obtain ⟨h1, h2⟩ := h'
    constructor <;> linarith

/-- Rates in the unit interval are correlations in `[-1, 1]`. -/
theorem inBox_correlation_iff (d : Table) :
    (∀ x y, 0 ≤ d x y ∧ d x y ≤ 1) ↔ InBox (correlation d) := by
  constructor
  · rintro h ⟨x, y⟩
    obtain ⟨h0, h1⟩ := h x y
    simp only [correlation]
    rw [abs_le]
    constructor <;> linarith
  · intro h x y
    have h' := abs_le.mp (h (x, y))
    simp only [correlation] at h'
    obtain ⟨h1, h2⟩ := h'
    constructor <;> linarith

/-- The character `(-1)^b` of one bit. -/
def bitSign (b : Bool) : ℝ := if b then -1 else 1

/-- The character of the bit `false` is `1`. -/
@[simp] theorem bitSign_false : bitSign false = 1 := by simp [bitSign]

/-- The character of the bit `true` is `-1`. -/
@[simp] theorem bitSign_true : bitSign true = -1 := by simp [bitSign]

/-- The coefficient of `E` along the character `(x, y) ↦ (-1)^(p x + q y)`: one quarter of the
inner product of `E` with that character. -/
noncomputable def coef (E : Bool × Bool → ℝ) (p q : Bool) : ℝ :=
  (E (false, false) + bitSign q * E (false, true) + bitSign p * E (true, false) +
    bitSign p * bitSign q * E (true, true)) / 4

/-- Every vector is the sum of the four characters weighted by its coefficients. -/
theorem apply_eq_sum_coef (E : Bool × Bool → ℝ) (x y : Bool) :
    E (x, y) = ∑ p, ∑ q, bitSign (p && x) * bitSign (q && y) * coef E p q := by
  cases x <;> cases y <;> simp only [Fintype.sum_bool, coef, Bool.and_true, Bool.and_false,
    bitSign_true, bitSign_false] <;> ring

/-- The deterministic pair of index `(p, q, s)`: the first party reports `s xor (p and x)` on test
`x`, the second party reports `q and y` on test `y`. -/
def hullVertex (i : Bool × Bool × Bool) : Bool × Bool → ℝ :=
  deterministicCorrelation (fun x => xor i.2.2 (i.1 && x)) (fun y => i.2.1 && y)

/-- The vertex of index `(p, q, s)` is `(-1)^s` times the character of `(p, q)`. -/
theorem hullVertex_apply (p q s x y : Bool) :
    hullVertex (p, q, s) (x, y) = bitSign s * bitSign (p && x) * bitSign (q && y) := by
  cases p <;> cases q <;> cases s <;> cases x <;> cases y <;>
    norm_num [hullVertex, deterministicCorrelation, boolSign]

/-- The eight indexed vertices are the eight deterministic correlation vectors. -/
theorem range_hullVertex :
    Set.range hullVertex = Set.range (fun ab : (Bool → Bool) × (Bool → Bool) =>
      deterministicCorrelation ab.1 ab.2) := by
  ext e
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨((fun x => xor i.2.2 (i.1 && x)), (fun y => i.2.1 && y)), rfl⟩
  · rintro ⟨⟨a, b⟩, rfl⟩
    refine ⟨(xor (a false) (a true), xor (b false) (b true), xor (a false) (b false)), ?_⟩
    funext ⟨x, y⟩
    rw [hullVertex_apply]
    cases x <;> cases y <;>
      cases ha0 : a false <;> cases ha1 : a true <;>
      cases hb0 : b false <;> cases hb1 : b true <;>
      norm_num [deterministicCorrelation, boolSign, ha0, ha1, hb0, hb1]

/-- Distinct indices give distinct vertices. -/
theorem hullVertex_injective : Function.Injective hullVertex := by
  rintro ⟨p, q, s⟩ ⟨p', q', s'⟩ h
  have h00 := congrFun h (false, false)
  have h01 := congrFun h (false, true)
  have h10 := congrFun h (true, false)
  simp only [hullVertex_apply] at h00 h01 h10
  cases p <;> cases q <;> cases s <;> cases p' <;> cases q' <;> cases s' <;>
    norm_num at h00 h01 h10 ⊢

/-- The coefficients of a vertex: `(-1)^s` at its own character and `0` at the three others. -/
theorem coef_hullVertex (p q s p' q' : Bool) :
    coef (hullVertex (p, q, s)) p' q' = if p' = p ∧ q' = q then bitSign s else 0 := by
  cases p <;> cases q <;> cases s <;> cases p' <;> cases q' <;>
    norm_num [coef, hullVertex_apply]

/-- The linear form of the sign pattern `s`: `∑ (-1)^(s p q) coef E p q`. The sixteen sign
patterns give the sixteen inequalities `facetForm s E ≤ 1`. -/
noncomputable def facetForm (s : Bool × Bool → Bool) (E : Bool × Bool → ℝ) : ℝ :=
  ∑ pq, bitSign (s pq) * coef E pq.1 pq.2

/-- The value of a sign-pattern form at a vertex. -/
theorem facetForm_hullVertex (s : Bool × Bool → Bool) (p q σ : Bool) :
    facetForm s (hullVertex (p, q, σ)) = bitSign (s (p, q)) * bitSign σ := by
  simp only [facetForm, coef_hullVertex, Fintype.sum_prod_type, Fintype.sum_bool]
  cases p <;> cases q <;> simp

/-- The sign-pattern form written out in the four correlations. -/
theorem facetForm_eq (s : Bool × Bool → Bool) (E : Bool × Bool → ℝ) :
    facetForm s E =
      bitSign (s (false, false)) * coef E false false +
        bitSign (s (false, true)) * coef E false true +
        bitSign (s (true, false)) * coef E true false +
        bitSign (s (true, true)) * coef E true true := by
  simp only [facetForm, Fintype.sum_prod_type, Fintype.sum_bool]
  ring

/-- The eight bounds and the eight cycle inequalities imply the sixteen sign-pattern
inequalities. -/
theorem facetForm_le_one_of_inBox_cycleIneqE {E : Bool × Bool → ℝ} (hb : InBox E)
    (hc : CycleIneqE E) (s : Bool × Bool → Bool) : facetForm s E ≤ 1 := by
  obtain ⟨b1, b1'⟩ := abs_le.mp (hb (false, false))
  obtain ⟨b2, b2'⟩ := abs_le.mp (hb (false, true))
  obtain ⟨b3, b3'⟩ := abs_le.mp (hb (true, false))
  obtain ⟨b4, b4'⟩ := abs_le.mp (hb (true, true))
  have c1 := hc (false, false)
  have c2 := hc (false, true)
  have c3 := hc (true, false)
  have c4 := hc (true, true)
  rw [sum_erase_eq] at c1 c2 c3 c4
  obtain ⟨c1, c1'⟩ := c1
  obtain ⟨c2, c2'⟩ := c2
  obtain ⟨c3, c3'⟩ := c3
  obtain ⟨c4, c4'⟩ := c4
  rw [facetForm_eq]
  simp only [coef, bitSign_true, bitSign_false]
  cases s (false, false) <;> cases s (false, true) <;> cases s (true, false) <;>
    cases s (true, true) <;> simp only [bitSign_true, bitSign_false]
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith

/-- The sign-pattern inequality with the four signs `a, b, c, e`, written out. -/
theorem signPattern_le {E : Bool × Bool → ℝ} (h : ∀ s : Bool × Bool → Bool, facetForm s E ≤ 1)
    (a b c e : Bool) :
    bitSign a * coef E false false + bitSign b * coef E false true +
      bitSign c * coef E true false + bitSign e * coef E true true ≤ 1 := by
  have h' := h (fun pq => if pq.1 then (if pq.2 then e else c) else (if pq.2 then b else a))
  rw [facetForm_eq] at h'
  simpa only [if_true, if_false, Bool.false_eq_true] using h'

/-- The sixteen sign-pattern inequalities imply the eight bounds and the eight cycle
inequalities. -/
theorem inBox_cycleIneqE_of_facetForm {E : Bool × Bool → ℝ}
    (h : ∀ s : Bool × Bool → Bool, facetForm s E ≤ 1) : InBox E ∧ CycleIneqE E := by
  have k := signPattern_le h
  simp only [coef, bitSign_true, bitSign_false] at k
  refine ⟨fun xy => ?_, fun xy => ?_⟩
  · obtain ⟨x, y⟩ := xy
    rw [abs_le]
    cases x <;> cases y
    · have h1 := k false false false false
      have h2 := k true true true true
      simp only [bitSign_true, bitSign_false] at h1 h2
      constructor <;> linarith
    · have h1 := k false true false true
      have h2 := k true false true false
      simp only [bitSign_true, bitSign_false] at h1 h2
      constructor <;> linarith
    · have h1 := k false false true true
      have h2 := k true true false false
      simp only [bitSign_true, bitSign_false] at h1 h2
      constructor <;> linarith
    · have h1 := k false true true false
      have h2 := k true false false true
      simp only [bitSign_true, bitSign_false] at h1 h2
      constructor <;> linarith
  · rw [sum_erase_eq]
    obtain ⟨x, y⟩ := xy
    cases x <;> cases y
    · have h1 := k false true true true
      have h2 := k true false false false
      simp only [bitSign_true, bitSign_false] at h1 h2
      constructor <;> linarith
    · have h1 := k false false true false
      have h2 := k true true false true
      simp only [bitSign_true, bitSign_false] at h1 h2
      constructor <;> linarith
    · have h1 := k false true false false
      have h2 := k true false true true
      simp only [bitSign_true, bitSign_false] at h1 h2
      constructor <;> linarith
    · have h1 := k false false false true
      have h2 := k true true true false
      simp only [bitSign_true, bitSign_false] at h1 h2
      constructor <;> linarith

/-- The eight bounds and the eight cycle inequalities are the sixteen sign-pattern
inequalities. -/
theorem inBox_cycleIneqE_iff (E : Bool × Bool → ℝ) :
    InBox E ∧ CycleIneqE E ↔ ∀ s : Bool × Bool → Bool, facetForm s E ≤ 1 :=
  ⟨fun h => facetForm_le_one_of_inBox_cycleIneqE h.1 h.2, inBox_cycleIneqE_of_facetForm⟩

/-- Under the sixteen inequalities the four coefficients have absolute values of sum at most
one. -/
theorem sum_abs_coef_le_one {E : Bool × Bool → ℝ} (h : ∀ s, facetForm s E ≤ 1) :
    ∑ pq : Bool × Bool, |coef E pq.1 pq.2| ≤ 1 := by
  calc ∑ pq : Bool × Bool, |coef E pq.1 pq.2|
      = facetForm (fun pq => decide (coef E pq.1 pq.2 < 0)) E := by
        unfold facetForm
        refine Finset.sum_congr rfl fun pq _ => ?_
        by_cases hc : coef E pq.1 pq.2 < 0
        · simp [hc, abs_of_neg hc]
        · simp [hc, abs_of_nonneg (not_lt.mp hc)]
    _ ≤ 1 := h _

/-- The mass left over after each coefficient takes its absolute value. -/
noncomputable def hullSlack (E : Bool × Bool → ℝ) : ℝ :=
  1 - ∑ pq : Bool × Bool, |coef E pq.1 pq.2|

/-- The weight of the vertex `(p, q, s)`: the positive or negative part of `coef E p q`, plus an
equal share of the slack. -/
noncomputable def hullWeight (E : Bool × Bool → ℝ) (i : Bool × Bool × Bool) : ℝ :=
  (|coef E i.1 i.2.1| + bitSign i.2.2 * coef E i.1 i.2.1) / 2 + hullSlack E / 8

/-- The converse: a vector satisfying the sixteen inequalities is the convex combination of the
eight vertices with the weights `hullWeight`. -/
theorem mem_convexHull_of_facetForm {E : Bool × Bool → ℝ} (h : ∀ s, facetForm s E ≤ 1) :
    E ∈ convexHull ℝ (Set.range (fun ab : (Bool → Bool) × (Bool → Bool) =>
      deterministicCorrelation ab.1 ab.2)) := by
  have hslack : 0 ≤ hullSlack E := by
    unfold hullSlack
    linarith [sum_abs_coef_le_one h]
  have hw : ∀ i ∈ (Finset.univ : Finset (Bool × Bool × Bool)), 0 ≤ hullWeight E i := by
    rintro ⟨p, q, s⟩ -
    have h1 := neg_abs_le (coef E p q)
    have h2 := le_abs_self (coef E p q)
    cases s <;> simp only [hullWeight, bitSign_true, bitSign_false] <;> linarith
  have hsum : ∑ i ∈ (Finset.univ : Finset (Bool × Bool × Bool)), hullWeight E i = 1 := by
    simp only [hullWeight, hullSlack, Fintype.sum_prod_type, Fintype.sum_bool, bitSign_true,
      bitSign_false]
    ring
  have hmem : ∀ i ∈ (Finset.univ : Finset (Bool × Bool × Bool)),
      hullVertex i ∈ convexHull ℝ (Set.range (fun ab : (Bool → Bool) × (Bool → Bool) =>
        deterministicCorrelation ab.1 ab.2)) := fun i _ =>
    subset_convexHull ℝ _ ⟨((fun x => xor i.2.2 (i.1 && x)), (fun y => i.2.1 && y)), rfl⟩
  have hc := (convex_convexHull ℝ _).sum_mem hw hsum hmem
  convert hc using 1
  funext ⟨x, y⟩
  rw [apply_eq_sum_coef E x y]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fintype.sum_prod_type,
    Fintype.sum_bool, hullVertex_apply, hullWeight]
  cases x <;> cases y <;> simp only [Bool.and_true, Bool.and_false, bitSign_true,
    bitSign_false] <;> ring

/-- The forward direction: every point of the hull satisfies the sixteen inequalities. -/
theorem facetForm_le_one_of_mem {E : Bool × Bool → ℝ}
    (hE : E ∈ convexHull ℝ (Set.range (fun ab : (Bool → Bool) × (Bool → Bool) =>
      deterministicCorrelation ab.1 ab.2))) :
    ∀ s, facetForm s E ≤ 1 := by
  have hconv : Convex ℝ {E : Bool × Bool → ℝ | ∀ s, facetForm s E ≤ 1} := by
    intro x hx y hy a b ha hb hab
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    intro s
    have hlin : facetForm s (a • x + b • y) = a * facetForm s x + b * facetForm s y := by
      simp only [facetForm, coef, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Fintype.sum_prod_type, Fintype.sum_bool]
      ring
    rw [hlin]
    linarith [mul_le_mul_of_nonneg_left (hx s) ha, mul_le_mul_of_nonneg_left (hy s) hb]
  have hsub : Set.range hullVertex ⊆ {E : Bool × Bool → ℝ | ∀ s, facetForm s E ≤ 1} := by
    rintro _ ⟨⟨p, q, σ⟩, rfl⟩
    simp only [Set.mem_setOf_eq]
    intro s
    rw [facetForm_hullVertex]
    cases s (p, q) <;> cases σ <;> norm_num
  rw [← range_hullVertex] at hE
  exact convexHull_min hsub hconv hE

/--
The half-space description of the correlation polytope.

Proves: a vector `E : Bool × Bool → ℝ` lies in the convex hull of the eight deterministic
correlation vectors iff it lies in the cube `[-1, 1]^4` and satisfies the eight cycle
inequalities. The forward direction holds since each vertex satisfies the sixteen inequalities
and they are preserved under convex combination; the converse writes `E` as the convex
combination of the eight vertices with the weights `hullWeight E`.
Relation: none. Trust: kernel-only.
-/
theorem mem_correlationPolytope_iff (E : Bool × Bool → ℝ) :
    E ∈ convexHull ℝ (Set.range (fun ab : (Bool → Bool) × (Bool → Bool) =>
      deterministicCorrelation ab.1 ab.2)) ↔ InBox E ∧ CycleIneqE E := by
  rw [inBox_cycleIneqE_iff]
  exact ⟨facetForm_le_one_of_mem, mem_convexHull_of_facetForm⟩

/--
Fine's theorem for two tests on each side, Theorem `thm:observer-tables`(ii).

Proves: a table with rates in `[0, 1]` that satisfies the cycle inequalities with bound `1` has an
observer, through the half-space description of the hull. The same statement is
`ObserverRealization.observer_of_cycle`, proved there by gluing two binary laws.
Relation: none. Trust: kernel-only.
-/
theorem fine_theorem (d : Table) (hd : ∀ x y, 0 ≤ d x y ∧ d x y ≤ 1) (hc : CycleIneq d 1) :
    HasObserver d :=
  (hasObserver_iff_mem_correlationPolytope d).2 ((mem_correlationPolytope_iff _).2
    ⟨(inBox_correlation_iff d).1 hd, (cycleIneq_correlation_iff d).1 hc⟩)

/-- For a table with rates in `[0, 1]`, an observer exists iff the rates satisfy the cycle
inequalities with bound `1`: `observer_cycleIneq` and `fine_theorem`. -/
theorem hasObserver_iff_cycleIneq (d : Table) (hd : ∀ x y, 0 ≤ d x y ∧ d x y ≤ 1) :
    HasObserver d ↔ CycleIneq d 1 :=
  ⟨observer_cycleIneq, fine_theorem d hd⟩

/-- The four vertices `hullVertex (p, q, s (p, q))` are linearly independent in
`Bool × Bool → ℝ`: up to sign they are the four orthogonal characters. -/
theorem facetVertices_linearIndependent (s : Bool × Bool → Bool) :
    LinearIndependent ℝ (fun pq : Bool × Bool => hullVertex (pq.1, pq.2, s pq)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg pq
  have e00 := congrFun hg (false, false)
  have e01 := congrFun hg (false, true)
  have e10 := congrFun hg (true, false)
  have e11 := congrFun hg (true, true)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fintype.sum_prod_type,
    Fintype.sum_bool, hullVertex_apply, Pi.zero_apply, Bool.and_true, Bool.and_false,
    bitSign_true, bitSign_false] at e00 e01 e10 e11
  obtain ⟨p, q⟩ := pq
  cases h1 : s (false, false) <;> cases h2 : s (false, true) <;> cases h3 : s (true, false) <;>
    cases h4 : s (true, true) <;>
    simp only [h1, h2, h3, h4, bitSign_true, bitSign_false] at e00 e01 e10 e11 <;>
    cases p <;> cases q <;> linarith

/--
The sixteen facets.

Proves: for each sign pattern `s`, the inequality `facetForm s E ≤ 1` holds at every deterministic
correlation vector, it is tight at a deterministic vector iff that vector is one of the four
vertices `hullVertex (p, q, s (p, q))`, and those four vertices are affinely independent. With
`inBox_cycleIneqE_iff` the sixteen forms are the eight bounds and the eight cycle inequalities,
with `facetForm_injective` they are sixteen distinct forms, and with
`correlationPolytope_fullDim` the hull has dimension four, so each face is a facet.
Relation: none. Trust: kernel-only.
-/
theorem sixteen_facets (s : Bool × Bool → Bool) :
    (∀ v ∈ Set.range (fun ab : (Bool → Bool) × (Bool → Bool) =>
        deterministicCorrelation ab.1 ab.2), facetForm s v ≤ 1) ∧
    (∀ v ∈ Set.range (fun ab : (Bool → Bool) × (Bool → Bool) =>
        deterministicCorrelation ab.1 ab.2),
      facetForm s v = 1 ↔ v ∈ Set.range (fun pq : Bool × Bool => hullVertex (pq.1, pq.2, s pq))) ∧
    AffineIndependent ℝ (fun pq : Bool × Bool => hullVertex (pq.1, pq.2, s pq)) := by
  refine ⟨fun v hv => facetForm_le_one_of_mem (subset_convexHull ℝ _ hv) s, ?_, ?_⟩
  · rw [← range_hullVertex]
    rintro _ ⟨⟨p, q, σ⟩, rfl⟩
    rw [facetForm_hullVertex]
    constructor
    · intro hσ
      have hs : s (p, q) = σ := by
        cases h1 : s (p, q) <;> cases σ <;> rw [h1] at hσ <;> norm_num at hσ ⊢
      exact ⟨(p, q), by simp [hs]⟩
    · rintro ⟨⟨p', q'⟩, hpq⟩
      have := hullVertex_injective hpq
      simp only [Prod.mk.injEq] at this
      obtain ⟨rfl, rfl, hσ⟩ := this
      rw [← hσ]
      cases s (p', q') <;> norm_num
  · exact affineIndependent_iff.2 fun t w _ hw =>
      linearIndependent_iff'.1 (facetVertices_linearIndependent s) t w hw

/-- Distinct sign patterns give distinct linear forms: the form of `s` takes the value
`(-1)^(s (p, q))` at the vertex `hullVertex (p, q, false)`. -/
theorem facetForm_injective : Function.Injective facetForm := by
  intro s s' h
  funext pq
  obtain ⟨p, q⟩ := pq
  have hv := congrFun h (hullVertex (p, q, false))
  rw [facetForm_hullVertex, facetForm_hullVertex] at hv
  cases h1 : s (p, q) <;> cases h2 : s' (p, q) <;> rw [h1, h2] at hv <;> norm_num at hv ⊢

/-- Five deterministic correlation vectors: the four characters `(1, 1, 1, 1)`, `(1, -1, 1, -1)`,
`(1, 1, -1, -1)`, `(1, -1, -1, 1)` and the negative `(-1, -1, -1, -1)` of the constant one. -/
def fullDimVertex : Option (Bool × Bool) → Bool × Bool → ℝ
  | none => hullVertex (false, false, true)
  | some pq => hullVertex (pq.1, pq.2, false)

/--
The correlation polytope is full-dimensional.

Proves: the five vectors `fullDimVertex` are deterministic correlation vectors and affinely
independent in `Bool × Bool → ℝ`, and the affine span of the eight deterministic correlation
vectors is the whole space.
Relation: none. Trust: kernel-only.
-/
theorem correlationPolytope_fullDim :
    (∀ i, fullDimVertex i ∈ Set.range (fun ab : (Bool → Bool) × (Bool → Bool) =>
        deterministicCorrelation ab.1 ab.2)) ∧
    AffineIndependent ℝ fullDimVertex ∧
    affineSpan ℝ (Set.range (fun ab : (Bool → Bool) × (Bool → Bool) =>
        deterministicCorrelation ab.1 ab.2)) = ⊤ := by
  have hmem : ∀ i, fullDimVertex i ∈ Set.range (fun ab : (Bool → Bool) × (Bool → Bool) =>
      deterministicCorrelation ab.1 ab.2) := by
    intro i
    rw [← range_hullVertex]
    rcases i with _ | pq
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
  have hind : AffineIndependent ℝ fullDimVertex := by
    rw [affineIndependent_iff_of_fintype]
    intro w hw0 hw1
    rw [Finset.weightedVSub_eq_linear_combination _ hw0] at hw1
    have e00 := congrFun hw1 (false, false)
    have e01 := congrFun hw1 (false, true)
    have e10 := congrFun hw1 (true, false)
    have e11 := congrFun hw1 (true, true)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fintype.sum_option, fullDimVertex,
      Fintype.sum_prod_type, Fintype.sum_bool, hullVertex_apply, Pi.zero_apply, Bool.and_true,
      Bool.and_false, bitSign_true, bitSign_false] at e00 e01 e10 e11 hw0
    intro i
    rcases i with _ | ⟨p, q⟩
    · linarith
    · cases p <;> cases q <;> linarith
  refine ⟨hmem, hind, ?_⟩
  have htop : affineSpan ℝ (Set.range fullDimVertex) = ⊤ := by
    rw [hind.affineSpan_eq_top_iff_card_eq_finrank_add_one, Module.finrank_fintype_fun_eq_card]
    simp
  refine top_unique ?_
  rw [← htop]
  exact affineSpan_mono ℝ (Set.range_subset_iff.2 hmem)

/-- The control table `(-1/4, 1/2, 1/2, 1/2)`: the rate `-1/4` at `false, false` and `1/2` at the
three other pairs of tests. -/
noncomputable def cycleControl : Table := fun x y => if x || y then 1 / 2 else -1 / 4

/--
The control for the eight bounds.

Proves: the table `cycleControl` satisfies the cycle inequalities with bound `1`, has a rate
outside `[0, 1]`, its correlation vector lies outside the hull, and it has no observer. The cycle
inequalities alone therefore do not describe the hull.
Relation: none. Trust: kernel-only.
-/
theorem cycle_without_box :
    CycleIneq cycleControl 1 ∧ ¬ (∀ x y, 0 ≤ cycleControl x y ∧ cycleControl x y ≤ 1) ∧
      correlation cycleControl ∉ convexHull ℝ (Set.range
        (fun ab : (Bool → Bool) × (Bool → Bool) => deterministicCorrelation ab.1 ab.2)) ∧
      ¬ HasObserver cycleControl := by
  have hnot : correlation cycleControl ∉ convexHull ℝ (Set.range
      (fun ab : (Bool → Bool) × (Bool → Bool) => deterministicCorrelation ab.1 ab.2)) := by
    intro hmem
    have := abs_le.mp (((mem_correlationPolytope_iff _).1 hmem).1 (false, false))
    norm_num [correlation, cycleControl] at this
  refine ⟨?_, ?_, hnot, fun hobs => hnot ((hasObserver_iff_mem_correlationPolytope _).1 hobs)⟩
  · intro x y
    cases x <;> cases y <;> norm_num [cycleControl]
  · intro h
    have := (h false false).1
    norm_num [cycleControl] at this

end OperatorKO7.Meta.BoundaryObserver.PitowskyPolytope
