import OperatorKO7.Meta.OperationalInexpressibility.FiberDeficitCore
import OperatorKO7.Meta.InformationalIncompleteness.FiniteSupportEntropy
import OperatorKO7.Meta.InformationalIncompleteness.ConditionalEntropy

/-!
# Shannon bound on the zero-error side capacity

For a finite source with a probability prior, an observer, and a target, the conditional Shannon
entropy of the target given the observer is at most the natural logarithm of the fiber
multiplicity, the largest number of target values realized in one observer fiber. The fiber
multiplicity is the exact size of the smallest zero-error side channel, so the entropy is a lower
bound for the logarithm of the zero-error side capacity. The bound is attained exactly when every
fiber of positive mass realizes the full multiplicity under the uniform conditional law. The
conditional entropy vanishes exactly when the target is licensed by the observer on the support of
the prior. Two controls: a nonuniform fiber law lies strictly below the bound, and a collision
carried by a zero-mass state leaves the entropy at zero.

Relation: equality on observer fibers.
Property: conditional entropy against fiber multiplicity; equality and zero cases.
Trust: kernel only; real-analysis surface (`negMulLog`, strict concavity and Jensen equality).
Scope: finite source, observation, and target types in `Type`; nonnegative priors summing to one.
-/

set_option autoImplicit false

open scoped BigOperators

namespace OperatorKO7.Meta.OperationalInexpressibility.FiberEntropy

open OperatorKO7.Meta.InformationalIncompleteness.ShannonFinite
open OperatorKO7.Meta.InformationalIncompleteness.FiniteSupportEntropy
open OperatorKO7.Meta.InformationalIncompleteness.ConditionalEntropy
open OperatorKO7.Meta.OperationalInexpressibility.FiberDeficit

noncomputable section

variable {X Q V : Type} [Fintype X] [DecidableEq Q] [DecidableEq V]

/-! ## Fiber masses and the conditional law -/

/-- Prior mass of the observer fiber over `u`. -/
def fiberMass (μ : X → ℝ) (q : X → Q) (u : Q) : ℝ :=
  ∑ x, if q x = u then μ x else 0

/-- Joint prior mass of observer value `u` and target value `v`. -/
def fiberTargetMass (μ : X → ℝ) (q : X → Q) (P : X → V) (u : Q) (v : V) : ℝ :=
  ∑ x, if q x = u ∧ P x = v then μ x else 0

/-- Conditional law of the target given observer value `u`; zero on fibers of zero mass. -/
def condLaw (μ : X → ℝ) (q : X → Q) (P : X → V) (u : Q) (v : V) : ℝ :=
  fiberTargetMass μ q P u v / fiberMass μ q u

/-- Conditional Shannon entropy of the target given the observer, in natural-log units. -/
def targetCondEntropy [Fintype Q] [Fintype V] (μ : X → ℝ) (q : X → Q) (P : X → V) : ℝ :=
  condEntropy (fiberMass μ q) (condLaw μ q P)

/-- The target is licensed by the observer on the support of the prior. -/
def LicensedOnSupport (μ : X → ℝ) (q : X → Q) (P : X → V) : Prop :=
  ∀ x y, 0 < μ x → 0 < μ y → q x = q y → P x = P y

variable {μ : X → ℝ} {q : X → Q} {P : X → V}

theorem fiberMass_nonneg (hμ : ∀ x, 0 ≤ μ x) (u : Q) : 0 ≤ fiberMass μ q u :=
  Finset.sum_nonneg fun x _ => ite_nonneg (hμ x) le_rfl

theorem fiberTargetMass_nonneg (hμ : ∀ x, 0 ≤ μ x) (u : Q) (v : V) :
    0 ≤ fiberTargetMass μ q P u v :=
  Finset.sum_nonneg fun x _ => ite_nonneg (hμ x) le_rfl

/-- The joint masses of one fiber sum to the fiber mass. -/
theorem sum_fiberTargetMass [Fintype V] (u : Q) :
    ∑ v, fiberTargetMass μ q P u v = fiberMass μ q u := by
  unfold fiberTargetMass fiberMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : q x = u
  · simp [hx]
  · simp [hx]

/-- The fiber masses sum to the total prior mass. -/
theorem sum_fiberMass [Fintype Q] : ∑ u, fiberMass μ q u = ∑ x, μ x := by
  unfold fiberMass
  rw [Finset.sum_comm]
  simp

theorem single_le_fiberMass (hμ : ∀ x, 0 ≤ μ x) (x : X) : μ x ≤ fiberMass μ q (q x) := by
  unfold fiberMass
  calc μ x = (if q x = q x then μ x else 0) := (if_pos rfl).symm
    _ ≤ ∑ z, (if q z = q x then μ z else 0) :=
        Finset.single_le_sum (f := fun z => if q z = q x then μ z else 0)
          (fun z _ => ite_nonneg (hμ z) le_rfl) (Finset.mem_univ x)

theorem single_le_fiberTargetMass (hμ : ∀ x, 0 ≤ μ x) {x : X} {u : Q} {v : V}
    (hxu : q x = u) (hxv : P x = v) : μ x ≤ fiberTargetMass μ q P u v := by
  unfold fiberTargetMass
  calc μ x = (if q x = u ∧ P x = v then μ x else 0) := (if_pos ⟨hxu, hxv⟩).symm
    _ ≤ ∑ z, (if q z = u ∧ P z = v then μ z else 0) :=
        Finset.single_le_sum (f := fun z => if q z = u ∧ P z = v then μ z else 0)
          (fun z _ => ite_nonneg (hμ z) le_rfl) (Finset.mem_univ x)

theorem fiberTargetMass_le_fiberMass [Fintype V] (hμ : ∀ x, 0 ≤ μ x) (u : Q) (v : V) :
    fiberTargetMass μ q P u v ≤ fiberMass μ q u := by
  rw [← sum_fiberTargetMass (P := P) u]
  exact Finset.single_le_sum (fun w _ => fiberTargetMass_nonneg hμ u w) (Finset.mem_univ v)

theorem condLaw_nonneg (hμ : ∀ x, 0 ≤ μ x) (u : Q) (v : V) : 0 ≤ condLaw μ q P u v :=
  div_nonneg (fiberTargetMass_nonneg hμ u v) (fiberMass_nonneg hμ u)

theorem condLaw_le_one [Fintype V] (hμ : ∀ x, 0 ≤ μ x) (u : Q) (v : V) :
    condLaw μ q P u v ≤ 1 := by
  unfold condLaw
  rcases (fiberMass_nonneg (q := q) hμ u).lt_or_eq with hpos | hzero
  · exact (div_le_one hpos).2 (fiberTargetMass_le_fiberMass hμ u v)
  · rw [← hzero, div_zero]
    exact zero_le_one

/-- On a fiber of positive mass the conditional law is a probability law. -/
theorem condLaw_sum_one [Fintype V] {u : Q} (hu : fiberMass μ q u ≠ 0) :
    ∑ v, condLaw μ q P u v = 1 := by
  unfold condLaw
  rw [← Finset.sum_div, sum_fiberTargetMass, div_self hu]

theorem fiberTargetMass_eq_zero_of_not_mem {u : Q} {v : V} (hv : v ∉ fiberVerdicts q P u) :
    fiberTargetMass μ q P u v = 0 := by
  unfold fiberTargetMass
  apply Finset.sum_eq_zero
  intro x _
  rw [if_neg]
  rintro ⟨hxu, hxv⟩
  exact hv (mem_fiberVerdicts.2 ⟨x, hxu, hxv⟩)

theorem condLaw_eq_zero_of_not_mem {u : Q} {v : V} (hv : v ∉ fiberVerdicts q P u) :
    condLaw μ q P u v = 0 := by
  unfold condLaw
  rw [fiberTargetMass_eq_zero_of_not_mem hv, zero_div]

/-- A fiber of positive mass realizes at least one target value. -/
theorem fiberVerdicts_nonempty [Fintype V] {u : Q} (hu : fiberMass μ q u ≠ 0) :
    (fiberVerdicts q P u).Nonempty := by
  by_contra hempty
  rw [Finset.not_nonempty_iff_eq_empty] at hempty
  apply hu
  rw [← sum_fiberTargetMass (P := P) u]
  apply Finset.sum_eq_zero
  intro v _
  apply fiberTargetMass_eq_zero_of_not_mem
  rw [hempty]
  exact Finset.notMem_empty v

/-- The entropy of the conditional law is a sum over the realized target values. -/
theorem H_condLaw_eq_sum_fiberVerdicts [Fintype V] (u : Q) :
    H (condLaw μ q P u) = ∑ v ∈ fiberVerdicts q P u, Real.negMulLog (condLaw μ q P u v) := by
  unfold H
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro v _ hv
  rw [condLaw_eq_zero_of_not_mem hv, Real.negMulLog_zero]

/-- The conditional law restricted to the realized target values of one fiber. -/
def fiberLaw (μ : X → ℝ) (q : X → Q) (P : X → V) (u : Q) :
    {v // v ∈ fiberVerdicts q P u} → ℝ :=
  fun v => condLaw μ q P u v.1

theorem H_fiberLaw [Fintype V] (u : Q) : H (fiberLaw μ q P u) = H (condLaw μ q P u) := by
  rw [H_condLaw_eq_sum_fiberVerdicts]
  unfold H fiberLaw
  exact Finset.sum_coe_sort (fiberVerdicts q P u) (fun v => Real.negMulLog (condLaw μ q P u v))

theorem fiberLaw_sum_one [Fintype V] {u : Q} (hu : fiberMass μ q u ≠ 0) :
    ∑ v, fiberLaw μ q P u v = 1 := by
  unfold fiberLaw
  rw [Finset.sum_coe_sort (fiberVerdicts q P u) (fun v => condLaw μ q P u v),
    ← condLaw_sum_one (P := P) hu]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro v _ hv
  exact condLaw_eq_zero_of_not_mem hv

/-- On a fiber of positive mass, the conditional entropy is at most the logarithm of the number of
realized target values. -/
theorem H_condLaw_le_log_card [Fintype V] (hμ : ∀ x, 0 ≤ μ x) {u : Q}
    (hu : fiberMass μ q u ≠ 0) :
    H (condLaw μ q P u) ≤ Real.log (fiberVerdicts q P u).card := by
  haveI : Nonempty {v // v ∈ fiberVerdicts q P u} := (fiberVerdicts_nonempty hu).to_subtype
  have hbound := H_le_log_card (fiberLaw μ q P u) (fun v => condLaw_nonneg hμ u v.1)
    (fiberLaw_sum_one hu)
  rw [H_fiberLaw, Fintype.card_coe] at hbound
  exact hbound

/-! ## The bound -/

/-- **Shannon bound on the zero-error side capacity.** The conditional entropy of the target given
the observer is at most the natural logarithm of the fiber multiplicity. -/
theorem conditionalEntropy_le_log_fiberMultiplicity [Fintype Q] [Fintype V]
    (hμ : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1) :
    targetCondEntropy μ q P ≤ Real.log (fiberMultiplicity q P) := by
  unfold targetCondEntropy condEntropy
  calc ∑ u, fiberMass μ q u * H (condLaw μ q P u)
      ≤ ∑ u, fiberMass μ q u * Real.log (fiberMultiplicity q P) := by
        apply Finset.sum_le_sum
        intro u _
        by_cases hu : fiberMass μ q u = 0
        · simp [hu]
        · apply mul_le_mul_of_nonneg_left _ (fiberMass_nonneg hμ u)
          calc H (condLaw μ q P u) ≤ Real.log (fiberVerdicts q P u).card :=
                H_condLaw_le_log_card hμ hu
            _ ≤ Real.log (fiberMultiplicity q P) := by
                apply Real.log_le_log
                · exact_mod_cast (fiberVerdicts_nonempty hu).card_pos
                · exact_mod_cast fiberVerdicts_card_le q P u
    _ = Real.log (fiberMultiplicity q P) := by
        rw [← Finset.sum_mul, sum_fiberMass, hμ1, one_mul]

/-- The bound in bits. -/
theorem conditionalEntropyBits_le_logb_fiberMultiplicity [Fintype Q] [Fintype V]
    (hμ : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1) :
    targetCondEntropy μ q P / Real.log 2 ≤ Real.logb 2 (fiberMultiplicity q P) := by
  unfold Real.logb
  exact (div_le_div_iff_of_pos_right (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr
    (conditionalEntropy_le_log_fiberMultiplicity hμ hμ1)

/-! ## The zero case -/

theorem negMulLog_eq_zero_iff_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    Real.negMulLog x = 0 ↔ x = 0 ∨ x = 1 := by
  rw [show Real.negMulLog x = -x * Real.log x from rfl, mul_eq_zero, neg_eq_zero,
    Real.log_eq_zero]
  constructor
  · rintro (h | h | h | h)
    · exact Or.inl h
    · exact Or.inl h
    · exact Or.inr h
    · linarith
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))

/-- A law with values in `[0, 1]` has zero entropy exactly when every value is `0` or `1`. -/
theorem H_eq_zero_iff {α : Type} [Fintype α] (p : α → ℝ) (h0 : ∀ x, 0 ≤ p x)
    (h1 : ∀ x, p x ≤ 1) : H p = 0 ↔ ∀ x, p x = 0 ∨ p x = 1 := by
  unfold H
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun x _ => Real.negMulLog_nonneg (h0 x) (h1 x))]
  exact ⟨fun h x => (negMulLog_eq_zero_iff_of_nonneg (h0 x)).1 (h x (Finset.mem_univ x)),
    fun h x _ => (negMulLog_eq_zero_iff_of_nonneg (h0 x)).2 (h x)⟩

theorem exists_pos_of_fiberTargetMass_ne_zero (hμ : ∀ x, 0 ≤ μ x) {u : Q} {v : V}
    (h : fiberTargetMass μ q P u v ≠ 0) : ∃ x, q x = u ∧ P x = v ∧ 0 < μ x := by
  unfold fiberTargetMass at h
  obtain ⟨x, _, hx⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  by_cases hc : q x = u ∧ P x = v
  · rw [if_pos hc] at hx
    exact ⟨x, hc.1, hc.2, lt_of_le_of_ne (hμ x) (Ne.symm hx)⟩
  · rw [if_neg hc] at hx
    exact absurd rfl hx

/-- **Zero conditional entropy is licensing on the support.** -/
theorem conditionalEntropy_eq_zero_iff_licensedOnSupport [Fintype Q] [Fintype V]
    (hμ : ∀ x, 0 ≤ μ x) :
    targetCondEntropy μ q P = 0 ↔ LicensedOnSupport μ q P := by
  unfold targetCondEntropy condEntropy
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun u _ => mul_nonneg (fiberMass_nonneg hμ u)
    (H_nonneg _ (condLaw_nonneg hμ u) (condLaw_le_one hμ u)))]
  constructor
  · intro h x y hx hy hxy
    have hpos : 0 < fiberMass μ q (q x) := lt_of_lt_of_le hx (single_le_fiberMass hμ x)
    have hHu : H (condLaw μ q P (q x)) = 0 := by
      rcases mul_eq_zero.1 (h (q x) (Finset.mem_univ _)) with h' | h'
      · exact absurd h' hpos.ne'
      · exact h'
    have h01 := (H_eq_zero_iff _ (condLaw_nonneg hμ (q x)) (condLaw_le_one hμ (q x))).1 hHu
    have hcx : 0 < condLaw μ q P (q x) (P x) :=
      div_pos (lt_of_lt_of_le hx (single_le_fiberTargetMass hμ rfl rfl)) hpos
    have hcy : 0 < condLaw μ q P (q x) (P y) :=
      div_pos (lt_of_lt_of_le hy (single_le_fiberTargetMass hμ hxy.symm rfl)) hpos
    by_contra hne
    have hx1 : condLaw μ q P (q x) (P x) = 1 := (h01 (P x)).resolve_left hcx.ne'
    have hy1 : condLaw μ q P (q x) (P y) = 1 := (h01 (P y)).resolve_left hcy.ne'
    have hsum := condLaw_sum_one (P := P) hpos.ne'
    have hpair : condLaw μ q P (q x) (P x) + condLaw μ q P (q x) (P y) ≤
        ∑ v, condLaw μ q P (q x) v := by
      rw [← Finset.sum_pair hne]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun v _ _ => condLaw_nonneg hμ (q x) v)
    linarith
  · intro hlic u _
    by_cases hu : fiberMass μ q u = 0
    · rw [hu, zero_mul]
    · rw [(H_eq_zero_iff _ (condLaw_nonneg hμ u) (condLaw_le_one hμ u)).2 ?_, mul_zero]
      intro v
      by_cases hv : fiberTargetMass μ q P u v = 0
      · left
        unfold condLaw
        rw [hv, zero_div]
      · right
        obtain ⟨x₀, hx₀u, hx₀v, hx₀⟩ := exists_pos_of_fiberTargetMass_ne_zero hμ hv
        have hfull : fiberTargetMass μ q P u v = fiberMass μ q u := by
          unfold fiberTargetMass fiberMass
          apply Finset.sum_congr rfl
          intro z _
          by_cases hz : q z = u
          · rw [if_pos hz]
            rcases (hμ z).lt_or_eq with hzpos | hzero
            · have hPz : P z = v := by
                rw [← hx₀v]
                exact hlic z x₀ hzpos hx₀ (hz.trans hx₀u.symm)
              rw [if_pos ⟨hz, hPz⟩]
            · by_cases hc : q z = u ∧ P z = v
              · rw [if_pos hc]
              · rw [if_neg hc, ← hzero]
          · rw [if_neg hz, if_neg (fun hc => hz hc.1)]
        unfold condLaw
        rw [hfull, div_self hu]

/-! ## The equality case -/

/-- The finite Shannon-Hartley bound is attained only by the uniform law. -/
theorem eq_uniform_of_H_eq_log_card {α : Type} [Fintype α] [Nonempty α] (p : α → ℝ)
    (h0 : ∀ x, 0 ≤ p x) (h1 : ∑ x, p x = 1) (hH : H p = Real.log (Fintype.card α)) :
    ∀ x, p x = 1 / (Fintype.card α : ℝ) := by
  have hnpos : 0 < (Fintype.card α : ℝ) := card_cast_pos α
  have hw0 : ∀ i ∈ (Finset.univ : Finset α), 0 < 1 / (Fintype.card α : ℝ) :=
    fun _ _ => one_div_pos.mpr hnpos
  have hw1 : ∑ _i ∈ (Finset.univ : Finset α), 1 / (Fintype.card α : ℝ) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  have hmem : ∀ i ∈ (Finset.univ : Finset α), p i ∈ Set.Ici (0 : ℝ) :=
    fun i _ => Set.mem_Ici.2 (h0 i)
  have hiff := Real.strictConcaveOn_negMulLog.map_sum_eq_iff (t := Finset.univ)
    (w := fun _ => 1 / (Fintype.card α : ℝ)) (p := p) hw0 hw1 hmem
  have havg : ∑ i ∈ (Finset.univ : Finset α), (1 / (Fintype.card α : ℝ)) • p i =
      1 / (Fintype.card α : ℝ) := by
    simp only [smul_eq_mul]
    rw [← Finset.mul_sum, h1, mul_one]
  have hlhs : Real.negMulLog (∑ i ∈ (Finset.univ : Finset α),
      (1 / (Fintype.card α : ℝ)) • p i) =
      ∑ i ∈ (Finset.univ : Finset α), (1 / (Fintype.card α : ℝ)) • Real.negMulLog (p i) := by
    rw [havg]
    simp only [smul_eq_mul]
    rw [← Finset.mul_sum]
    have hHsum : ∑ i, Real.negMulLog (p i) = Real.log (Fintype.card α) := hH
    rw [hHsum, show Real.negMulLog (1 / (Fintype.card α : ℝ)) =
      -(1 / (Fintype.card α : ℝ)) * Real.log (1 / (Fintype.card α : ℝ)) from rfl,
      one_div, Real.log_inv]
    ring
  have hall := hiff.1 hlhs
  intro x
  rw [hall x (Finset.mem_univ x), havg]

/-- The uniform law on the realized values of a fiber attains the logarithm of their number. -/
theorem H_condLaw_eq_log_of_uniform [Fintype V] {u : Q} {m : ℕ}
    (hcard : (fiberVerdicts q P u).card = m)
    (hunif : ∀ v ∈ fiberVerdicts q P u, condLaw μ q P u v = 1 / (m : ℝ)) :
    H (condLaw μ q P u) = Real.log m := by
  rw [H_condLaw_eq_sum_fiberVerdicts, Finset.sum_congr rfl
    (fun v hv => by rw [hunif v hv]), Finset.sum_const, hcard, nsmul_eq_mul]
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp
  · have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
    rw [show Real.negMulLog (1 / (m : ℝ)) = -(1 / (m : ℝ)) * Real.log (1 / (m : ℝ)) from rfl,
      one_div, Real.log_inv]
    field_simp

/-- **Equality case of the Shannon bound.** The conditional entropy equals the logarithm of the
fiber multiplicity exactly when every fiber of positive mass realizes the full multiplicity under
the uniform conditional law. -/
theorem conditionalEntropy_eq_log_fiberMultiplicity_iff [Fintype Q] [Fintype V]
    (hμ : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1) :
    targetCondEntropy μ q P = Real.log (fiberMultiplicity q P) ↔
      ∀ u, 0 < fiberMass μ q u →
        (fiberVerdicts q P u).card = fiberMultiplicity q P ∧
          ∀ v ∈ fiberVerdicts q P u, condLaw μ q P u v = 1 / (fiberMultiplicity q P : ℝ) := by
  have hterm : ∀ u ∈ (Finset.univ : Finset Q),
      fiberMass μ q u * H (condLaw μ q P u) ≤
        fiberMass μ q u * Real.log (fiberMultiplicity q P) := by
    intro u _
    by_cases hu : fiberMass μ q u = 0
    · simp [hu]
    · apply mul_le_mul_of_nonneg_left _ (fiberMass_nonneg hμ u)
      calc H (condLaw μ q P u) ≤ Real.log (fiberVerdicts q P u).card :=
            H_condLaw_le_log_card hμ hu
        _ ≤ Real.log (fiberMultiplicity q P) := by
            apply Real.log_le_log
            · exact_mod_cast (fiberVerdicts_nonempty hu).card_pos
            · exact_mod_cast fiberVerdicts_card_le q P u
  have hrhs : ∑ u, fiberMass μ q u * Real.log (fiberMultiplicity q P) =
      Real.log (fiberMultiplicity q P) := by
    rw [← Finset.sum_mul, sum_fiberMass, hμ1, one_mul]
  unfold targetCondEntropy condEntropy
  constructor
  · intro heq u hupos
    have hsum : ∑ u, fiberMass μ q u * H (condLaw μ q P u) =
        ∑ u, fiberMass μ q u * Real.log (fiberMultiplicity q P) := by rw [heq, hrhs]
    have hall := (Finset.sum_eq_sum_iff_of_le hterm).1 hsum
    have hHu : H (condLaw μ q P u) = Real.log (fiberMultiplicity q P) :=
      mul_left_cancel₀ hupos.ne' (hall u (Finset.mem_univ u))
    have hcardpos : 0 < (fiberVerdicts q P u).card :=
      (fiberVerdicts_nonempty hupos.ne').card_pos
    have hle1 : H (condLaw μ q P u) ≤ Real.log (fiberVerdicts q P u).card :=
      H_condLaw_le_log_card hμ hupos.ne'
    have hle2 : Real.log ((fiberVerdicts q P u).card : ℝ) ≤ Real.log (fiberMultiplicity q P) :=
      Real.log_le_log (by exact_mod_cast hcardpos) (by exact_mod_cast fiberVerdicts_card_le q P u)
    have hlogeq : Real.log ((fiberVerdicts q P u).card : ℝ) = Real.log (fiberMultiplicity q P) :=
      le_antisymm hle2 (hHu ▸ hle1)
    have hmpos : 0 < fiberMultiplicity q P :=
      lt_of_lt_of_le hcardpos (fiberVerdicts_card_le q P u)
    have hcard : (fiberVerdicts q P u).card = fiberMultiplicity q P := by
      have := Real.log_injOn_pos (Set.mem_Ioi.2 (by exact_mod_cast hcardpos : (0 : ℝ) < _))
        (Set.mem_Ioi.2 (by exact_mod_cast hmpos : (0 : ℝ) < _)) hlogeq
      exact_mod_cast this
    refine ⟨hcard, fun v hv => ?_⟩
    haveI : Nonempty {w // w ∈ fiberVerdicts q P u} :=
      (fiberVerdicts_nonempty hupos.ne').to_subtype
    have hHfiber : H (fiberLaw μ q P u) =
        Real.log (Fintype.card {w // w ∈ fiberVerdicts q P u}) := by
      rw [H_fiberLaw, Fintype.card_coe, hcard, hHu]
    have hunif := eq_uniform_of_H_eq_log_card (fiberLaw μ q P u)
      (fun w => condLaw_nonneg hμ u w.1) (fiberLaw_sum_one hupos.ne') hHfiber ⟨v, hv⟩
    rw [Fintype.card_coe, hcard] at hunif
    exact hunif
  · intro h
    rw [← hrhs]
    apply Finset.sum_congr rfl
    intro u _
    by_cases hu : fiberMass μ q u = 0
    · rw [hu, zero_mul, zero_mul]
    · have hupos : 0 < fiberMass μ q u := lt_of_le_of_ne (fiberMass_nonneg hμ u) (Ne.symm hu)
      obtain ⟨hcard, hunif⟩ := h u hupos
      rw [H_condLaw_eq_log_of_uniform hcard hunif]

/-! ## Controls -/

/-- A prior on two states with masses one quarter and three quarters. -/
def nonuniformPrior (x : Fin 2) : ℝ := if x = 0 then 1 / 4 else 3 / 4

/-- **Nonuniform control.** One fiber holds both target values with masses one quarter and three
quarters; the conditional entropy is strictly below the logarithm of the fiber multiplicity. -/
theorem nonuniform_fiber_law_lt_log_fiberMultiplicity :
    targetCondEntropy nonuniformPrior (fun _ : Fin 2 => ()) (fun x : Fin 2 => x) <
      Real.log (fiberMultiplicity (fun _ : Fin 2 => ()) (fun x : Fin 2 => x)) := by
  have h0 : ∀ x, 0 ≤ nonuniformPrior x := by
    intro x
    unfold nonuniformPrior
    split_ifs <;> norm_num
  have h1 : ∑ x, nonuniformPrior x = 1 := by
    norm_num [nonuniformPrior, Fin.sum_univ_two]
  refine lt_of_le_of_ne (conditionalEntropy_le_log_fiberMultiplicity h0 h1) fun heq => ?_
  have hm : fiberMultiplicity (fun _ : Fin 2 => ()) (fun x : Fin 2 => x) = 2 := by decide
  have hmass : 0 < fiberMass nonuniformPrior (fun _ : Fin 2 => ()) () := by
    norm_num [fiberMass, nonuniformPrior, Fin.sum_univ_two]
  obtain ⟨_, hunif⟩ := (conditionalEntropy_eq_log_fiberMultiplicity_iff h0 h1).1 heq () hmass
  have h00 := hunif 0 (mem_fiberVerdicts.2 ⟨0, rfl, rfl⟩)
  rw [hm] at h00
  norm_num [condLaw, fiberTargetMass, fiberMass, nonuniformPrior, Fin.sum_univ_two] at h00

/-- A prior with all mass on the first of two states. -/
def pointPrior (x : Fin 2) : ℝ := if x = 0 then 1 else 0

/-- **Zero-mass control.** The two states collide under the constant observer and carry different
target values, and the conditional entropy is still zero because the second state has zero mass:
the zero case is a statement about the support of the prior. -/
theorem zeroMass_collision_conditionalEntropy_eq_zero :
    targetCondEntropy pointPrior (fun _ : Fin 2 => ()) (fun x : Fin 2 => x) = 0 ∧
      ¬ ∀ x y : Fin 2, (fun _ : Fin 2 => ()) x = (fun _ : Fin 2 => ()) y →
        (fun x : Fin 2 => x) x = (fun x : Fin 2 => x) y := by
  have h0 : ∀ x, 0 ≤ pointPrior x := by
    intro x
    unfold pointPrior
    split_ifs <;> norm_num
  refine ⟨(conditionalEntropy_eq_zero_iff_licensedOnSupport h0).2 ?_,
    fun h => absurd (h 0 1 rfl) (by decide)⟩
  intro x y hx hy _
  have hx0 : x = 0 := by
    by_contra hne
    simp [pointPrior, hne] at hx
  have hy0 : y = 0 := by
    by_contra hne
    simp [pointPrior, hne] at hy
  rw [hx0, hy0]

end

end OperatorKO7.Meta.OperationalInexpressibility.FiberEntropy
