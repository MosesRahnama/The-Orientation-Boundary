import OperatorKO7.Meta.BoundaryObserver.PairResolution

set_option autoImplicit false

/-!
# Finite fiber resolution

Exact M6.5 goals, with the finite-law and stopped-protocol semantics
of ProtocolResolution, BoundarySingularity and PairResolution.
Relation: finite probabilistic channels. Trust: kernel-only.
-/

namespace OperatorKO7.Meta.BoundaryObserver.FiberResolution

open scoped BigOperators
open ProtocolResolution BoundarySingularity PairResolution

noncomputable section

/-! ## M6.5: exact goal declarations -/

/-- One n-ary reading has a prior-weighted pairwise discrimination bound. -/
def FiberOneReadingGoal : Prop :=
  ∀ (n : ℕ) (Y : Type) [Fintype Y] (p : FiniteLaw (Fin n)) (K : Fin n → FiniteLaw Y),
    jointMI (fun by_ : Fin n × Y => p.mass by_.1 * (K by_.1).mass by_.2) ≤
      (∑ b, ∑ b', if b ≠ b' then
        (p.mass b + p.mass b') * discrimination (K b).mass (K b').mass else 0) /
          (2 * Real.log 2)

/-- At every history and action all label rows are within δ, with unit lower cost. -/
structure FiberMenu {n : ℕ} {A Y : Type} [Fintype A] [Fintype Y]
    (p : FiniteProtocol (Fin n) A Y) (δ : ℝ) : Prop where
  rows : ∀ h a b b',
    discrimination (p.observation h a b).mass (p.observation h a b').mass ≤ δ
  reading_cost : ∀ h a, 1 ≤ p.cost h a

/-- The local n-ary capacity follows from the pairwise bound. -/
def FiberCapacityGoal : Prop :=
  ∀ (n : ℕ) (A Y : Type) [Fintype A] [Fintype Y] (p : FiniteProtocol (Fin n) A Y) (δ : ℝ),
    FiberMenu p δ → 0 ≤ δ → LocalCapacityBound p (((n : ℝ) - 1) * δ / Real.log 2)

/-- Repeated n-ary reading at unit cost, stopping after N readings. -/
def repeatFiber {n : ℕ} {Y : Type} [Fintype Y] (p0 : FiniteLaw (Fin n))
    (K : Fin n → FiniteLaw Y) (N : ℕ) : FiniteProtocol (Fin n) Unit Y where
  prior := p0
  policy _ := unitLaw
  observation _ _ b := K b
  stop h := decide (N ≤ h.length)
  cost _ _ := 1
  cost_nonnegative _ _ := zero_le_one

/-- Conditional likelihood of a retained history under label b. -/
def fiberLikelihood {n : ℕ} {Y : Type} [Fintype Y] (K : Fin n → FiniteLaw Y) (b : Fin n)
    (h : List (Unit × Y)) : ℝ :=
  (h.map (fun ay => (K b).mass ay.2)).prod

/-- Joint mass of decoded errors at the fixed reading horizon. -/
def fiberError {n : ℕ} {Y : Type} [Fintype Y] (p0 : FiniteLaw (Fin n))
    (K : Fin n → FiniteLaw Y) (N : ℕ) (g : List (Unit × Y) → Fin n) : ℝ :=
  ∑ h ∈ historySet (Unit × Y) N, ∑ b,
    if g h ≠ b then stoppedMass (repeatFiber p0 K N) N b h else 0

/-- The ML error exponent is controlled by the pairwise Bhattacharyya coefficient. -/
def FiberAttainmentGoal : Prop :=
  ∀ (n : ℕ) (Y : Type) [Fintype Y] (p0 : FiniteLaw (Fin n)) (K : Fin n → FiniteLaw Y) (β : ℝ)
    (g : List (Unit × Y) → Fin n) (N : ℕ),
    (∀ b, p0.mass b = 1 / n) →
    (∀ b b', b ≠ b' → bhattacharyya (K b).mass (K b').mass ≤ β) →
    (∀ h b, fiberLikelihood K b h ≤ fiberLikelihood K (g h) h) →
      fiberError p0 K N g ≤ ((n : ℝ) - 1) * β ^ N

/-- Fano inequality on the actual stopped law of a repeated n-ary reading. -/
def FiberFanoGoal : Prop :=
  ∀ (n : ℕ) (Y : Type) [Fintype Y] (p0 : FiniteLaw (Fin n)) (K : Fin n → FiniteLaw Y)
    (g : List (Unit × Y) → Fin n) (N : ℕ),
    (∀ b, p0.mass b = 1 / n) → 2 ≤ n → fiberError p0 K N g ≤ 1 - 1 / n →
      Real.logb 2 n -
          (Real.binEntropy (fiberError p0 K N g) +
            fiberError p0 K N g * Real.log ((n : ℝ) - 1)) / Real.log 2 ≤
        terminalMI (repeatFiber p0 K N) N (historyBank Unit Y N)

/-- A sparse row reveals the input with probability ε, otherwise samples uniformly. -/
def sparseRow (n : ℕ) (ε : ℝ) (b y : Fin n) : ℝ :=
  (1 - ε) / n + if y = b then ε else 0

/-- Sparse rows have bounded pairwise discrimination yet unbounded n-ary information. -/
def SparseControlGoal : Prop :=
  ∀ C : ℝ, ∃ n : ℕ, 2 ≤ n ∧
    (∀ b b' : Fin n, discrimination (sparseRow n (1 / 2) b) (sparseRow n (1 / 2) b') ≤ 1) ∧
    C < jointMI (fun by_ : Fin n × Fin n => (1 / n : ℝ) * sparseRow n (1 / 2) by_.1 by_.2)

/-! ## One-reading chi-square / variance ingredients -/

/-- The ordered pair contribution of a weighted variance is bounded by the
pair's triangular-discrimination contribution whenever the mixture includes
both distinct cells. The zero-denominator cases are explicit. -/
private theorem pairwise_chi_term_le
    (w v a b m : ℝ) (hw : 0 ≤ w) (hv : 0 ≤ v)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hM : w * a + v * b ≤ m) :
    w * v * (a - b) ^ 2 / m ≤ (w + v) * (a - b) ^ 2 / (a + b) := by
  have hm0 : 0 ≤ m :=
    (add_nonneg (mul_nonneg hw ha) (mul_nonneg hv hb)).trans hM
  by_cases hm : m = 0
  · rw [hm, div_zero]
    exact div_nonneg (mul_nonneg (add_nonneg hw hv) (sq_nonneg _))
      (add_nonneg ha hb)
  by_cases hab : a + b = 0
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    simp [ha0, hb0]
  have hmpos : 0 < m := lt_of_le_of_ne hm0 (Ne.symm hm)
  have habpos : 0 < a + b :=
    lt_of_le_of_ne (add_nonneg ha hb) (Ne.symm hab)
  rw [div_le_div_iff₀ hmpos habpos]
  have hpair : w * v * (a + b) ≤ (w + v) * (w * a + v * b) := by
    have heq : (w + v) * (w * a + v * b) - w * v * (a + b) =
        w * w * a + v * v * b := by ring
    have hnon : 0 ≤ w * w * a + v * v * b :=
      add_nonneg
        (mul_nonneg (mul_nonneg hw hw) ha)
        (mul_nonneg (mul_nonneg hv hv) hb)
    linarith
  have hbig : w * v * (a + b) ≤ (w + v) * m :=
    hpair.trans (mul_le_mul_of_nonneg_left hM (add_nonneg hw hv))
  calc
    (w * v * (a - b) ^ 2) * (a + b) =
        (w * v * (a + b)) * (a - b) ^ 2 := by ring
    _ ≤ ((w + v) * m) * (a - b) ^ 2 :=
      mul_le_mul_of_nonneg_right hbig (sq_nonneg _)
    _ = ((w + v) * (a - b) ^ 2) * m := by ring

/-! ## Repeated-fiber likelihood and stopped-law identities -/

private theorem fiberLikelihood_nil {n : ℕ} {Y : Type} [Fintype Y]
    (K : Fin n → FiniteLaw Y) (b : Fin n) :
    fiberLikelihood K b [] = 1 := by simp [fiberLikelihood]

private theorem fiberLikelihood_append {n : ℕ} {Y : Type} [Fintype Y]
    (K : Fin n → FiniteLaw Y) (b : Fin n)
    (h : List (Unit × Y)) (ay : Unit × Y) :
    fiberLikelihood K b (h ++ [ay]) =
      fiberLikelihood K b h * (K b).mass ay.2 := by
  simp [fiberLikelihood, List.map_append, List.prod_append]

private theorem fiberLikelihood_nonnegative {n : ℕ} {Y : Type} [Fintype Y]
    (K : Fin n → FiniteLaw Y) (b : Fin n) (h : List (Unit × Y)) :
    0 ≤ fiberLikelihood K b h := by
  unfold fiberLikelihood
  apply List.prod_nonneg
  intro x hx
  obtain ⟨ay, _, rfl⟩ := List.mem_map.mp hx
  exact (K b).nonnegative ay.2

private theorem repeatFiber_stop_false {n : ℕ} {Y : Type} [Fintype Y]
    (p0 : FiniteLaw (Fin n)) (K : Fin n → FiniteLaw Y) (N : ℕ)
    {h : List (Unit × Y)} (hl : h.length < N) :
    (repeatFiber p0 K N).stop h = false := by
  change decide (N ≤ h.length) = false
  rw [decide_eq_false_iff_not]
  omega

private theorem prefixMass_repeatFiber {n : ℕ} {Y : Type} [Fintype Y]
    (p0 : FiniteLaw (Fin n)) (K : Fin n → FiniteLaw Y) (N : ℕ)
    (b : Fin n) (h : List (Unit × Y)) (hl : h.length ≤ N) :
    prefixMass (repeatFiber p0 K N) b h = p0.mass b * fiberLikelihood K b h := by
  induction h using List.reverseRecOn with
  | nil => simp [prefixMass_nil, repeatFiber, fiberLikelihood_nil]
  | append_singleton h ay ih =>
    have hlt : h.length < N := by
      simp only [List.length_append, List.length_singleton] at hl
      omega
    rw [prefixMass_append, repeatFiber_stop_false p0 K N hlt]
    simp only [Bool.false_eq_true, if_false]
    rw [ih hlt.le, fiberLikelihood_append]
    change p0.mass b * fiberLikelihood K b h * 1 * (K b).mass ay.2 =
      p0.mass b * (fiberLikelihood K b h * (K b).mass ay.2)
    ring

private theorem stoppedMass_repeatFiber {n : ℕ} {Y : Type} [Fintype Y]
    (p0 : FiniteLaw (Fin n)) (K : Fin n → FiniteLaw Y) (N : ℕ)
    (b : Fin n) (h : List (Unit × Y)) :
    stoppedMass (repeatFiber p0 K N) N b h =
      if h.length = N then p0.mass b * fiberLikelihood K b h else 0 := by
  unfold stoppedMass
  by_cases hl : h.length = N
  · rw [if_pos hl, if_pos ⟨hl.le, Or.inr hl⟩,
        prefixMass_repeatFiber p0 K N b h hl.le]
  · rw [if_neg hl, if_neg]
    rintro ⟨hle, hs | he⟩
    · change decide (N ≤ h.length) = true at hs
      rw [decide_eq_true_iff] at hs
      exact hl (le_antisymm hle hs)
    · exact hl he

/-! ## Bhattacharyya product controls for n-ary repeated readings -/

/-- Pairwise square-root likelihoods factor across all retained readings. -/
private theorem sqrt_fiberLikelihood_mul {n : ℕ} {Y : Type} [Fintype Y]
    (K : Fin n → FiniteLaw Y) (b c : Fin n) (h : List (Unit × Y)) :
    Real.sqrt (fiberLikelihood K b h * fiberLikelihood K c h) =
      (h.map (fun ay => Real.sqrt ((K b).mass ay.2 * (K c).mass ay.2))).prod := by
  induction h with
  | nil => simp [fiberLikelihood_nil]
  | cons ay h ih =>
    unfold fiberLikelihood at ih ⊢
    simp only [List.map_cons, List.prod_cons]
    rw [show (K b).mass ay.2 * (h.map (fun ay => (K b).mass ay.2)).prod *
          ((K c).mass ay.2 * (h.map (fun ay => (K c).mass ay.2)).prod) =
          ((K b).mass ay.2 * (K c).mass ay.2) *
            ((h.map (fun ay => (K b).mass ay.2)).prod *
              (h.map (fun ay => (K c).mass ay.2)).prod) by ring,
        Real.sqrt_mul (mul_nonneg ((K b).nonnegative _) ((K c).nonnegative _)), ih]

/-- The full depth-N pairwise affinity is the Nth power of one-reading affinity. -/
private theorem bhattacharyya_fiber_level {n : ℕ} {Y : Type} [Fintype Y]
    (K : Fin n → FiniteLaw Y) (b c : Fin n) (N : ℕ) :
    (∑ h ∈ historySet (Unit × Y) N, if h.length = N then
      Real.sqrt (fiberLikelihood K b h * fiberLikelihood K c h) else 0) =
      (bhattacharyya (K b).mass (K c).mass) ^ N := by
  calc
    (∑ h ∈ historySet (Unit × Y) N, if h.length = N then
        Real.sqrt (fiberLikelihood K b h * fiberLikelihood K c h) else 0) =
      (∑ h ∈ historySet (Unit × Y) N, if h.length = N then
        (h.map (fun ay => Real.sqrt ((K b).mass ay.2 * (K c).mass ay.2))).prod
        else 0) := by
        apply Finset.sum_congr rfl
        intro h _
        by_cases hh : h.length = N
        · simp only [hh, if_true, sqrt_fiberLikelihood_mul]
        · simp only [hh, if_false]
    _ = (bhattacharyya (K b).mass (K c).mass) ^ N := by
      rw [ResolutionAttainment.historySet_level_prod]
      congr 1
      rw [Fintype.sum_prod_type]
      simp [bhattacharyya]

/-- If the chosen label is at least as likely, an unchosen likelihood is
bounded by the pairwise square-root likelihood. -/
private theorem fiberLikelihood_le_sqrt_of_le {n : ℕ} {Y : Type} [Fintype Y]
    (K : Fin n → FiniteLaw Y) (b c : Fin n) (h : List (Unit × Y))
    (hle : fiberLikelihood K b h ≤ fiberLikelihood K c h) :
    fiberLikelihood K b h ≤
      Real.sqrt (fiberLikelihood K b h * fiberLikelihood K c h) := by
  calc
    fiberLikelihood K b h =
        min (fiberLikelihood K b h) (fiberLikelihood K c h) :=
          (min_eq_left hle).symm
    _ ≤ Real.sqrt (fiberLikelihood K b h * fiberLikelihood K c h) :=
      PairResolution.min_le_sqrt_mul _ _
        (fiberLikelihood_nonnegative K b h) (fiberLikelihood_nonnegative K c h)

/-! ## G14: the exact one-reading pairwise information bound -/

/-- The finite weighted second moment is the ordered-pair variance.
The identity uses normalization, not strictly positive prior weights. -/
private theorem finite_weighted_variance {B : Type} [Fintype B]
    (w a : B → ℝ) (hw1 : ∑ b, w b = 1) :
    (∑ b, w b * (a b * (a b - ∑ c, w c * a c))) =
      (1 / 2 : ℝ) * (∑ b, ∑ c, w b * w c * (a b - a c) ^ 2) := by
  classical
  let m : ℝ := ∑ b, w b * a b
  have hleft :
      (∑ b, w b * (a b * (a b - m))) =
        (∑ b, w b * a b ^ 2) - m ^ 2 := by
    calc
      _ = ∑ b, (w b * a b ^ 2 - (w b * a b) * m) := by
        apply Finset.sum_congr rfl
        intro b _
        ring
      _ = (∑ b, w b * a b ^ 2) - ∑ b, (w b * a b) * m :=
        by rw [Finset.sum_sub_distrib]
      _ = _ := by
        rw [← Finset.sum_mul]
        dsimp [m]
        ring
  have hfirst :
      (∑ b, ∑ c, w b * w c * a b ^ 2) =
        (∑ b, w b * a b ^ 2) * (∑ c, w c) := by
    calc
      _ = ∑ b, ∑ c, (w b * a b ^ 2) * w c := by
        apply Finset.sum_congr rfl
        intro b _
        apply Finset.sum_congr rfl
        intro c _
        ring
      _ = _ := by simp only [← Finset.mul_sum, ← Finset.sum_mul]
  have hsecond :
      (∑ b, ∑ c, w b * w c * a c ^ 2) =
        (∑ b, w b) * (∑ c, w c * a c ^ 2) := by
    calc
      _ = ∑ b, ∑ c, w b * (w c * a c ^ 2) := by
        apply Finset.sum_congr rfl
        intro b _
        apply Finset.sum_congr rfl
        intro c _
        ring
      _ = _ := by simp only [← Finset.mul_sum, ← Finset.sum_mul]
  have hcross :
      (∑ b, ∑ c, w b * w c * (a b * a c)) =
        (∑ b, w b * a b) * (∑ c, w c * a c) := by
    calc
      _ = ∑ b, ∑ c, (w b * a b) * (w c * a c) := by
        apply Finset.sum_congr rfl
        intro b _
        apply Finset.sum_congr rfl
        intro c _
        ring
      _ = _ := by simp only [← Finset.mul_sum, ← Finset.sum_mul]
  have hfull :
      (∑ b, ∑ c, w b * w c * (a b - a c) ^ 2) =
        (∑ b, ∑ c, w b * w c * a b ^ 2) +
          (∑ b, ∑ c, w b * w c * a c ^ 2) -
            2 * (∑ b, ∑ c, w b * w c * (a b * a c)) := by
    calc
      _ = ∑ b, ∑ c,
            (w b * w c * a b ^ 2 + w b * w c * a c ^ 2 -
              2 * (w b * w c * (a b * a c))) := by
        apply Finset.sum_congr rfl
        intro b _
        apply Finset.sum_congr rfl
        intro c _
        ring
      _ = _ := by
        simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
          ← Finset.mul_sum]
  change (∑ b, w b * (a b * (a b - m))) =
    (1 / 2 : ℝ) * (∑ b, ∑ c, w b * w c * (a b - a c) ^ 2)
  calc
    _ = (∑ b, w b * a b ^ 2) - m ^ 2 := hleft
    _ = (1 / 2 : ℝ) *
        (2 * (∑ b, w b * a b ^ 2) * (∑ b, w b) - 2 * m ^ 2) := by
          rw [hw1]
          ring
    _ = _ := by
      rw [hfull, hfirst, hsecond, hcross, hw1]
      dsimp [m]
      ring

/-- Entropy of a finite nonnegative weighted mixture is bounded by the
weighted chi-square expression, with the entire zero-mixture case included. -/
private theorem finite_negMulLog_mix_le {B : Type} [Fintype B]
    (w a : B → ℝ) (hw : ∀ b, 0 ≤ w b) (ha : ∀ b, 0 ≤ a b) :
    Real.negMulLog (∑ b, w b * a b) -
        ∑ b, w b * Real.negMulLog (a b) ≤
      (∑ b, w b * (a b * (a b - ∑ c, w c * a c))) /
        (∑ b, w b * a b) := by
  classical
  let m : ℝ := ∑ b, w b * a b
  have hm0 : 0 ≤ m :=
    Finset.sum_nonneg (fun b _ => mul_nonneg (hw b) (ha b))
  change Real.negMulLog m - ∑ b, w b * Real.negMulLog (a b) ≤
    (∑ b, w b * (a b * (a b - m))) / m
  rcases hm0.eq_or_lt with hm | hm
  · have hwaz : ∀ b, w b * a b = 0 := by
      intro b
      have hle : w b * a b ≤ m :=
        Finset.single_le_sum
          (fun c _ => mul_nonneg (hw c) (ha c)) (Finset.mem_univ b)
      have hnon := mul_nonneg (hw b) (ha b)
      linarith
    have hterm : ∀ b, w b * Real.negMulLog (a b) = 0 := by
      intro b
      rcases mul_eq_zero.mp (hwaz b) with hz | hz
      · simp [hz]
      · simp [hz]
    have hsum : (∑ b, w b * Real.negMulLog (a b)) = 0 :=
      Finset.sum_eq_zero (fun b _ => hterm b)
    rw [← hm, Real.negMulLog_zero, hsum, div_zero]
    norm_num
  · have hbound (b : B) :
        a b * Real.log (a b) - a b * Real.log m ≤
          a b * (a b - m) / m := by
      rcases (ha b).eq_or_lt with hz | hp
      · rw [← hz]
        simp
      · have hlog : Real.log (a b) - Real.log m ≤ a b / m - 1 := by
          rw [← Real.log_div hp.ne' hm.ne']
          exact Real.log_le_sub_one_of_pos (div_pos hp hm)
        calc
          a b * Real.log (a b) - a b * Real.log m =
              a b * (Real.log (a b) - Real.log m) := by ring
          _ ≤ a b * (a b / m - 1) :=
            mul_le_mul_of_nonneg_left hlog hp.le
          _ = a b * (a b - m) / m := by
            field_simp [ne_of_gt hm]
    have hsumlog :
        (∑ b, w b * Real.negMulLog (a b)) =
          -(∑ b, w b * (a b * Real.log (a b))) := by
      simp only [Real.negMulLog]
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro b _
      ring
    have hsum_m :
        (∑ b, w b * (a b * Real.log m)) = m * Real.log m := by
      calc
        _ = ∑ b, (w b * a b) * Real.log m := by
          apply Finset.sum_congr rfl
          intro b _
          ring
        _ = _ := by
          rw [← Finset.sum_mul]
    have hkey :
        Real.negMulLog m - ∑ b, w b * Real.negMulLog (a b) =
          ∑ b, w b * (a b * Real.log (a b) - a b * Real.log m) := by
      calc
        _ = (∑ b, w b * (a b * Real.log (a b))) -
              m * Real.log m := by
                rw [hsumlog]
                simp only [Real.negMulLog]
                ring
        _ = (∑ b, w b * (a b * Real.log (a b))) -
              ∑ b, w b * (a b * Real.log m) := by rw [hsum_m]
        _ = _ := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro b _
          ring
    rw [hkey]
    calc
      (∑ b, w b * (a b * Real.log (a b) - a b * Real.log m)) ≤
          ∑ b, w b * (a b * (a b - m) / m) := by
            apply Finset.sum_le_sum
            intro b _
            exact mul_le_mul_of_nonneg_left (hbound b) (hw b)
      _ = (∑ b, w b * (a b * (a b - m))) / m := by
        calc
          _ = ∑ b, (w b * (a b * (a b - m))) / m := by
            apply Finset.sum_congr rfl
            intro b _
            ring
          _ = _ := by rw [← Finset.sum_div]

/-- Every distinct ordered pair sits inside the mixture, so its weighted
variance term is dominated by its pairwise triangular-discrimination term. -/
private theorem finite_pairwise_chi_bound {B : Type} [Fintype B]
    (w a : B → ℝ) (hw : ∀ b, 0 ≤ w b) (ha : ∀ b, 0 ≤ a b) :
    (∑ b, ∑ c, w b * w c * (a b - a c) ^ 2 /
      (∑ d, w d * a d)) ≤
    (∑ b, ∑ c, (w b + w c) * (a b - a c) ^ 2 / (a b + a c)) := by
  classical
  apply Finset.sum_le_sum
  intro b _
  apply Finset.sum_le_sum
  intro c _
  by_cases hbc : b = c
  · subst c
    simp
  · have hsubset :
        (∑ d ∈ ({b, c} : Finset B), w d * a d) ≤
          (∑ d, w d * a d) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro d _ _
      exact mul_nonneg (hw d) (ha d)
    have htwopair :
        w b * a b + w c * a c ≤ (∑ d, w d * a d) := by
      simpa [Finset.sum_insert, hbc] using hsubset
    exact pairwise_chi_term_le (w b) (w c) (a b) (a c)
      (∑ d, w d * a d) (hw b) (hw c) (ha b) (ha c) htwopair

/-- The pointwise Jensen gap is bounded by half the ordered weighted
pair-discrimination sum, with no strictly positive-weight premise. -/
private theorem finite_negMulLog_pairwise_le {B : Type} [Fintype B]
    (w a : B → ℝ) (hw : ∀ b, 0 ≤ w b) (ha : ∀ b, 0 ≤ a b)
    (hw1 : ∑ b, w b = 1) :
    Real.negMulLog (∑ b, w b * a b) -
        ∑ b, w b * Real.negMulLog (a b) ≤
      (1 / 2 : ℝ) *
        (∑ b, ∑ c, (w b + w c) * (a b - a c) ^ 2 / (a b + a c)) := by
  calc
    _ ≤ (∑ b, w b * (a b * (a b - ∑ c, w c * a c))) /
        (∑ b, w b * a b) := finite_negMulLog_mix_le w a hw ha
    _ = (1 / 2 : ℝ) *
        (∑ b, ∑ c, w b * w c * (a b - a c) ^ 2 /
          (∑ d, w d * a d)) := by
            have hden :
                (∑ b, ∑ c, w b * w c * (a b - a c) ^ 2 /
                  (∑ d, w d * a d)) =
                (∑ b, ∑ c, w b * w c * (a b - a c) ^ 2) /
                  (∑ d, w d * a d) := by
              calc
                _ = ∑ b, (∑ c, w b * w c * (a b - a c) ^ 2) /
                    (∑ d, w d * a d) := by
                      apply Finset.sum_congr rfl
                      intro b _
                      rw [← Finset.sum_div]
                _ = _ := by rw [← Finset.sum_div]
            rw [finite_weighted_variance w a hw1, hden]
            ring
    _ ≤ (1 / 2 : ℝ) *
        (∑ b, ∑ c, (w b + w c) * (a b - a c) ^ 2 / (a b + a c)) :=
      mul_le_mul_of_nonneg_left (finite_pairwise_chi_bound w a hw ha) (by norm_num)

/-- G14. Exact n-ary one-reading information bound for a normalized finite
prior, retaining the coefficient p_b+p_b' on each ordered pair. -/
theorem fiberOneReading : FiberOneReadingGoal := by
  classical
  intro n Y _ p K
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hmi :
      jointMI (fun by_ : Fin n × Y => p.mass by_.1 * (K by_.1).mass by_.2) =
        (∑ y, (Real.negMulLog (∑ b, p.mass b * (K b).mass y) -
          (∑ b, p.mass b * Real.negMulLog ((K b).mass y)))) / Real.log 2 := by
    have hA :
        entropy (fun y => ∑ b, p.mass b * (K b).mass y) =
          (∑ y, Real.negMulLog (∑ b, p.mass b * (K b).mass y)) /
            Real.log 2 := rfl
    have hB :
        (∑ b, p.mass b * entropy (K b).mass) =
          (∑ y, ∑ b, p.mass b * Real.negMulLog ((K b).mass y)) /
            Real.log 2 := by
      calc
        _ = ∑ b, ∑ y, (p.mass b * Real.negMulLog ((K b).mass y)) /
              Real.log 2 := by
                apply Finset.sum_congr rfl
                intro b _
                change p.mass b *
                    ((∑ y, Real.negMulLog ((K b).mass y)) / Real.log 2) = _
                simp only [← Finset.sum_div, ← Finset.mul_sum]
                ring
        _ = _ := by
          rw [Finset.sum_comm]
          simp only [← Finset.sum_div]
    calc
      _ = entropy (fun y => ∑ b, p.mass b * (K b).mass y) -
            ∑ b, p.mass b * entropy (K b).mass :=
              jointMI_kernel p.mass (fun b => (K b).mass)
                (fun b => (K b).total)
      _ = (∑ y, Real.negMulLog (∑ b, p.mass b * (K b).mass y)) /
            Real.log 2 -
          (∑ y, ∑ b, p.mass b * Real.negMulLog ((K b).mass y)) /
            Real.log 2 := by rw [hA, hB]
      _ = _ := by
        rw [← sub_div, Finset.sum_sub_distrib]
  have hdisc :
      (∑ b, ∑ c, if b ≠ c then
        (p.mass b + p.mass c) * discrimination (K b).mass (K c).mass else 0) =
      (∑ y, ∑ b, ∑ c, (p.mass b + p.mass c) *
        ((K b).mass y - (K c).mass y) ^ 2 /
          ((K b).mass y + (K c).mass y)) := by
    calc
      _ = ∑ b, ∑ c,
          (p.mass b + p.mass c) * discrimination (K b).mass (K c).mass := by
            apply Finset.sum_congr rfl
            intro b _
            apply Finset.sum_congr rfl
            intro c _
            by_cases hbc : b = c
            · subst c
              simp [discrimination]
            · simp [hbc]
      _ = ∑ b, ∑ c, ∑ y,
            (p.mass b + p.mass c) *
              ((K b).mass y - (K c).mass y) ^ 2 /
                ((K b).mass y + (K c).mass y) := by
            apply Finset.sum_congr rfl
            intro b _
            apply Finset.sum_congr rfl
            intro c _
            simp only [discrimination, Finset.mul_sum, mul_div_assoc]
      _ = _ := by
        calc
          _ = ∑ b, ∑ y, ∑ c,
              (p.mass b + p.mass c) *
                ((K b).mass y - (K c).mass y) ^ 2 /
                  ((K b).mass y + (K c).mass y) := by
                    apply Finset.sum_congr rfl
                    intro b _
                    exact Finset.sum_comm
          _ = _ := Finset.sum_comm
  have hnat :
      (∑ y, (Real.negMulLog (∑ b, p.mass b * (K b).mass y) -
        (∑ b, p.mass b * Real.negMulLog ((K b).mass y)))) ≤
      (1 / 2 : ℝ) *
        (∑ y, ∑ b, ∑ c, (p.mass b + p.mass c) *
          ((K b).mass y - (K c).mass y) ^ 2 /
            ((K b).mass y + (K c).mass y)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro y _
    exact finite_negMulLog_pairwise_le p.mass
      (fun b => (K b).mass y)
      p.nonnegative (fun b => (K b).nonnegative y) p.total
  rw [hmi, hdisc]
  calc
    (∑ y, (Real.negMulLog (∑ b, p.mass b * (K b).mass y) -
      (∑ b, p.mass b * Real.negMulLog ((K b).mass y)))) / Real.log 2 ≤
      ((1 / 2 : ℝ) * (∑ y, ∑ b, ∑ c,
        (p.mass b + p.mass c) *
          ((K b).mass y - (K c).mass y) ^ 2 /
            ((K b).mass y + (K c).mass y))) / Real.log 2 :=
      div_le_div_of_nonneg_right hnat hlog.le
    _ = _ := by
      field_simp [ne_of_gt hlog]

/-! ## G15: the exact local capacity of an n-ary fiber menu -/

/-- Deleting the diagonal in the ordered sum counts each prior weight
exactly n-1 times in each coordinate. -/
private theorem finite_ordered_weight_count {n : ℕ} (w : Fin n → ℝ)
    (hw1 : ∑ b, w b = 1) :
    (∑ b, ∑ c, if b ≠ c then w b + w c else 0) =
      2 * ((n : ℝ) - 1) := by
  classical
  have hinner (b : Fin n) :
      (∑ c, if b ≠ c then w b + w c else 0) =
        ((n : ℝ) - 1) * w b + (1 - w b) := by
    have hconst :
        (∑ c : Fin n, if b ≠ c then w b else 0) =
          (n : ℝ) * w b - w b := by
      calc
        _ = ∑ c : Fin n, (w b - if c = b then w b else 0) := by
          apply Finset.sum_congr rfl
          intro c _
          by_cases hbc : c = b
          · subst c
            simp
          · have hcb : b ≠ c := Ne.symm hbc
            simp [hbc, hcb]
        _ = (∑ c : Fin n, w b) -
            (∑ c : Fin n, if c = b then w b else 0) :=
              by rw [Finset.sum_sub_distrib]
        _ = (n : ℝ) * w b - w b := by simp
    have hvariable :
        (∑ c : Fin n, if b ≠ c then w c else 0) = 1 - w b := by
      calc
        _ = ∑ c : Fin n, (w c - if c = b then w c else 0) := by
          apply Finset.sum_congr rfl
          intro c _
          by_cases hbc : c = b
          · subst c
            simp
          · have hcb : b ≠ c := Ne.symm hbc
            simp [hbc, hcb]
        _ = (∑ c : Fin n, w c) -
            (∑ c : Fin n, if c = b then w c else 0) :=
              by rw [Finset.sum_sub_distrib]
        _ = 1 - w b := by simp [hw1]
    calc
      _ = (∑ c : Fin n, if b ≠ c then w b else 0) +
          (∑ c : Fin n, if b ≠ c then w c else 0) := by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro c _
            by_cases hbc : b = c <;> simp [hbc]
      _ = ((n : ℝ) - 1) * w b + (1 - w b) := by
            rw [hconst, hvariable]
            ring
  calc
    _ = ∑ b, (((n : ℝ) - 1) * w b + (1 - w b)) := by
      apply Finset.sum_congr rfl
      intro b _
      exact hinner b
    _ = ((n : ℝ) - 1) * (∑ b, w b) +
        ((∑ b : Fin n, (1 : ℝ)) - ∑ b, w b) := by
          simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
            ← Finset.mul_sum]
    _ = 2 * ((n : ℝ) - 1) := by
      rw [hw1]
      simp
      ring

/-- G15. Each active n-ary reading has gain at most
(n-1)δ/log 2 and costs at least one. -/
theorem fiberCapacity : FiberCapacityGoal := by
  classical
  intro n A Y _ _ p δ menu hδ
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hn : 1 ≤ n := by
    by_contra h
    have hzero : n = 0 := by omega
    subst n
    have hp := p.prior.total
    simp at hp
  have hcast : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hκ : 0 ≤ (((n : ℝ) - 1) * δ / Real.log 2) :=
    div_nonneg (mul_nonneg (sub_nonneg.mpr hcast) hδ) hlog.le
  intro h a hw _ _
  let q : FiniteLaw (Fin n) :=
    { mass := posterior p h
      nonnegative := posterior_nonnegative p h
      total := posterior_total p h hw }
  have hrows :
      (∑ b, ∑ c, if b ≠ c then
        (q.mass b + q.mass c) *
          discrimination (p.observation h a b).mass
            (p.observation h a c).mass else 0) ≤
      δ * (∑ b, ∑ c, if b ≠ c then q.mass b + q.mass c else 0) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro b _
    apply Finset.sum_le_sum
    intro c _
    by_cases hbc : b = c
    · simp [hbc]
    · simp only [if_pos hbc]
      calc
        (q.mass b + q.mass c) *
            discrimination (p.observation h a b).mass
              (p.observation h a c).mass ≤
          (q.mass b + q.mass c) * δ :=
            mul_le_mul_of_nonneg_left (menu.rows h a b c)
              (add_nonneg (q.nonnegative b) (q.nonnegative c))
        _ = δ * (q.mass b + q.mass c) := mul_comm _ _
  have hcount :
      (∑ b, ∑ c, if b ≠ c then q.mass b + q.mass c else 0) =
      2 * ((n : ℝ) - 1) :=
        finite_ordered_weight_count q.mass q.total
  have hsingle :
      localGain p h a ≤ (((n : ℝ) - 1) * δ) / Real.log 2 := by
    calc
      localGain p h a ≤
        (∑ b, ∑ c, if b ≠ c then
          (q.mass b + q.mass c) *
            discrimination (p.observation h a b).mass
              (p.observation h a c).mass else 0) /
          (2 * Real.log 2) := by
            exact fiberOneReading n Y q (fun b => p.observation h a b)
      _ ≤ δ * (2 * ((n : ℝ) - 1)) / (2 * Real.log 2) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        rw [← hcount]
        exact hrows
      _ = _ := by
        field_simp [ne_of_gt hlog]
        ring
  exact hsingle.trans (le_mul_of_one_le_right hκ (menu.reading_cost h a))

/-! ## G16: maximum-likelihood attainment for n labels -/

/-- Off-diagonal sums over `Fin n` count n - 1 copies. -/
private theorem sum_ne_const {n : ℕ} (b : Fin n) (x : ℝ) :
    (∑ c : Fin n, if c ≠ b then x else 0) = ((n : ℝ) - 1) * x := by
  classical
  have hsplit :
      (∑ c : Fin n, x) =
        (∑ c : Fin n, if c ≠ b then x else 0) +
          ∑ c : Fin n, if c = b then x else 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro c _
    by_cases hc : c = b
    · rw [if_neg (not_not.mpr hc), if_pos hc, zero_add]
    · rw [if_pos hc, if_neg hc, add_zero]
  have hdiag : (∑ c : Fin n, if c = b then x else 0) = x := by
    rw [Finset.sum_ite_eq']
    exact if_pos (Finset.mem_univ b)
  have hconst : (∑ _c : Fin n, x) = (n : ℝ) * x := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  linarith

/-- The pairwise affinity term of an ordered pair of distinct labels. -/
private noncomputable def offAffinity {n : ℕ} {Y : Type} [Fintype Y]
    (K : Fin n → FiniteLaw Y) (N : ℕ) (h : List (Unit × Y)) (b c : Fin n) : ℝ :=
  if c ≠ b then
    (if h.length = N then
      Real.sqrt (fiberLikelihood K b h * fiberLikelihood K c h) else 0)
  else 0

private theorem offAffinity_nonnegative {n : ℕ} {Y : Type} [Fintype Y]
    (K : Fin n → FiniteLaw Y) (N : ℕ) (h : List (Unit × Y)) (b c : Fin n) :
    0 ≤ offAffinity K N h b c := by
  unfold offAffinity
  split_ifs
  · exact Real.sqrt_nonneg _
  · exact le_refl 0
  · exact le_refl 0

/-- Summing the depth-N affinity of one ordered pair over all histories. -/
private theorem sum_offAffinity {n : ℕ} {Y : Type} [Fintype Y]
    (K : Fin n → FiniteLaw Y) (N : ℕ) (b c : Fin n) :
    (∑ h ∈ historySet (Unit × Y) N, offAffinity K N h b c) =
      if c ≠ b then (bhattacharyya (K b).mass (K c).mass) ^ N else 0 := by
  by_cases hcb : c ≠ b
  · rw [if_pos hcb, ← bhattacharyya_fiber_level K b c N]
    apply Finset.sum_congr rfl
    intro h _
    unfold offAffinity
    rw [if_pos hcb]
  · rw [if_neg hcb]
    apply Finset.sum_eq_zero
    intro h _
    unfold offAffinity
    rw [if_neg hcb]

/-- G16. Under the uniform prior and a maximum-likelihood decoder, the stopped
error mass of the repeated n-ary reading is at most (n - 1) β ^ N, where β
bounds the Bhattacharyya coefficient of every pair of distinct rows. -/
theorem fiberAttainment : FiberAttainmentGoal := by
  classical
  intro n Y _ p0 K β g N hunif hbc hml
  have hn : 1 ≤ n := by
    by_contra h
    have hzero : n = 0 := by omega
    subst n
    have hp := p0.total
    simp at hp
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hinv : 0 ≤ 1 / (n : ℝ) := le_of_lt (one_div_pos.mpr hnpos)
  have hterm : ∀ h ∈ historySet (Unit × Y) N, ∀ b : Fin n,
      (if g h ≠ b then stoppedMass (repeatFiber p0 K N) N b h else 0) ≤
        (1 / (n : ℝ)) * ∑ c, offAffinity K N h b c := by
    intro h _ b
    have hsum0 : 0 ≤ ∑ c, offAffinity K N h b c :=
      Finset.sum_nonneg (fun c _ => offAffinity_nonnegative K N h b c)
    by_cases hgb : g h ≠ b
    · rw [if_pos hgb, stoppedMass_repeatFiber]
      by_cases hl : h.length = N
      · rw [if_pos hl, hunif b]
        apply mul_le_mul_of_nonneg_left _ hinv
        calc
          fiberLikelihood K b h ≤
              Real.sqrt (fiberLikelihood K b h * fiberLikelihood K (g h) h) :=
            fiberLikelihood_le_sqrt_of_le K b (g h) h (hml h b)
          _ = offAffinity K N h b (g h) := by
            unfold offAffinity
            rw [if_pos hgb, if_pos hl]
          _ ≤ ∑ c, offAffinity K N h b c :=
            Finset.single_le_sum
              (fun c _ => offAffinity_nonnegative K N h b c) (Finset.mem_univ (g h))
      · rw [if_neg hl]
        exact mul_nonneg hinv hsum0
    · rw [if_neg hgb]
      exact mul_nonneg hinv hsum0
  have hswap :
      (∑ h ∈ historySet (Unit × Y) N, ∑ b : Fin n,
          (1 / (n : ℝ)) * ∑ c, offAffinity K N h b c) =
        (1 / (n : ℝ)) * ∑ b : Fin n, ∑ c : Fin n,
          (if c ≠ b then (bhattacharyya (K b).mass (K c).mass) ^ N else 0) := by
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    rw [← Finset.mul_sum, Finset.sum_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro c _
    exact sum_offAffinity K N b c
  have hpow : ∀ b c : Fin n,
      (if c ≠ b then (bhattacharyya (K b).mass (K c).mass) ^ N else 0) ≤
        (if c ≠ b then β ^ N else 0) := by
    intro b c
    by_cases hcb : c ≠ b
    · rw [if_pos hcb, if_pos hcb]
      exact pow_le_pow_left₀ (bhattacharyya_nonneg _ _)
        (hbc b c (fun hbc' => hcb hbc'.symm)) N
    · rw [if_neg hcb, if_neg hcb]
  calc
    fiberError p0 K N g =
        ∑ h ∈ historySet (Unit × Y) N, ∑ b : Fin n,
          (if g h ≠ b then stoppedMass (repeatFiber p0 K N) N b h else 0) := rfl
    _ ≤ ∑ h ∈ historySet (Unit × Y) N, ∑ b : Fin n,
          (1 / (n : ℝ)) * ∑ c, offAffinity K N h b c :=
      Finset.sum_le_sum (fun h hh => Finset.sum_le_sum (fun b _ => hterm h hh b))
    _ = (1 / (n : ℝ)) * ∑ b : Fin n, ∑ c : Fin n,
          (if c ≠ b then (bhattacharyya (K b).mass (K c).mass) ^ N else 0) := hswap
    _ ≤ (1 / (n : ℝ)) * ∑ b : Fin n, ∑ c : Fin n, (if c ≠ b then β ^ N else 0) :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum (fun b _ => Finset.sum_le_sum (fun c _ => hpow b c))) hinv
    _ = ((n : ℝ) - 1) * β ^ N := by
      simp only [sum_ne_const]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp

/-! ## G18: sparse rows, bounded discrimination, unbounded information -/

private theorem sparseRow_nonnegative {n : ℕ} (b y : Fin n) :
    0 ≤ sparseRow n (1 / 2) b y := by
  have hc : 0 ≤ (1 - (1 / 2 : ℝ)) / n := div_nonneg (by norm_num) (Nat.cast_nonneg n)
  unfold sparseRow
  split_ifs
  · linarith
  · linarith

private theorem sparseRow_total {n : ℕ} (hn : 1 ≤ n) (b : Fin n) :
    ∑ y, sparseRow n (1 / 2) b y = 1 := by
  classical
  have hn0 : (n : ℝ) ≠ 0 := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    exact ne_of_gt this
  unfold sparseRow
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Finset.sum_ite_eq', if_pos (Finset.mem_univ b),
    mul_div_cancel₀ _ hn0]
  norm_num

/-- Every pair of sparse rows at ε = 1/2 has discrimination at most one. -/
private theorem sparse_discrimination_le_one {n : ℕ} (b b' : Fin n) :
    discrimination (sparseRow n (1 / 2) b) (sparseRow n (1 / 2) b') ≤ 1 := by
  classical
  refine (discrimination_le_sum_abs _ _ (sparseRow_nonnegative b)
    (sparseRow_nonnegative b')).trans ?_
  have hterm : ∀ y : Fin n,
      |sparseRow n (1 / 2) b y - sparseRow n (1 / 2) b' y| ≤
        (if y = b then (1 / 2 : ℝ) else 0) + (if y = b' then (1 / 2 : ℝ) else 0) := by
    intro y
    rw [abs_sub_le_iff]
    unfold sparseRow
    split_ifs <;> constructor <;> linarith
  calc
    (∑ y, |sparseRow n (1 / 2) b y - sparseRow n (1 / 2) b' y|) ≤
        ∑ y : Fin n, ((if y = b then (1 / 2 : ℝ) else 0) +
          (if y = b' then (1 / 2 : ℝ) else 0)) :=
      Finset.sum_le_sum (fun y _ => hterm y)
    _ = 1 := by
      rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq',
        if_pos (Finset.mem_univ b), if_pos (Finset.mem_univ b')]
      norm_num

/-- The uniform law on `Fin n` has entropy log n / log 2 bits. -/
private theorem entropy_uniform_fin {n : ℕ} (hn : 1 ≤ n) :
    ProtocolResolution.entropy (fun _ : Fin n => (1 / (n : ℝ))) =
      Real.log n / Real.log 2 := by
  have hn0 : (n : ℝ) ≠ 0 := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    exact ne_of_gt this
  unfold ProtocolResolution.entropy BitDivision.entropy
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  congr 1
  unfold Real.negMulLog
  rw [one_div, Real.log_inv]
  field_simp

/-- Each sparse row has entropy (log 2 + log n - ((n+1)/(2n)) log(n+1)) / log 2 bits. -/
private theorem entropy_sparseRow {n : ℕ} (hn : 1 ≤ n) (z : Fin n) :
    ProtocolResolution.entropy (sparseRow n (1 / 2) z) =
      (Real.log 2 + Real.log n -
        ((n : ℝ) + 1) / (2 * n) * Real.log ((n : ℝ) + 1)) / Real.log 2 := by
  classical
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  set c : ℝ := (1 - (1 / 2 : ℝ)) / n with hcdef
  have hsplit : ∀ y : Fin n,
      Real.negMulLog (sparseRow n (1 / 2) z y) =
        (if y = z then Real.negMulLog (c + 1 / 2) else 0) +
          (if y ≠ z then Real.negMulLog c else 0) := by
    intro y
    unfold sparseRow
    by_cases hy : y = z
    · rw [if_pos hy, if_pos hy, if_neg (not_not.mpr hy), add_zero]
    · rw [if_neg hy, if_neg hy, if_pos hy, add_zero, zero_add]
  unfold ProtocolResolution.entropy BitDivision.entropy
  congr 1
  rw [Finset.sum_congr rfl (fun y _ => hsplit y), Finset.sum_add_distrib,
    Finset.sum_ite_eq', if_pos (Finset.mem_univ z), sum_ne_const]
  have hc1 : c + 1 / 2 = ((n : ℝ) + 1) / (2 * n) := by
    rw [hcdef]
    field_simp
    ring
  have hc2 : c = 1 / (2 * n) := by
    rw [hcdef]
    field_simp
    ring
  have h2n : (2 : ℝ) * n ≠ 0 := mul_ne_zero two_ne_zero hn0
  have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have hlog1 : Real.log (((n : ℝ) + 1) / (2 * n)) =
      Real.log ((n : ℝ) + 1) - (Real.log 2 + Real.log n) := by
    rw [Real.log_div hn1 h2n, Real.log_mul two_ne_zero hn0]
  have hlog2 : Real.log (1 / (2 * (n : ℝ))) = -(Real.log 2 + Real.log n) := by
    rw [one_div, Real.log_inv, Real.log_mul two_ne_zero hn0]
  unfold Real.negMulLog
  rw [hc1, hc2, hlog1, hlog2]
  field_simp
  ring

/-- The sparse channel under the uniform prior carries
(((n+1)/(2n)) log(n+1) - log 2) / log 2 bits. -/
private theorem sparse_information {n : ℕ} (hn : 1 ≤ n) :
    jointMI (fun by_ : Fin n × Fin n => (1 / n : ℝ) * sparseRow n (1 / 2) by_.1 by_.2) =
      ((((n : ℝ) + 1) / (2 * n)) * Real.log ((n : ℝ) + 1) - Real.log 2) /
        Real.log 2 := by
  classical
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  rw [jointMI_kernel (fun _ : Fin n => (1 / n : ℝ)) (sparseRow n (1 / 2))
    (sparseRow_total hn)]
  have hmarg : (fun y : Fin n => ∑ z : Fin n, (1 / (n : ℝ)) * sparseRow n (1 / 2) z y) =
      fun _ => 1 / (n : ℝ) := by
    funext y
    rw [← Finset.mul_sum]
    unfold sparseRow
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Finset.sum_ite_eq, if_pos (Finset.mem_univ y),
      mul_div_cancel₀ _ hn0]
    norm_num
  rw [hmarg, entropy_uniform_fin hn]
  simp only [entropy_sparseRow hn]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

/-- G18. Sparse rows at ε = 1/2 keep every pairwise discrimination at most one,
while the uniform-prior information exceeds every real bound for large n. -/
theorem sparseControl : SparseControlGoal := by
  intro C
  obtain ⟨m, hm⟩ := exists_nat_gt (Real.exp (2 * (|C| + 1)))
  refine ⟨m + 2, by omega, fun b b' => sparse_discrimination_le_one b b', ?_⟩
  have hn : 1 ≤ m + 2 := by omega
  rw [sparse_information hn]
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlog1 : Real.log 2 < 1 := by
    have := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num)
    linarith
  set N : ℝ := ((m + 2 : ℕ) : ℝ) with hN
  have hNpos : 0 < N := by rw [hN]; positivity
  have hL : 2 * (|C| + 1) < Real.log (N + 1) := by
    rw [Real.lt_log_iff_exp_lt (by positivity)]
    have hmN : (m : ℝ) < N + 1 := by
      rw [hN]
      push_cast
      linarith
    linarith
  have hL0 : 0 ≤ Real.log (N + 1) := le_of_lt ((by positivity : (0 : ℝ) ≤ 2 * (|C| + 1)).trans_lt hL)
  have hfrac : (1 / 2 : ℝ) ≤ (N + 1) / (2 * N) := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    linarith
  have h3 : (1 / 2 : ℝ) * Real.log (N + 1) ≤ (N + 1) / (2 * N) * Real.log (N + 1) :=
    mul_le_mul_of_nonneg_right hfrac hL0
  have h1 : C * Real.log 2 ≤ |C| * Real.log 2 :=
    mul_le_mul_of_nonneg_right (le_abs_self C) hlog.le
  have h2 : |C| * Real.log 2 ≤ |C| := mul_le_of_le_one_right (abs_nonneg C) hlog1.le
  rw [lt_div_iff₀ hlog]
  linarith

/-! ## G17: Fano's inequality on the stopped law of the repeated reading -/

/-- Tangent-line bound of the concave function negMulLog at a positive point. -/
private theorem negMulLog_le_tangent (x a : ℝ) (hx : 0 ≤ x) (ha : 0 < a) :
    Real.negMulLog x ≤ -x * Real.log a - x + a := by
  unfold Real.negMulLog
  rcases hx.eq_or_lt with h0 | hpos
  · rw [← h0]
    simp only [neg_zero, zero_mul, sub_zero, zero_add]
    exact ha.le
  · have hlog := Real.log_le_sub_one_of_pos (div_pos ha hpos)
    rw [Real.log_div (ne_of_gt ha) (ne_of_gt hpos)] at hlog
    have hmul := mul_le_mul_of_nonneg_left hlog hpos.le
    have hx' : x * (a / x - 1) = a - x := by
      field_simp
    rw [hx'] at hmul
    linarith

/-- Unnormalized entropy on a finite set is at most its mass times log of its size. -/
private theorem sum_negMulLog_le_log_card {Z : Type} (S : Finset Z) (m : Z → ℝ)
    (hm : ∀ z, 0 ≤ m z) :
    (∑ z ∈ S, Real.negMulLog (m z)) ≤
      Real.negMulLog (∑ z ∈ S, m z) + (∑ z ∈ S, m z) * Real.log S.card := by
  have ht0 : 0 ≤ ∑ z ∈ S, m z := Finset.sum_nonneg (fun z _ => hm z)
  rcases ht0.eq_or_lt with h0 | hpos
  · have hz : ∀ z ∈ S, m z = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun z _ => hm z)).mp h0.symm
    rw [Finset.sum_eq_zero (fun z hz' => by rw [hz z hz', Real.negMulLog_zero]), ← h0,
      Real.negMulLog_zero, zero_mul, add_zero]
  · have hne : S.Nonempty := by
      by_contra hne
      rw [Finset.not_nonempty_iff_eq_empty] at hne
      rw [hne, Finset.sum_empty] at hpos
      exact lt_irrefl _ hpos
    have hcard : (0 : ℝ) < S.card := by exact_mod_cast hne.card_pos
    have ha : 0 < (∑ z ∈ S, m z) / S.card := div_pos hpos hcard
    calc
      (∑ z ∈ S, Real.negMulLog (m z)) ≤
          ∑ z ∈ S, (-(m z) * Real.log ((∑ z ∈ S, m z) / S.card) - m z +
            (∑ z ∈ S, m z) / S.card) :=
        Finset.sum_le_sum (fun z _ => negMulLog_le_tangent (m z) _ (hm z) ha)
      _ = -(∑ z ∈ S, m z) * Real.log ((∑ z ∈ S, m z) / S.card) -
            (∑ z ∈ S, m z) + S.card * ((∑ z ∈ S, m z) / S.card) := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
          Finset.sum_neg_distrib, Finset.sum_const, nsmul_eq_mul]
      _ = Real.negMulLog (∑ z ∈ S, m z) + (∑ z ∈ S, m z) * Real.log S.card := by
        rw [Real.log_div (ne_of_gt hpos) (ne_of_gt hcard),
          mul_div_cancel₀ _ (ne_of_gt hcard)]
        unfold Real.negMulLog
        ring

/-- The uncertainty of one stopped slice is at most the uncertainty of its
(error, correct) binary slice plus the error mass times log(n - 1), in bits. -/
private theorem massUncertainty_le_error_split {n : ℕ} (hn : 1 ≤ n)
    (m : Fin n → ℝ) (hm : ∀ z, 0 ≤ m z) (g0 : Fin n) :
    massUncertainty m ≤
      massUncertainty (fun b : Bool => cond b (∑ z, if g0 ≠ z then m z else 0) (m g0)) +
        (∑ z, if g0 ≠ z then m z else 0) * Real.log ((n : ℝ) - 1) / Real.log 2 := by
  classical
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hsplit : ∀ f : Fin n → ℝ,
      (∑ z, f z) = f g0 + ∑ z, if g0 ≠ z then f z else 0 := by
    intro f
    have hpt : ∀ z, f z = (if g0 = z then f z else 0) + (if g0 ≠ z then f z else 0) := by
      intro z
      by_cases hz : g0 = z
      · rw [if_pos hz, if_neg (not_not.mpr hz), add_zero]
      · rw [if_neg hz, if_pos hz, zero_add]
    rw [Finset.sum_congr rfl (fun z _ => hpt z), Finset.sum_add_distrib,
      Finset.sum_ite_eq, if_pos (Finset.mem_univ g0)]
  have hfilter : ∀ f : Fin n → ℝ,
      (∑ z, if g0 ≠ z then f z else 0) =
        ∑ z ∈ Finset.univ.filter (fun z => g0 ≠ z), f z := by
    intro f
    rw [Finset.sum_filter]
  have hcard : ((Finset.univ.filter (fun z : Fin n => g0 ≠ z)).card : ℝ) = (n : ℝ) - 1 := by
    rw [Finset.filter_ne, Finset.card_erase_of_mem (Finset.mem_univ g0), Finset.card_univ,
      Fintype.card_fin, Nat.cast_sub hn, Nat.cast_one]
  have hset := sum_negMulLog_le_log_card (Finset.univ.filter (fun z : Fin n => g0 ≠ z)) m hm
  rw [hcard] at hset
  have hent : (∑ z, if g0 ≠ z then entropyTerm (m z) else 0) =
      (∑ z ∈ Finset.univ.filter (fun z => g0 ≠ z), Real.negMulLog (m z)) / Real.log 2 := by
    rw [hfilter (fun z => entropyTerm (m z)), Finset.sum_div]
    rfl
  have hbound :
      (∑ z, if g0 ≠ z then entropyTerm (m z) else 0) -
          entropyTerm (∑ z, if g0 ≠ z then m z else 0) ≤
        (∑ z, if g0 ≠ z then m z else 0) * Real.log ((n : ℝ) - 1) / Real.log 2 := by
    rw [hent, hfilter m]
    unfold entropyTerm
    rw [div_sub_div_same]
    apply div_le_div_of_nonneg_right _ hlog.le
    linarith
  unfold massUncertainty
  rw [entropy_eq_sum, entropy_eq_sum, Fintype.sum_bool, Fintype.sum_bool]
  simp only [cond_true, cond_false]
  rw [hsplit (fun z => entropyTerm (m z)), hsplit m]
  rw [add_comm (m g0) (∑ z, if g0 ≠ z then m z else 0)]
  linarith

/-- G17. Under the uniform prior, the terminal information of the repeated
n-ary reading is at least log₂ n minus the Fano term of the decoder's error. -/
theorem fiberFano : FiberFanoGoal := by
  classical
  intro n Y _ p0 K g N hunif hn2 _herr
  have hn : 1 ≤ n := by omega
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  rw [terminalMI_eq_entropy_sub (repeatFiber p0 K N) N (historyBank Unit Y N)
    (historyBank_complete Unit Y N)]
  have hprior : (repeatFiber p0 K N).prior.mass = fun _ => 1 / (n : ℝ) :=
    funext hunif
  rw [hprior, entropy_uniform_fin hn, Real.log_div_log]
  have hslice : ∀ h ∈ historySet (Unit × Y) N,
      massUncertainty (fun z => stoppedMass (repeatFiber p0 K N) N z h) ≤
        massUncertainty (fun b : Bool => cond b
          (∑ z, if g h ≠ z then stoppedMass (repeatFiber p0 K N) N z h else 0)
          (stoppedMass (repeatFiber p0 K N) N (g h) h)) +
          (∑ z, if g h ≠ z then stoppedMass (repeatFiber p0 K N) N z h else 0) *
            Real.log ((n : ℝ) - 1) / Real.log 2 :=
    fun h _ => massUncertainty_le_error_split hn _
      (fun z => stoppedMass_nonnegative _ _ _ _) (g h)
  have hnon : ∀ (h : List (Unit × Y)) (b : Bool), 0 ≤ cond b
      (∑ z, if g h ≠ z then stoppedMass (repeatFiber p0 K N) N z h else 0)
      (stoppedMass (repeatFiber p0 K N) N (g h) h) := by
    intro h b
    cases b
    · exact stoppedMass_nonnegative _ _ _ _
    · exact Finset.sum_nonneg (fun z _ => by
        split_ifs
        · exact stoppedMass_nonnegative _ _ _ _
        · exact le_refl 0)
  have htot : (∑ h ∈ historySet (Unit × Y) N,
      (cond true
        (∑ z, if g h ≠ z then stoppedMass (repeatFiber p0 K N) N z h else 0)
        (stoppedMass (repeatFiber p0 K N) N (g h) h) +
      cond false
        (∑ z, if g h ≠ z then stoppedMass (repeatFiber p0 K N) N z h else 0)
        (stoppedMass (repeatFiber p0 K N) N (g h) h))) = 1 := by
    have hrow : ∀ h : List (Unit × Y),
        (cond true
          (∑ z, if g h ≠ z then stoppedMass (repeatFiber p0 K N) N z h else 0)
          (stoppedMass (repeatFiber p0 K N) N (g h) h) +
        cond false
          (∑ z, if g h ≠ z then stoppedMass (repeatFiber p0 K N) N z h else 0)
          (stoppedMass (repeatFiber p0 K N) N (g h) h)) =
          ∑ z, stoppedMass (repeatFiber p0 K N) N z h := by
      intro h
      simp only [cond_true, cond_false]
      have hpt : ∀ z, stoppedMass (repeatFiber p0 K N) N z h =
          (if g h = z then stoppedMass (repeatFiber p0 K N) N z h else 0) +
            (if g h ≠ z then stoppedMass (repeatFiber p0 K N) N z h else 0) := by
        intro z
        by_cases hz : g h = z
        · rw [if_pos hz, if_neg (not_not.mpr hz), add_zero]
        · rw [if_neg hz, if_pos hz, zero_add]
      rw [Finset.sum_congr rfl (fun z _ => hpt z), Finset.sum_add_distrib,
        Finset.sum_ite_eq, if_pos (Finset.mem_univ (g h)), add_comm]
    rw [Finset.sum_congr rfl (fun h _ => hrow h), Finset.sum_comm]
    simp only [historySet_stoppedMass_target_marginal]
    exact (repeatFiber p0 K N).prior.total
  have hfano := ResolutionAttainment.sum_massUncertainty_le_binEntropy (historySet (Unit × Y) N)
    (fun h b => cond b
      (∑ z, if g h ≠ z then stoppedMass (repeatFiber p0 K N) N z h else 0)
      (stoppedMass (repeatFiber p0 K N) N (g h) h))
    hnon htot (fun _ => false)
  simp only [Bool.not_false, cond_true] at hfano
  have herr_eq : (∑ h ∈ historySet (Unit × Y) N,
      ∑ z, if g h ≠ z then stoppedMass (repeatFiber p0 K N) N z h else 0) =
        fiberError p0 K N g := rfl
  rw [herr_eq] at hfano
  have hsum := Finset.sum_le_sum hslice
  rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_mul, herr_eq] at hsum
  rw [add_div]
  linarith

/-! ## N19: per-state and maximum likelihood decoding error -/

/-- The conditional error chance under a fixed state at exactly N readings. -/
noncomputable def fiberStateError {n : ℕ} {Y : Type} [Fintype Y]
    (K : Fin n → FiniteLaw Y) (N : ℕ)
    (g : List (Unit × Y) → Fin n) (b : Fin n) : ℝ :=
  ∑ h ∈ historySet (Unit × Y) N,
    if g h ≠ b then (if h.length = N then fiberLikelihood K b h else 0) else 0

/-- The largest conditional error chance across the n states of a nontrivial fiber. -/
noncomputable def fiberMaxError {n : ℕ} {Y : Type} [Fintype Y]
    (hn : 2 ≤ n) (K : Fin n → FiniteLaw Y) (N : ℕ)
    (g : List (Unit × Y) → Fin n) : ℝ := by
  classical
  let b : Fin n := ⟨0, by omega⟩
  exact Finset.sup' Finset.univ ⟨b, Finset.mem_univ b⟩ (fiberStateError K N g)

/-- Every state's likelihood-decoder error is bounded by the sum of pairwise
Bhattacharyya affinities, with no prior distribution assumption. -/
theorem fiberStateError_le_bhattacharyya {n : ℕ} {Y : Type} [Fintype Y]
    (K : Fin n → FiniteLaw Y) (N : ℕ) (g : List (Unit × Y) → Fin n)
    (β : ℝ)
    (hbc : ∀ b c, b ≠ c → bhattacharyya (K b).mass (K c).mass ≤ β)
    (hml : ∀ h b, fiberLikelihood K b h ≤ fiberLikelihood K (g h) h)
    (b : Fin n) :
    fiberStateError K N g b ≤ ((n : ℝ) - 1) * β ^ N := by
  classical
  have hterm :
      ∀ h ∈ historySet (Unit × Y) N,
      (if g h ≠ b then (if h.length = N then fiberLikelihood K b h else 0) else 0) ≤
        ∑ c : Fin n, offAffinity K N h b c := by
    intro h _
    have hsum0 : 0 ≤ ∑ c : Fin n, offAffinity K N h b c :=
      Finset.sum_nonneg (fun c _ => offAffinity_nonnegative K N h b c)
    by_cases hgb : g h ≠ b
    · rw [if_pos hgb]
      by_cases hl : h.length = N
      · rw [if_pos hl]
        calc
          fiberLikelihood K b h ≤
              Real.sqrt (fiberLikelihood K b h * fiberLikelihood K (g h) h) :=
            fiberLikelihood_le_sqrt_of_le K b (g h) h (hml h b)
          _ = offAffinity K N h b (g h) := by
            unfold offAffinity
            rw [if_pos hgb, if_pos hl]
          _ ≤ ∑ c : Fin n, offAffinity K N h b c :=
            Finset.single_le_sum
              (fun c _ => offAffinity_nonnegative K N h b c)
              (Finset.mem_univ (g h))
      · rw [if_neg hl]
        exact hsum0
    · rw [if_neg hgb]
      exact hsum0
  have hswap :
      (∑ h ∈ historySet (Unit × Y) N,
        ∑ c : Fin n, offAffinity K N h b c) =
      ∑ c : Fin n,
        if c ≠ b then (bhattacharyya (K b).mass (K c).mass) ^ N else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro c _
    exact sum_offAffinity K N b c
  have hpow : ∀ c : Fin n,
      (if c ≠ b then (bhattacharyya (K b).mass (K c).mass) ^ N else 0) ≤
        (if c ≠ b then β ^ N else 0) := by
    intro c
    by_cases hcb : c ≠ b
    · rw [if_pos hcb, if_pos hcb]
      exact pow_le_pow_left₀ (bhattacharyya_nonneg _ _)
        (hbc b c (Ne.symm hcb)) N
    · rw [if_neg hcb, if_neg hcb]
  calc
    fiberStateError K N g b =
        ∑ h ∈ historySet (Unit × Y) N,
          (if g h ≠ b then (if h.length = N then fiberLikelihood K b h else 0) else 0) :=
      rfl
    _ ≤ ∑ h ∈ historySet (Unit × Y) N,
          ∑ c : Fin n, offAffinity K N h b c :=
      Finset.sum_le_sum (fun h hh => hterm h hh)
    _ = ∑ c : Fin n,
          (if c ≠ b then (bhattacharyya (K b).mass (K c).mass) ^ N else 0) := hswap
    _ ≤ ∑ c : Fin n, (if c ≠ b then β ^ N else 0) :=
      Finset.sum_le_sum (fun c _ => hpow c)
    _ = ((n : ℝ) - 1) * β ^ N := sum_ne_const b _

/-- Pairwise discrimination lower bounds give an exponential error bound for
each true state, independently of the prior. -/
theorem fiberStateError_le_exp {n : ℕ} {Y : Type} [Fintype Y]
    (K : Fin n → FiniteLaw Y) (N : ℕ) (g : List (Unit × Y) → Fin n)
    (Δmin : ℝ)
    (hdisc : ∀ b c, b ≠ c →
      Δmin ≤ discrimination (K b).mass (K c).mass)
    (hml : ∀ h b, fiberLikelihood K b h ≤ fiberLikelihood K (g h) h)
    (b : Fin n) :
    fiberStateError K N g b ≤
      ((n : ℝ) - 1) * Real.exp (-((N : ℝ) * Δmin / 4)) := by
  have hbc : ∀ b c : Fin n, b ≠ c →
      bhattacharyya (K b).mass (K c).mass ≤ Real.exp (-(Δmin / 4)) := by
    intro b c hneq
    have hpair := bhattacharyya_le_one_sub_quarter_discrimination
      (K b).mass (K c).mass
      (K b).nonnegative (K c).nonnegative (K b).total (K c).total
    have hmin := hdisc b c hneq
    have hexp := Real.add_one_le_exp (-(Δmin / 4))
    linarith
  calc
    fiberStateError K N g b ≤
        ((n : ℝ) - 1) * (Real.exp (-(Δmin / 4))) ^ N :=
      fiberStateError_le_bhattacharyya K N g _ hbc hml b
    _ = ((n : ℝ) - 1) * Real.exp (-((N : ℝ) * Δmin / 4)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring_nf

/-- The largest state-wise error inherits the exponential pair-discrimination bound. -/
theorem fiberMaxError_le_exp {n : ℕ} {Y : Type} [Fintype Y]
    (hn : 2 ≤ n) (K : Fin n → FiniteLaw Y) (N : ℕ)
    (g : List (Unit × Y) → Fin n) (Δmin : ℝ)
    (hdisc : ∀ b c, b ≠ c →
      Δmin ≤ discrimination (K b).mass (K c).mass)
    (hml : ∀ h b, fiberLikelihood K b h ≤ fiberLikelihood K (g h) h) :
    fiberMaxError hn K N g ≤
      ((n : ℝ) - 1) * Real.exp (-((N : ℝ) * Δmin / 4)) := by
  classical
  unfold fiberMaxError
  apply Finset.sup'_le
  intro b _
  exact fiberStateError_le_exp K N g Δmin hdisc hml b

/-- A ceiling horizon based on positive minimum discrimination makes the
maximum error of the likelihood decoder at most the requested positive η. -/
theorem fiber_resolution_horizon {n : ℕ} {Y : Type} [Fintype Y]
    (hn : 2 ≤ n) (K : Fin n → FiniteLaw Y)
    (g : List (Unit × Y) → Fin n) (Δmin η : ℝ)
    (hΔ : 0 < Δmin) (hη : 0 < η)
    (hdisc : ∀ b c, b ≠ c →
      Δmin ≤ discrimination (K b).mass (K c).mass)
    (hml : ∀ h b, fiberLikelihood K b h ≤ fiberLikelihood K (g h) h)
    (N : ℕ)
    (hN : N = ⌈4 * Real.log (((n : ℝ) - 1) / η) / Δmin⌉₊) :
    fiberMaxError hn K N g ≤ η := by
  have hnreal : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hf : 0 < (n : ℝ) - 1 := by linarith
  have hratio : 0 < ((n : ℝ) - 1) / η := div_pos hf hη
  have hceil : 4 * Real.log (((n : ℝ) - 1) / η) / Δmin ≤ (N : ℝ) := by
    simpa [hN] using
      (Nat.le_ceil (4 * Real.log (((n : ℝ) - 1) / η) / Δmin))
  have hlog : Real.log (((n : ℝ) - 1) / η) ≤ (N : ℝ) * Δmin / 4 := by
    rw [div_le_iff₀ hΔ] at hceil
    linarith
  have hexp :
      Real.exp (-((N : ℝ) * Δmin / 4)) ≤ η / ((n : ℝ) - 1) := by
    calc
      Real.exp (-((N : ℝ) * Δmin / 4)) ≤
          Real.exp (-Real.log (((n : ℝ) - 1) / η)) :=
        Real.exp_le_exp.mpr (by linarith)
      _ = η / ((n : ℝ) - 1) := by
        rw [Real.exp_neg, Real.exp_log hratio]
        field_simp [ne_of_gt hf, ne_of_gt hη]
  calc
    fiberMaxError hn K N g ≤
        ((n : ℝ) - 1) * Real.exp (-((N : ℝ) * Δmin / 4)) :=
      fiberMaxError_le_exp hn K N g Δmin hdisc hml
    _ ≤ ((n : ℝ) - 1) * (η / ((n : ℝ) - 1)) :=
      mul_le_mul_of_nonneg_left hexp hf.le
    _ = η := by
      field_simp [ne_of_gt hf]

end

end OperatorKO7.Meta.BoundaryObserver.FiberResolution
