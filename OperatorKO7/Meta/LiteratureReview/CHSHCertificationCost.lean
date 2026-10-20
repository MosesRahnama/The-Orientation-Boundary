import Mathlib
namespace OperatorKO7.Meta.LiteratureReview
/-!
Manuscript label: cor:chsh-certification-cost.
Finite randomized adaptive tests and independent finite records have the stated
lower and upper certification bounds for four binary-pair probability laws.
The lower expectation uses a fair prior on the tested table and the constructed
observer table; a uniform expected-round budget therefore satisfies the bound.
The pole assertion requires a fixed positive entry bound and fixed error below
one half. The lower protocol model uses finite trees and limits of their errors under a
uniform expected cost bound. Arbitrary stopping-time representations are outside
this file; this restriction makes the protocol semantics explicit. The upper
protocol is its independent product record experiment. Random seeds are label
independent.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
namespace CHSHCost

structure Row (n : ℕ) where
  mass : Fin n → ℝ
  nonneg : ∀ i, 0 ≤ mass i
  total : ∑ i, mass i = 1

abbrev Table := Fin 4 → Row 4

def productSign : Fin 4 → ℝ := ![1, -1, -1, 1]
def orientation : Fin 4 → ℝ := ![1, 1, 1, -1]
def corr (d : Table) (s : Fin 4) : ℝ :=
  ∑ i, (d s).mass i * productSign i
def score (e : Fin 4 → ℝ) : ℝ := e 0 + e 1 + e 2 - e 3
def S (d : Table) : ℝ := score (corr d)
def IsSign (x : ℝ) : Prop := x = 1 ∨ x = -1
def vertex (a b : Fin 2 → ℝ) : Fin 4 → ℝ :=
  ![a 0 * b 0, a 0 * b 1, a 1 * b 0, a 1 * b 1]
def HasObserver (d : Table) : Prop :=
  ∃ (n : ℕ) (w : Row n) (a b : Fin 2 → Fin n → ℝ),
    (∀ x i, IsSign (a x i)) ∧ (∀ y i, IsSign (b y i)) ∧
    ∀ s, corr d s =
      ∑ i, w.mass i * vertex (fun x => a x i) (fun y => b y i) s

lemma mass_le_one {n : ℕ} (p : Row n) (i : Fin n) : p.mass i ≤ 1 := by
  calc
    p.mass i ≤ ∑ j, p.mass j :=
      Finset.single_le_sum (fun j _ => p.nonneg j) (Finset.mem_univ i)
    _ = 1 := p.total

lemma productSign_bounds (i : Fin 4) :
    -1 ≤ productSign i ∧ productSign i ≤ 1 := by
  fin_cases i <;> norm_num [productSign]

lemma corr_bounds (d : Table) (s : Fin 4) :
    -1 ≤ corr d s ∧ corr d s ≤ 1 := by
  constructor
  · calc
      -1 = ∑ i, (d s).mass i * (-1) := by
        rw [← Finset.sum_mul, (d s).total]; ring
      _ ≤ corr d s := Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (productSign_bounds i).1 ((d s).nonneg i)
  · calc
      corr d s ≤ ∑ i, (d s).mass i * 1 :=
        Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (productSign_bounds i).2 ((d s).nonneg i)
      _ = 1 := by simpa using (d s).total

lemma observer_score (d : Table) (hd : HasObserver d) : S d ≤ 2 := by
  obtain ⟨n, w, a, b, ha, hb, he⟩ := hd
  have hv (i : Fin n) :
      score (vertex (fun x => a x i) (fun y => b y i)) ≤ 2 := by
    rcases ha 0 i with h0 | h0 <;> rcases ha 1 i with h1 | h1 <;>
      rcases hb 0 i with h2 | h2 <;> rcases hb 1 i with h3 | h3 <;>
      norm_num [score, vertex, h0, h1, h2, h3,
        Matrix.cons_val_two, Matrix.cons_val_three]
  calc
    S d = ∑ i, w.mass i *
        score (vertex (fun x => a x i) (fun y => b y i)) := by
      simp only [S, score, he, Finset.sum_add_distrib,
        Finset.sum_sub_distrib, mul_add, mul_sub]
    _ ≤ ∑ i, w.mass i * 2 :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hv i) (w.nonneg i)
    _ = 2 := by rw [← Finset.sum_mul, w.total]; ring

def mix (d : Table) (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1) : Table :=
  fun s =>
  { mass := fun i => t * (d s).mass i + (1 - t) / 4
    nonneg := fun i => add_nonneg (mul_nonneg ht.1 ((d s).nonneg i))
      (div_nonneg (sub_nonneg.mpr ht.2) (by norm_num))
    total := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
        (d s).total, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      norm_num ; ring }

lemma mix_corr (d : Table) (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1)
    (s : Fin 4) : corr (mix d t ht) s = t * corr d s := by
  norm_num [corr, mix, productSign, Fin.sum_univ_succ] ; ring

lemma mixture_observer (d : Table) (hs : 2 < S d) :
    ∃ r : Table, HasObserver r ∧
      (∀ s i, (r s).mass i =
        (2 / S d) * (d s).mass i + (1 - 2 / S d) / 4) := by
  have hs0 : 0 < S d := by linarith
  have ht : 0 ≤ 2 / S d ∧ 2 / S d ≤ 1 := by
    constructor
    · positivity
    · exact (div_le_iff₀ hs0).mpr (by linarith)
  let r := mix d (2 / S d) ht
  have hrS : S r = 2 := by
    have h : S r = (2 / S d) * S d := by
      simp only [r, S, score, mix_corr]; ring
    rw [h]; field_simp [hs0.ne']
  have hscore :
      corr r 0 + corr r 1 + corr r 2 - corr r 3 = 2 := hrS
  let w : Row 4 :=
    { mass := fun i => (1 - orientation i * corr r i) / 2
      nonneg := by
        intro i
        have h := corr_bounds r i
        fin_cases i <;> norm_num [orientation] at * <;> linarith
      total := by
        rw [Fin.sum_univ_four]
        norm_num [orientation, Matrix.cons_val_two, Matrix.cons_val_three]
        linarith [hscore] }
  let a : Fin 2 → Fin 4 → ℝ := ![![1, 1, 1, 1], ![-1, 1, -1, 1]]
  let b : Fin 2 → Fin 4 → ℝ := ![![-1, 1, 1, 1], ![1, -1, 1, 1]]
  have ha : ∀ (x : Fin 2) (i : Fin 4), IsSign (a x i) := by
    intro x i
    fin_cases x <;> fin_cases i <;> norm_num [a, IsSign]
  have hb : ∀ (y : Fin 2) (i : Fin 4), IsSign (b y i) := by
    intro y i
    fin_cases y <;> fin_cases i <;> norm_num [b, IsSign]
  have he : ∀ s : Fin 4, corr r s =
      ∑ i, w.mass i * vertex (fun x => a x i) (fun y => b y i) s := by
    intro s
    have hs_cases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 := by
      fin_cases s <;> decide
    rcases hs_cases with rfl | rfl | rfl | rfl <;>
      norm_num [w, a, b, vertex, orientation, Fin.sum_univ_four,
        Matrix.cons_val_two, Matrix.cons_val_three] <;>
      linarith [hscore]
  exact ⟨r, ⟨4, w, a, b, ha, hb, he⟩, fun _ _ => rfl⟩

def discrimination {n : ℕ} (p q : Row n) : ℝ :=
  ∑ i, (p.mass i - q.mass i) ^ 2 / (p.mass i + q.mass i)

lemma uniform_deviation (p : Row 4) :
    ∑ i, (p.mass i - 1 / 4) ^ 2 ≤ 1 := by
  have hsq : ∑ i, p.mass i ^ 2 ≤ 1 := by
    calc
      ∑ i, p.mass i ^ 2 ≤ ∑ i, p.mass i :=
        Finset.sum_le_sum fun i _ => by
          nlinarith [mul_nonneg (p.nonneg i)
            (sub_nonneg.mpr (mass_le_one p i))]
      _ = 1 := p.total
  have ht := p.total
  norm_num [Fin.sum_univ_succ] at hsq ht ⊢
  nlinarith

lemma mixture_cap (d r : Table) (m : ℝ) (hm : 0 < m)
    (hentry : ∀ s i, m ≤ (d s).mass i) (hs : 2 < S d)
    (hr : ∀ s i, (r s).mass i =
      (2 / S d) * (d s).mass i + (1 - 2 / S d) / 4) (s : Fin 4) :
    discrimination (d s) (r s) ≤ (S d - 2) ^ 2 / (4 * m) := by
  have hs0 : 0 < S d := by linarith
  let t := 2 / S d
  have ht0 : 0 < t := div_pos (by norm_num) hs0
  have ht1 : t ≤ 1 := (div_le_iff₀ hs0).mpr (by linarith)
  have htm : 0 < t * m := mul_pos ht0 hm
  have hden (i : Fin 4) : t * m ≤ (d s).mass i + (r s).mass i := by
    rw [hr]
    have h := mul_le_mul_of_nonneg_left (hentry s i) ht0.le
    have hn := (d s).nonneg i
    change t * m ≤ (d s).mass i + (t * (d s).mass i + (1 - t) / 4)
    linarith
  have hdiff (i : Fin 4) :
      (d s).mass i - (r s).mass i = (1 - t) * ((d s).mass i - 1 / 4) := by
    rw [hr]; dsimp [t]; ring
  calc
    discrimination (d s) (r s) ≤
        ∑ i, ((1 - t) ^ 2 / (t * m)) * ((d s).mass i - 1 / 4) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      calc
        _ ≤ ((d s).mass i - (r s).mass i) ^ 2 / (t * m) :=
          div_le_div_of_nonneg_left (sq_nonneg _) htm (hden i)
        _ = _ := by rw [hdiff]; ring
    _ = ((1 - t) ^ 2 / (t * m)) *
        (∑ i, ((d s).mass i - 1 / 4) ^ 2) := by rw [Finset.mul_sum]
    _ ≤ ((1 - t) ^ 2 / (t * m)) * 1 :=
      mul_le_mul_of_nonneg_left (uniform_deviation (d s))
        (div_nonneg (sq_nonneg _) htm.le)
    _ = (S d - 2) ^ 2 / (2 * S d * m) := by
      dsimp [t]; field_simp [hs0.ne', hm.ne']; ring
    _ ≤ (S d - 2) ^ 2 / (4 * m) :=
      div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
        (by nlinarith [mul_nonneg hm.le (sub_nonneg.mpr hs.le)])

lemma sqrt_cauchy {n : ℕ} (a b : Fin n → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) :
    ∑ i, Real.sqrt (a i * b i) ≤ Real.sqrt ((∑ i, a i) * ∑ i, b i) := by
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul Finset.univ
    (r := fun i => Real.sqrt (a i * b i))
    (fun i _ => ha i) (fun i _ => hb i)
    (fun i _ => Real.sq_sqrt (mul_nonneg (ha i) (hb i)))
  exact Real.le_sqrt_of_sq_le h

lemma affinity_gap {n : ℕ} (p q : Row n) :
    1 - ∑ i, Real.sqrt (p.mass i * q.mass i) ≤ discrimination p q / 2 := by
  have hterm (i : Fin n) :
      p.mass i + q.mass i - 2 * Real.sqrt (p.mass i * q.mass i) ≤
        (p.mass i - q.mass i) ^ 2 / (p.mass i + q.mass i) := by
    have hp := p.nonneg i
    have hq := q.nonneg i
    have hz := Real.sqrt_nonneg (p.mass i * q.mass i)
    have hs := Real.sq_sqrt (mul_nonneg hp hq)
    by_cases h0 : p.mass i + q.mass i = 0
    · have h1 : p.mass i = 0 := by linarith
      have h2 : q.mass i = 0 := by linarith
      simp [h1, h2]
    · have hd : 0 < p.mass i + q.mass i := lt_of_le_of_ne (add_nonneg hp hq) (Ne.symm h0)
      have ham : 2 * Real.sqrt (p.mass i * q.mass i) ≤ p.mass i + q.mass i := by
        have hp2 := Real.sq_sqrt hp
        have hq2 := Real.sq_sqrt hq
        rw [Real.sqrt_mul hp]
        nlinarith [sq_nonneg (Real.sqrt (p.mass i) - Real.sqrt (q.mass i))]
      apply (le_div_iff₀ hd).mpr
      nlinarith [mul_nonneg hz (sub_nonneg.mpr ham)]
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hterm i)
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, p.total, q.total] at hsum
  dsimp [discrimination]
  linarith

inductive Action where
  | observe (setting : Fin 4)
  | random (law : Row 4)

def Action.law (a : Action) (d : Table) : Row 4 :=
  match a with
  | .observe s => d s
  | .random p => p

def Action.charge : Action → ℝ
  | .observe _ => 1
  | .random _ => 0

inductive Test where
  | stop (answer : Bool)
  | node (action : Action) (next : Fin 4 → Test)

def rounds (d : Table) : Test → ℝ
  | .stop _ => 0
  | .node a f => a.charge + ∑ i, (a.law d).mass i * rounds d (f i)

def error (d r : Table) : Test → ℝ → ℝ → ℝ
  | .stop answer, a, b => if answer then b else a
  | .node action f, a, b =>
      ∑ i, error d r (f i) (a * (action.law d).mass i) (b * (action.law r).mass i)

def overlap (d r : Table) : Test → ℝ → ℝ → ℝ
  | .stop _, a, b => Real.sqrt (a * b)
  | .node action f, a, b =>
      ∑ i, overlap d r (f i) (a * (action.law d).mass i) (b * (action.law r).mass i)

lemma rounds_nonneg (d : Table) (t : Test) : 0 ≤ rounds d t := by
  induction t with
  | stop _ => exact le_rfl
  | node a f ih =>
    have hc : 0 ≤ a.charge := by cases a <;> norm_num [Action.charge]
    exact add_nonneg hc (Finset.sum_nonneg fun i _ =>
      mul_nonneg ((a.law d).nonneg i) (ih i))

lemma error_bounds (d r : Table) (t : Test) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ error d r t a b ∧ error d r t a b ≤ a + b := by
  induction t generalizing a b with
  | stop z =>
    cases z
    · change 0 ≤ a ∧ a ≤ a + b
      exact ⟨ha, le_add_of_nonneg_right hb⟩
    · change 0 ≤ b ∧ b ≤ a + b
      exact ⟨hb, le_add_of_nonneg_left ha⟩
  | node action f ih =>
    have hi (i : Fin 4) := ih i _ _
      (mul_nonneg ha ((action.law d).nonneg i))
      (mul_nonneg hb ((action.law r).nonneg i))
    constructor
    · exact Finset.sum_nonneg fun i _ => (hi i).1
    · calc
        error d r (.node action f) a b ≤
            ∑ i, (a * (action.law d).mass i + b * (action.law r).mass i) :=
          Finset.sum_le_sum fun i _ => (hi i).2
        _ = a + b := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
            (action.law d).total, (action.law r).total]
          ring

lemma error_linear (d r : Table) (t : Test) (a b : ℝ) :
    error d r t a b = a * error d r t 1 0 + b * error d r t 0 1 := by
  induction t generalizing a b with
  | stop z => cases z <;> simp [error]
  | node action f ih =>
    have hp :
        (∑ i, error d r (f i) ((action.law d).mass i) 0) =
        ∑ i, (action.law d).mass i * error d r (f i) 1 0 := by
      apply Finset.sum_congr rfl
      intro i _
      simpa only [zero_mul, add_zero] using ih i ((action.law d).mass i) 0
    have hq :
        (∑ i, error d r (f i) 0 ((action.law r).mass i)) =
        ∑ i, (action.law r).mass i * error d r (f i) 0 1 := by
      apply Finset.sum_congr rfl
      intro i _
      simpa only [zero_mul, zero_add] using ih i 0 ((action.law r).mass i)
    simp only [error, one_mul, zero_mul]
    rw [hp, hq]
    calc
      _ = ∑ i, ((a * (action.law d).mass i) * error d r (f i) 1 0 +
          (b * (action.law r).mass i) * error d r (f i) 0 1) :=
        Finset.sum_congr rfl fun i _ => ih i _ _
      _ = _ := by simp only [Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]

lemma overlap_error (d r : Table) (t : Test) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    overlap d r t a b ≤
      Real.sqrt (error d r t a b * (a + b - error d r t a b)) := by
  induction t generalizing a b with
  | stop z =>
    cases z
    · change Real.sqrt (a * b) ≤ Real.sqrt (a * (a + b - a))
      rw [show a + b - a = b by ring]
    · change Real.sqrt (a * b) ≤ Real.sqrt (b * (a + b - b))
      rw [show a + b - b = a by ring, mul_comm]
  | node action f ih =>
    let aa := fun i => a * (action.law d).mass i
    let bb := fun i => b * (action.law r).mass i
    let ee := fun i => error d r (f i) (aa i) (bb i)
    have he (i : Fin 4) := error_bounds d r (f i) (aa i) (bb i)
      (mul_nonneg ha ((action.law d).nonneg i))
      (mul_nonneg hb ((action.law r).nonneg i))
    have hc := sqrt_cauchy ee (fun i => aa i + bb i - ee i)
      (fun i => (he i).1) (fun i => sub_nonneg.mpr (he i).2)
    have hmass : ∑ i, (aa i + bb i - ee i) = a + b - ∑ i, ee i := by
      dsimp [aa, bb]
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum, (action.law d).total,
        (action.law r).total]
      ring
    rw [hmass] at hc
    exact (Finset.sum_le_sum fun i _ =>
      ih i (aa i) (bb i)
        (mul_nonneg ha ((action.law d).nonneg i))
        (mul_nonneg hb ((action.law r).nonneg i))).trans hc

lemma sqrt_weight (a b p q : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt ((a * p) * (b * q)) = Real.sqrt (a * b) * Real.sqrt (p * q) := by
  rw [show (a * p) * (b * q) = (a * b) * (p * q) by ring,
    Real.sqrt_mul (mul_nonneg ha hb)]

lemma action_gap (d r : Table) (D : ℝ)
    (hcap : ∀ s, discrimination (d s) (r s) ≤ D) (act : Action) :
    1 - ∑ i, Real.sqrt ((act.law d).mass i * (act.law r).mass i) ≤
      D / 2 * act.charge := by
  cases act with
  | observe s => exact (affinity_gap (d s) (r s)).trans (by simpa [Action.charge] using div_le_div_of_nonneg_right (hcap s) (by norm_num : (0 : ℝ) ≤ 2))
  | random p =>
    simp only [Action.law, Action.charge, mul_zero]
    have he : ∑ i, Real.sqrt (p.mass i * p.mass i) = 1 := by
      calc
        _ = ∑ i, p.mass i := Finset.sum_congr rfl fun i _ =>
          Real.sqrt_mul_self (p.nonneg i)
        _ = 1 := p.total
    rw [he, sub_self]

lemma overlap_cost (d r : Table) (D : ℝ) (hD : 0 ≤ D)
    (hcap : ∀ s, discrimination (d s) (r s) ≤ D)
    (t : Test) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a * b) - overlap d r t a b ≤
      D / 4 * (a * rounds d t + b * rounds r t) := by
  induction t generalizing a b with
  | stop z => simp [overlap, rounds]
  | node act f ih =>
    let p := act.law d
    let q := act.law r
    have hc : 0 ≤ act.charge := by cases act <;> norm_num [Action.charge]
    have hg := mul_le_mul_of_nonneg_left (action_gap d r D hcap act)
      (Real.sqrt_nonneg (a * b))
    have ham : 2 * Real.sqrt (a * b) ≤ a + b := by
      rw [Real.sqrt_mul ha]
      nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb,
        sq_nonneg (Real.sqrt a - Real.sqrt b)]
    have hh := mul_le_mul_of_nonneg_right ham
      (mul_nonneg hD hc)
    have hlocal :
        Real.sqrt (a * b) -
          (∑ i, Real.sqrt ((a * p.mass i) * (b * q.mass i))) ≤
        D / 4 * (a + b) * act.charge := by
      simp_rw [sqrt_weight _ _ _ _ ha hb]
      rw [← Finset.mul_sum]
      dsimp [p, q]
      nlinarith
    have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) =>
      ih i (a * p.mass i) (b * q.mass i)
        (mul_nonneg ha (p.nonneg i)) (mul_nonneg hb (q.nonneg i))
    simp only [Finset.sum_sub_distrib] at hsum
    have hcst :
        (∑ i, D / 4 * ((a * p.mass i) * rounds d (f i) +
          (b * q.mass i) * rounds r (f i))) =
        D / 4 * (a * (∑ i, p.mass i * rounds d (f i)) +
          b * (∑ i, q.mass i * rounds r (f i))) := by
      simp_rw [mul_add, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hcst] at hsum
    change Real.sqrt (a * b) -
      (∑ i, overlap d r (f i) (a * p.mass i) (b * q.mass i)) ≤
      D / 4 * (a * (act.charge + ∑ i, p.mass i * rounds d (f i)) +
        b * (act.charge + ∑ i, q.mass i * rounds r (f i)))
    nlinarith

lemma entropy_deficit_sq (η : ℝ) (hη : 0 < η) (hη1 : η < 1) :
    Real.log 2 - Real.binEntropy η ≤ (1 - 2 * η) ^ 2 := by
  have h1 := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (show 0 < 2 * η by positivity)) hη.le
  have h2 := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos
      (mul_pos (by norm_num : (0 : ℝ) < 2) (sub_pos.mpr hη1)))
    (sub_nonneg.mpr hη1.le)
  rw [Real.log_mul (by norm_num) hη.ne'] at h1
  rw [Real.log_mul (by norm_num) (sub_pos.mpr hη1).ne'] at h2
  simp only [Real.binEntropy, Real.log_inv]
  nlinarith

lemma finite_test_lower (d r : Table) (D η : ℝ)
    (hD : 0 < D) (hη : 0 < η) (hηh : η ≤ 1 / 2)
    (hcap : ∀ s, discrimination (d s) (r s) ≤ D)
    (t : Test) (he0 : error d r t 1 0 ≤ η)
    (he1 : error d r t 0 1 ≤ η) :
    (Real.log 2 - Real.binEntropy η) / D ≤
      (rounds d t + rounds r t) / 2 := by
  let e := error d r t (1 / 2) (1 / 2)
  have he := error_bounds d r t (1 / 2) (1 / 2) (by norm_num) (by norm_num)
  have heη : e ≤ η := by
    dsimp [e]
    rw [error_linear]
    linarith
  have he0' : 0 ≤ e := he.1
  have hehalf : e ≤ 1 / 2 := heη.trans hηh
  have hprob : 0 ≤ e * (1 - e) := mul_nonneg he0' (by linarith)
  have hs := Real.sq_sqrt hprob
  have hn := Real.sqrt_nonneg (e * (1 - e))
  have hsmall : Real.sqrt (e * (1 - e)) ≤ 1 / 2 := by
    nlinarith [sq_nonneg (e - 1 / 2)]
  have ho := overlap_error d r t (1 / 2) (1 / 2) (by norm_num) (by norm_num)
  have hc := overlap_cost d r D hD.le hcap t (1 / 2) (1 / 2)
    (by norm_num) (by norm_num)
  norm_num at ho hc
  change overlap d r t (1 / 2) (1 / 2) ≤ Real.sqrt (e * (1 - e)) at ho
  have hsquare : (1 - 2 * e) ^ 2 ≤ 2 - 4 * Real.sqrt (e * (1 - e)) := by
    nlinarith [sq_nonneg (2 * Real.sqrt (e * (1 - e)) - 1)]
  have hcompare : (1 - 2 * η) ^ 2 ≤ (1 - 2 * e) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr heη)
      (show 0 ≤ 1 - η - e by linarith)]
  have hent := entropy_deficit_sq η hη (by linarith)
  apply (div_le_iff₀ hD).mpr
  nlinarith

end CHSHCost
namespace CHSHCost

def entropyBits (η : ℝ) : ℝ := Real.binEntropy η / Real.log 2
def lowerBound (d : Table) (m η : ℝ) : ℝ :=
  4 * m * (1 - entropyBits η) * Real.log 2 / (S d - 2) ^ 2
def samplesPerSetting (d : Table) (η : ℝ) : ℕ :=
  ⌈162 * Real.log (8 / η) / (S d - 2) ^ 2⌉₊

lemma entropy_units (η : ℝ) :
    (1 - entropyBits η) * Real.log 2 = Real.log 2 - Real.binEntropy η := by
  have h : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  dsimp [entropyBits]
  field_simp [h]

lemma limit_test_lower (d r : Table) (D η : ℝ)
    (hD : 0 < D) (hη : 0 < η) (hηh : η ≤ 1 / 2)
    (hcap : ∀ s, discrimination (d s) (r s) ≤ D)
    (t : ℕ → Test) (e0 e1 C : ℝ)
    (h0 : Filter.Tendsto (fun n => error d r (t n) 1 0)
      Filter.atTop (nhds e0))
    (h1 : Filter.Tendsto (fun n => error d r (t n) 0 1)
      Filter.atTop (nhds e1))
    (he0 : e0 ≤ η) (he1 : e1 ≤ η)
    (hC : ∀ n, (rounds d (t n) + rounds r (t n)) / 2 ≤ C) :
    (Real.log 2 - Real.binEntropy η) / D ≤ C := by
  rcases lt_or_eq_of_le hηh with hhalf | hhalf
  · let u := fun n => max η (max (error d r (t n) 1 0) (error d r (t n) 0 1))
    have hu : Filter.Tendsto u Filter.atTop (nhds η) := by
      have h := Filter.Tendsto.max
        (_root_.tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => η)
          Filter.atTop (nhds η)) (h0.max h1)
      simpa only [max_eq_left (max_le he0 he1)] using h
    have huhalf : ∀ᶠ n in Filter.atTop, u n < 1 / 2 :=
      hu.eventually (isOpen_Iio.mem_nhds hhalf)
    have hb : Filter.Tendsto Real.binEntropy (nhds η)
        (nhds (Real.binEntropy η)) := Real.binEntropy_continuous.continuousAt
    have hconst :
        Filter.Tendsto (fun _ : ℕ => Real.log 2) Filter.atTop
          (nhds (Real.log 2)) :=
      _root_.tendsto_const_nhds
    have hlim : Filter.Tendsto
        (fun n => (Real.log 2 - Real.binEntropy (u n)) / D)
        Filter.atTop (nhds ((Real.log 2 - Real.binEntropy η) / D)) :=
      (hconst.sub (hb.comp hu)).div_const D
    apply le_of_tendsto hlim
    filter_upwards [huhalf] with n hn
    have hu0 : 0 < u n := hη.trans_le (le_max_left _ _)
    have ha : error d r (t n) 1 0 ≤ u n :=
      (le_max_left _ _).trans (le_max_right _ _)
    have hb : error d r (t n) 0 1 ≤ u n :=
      (le_max_right _ _).trans (le_max_right _ _)
    exact (finite_test_lower d r D (u n) hD hu0 hn.le hcap (t n) ha hb).trans (hC n)
  · have hb : Real.binEntropy (1 / 2 : ℝ) = Real.log 2 := by
      convert Real.binEntropy_two_inv using 1 ; norm_num
    rw [hhalf, hb, sub_self, zero_div]
    exact (div_nonneg (add_nonneg (rounds_nonneg d (t 0))
      (rounds_nonneg r (t 0))) (by norm_num)).trans (hC 0)

def fairRow : Row 4 :=
  { mass := ![1 / 2, 1 / 2, 0, 0]
    nonneg := by intro i; fin_cases i <;> norm_num
    total := by norm_num [Fin.sum_univ_succ] }

def fairGuess : Test :=
  .node (.random fairRow) (fun i => .stop (decide (i = 0)))

lemma fair_guess_counterexample (d r : Table) :
    rounds d fairGuess = 0 ∧
    error d r fairGuess 1 0 = 1 / 2 ∧
    error d r fairGuess 0 1 = 1 / 2 := by
  norm_num [fairGuess, fairRow, rounds, error, Action.law, Action.charge,
    Fin.sum_univ_succ]

lemma lower_coefficient_pos (m η : ℝ) (hm : 0 < m) (hη : η < 1 / 2) :
    0 < 4 * m * (1 - entropyBits η) * Real.log 2 := by
  have he : Real.binEntropy η < Real.log 2 :=
    Real.binEntropy_lt_log_two.mpr (by
      intro h
      rw [h] at hη
      norm_num at hη)
  rw [mul_assoc (4 * m), entropy_units]
  exact mul_pos (mul_pos (by norm_num) hm) (sub_pos.mpr he)

local instance outcomeMeasurableSpace : MeasurableSpace (Fin 4) := ⊤
local instance outcomeMeasurableSingleton : MeasurableSingletonClass (Fin 4) :=
  ⟨fun _ => trivial⟩

def rowPMF (p : Row 4) : PMF (Fin 4) :=
  PMF.ofFintype (fun i => ENNReal.ofReal (p.mass i)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => p.nonneg i), p.total]
    simp)

def rowMeasure (p : Row 4) : Measure (Fin 4) := (rowPMF p).toMeasure
instance rowMeasure_probability (p : Row 4) : IsProbabilityMeasure (rowMeasure p) := by
  dsimp [rowMeasure]
  infer_instance

abbrev Record (N : ℕ) := (Fin 4 × Fin N) → Fin 4
def recordLaw (d : Table) (N : ℕ) : Measure (Record N) :=
  Measure.pi (fun j : Fin 4 × Fin N => rowMeasure (d j.1))
instance recordLaw_probability (d : Table) (N : ℕ) :
    IsProbabilityMeasure (recordLaw d N) := by
  dsimp [recordLaw]
  infer_instance

def sample (N : ℕ) (s : Fin 4) (i : Fin N) (ω : Record N) : ℝ :=
  productSign (ω (s, i))
def estimate (N : ℕ) (ω : Record N) (s : Fin 4) : ℝ :=
  (∑ i, sample N s i ω) / N
def excessEvent (N : ℕ) (ε : ℝ) : Set (Record N) :=
  {ω | 2 + 4 * ε < score (estimate N ω)}

lemma productSign_measurable : Measurable productSign := by
  intro s hs
  trivial

lemma sample_measurable (N : ℕ) (s : Fin 4) (i : Fin N) :
    Measurable (sample N s i) :=
  productSign_measurable.comp (measurable_pi_apply (s, i))

lemma row_mean (d : Table) (s : Fin 4) :
    ∫ i, productSign i ∂rowMeasure (d s) = corr d s := by
  rw [rowMeasure, PMF.integral_eq_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [rowPMF, PMF.ofFintype_apply, ENNReal.toReal_ofReal ((d s).nonneg i)]
  rfl

lemma sample_mean (d : Table) (N : ℕ) (s : Fin 4) (i : Fin N) :
    ∫ ω, sample N s i ω ∂recordLaw d N = corr d s := by
  change (∫ ω : Record N, productSign (ω (s, i)) ∂
    Measure.pi (fun j : Fin 4 × Fin N => rowMeasure (d j.1))) = corr d s
  rw [MeasureTheory.integral_comp_eval
    (ι := Fin 4 × Fin N)
    (X := fun _ : Fin 4 × Fin N => Fin 4)
    (μ := fun j : Fin 4 × Fin N => rowMeasure (d j.1))
    (i := (s, i))
    (f := productSign)
    productSign_measurable.aestronglyMeasurable]
  exact row_mean d s

lemma sample_independent (d : Table) (N : ℕ) (s : Fin 4) :
    iIndepFun (sample N s) (recordLaw d N) := by
  have h := iIndepFun_pi
    (μ := fun j : Fin 4 × Fin N => rowMeasure (d j.1))
    (X := fun _ : Fin 4 × Fin N => productSign)
    (fun _ => productSign_measurable.aemeasurable)
  exact h.precomp (g := fun i : Fin N => (s, i))
    (by intro i j hij; exact (Prod.mk.inj hij).2)

lemma row_hoeffding (d : Table) (N : ℕ) (hN : 0 < N)
    (s : Fin 4) (ε : ℝ) (hε : 0 ≤ ε) :
    (recordLaw d N).real {ω | ε < |estimate N ω s - corr d s|} ≤
      2 * Real.exp (-(N : ℝ) * ε ^ 2 / 2) := by
  let μ := recordLaw d N
  let Y := fun i : Fin N => fun ω : Record N => sample N s i ω - corr d s
  have hn : 0 < (N : ℝ) := by exact_mod_cast hN
  have hind : iIndepFun Y μ := by
    simpa only [Y, Function.comp_def] using
      (sample_independent d N s).comp
        (fun _ => fun x : ℝ => x - corr d s) (fun _ => by fun_prop)
  have hsub (i : Fin N) : HasSubgaussianMGF (Y i) 1 μ := by
    have hb : ∀ᵐ ω ∂μ, sample N s i ω ∈ Set.Icc (-1) 1 :=
      ae_of_all _ (fun ω => productSign_bounds (ω (s, i)))
    have h := hasSubgaussianMGF_of_mem_Icc
      (sample_measurable N s i).aemeasurable hb
    have hc : ((‖(1 : ℝ) - (-1)‖₊ / 2) ^ 2 : ℝ≥0) = 1 := by norm_num
    rw [hc] at h
    simpa only [Y, μ, sample_mean] using h
  have hplus := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
    (c := fun _ : Fin N => (1 : ℝ≥0)) (s := Finset.univ) hind
    (fun i _ => hsub i) (mul_nonneg hn.le hε)
  have hnegind : iIndepFun (fun i => -Y i) μ := by
    simpa only [Function.comp_def] using hind.comp
      (fun _ => fun x : ℝ => -x) (fun _ => measurable_neg)
  have hminus := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
    (c := fun _ : Fin N => (1 : ℝ≥0)) (s := Finset.univ) hnegind
    (fun i _ => (hsub i).neg) (mul_nonneg hn.le hε)
  have hexp :
      -((N : ℝ) * ε) ^ 2 / (2 * (N : ℝ)) = -(N : ℝ) * ε ^ 2 / 2 := by
    field_simp [hn.ne'] ; ring
  have hp : μ.real {ω | (N : ℝ) * ε ≤ ∑ i, Y i ω} ≤
      Real.exp (-(N : ℝ) * ε ^ 2 / 2) := by
    simpa [hexp] using hplus
  have hm : μ.real {ω | (N : ℝ) * ε ≤ ∑ i, -Y i ω} ≤
      Real.exp (-(N : ℝ) * ε ^ 2 / 2) := by
    simpa [hexp] using hminus
  have hsum (ω : Record N) :
      ∑ i, Y i ω = (N : ℝ) * (estimate N ω s - corr d s) := by
    dsimp [Y, estimate]
    simp only [Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp [hn.ne']
  have hcover :
      {ω : Record N | ε < |estimate N ω s - corr d s|} ⊆
      {ω | (N : ℝ) * ε ≤ ∑ i, Y i ω} ∪
      {ω | (N : ℝ) * ε ≤ ∑ i, -Y i ω} := by
    intro ω hω
    change ε < |estimate N ω s - corr d s| at hω
    by_cases hz : 0 ≤ estimate N ω s - corr d s
    · left
      change (N : ℝ) * ε ≤ ∑ i, Y i ω
      rw [hsum]
      rw [abs_of_nonneg hz] at hω
      exact mul_le_mul_of_nonneg_left hω.le hn.le
    · right
      change (N : ℝ) * ε ≤ ∑ i, -Y i ω
      rw [Finset.sum_neg_distrib, hsum]
      rw [abs_of_neg (lt_of_not_ge hz)] at hω
      have h := mul_le_mul_of_nonneg_left hω.le hn.le
      nlinarith
  calc
    _ ≤ μ.real ({ω | (N : ℝ) * ε ≤ ∑ i, Y i ω} ∪
        {ω | (N : ℝ) * ε ≤ ∑ i, -Y i ω}) := measureReal_mono hcover
    _ ≤ μ.real {ω | (N : ℝ) * ε ≤ ∑ i, Y i ω} +
        μ.real {ω | (N : ℝ) * ε ≤ ∑ i, -Y i ω} := measureReal_union_le _ _
    _ ≤ _ := by linarith

lemma four_row_hoeffding (d : Table) (N : ℕ) (hN : 0 < N)
    (ε : ℝ) (hε : 0 ≤ ε) :
    (recordLaw d N).real
      (⋃ s : Fin 4, {ω | ε < |estimate N ω s - corr d s|}) ≤
      8 * Real.exp (-(N : ℝ) * ε ^ 2 / 2) := by
  calc
    _ ≤ ∑ s : Fin 4, (recordLaw d N).real
        {ω | ε < |estimate N ω s - corr d s|} :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _s : Fin 4, 2 * Real.exp (-(N : ℝ) * ε ^ 2 / 2) :=
      Finset.sum_le_sum fun s _ => row_hoeffding d N hN s ε hε
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

lemma score_error (e f : Fin 4 → ℝ) (ε : ℝ)
    (h : ∀ s, |f s - e s| ≤ ε) :
    |score f - score e| ≤ 4 * ε := by
  have h0 := abs_le.mp (h 0)
  have h1 := abs_le.mp (h 1)
  have h2 := abs_le.mp (h 2)
  have h3 := abs_le.mp (h 3)
  apply abs_le.mpr
  dsimp [score]
  constructor <;> linarith

lemma horizon_tail (d : Table) (η : ℝ)
    (hs : 2 < S d) (hη : 0 < η) (hηh : η ≤ 1 / 2) :
    0 < samplesPerSetting d η ∧
    8 * Real.exp (-(samplesPerSetting d η : ℝ) * ((S d - 2) / 9) ^ 2 / 2) ≤ η := by
  have hgap : 0 < S d - 2 := sub_pos.mpr hs
  have hlog : 0 < Real.log (8 / η) :=
    Real.log_pos ((lt_div_iff₀ hη).mpr (by linarith))
  have hceil : 162 * Real.log (8 / η) / (S d - 2) ^ 2 ≤
      (samplesPerSetting d η : ℝ) := Nat.le_ceil _
  have hn : 0 < samplesPerSetting d η := by
    by_contra hn
    have hz := Nat.eq_zero_of_not_pos hn
    rw [hz, Nat.cast_zero] at hceil
    have hx : 0 < 162 * Real.log (8 / η) / (S d - 2) ^ 2 := by positivity
    linarith
  constructor
  · exact hn
  have hscaled := (div_le_iff₀ (sq_pos_of_pos hgap)).mp hceil
  have hexp : -(samplesPerSetting d η : ℝ) * ((S d - 2) / 9) ^ 2 / 2 ≤
      -Real.log (8 / η) := by nlinarith
  calc
    _ ≤ 8 * Real.exp (-Real.log (8 / η)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by norm_num)
    _ = η := by
      rw [Real.exp_neg, Real.exp_log (div_pos (by norm_num) hη)]
      field_simp [hη.ne']

lemma quadratic_coefficients (m η : ℝ) (hm : 0 < m)
    (hη : 0 < η) (hhalf : η < 1 / 2) :
    0 < 4 * m * (1 - entropyBits η) * Real.log 2 ∧
    0 < 648 * Real.log (8 / η) + 16 ∧
    ∀ d : Table, 2 < S d →
      (4 * (samplesPerSetting d η : ℝ)) ≤
        (648 * Real.log (8 / η) + 16) / (S d - 2) ^ 2 := by
  have hl : 0 < Real.log (8 / η) :=
    Real.log_pos ((lt_div_iff₀ hη).mpr (by linarith))
  constructor
  · exact lower_coefficient_pos m η hm hhalf
  constructor
  · positivity
  intro d hs
  have hS : S d ≤ 4 := by
    have h0 := (corr_bounds d 0).2
    have h1 := (corr_bounds d 1).2
    have h2 := (corr_bounds d 2).2
    have h3 := (corr_bounds d 3).1
    dsimp [S, score]
    linarith
  have hg : 0 < S d - 2 := sub_pos.mpr hs
  have hsq : (S d - 2) ^ 2 ≤ 4 := by
    nlinarith [mul_nonneg (show 0 ≤ S d by linarith) (sub_nonneg.mpr hS)]
  have hx : 0 ≤ 162 * Real.log (8 / η) / (S d - 2) ^ 2 := by positivity
  have hn : (samplesPerSetting d η : ℝ) ≤
      162 * Real.log (8 / η) / (S d - 2) ^ 2 + 1 :=
    (Nat.ceil_lt_add_one hx).le
  calc
    _ ≤ 4 * (162 * Real.log (8 / η) / (S d - 2) ^ 2 + 1) :=
      mul_le_mul_of_nonneg_left hn (by norm_num)
    _ = (648 * Real.log (8 / η) + 4 * (S d - 2) ^ 2) /
        (S d - 2) ^ 2 := by field_simp [hg.ne'] ; ring
    _ ≤ _ := div_le_div_of_nonneg_right (by linarith [hsq]) (sq_nonneg _)

lemma sampling_upper (d : Table) (η : ℝ)
    (hs : 2 < S d) (hη : 0 < η) (hηh : η ≤ 1 / 2) :
    let N := samplesPerSetting d η
    let ε := (S d - 2) / 9
    (recordLaw d N).real (excessEvent N ε)ᶜ ≤ η ∧
    ∀ r : Table, HasObserver r →
      (recordLaw r N).real (excessEvent N ε) ≤ η := by
  let N := samplesPerSetting d η
  let ε := (S d - 2) / 9
  have hn := (horizon_tail d η hs hη hηh).1
  have ht := (horizon_tail d η hs hη hηh).2
  have hε : 0 ≤ ε := by dsimp [ε]; linarith
  constructor
  · have hsub : (excessEvent N ε)ᶜ ⊆
        ⋃ s : Fin 4, {ω | ε < |estimate N ω s - corr d s|} := by
      intro ω hω
      by_contra hb
      have hg (s : Fin 4) : |estimate N ω s - corr d s| ≤ ε := by
        apply le_of_not_gt
        intro h
        exact hb (Set.mem_iUnion.mpr ⟨s, h⟩)
      have he := (abs_le.mp (score_error (corr d) (estimate N ω) ε hg)).1
      have hexc : 2 + 4 * ε < score (estimate N ω) := by
        change -(4 * ε) ≤ score (estimate N ω) - S d at he
        dsimp [ε] at *
        linarith
      exact hω hexc
    exact (measureReal_mono hsub).trans
      ((four_row_hoeffding d N hn ε hε).trans ht)
  · intro r hr
    have hsub : excessEvent N ε ⊆
        ⋃ s : Fin 4, {ω | ε < |estimate N ω s - corr r s|} := by
      intro ω hω
      by_contra hb
      have hg (s : Fin 4) : |estimate N ω s - corr r s| ≤ ε := by
        apply le_of_not_gt
        intro h
        exact hb (Set.mem_iUnion.mpr ⟨s, h⟩)
      have he := (abs_le.mp (score_error (corr r) (estimate N ω) ε hg)).2
      have hl := observer_score r hr
      change score (estimate N ω) - S r ≤ 4 * ε at he
      change 2 + 4 * ε < score (estimate N ω) at hω
      linarith
    exact (measureReal_mono hsub).trans
      ((four_row_hoeffding r N hn ε hε).trans ht)

end CHSHCost

/-- cor:chsh-certification-cost, with fair-prior expected rounds and explicit limit semantics. -/
theorem chsh_certification_cost
    (d : CHSHCost.Table) (m η : ℝ) (hm : 0 < m)
    (hentry : ∀ s i, m ≤ (d s).mass i)
    (hs : 2 < CHSHCost.S d) (hη : 0 < η) (hηh : η ≤ 1 / 2) :
    (∃ r : CHSHCost.Table, CHSHCost.HasObserver r ∧
      ∀ (t : ℕ → CHSHCost.Test) (e0 e1 C : ℝ),
        Filter.Tendsto (fun n => CHSHCost.error d r (t n) 1 0)
          Filter.atTop (nhds e0) →
        Filter.Tendsto (fun n => CHSHCost.error d r (t n) 0 1)
          Filter.atTop (nhds e1) →
        e0 ≤ η → e1 ≤ η →
        (∀ n, (CHSHCost.rounds d (t n) + CHSHCost.rounds r (t n)) / 2 ≤ C) →
        CHSHCost.lowerBound d m η ≤ C) ∧
    (let N := CHSHCost.samplesPerSetting d η
     let ε := (CHSHCost.S d - 2) / 9
     0 < N ∧ Fintype.card (Fin 4 × Fin N) = 4 * N ∧
       (CHSHCost.recordLaw d N).real (CHSHCost.excessEvent N ε)ᶜ ≤ η ∧
       ∀ r : CHSHCost.Table, CHSHCost.HasObserver r →
         (CHSHCost.recordLaw r N).real (CHSHCost.excessEvent N ε) ≤ η) := by
  constructor
  · obtain ⟨r, hr, hmix⟩ := CHSHCost.mixture_observer d hs
    apply Exists.intro r
    constructor
    · exact hr
    intro t e0 e1 C h0 h1 he0 he1 hC
    let D := (CHSHCost.S d - 2) ^ 2 / (4 * m)
    have hD : 0 < D := div_pos (sq_pos_of_pos (sub_pos.mpr hs)) (by positivity)
    have hc (s : Fin 4) : CHSHCost.discrimination (d s) (r s) ≤ D :=
      CHSHCost.mixture_cap d r m hm hentry hs hmix s
    have h := CHSHCost.limit_test_lower d r D η hD hη hηh hc t e0 e1 C
      h0 h1 he0 he1 hC
    have hid : CHSHCost.lowerBound d m η =
        (Real.log 2 - Real.binEntropy η) / D := by
      dsimp [CHSHCost.lowerBound, D]
      rw [mul_assoc (4 * m), CHSHCost.entropy_units]
      field_simp [hm.ne', (sub_pos.mpr hs).ne'] ; ring
    rw [hid]
    exact h
  · constructor
    · exact (CHSHCost.horizon_tail d η hs hη hηh).1
    constructor
    · simp
    exact CHSHCost.sampling_upper d η hs hη hηh

#print axioms chsh_certification_cost
#print axioms CHSHCost.fair_guess_counterexample
end
end OperatorKO7.Meta.LiteratureReview
