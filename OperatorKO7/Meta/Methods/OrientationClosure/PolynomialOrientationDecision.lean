import OperatorKO7.Meta.Methods.OrientationClosure.InterpretationLaws
import OperatorKO7.Meta.Methods.OrientationClosure.PolynomialRegion
import OperatorKO7.Meta.Methods.OrientationClosure.SignatureGeneric
import Mathlib.Tactic

/-!
# Polynomial orientation decision for the free recursor

A constructor-local natural-coefficient polynomial interpretation of the free schema sends
`zero` to `z`, `succ n` to `β * n + a`, `wrap s y` to `W(s, y)` and `recur b s n` to
`R(b, s, n)`, where `W` and `R` are lists of monomials with natural coefficients. A rule is
oriented when it strictly decreases for every natural valuation of its variables.

For every successor slope `β ≥ 1`:

* a monomial of `W` with `y`-degree at least two excludes orientation of the successor rule
  (`ySquare_excludes`);
* a `y`-coefficient `wLin W s` of at least `β ^ d + 1`, with `d` the largest counter degree of
  `R`, excludes it (`leading_excludes`); a monomial `c * s ^ j * y` with `j ≥ 1` reaches that
  value at `s = β ^ d + 1` (`yPayload_excludes`);
* for a wrapper `w * y + C(s)` with `w ≤ 1`, and for `w ≥ 2` when every counter degree `k` of
  `R` satisfies `1 ≤ k` and `w ≤ β ^ k`, orientation is equivalent to a comparison of two
  univariate natural-coefficient polynomials in the payload (`orientsSucc_iff_wZero`,
  `orientsSucc_iff_wOne`, `orientsSucc_iff_high`);
* `ltAllB P Q` decides `∀ x, P x < Q x` by checking `x ≤ P 1 + Q 1 + 1` (`ltAllB_iff`).

`decideSuccAff` returns `some v` with `v` correct (`decideSuccAff_spec`) and an explicit failing
triple when `v = false` (`failSuccAff_spec`), or `none` exactly on the class of
`decideSuccAff_eq_none_iff`. For the unit successor `β = 1` the value is never `none`
(`decideSuccAff_unit_ne_none`), so orientation of both root rules is decided with soundness,
completeness and failing witnesses (`decideRootUnit_iff`). The class left undecided for
`β ≥ 2` contains orienting and non-orienting members (`residual_orienting_member`,
`residual_nonorienting_member`); no undecidability is claimed for it.
-/

set_option autoImplicit false

namespace OperatorKO7.Methods.OrientationClosure.PolynomialOrientationDecision

open OperatorKO7.Methods.OrientationClosure.InterpretationLaws

universe u

/-! ## Monomial lists and evaluation -/

/-- A univariate monomial `coeff * x ^ deg`. -/
structure UMono where
  coeff : Nat
  deg : Nat

/-- A wrapper monomial `coeff * s ^ sDeg * y ^ yDeg`. -/
structure WMono where
  coeff : Nat
  sDeg : Nat
  yDeg : Nat

/-- A recursor monomial `coeff * b ^ bDeg * s ^ sDeg * n ^ nDeg`. -/
structure RMono where
  coeff : Nat
  bDeg : Nat
  sDeg : Nat
  nDeg : Nat

/-- Value of a univariate monomial list. -/
def uEval : List UMono → Nat → Nat
  | [], _ => 0
  | m :: p, x => m.coeff * x ^ m.deg + uEval p x

/-- Value of a wrapper monomial list. -/
def wEval : List WMono → Nat → Nat → Nat
  | [], _, _ => 0
  | m :: p, s, y => m.coeff * s ^ m.sDeg * y ^ m.yDeg + wEval p s y

/-- Value of a recursor monomial list. -/
def rEval : List RMono → Nat → Nat → Nat → Nat
  | [], _, _, _ => 0
  | m :: p, b, s, n => m.coeff * b ^ m.bDeg * s ^ m.sDeg * n ^ m.nDeg + rEval p b s n

theorem uEval_append (p q : List UMono) (x : Nat) :
    uEval (p ++ q) x = uEval p x + uEval q x := by
  induction p with
  | nil => simp [uEval]
  | cons m p ih =>
    simp only [List.cons_append, uEval, ih]
    ring

/-- `R` as a polynomial in the payload at fixed base `b` and counter `n`. -/
def rAtBN : List RMono → Nat → Nat → List UMono
  | [], _, _ => []
  | m :: R, b, n => ⟨m.coeff * b ^ m.bDeg * n ^ m.nDeg, m.sDeg⟩ :: rAtBN R b n

/-- `R` as a polynomial in the base at fixed payload `s` and counter `n`. -/
def rAtSN : List RMono → Nat → Nat → List UMono
  | [], _, _ => []
  | m :: R, s, n => ⟨m.coeff * s ^ m.sDeg * n ^ m.nDeg, m.bDeg⟩ :: rAtSN R s n

/-- `W` as a polynomial in the payload at `y = 0`. -/
def wAtY0 : List WMono → List UMono
  | [] => []
  | m :: W => ⟨m.coeff * 0 ^ m.yDeg, m.sDeg⟩ :: wAtY0 W

theorem uEval_rAtBN (R : List RMono) (b n s : Nat) :
    uEval (rAtBN R b n) s = rEval R b s n := by
  induction R with
  | nil => simp [rAtBN, uEval, rEval]
  | cons m R ih =>
    simp only [rAtBN, uEval, rEval, ih]
    ring

theorem uEval_rAtSN (R : List RMono) (s n b : Nat) :
    uEval (rAtSN R s n) b = rEval R b s n := by
  induction R with
  | nil => simp [rAtSN, uEval, rEval]
  | cons m R ih =>
    simp only [rAtSN, uEval, rEval, ih]
    ring

theorem uEval_wAtY0 (W : List WMono) (s : Nat) : uEval (wAtY0 W) s = wEval W s 0 := by
  induction W with
  | nil => simp [wAtY0, uEval, wEval]
  | cons m W ih =>
    simp only [wAtY0, uEval, wEval, ih]
    ring

/-! ## Coefficient data -/

/-- Coefficient of `y` at payload `s`: the sum of `coeff * s ^ sDeg` over `y`-linear
monomials. -/
def wLin : List WMono → Nat → Nat
  | [], _ => 0
  | m :: W, s => (if m.yDeg = 1 then m.coeff * s ^ m.sDeg else 0) + wLin W s

/-- Largest counter degree among the monomials of `R` with positive coefficient. -/
def nDegMax : List RMono → Nat
  | [] => 0
  | m :: R => if 0 < m.coeff then max m.nDeg (nDegMax R) else nDegMax R

/-- `W` has a monomial with positive coefficient and `y`-degree at least two. -/
def HasYSquare (W : List WMono) : Prop := ∃ m ∈ W, 0 < m.coeff ∧ 2 ≤ m.yDeg

/-- `W` has a monomial `c * s ^ j * y` with `c ≥ 1` and `j ≥ 1`. -/
def HasYPayload (W : List WMono) : Prop := ∃ m ∈ W, 0 < m.coeff ∧ m.yDeg = 1 ∧ 1 ≤ m.sDeg

/-- Every monomial of `R` with positive coefficient has counter degree `k` with `1 ≤ k` and
`w ≤ β ^ k`. -/
def AllHigh (R : List RMono) (β w : Nat) : Prop :=
  ∀ m ∈ R, 0 < m.coeff → 1 ≤ m.nDeg ∧ w ≤ β ^ m.nDeg

instance decHasYSquare (W : List WMono) : Decidable (HasYSquare W) :=
  inferInstanceAs (Decidable (∃ m ∈ W, 0 < m.coeff ∧ 2 ≤ m.yDeg))

instance decHasYPayload (W : List WMono) : Decidable (HasYPayload W) :=
  inferInstanceAs (Decidable (∃ m ∈ W, 0 < m.coeff ∧ m.yDeg = 1 ∧ 1 ≤ m.sDeg))

instance decAllHigh (R : List RMono) (β w : Nat) : Decidable (AllHigh R β w) :=
  inferInstanceAs (Decidable (∀ m ∈ R, 0 < m.coeff → 1 ≤ m.nDeg ∧ w ≤ β ^ m.nDeg))

theorem wEval_ge_mem (W : List WMono) {m : WMono} (hm : m ∈ W) (s y : Nat) :
    m.coeff * s ^ m.sDeg * y ^ m.yDeg ≤ wEval W s y := by
  induction W with
  | nil => simp at hm
  | cons m' W ih =>
    simp only [wEval]
    rcases List.mem_cons.1 hm with h | h
    · subst h
      exact Nat.le_add_right _ _
    · exact le_trans (ih h) (Nat.le_add_left _ _)

theorem rEval_ge_mem (R : List RMono) {m : RMono} (hm : m ∈ R) (b s n : Nat) :
    m.coeff * b ^ m.bDeg * s ^ m.sDeg * n ^ m.nDeg ≤ rEval R b s n := by
  induction R with
  | nil => simp at hm
  | cons m' R ih =>
    simp only [rEval]
    rcases List.mem_cons.1 hm with h | h
    · subst h
      exact Nat.le_add_right _ _
    · exact le_trans (ih h) (Nat.le_add_left _ _)

theorem wEval_ge_wLin_mul (W : List WMono) (s y : Nat) : wLin W s * y ≤ wEval W s y := by
  induction W with
  | nil => simp [wLin, wEval]
  | cons m W ih =>
    simp only [wLin, wEval, add_mul]
    refine Nat.add_le_add ?_ ih
    split_ifs with h
    · rw [h, pow_one]
    · simp

theorem wLin_ge_mem (W : List WMono) {m : WMono} (hm : m ∈ W) (hy : m.yDeg = 1) (s : Nat) :
    m.coeff * s ^ m.sDeg ≤ wLin W s := by
  induction W with
  | nil => simp at hm
  | cons m' W ih =>
    simp only [wLin]
    rcases List.mem_cons.1 hm with h | h
    · subst h
      rw [if_pos hy]
      exact Nat.le_add_right _ _
    · exact le_trans (ih h) (Nat.le_add_left _ _)

theorem nDeg_le_nDegMax (R : List RMono) {m : RMono} (hm : m ∈ R) (hc : 0 < m.coeff) :
    m.nDeg ≤ nDegMax R := by
  induction R with
  | nil => simp at hm
  | cons m' R ih =>
    rcases List.mem_cons.1 hm with h | h
    · subst h
      simp only [nDegMax, if_pos hc]
      exact le_max_left _ _
    · have hle := ih h
      simp only [nDegMax]
      split_ifs
      · exact le_trans hle (le_max_right _ _)
      · exact hle

theorem nDegMax_tail_le (m : RMono) (R : List RMono) : nDegMax R ≤ nDegMax (m :: R) := by
  simp only [nDegMax]
  split_ifs
  · exact le_max_right _ _
  · exact le_refl _

theorem exists_growing_of_nDegMax (R : List RMono) (h : 1 ≤ nDegMax R) :
    ∃ m ∈ R, 0 < m.coeff ∧ 1 ≤ m.nDeg := by
  induction R with
  | nil => simp [nDegMax] at h
  | cons m R ih =>
    simp only [nDegMax] at h
    split_ifs at h with hc
    · by_cases hk : 1 ≤ m.nDeg
      · exact ⟨m, List.mem_cons_self .., hc, hk⟩
      · have hmax : max m.nDeg (nDegMax R) = nDegMax R := max_eq_right (by omega)
        rw [hmax] at h
        obtain ⟨m', hm', hc', hk'⟩ := ih h
        exact ⟨m', List.mem_cons_of_mem _ hm', hc', hk'⟩
    · obtain ⟨m', hm', hc', hk'⟩ := ih h
      exact ⟨m', List.mem_cons_of_mem _ hm', hc', hk'⟩

/-- With every positive monomial counter-free, `R` does not depend on the counter. -/
theorem rEval_counter_const (R : List RMono) (h : nDegMax R = 0) (b s n n' : Nat) :
    rEval R b s n = rEval R b s n' := by
  induction R with
  | nil => simp [rEval]
  | cons m R ih =>
    have hR : nDegMax R = 0 := by
      have := nDegMax_tail_le m R
      omega
    simp only [rEval, ih hR]
    rcases Nat.eq_zero_or_pos m.coeff with hc | hc
    · simp [hc]
    · have hk : m.nDeg = 0 := by
        have := nDeg_le_nDegMax (m :: R) (List.mem_cons_self ..) hc
        omega
      simp [hk]

/-! ## Monotonicity, normal form and exact criteria -/

/-- Uniform orientation of the successor rule under the successor `n ↦ β * n + a`. -/
def OrientsSucc (W : List WMono) (R : List RMono) (β a : Nat) : Prop :=
  ∀ b s n, wEval W s (rEval R b s n) < rEval R b s (β * n + a)

/-- Uniform orientation of the zero rule with zero interpreted as `z`. -/
def OrientsZero (R : List RMono) (z : Nat) : Prop :=
  ∀ b s, b < rEval R b s z

/-- Natural-coefficient polynomials are monotone in every argument. -/
theorem rEval_mono (R : List RMono) {b b' s s' n n' : Nat}
    (hb : b ≤ b') (hs : s ≤ s') (hn : n ≤ n') : rEval R b s n ≤ rEval R b' s' n' := by
  induction R with
  | nil => simp [rEval]
  | cons m R ih =>
    simp only [rEval]
    exact Nat.add_le_add (by gcongr) ih

/-- Without `y`-square and `y`-payload monomials, `W(s, y) = w * y + W(s, 0)` with
`w = wLin W 0`. -/
theorem wEval_normal (W : List WMono) (h1 : ¬ HasYSquare W) (h2 : ¬ HasYPayload W)
    (s y : Nat) : wEval W s y = wLin W 0 * y + wEval W s 0 := by
  induction W with
  | nil => simp [wEval, wLin]
  | cons m W ih =>
    have h1' : ¬ HasYSquare W := fun ⟨m', hm', hc⟩ => h1 ⟨m', List.mem_cons_of_mem _ hm', hc⟩
    have h2' : ¬ HasYPayload W := fun ⟨m', hm', hc⟩ => h2 ⟨m', List.mem_cons_of_mem _ hm', hc⟩
    have hm1 : ¬ (0 < m.coeff ∧ 2 ≤ m.yDeg) := fun hh => h1 ⟨m, List.mem_cons_self .., hh⟩
    have hm2 : ¬ (0 < m.coeff ∧ m.yDeg = 1 ∧ 1 ≤ m.sDeg) :=
      fun hh => h2 ⟨m, List.mem_cons_self .., hh⟩
    have key : m.coeff * s ^ m.sDeg * y ^ m.yDeg =
        (if m.yDeg = 1 then m.coeff * 0 ^ m.sDeg else 0) * y +
          m.coeff * s ^ m.sDeg * 0 ^ m.yDeg := by
      rcases Nat.eq_zero_or_pos m.coeff with hc | hc
      · simp [hc]
      · have hy : m.yDeg = 0 ∨ (m.yDeg = 1 ∧ m.sDeg = 0) := by omega
        rcases hy with hy | ⟨hy, hs⟩
        · rw [hy]
          simp
        · rw [hy, hs]
          simp
    simp only [wEval, wLin]
    rw [key, ih h1' h2']
    ring

/-- For `β ≥ 1`: `R(b, s, n) + R(0, s, a) ≤ R(b, s, β n + a) + R(0, s, 0)`. -/
theorem rEval_supermod (R : List RMono) {β : Nat} (hβ : 1 ≤ β) (b s n a : Nat) :
    rEval R b s n + rEval R 0 s a ≤ rEval R b s (β * n + a) + rEval R 0 s 0 := by
  induction R with
  | nil => simp [rEval]
  | cons m R ih =>
    have hn : n ≤ β * n := Nat.le_mul_of_pos_left n hβ
    have key : m.coeff * b ^ m.bDeg * s ^ m.sDeg * n ^ m.nDeg +
        m.coeff * 0 ^ m.bDeg * s ^ m.sDeg * a ^ m.nDeg ≤
        m.coeff * b ^ m.bDeg * s ^ m.sDeg * (β * n + a) ^ m.nDeg +
        m.coeff * 0 ^ m.bDeg * s ^ m.sDeg * 0 ^ m.nDeg := by
      rcases Nat.eq_zero_or_pos m.bDeg with hb | hb
      · rw [hb]
        simp only [pow_zero, mul_one]
        rcases Nat.eq_zero_or_pos m.nDeg with hk | hk
        · rw [hk]
          simp only [pow_zero, le_refl]
        · rw [Nat.zero_pow hk, mul_zero, add_zero]
          have hpow : n ^ m.nDeg + a ^ m.nDeg ≤ (β * n + a) ^ m.nDeg :=
            le_trans (pow_add_pow_le (Nat.zero_le n) (Nat.zero_le a) (by omega))
              (Nat.pow_le_pow_left (Nat.add_le_add_right hn a) _)
          calc m.coeff * s ^ m.sDeg * n ^ m.nDeg + m.coeff * s ^ m.sDeg * a ^ m.nDeg
              = m.coeff * s ^ m.sDeg * (n ^ m.nDeg + a ^ m.nDeg) := by ring
            _ ≤ m.coeff * s ^ m.sDeg * (β * n + a) ^ m.nDeg := Nat.mul_le_mul_left _ hpow
      · rw [Nat.zero_pow hb]
        simp only [mul_zero, zero_mul, add_zero]
        exact Nat.mul_le_mul_left _
          (Nat.pow_le_pow_left (le_trans hn (Nat.le_add_right _ _)) _)
    simp only [rEval]
    calc m.coeff * b ^ m.bDeg * s ^ m.sDeg * n ^ m.nDeg + rEval R b s n +
          (m.coeff * 0 ^ m.bDeg * s ^ m.sDeg * a ^ m.nDeg + rEval R 0 s a)
        = (m.coeff * b ^ m.bDeg * s ^ m.sDeg * n ^ m.nDeg +
            m.coeff * 0 ^ m.bDeg * s ^ m.sDeg * a ^ m.nDeg) +
            (rEval R b s n + rEval R 0 s a) := by ring
      _ ≤ (m.coeff * b ^ m.bDeg * s ^ m.sDeg * (β * n + a) ^ m.nDeg +
            m.coeff * 0 ^ m.bDeg * s ^ m.sDeg * 0 ^ m.nDeg) +
            (rEval R b s (β * n + a) + rEval R 0 s 0) := Nat.add_le_add key ih
      _ = _ := by ring

theorem rEval_zero_counter_of_allHigh (R : List RMono) {β w : Nat} (hR : AllHigh R β w)
    (b s : Nat) : rEval R b s 0 = 0 := by
  induction R with
  | nil => simp [rEval]
  | cons m R ih =>
    have hR' : AllHigh R β w := fun m' hm' hc => hR m' (List.mem_cons_of_mem _ hm') hc
    simp only [rEval, ih hR']
    rcases Nat.eq_zero_or_pos m.coeff with hc | hc
    · simp [hc]
    · have hk := (hR m (List.mem_cons_self ..) hc).1
      simp [Nat.zero_pow hk]

/-- Under `AllHigh R β w`: `w * R(b, s, n) + R(0, s, a) ≤ R(b, s, β n + a)`. -/
theorem rEval_high (R : List RMono) {β w : Nat} (hR : AllHigh R β w) (b s n a : Nat) :
    w * rEval R b s n + rEval R 0 s a ≤ rEval R b s (β * n + a) := by
  induction R with
  | nil => simp [rEval]
  | cons m R ih =>
    have hR' : AllHigh R β w := fun m' hm' hc => hR m' (List.mem_cons_of_mem _ hm') hc
    have key : w * (m.coeff * b ^ m.bDeg * s ^ m.sDeg * n ^ m.nDeg) +
        m.coeff * 0 ^ m.bDeg * s ^ m.sDeg * a ^ m.nDeg ≤
        m.coeff * b ^ m.bDeg * s ^ m.sDeg * (β * n + a) ^ m.nDeg := by
      rcases Nat.eq_zero_or_pos m.coeff with hc | hc
      · simp [hc]
      · obtain ⟨hk, hw⟩ := hR m (List.mem_cons_self ..) hc
        have hkne : m.nDeg ≠ 0 := by omega
        have hpow1 : w * n ^ m.nDeg ≤ (β * n) ^ m.nDeg := by
          rw [mul_pow]
          exact Nat.mul_le_mul_right _ hw
        rcases Nat.eq_zero_or_pos m.bDeg with hb | hb
        · rw [hb]
          simp only [pow_zero, mul_one]
          have hpow : w * n ^ m.nDeg + a ^ m.nDeg ≤ (β * n + a) ^ m.nDeg :=
            le_trans (Nat.add_le_add_right hpow1 _)
              (pow_add_pow_le (Nat.zero_le _) (Nat.zero_le _) hkne)
          calc w * (m.coeff * s ^ m.sDeg * n ^ m.nDeg) + m.coeff * s ^ m.sDeg * a ^ m.nDeg
              = m.coeff * s ^ m.sDeg * (w * n ^ m.nDeg + a ^ m.nDeg) := by ring
            _ ≤ m.coeff * s ^ m.sDeg * (β * n + a) ^ m.nDeg := Nat.mul_le_mul_left _ hpow
        · rw [Nat.zero_pow hb]
          simp only [mul_zero, zero_mul, add_zero]
          have hpow : w * n ^ m.nDeg ≤ (β * n + a) ^ m.nDeg :=
            le_trans hpow1 (Nat.pow_le_pow_left (Nat.le_add_right _ _) _)
          calc w * (m.coeff * b ^ m.bDeg * s ^ m.sDeg * n ^ m.nDeg)
              = m.coeff * b ^ m.bDeg * s ^ m.sDeg * (w * n ^ m.nDeg) := by ring
            _ ≤ m.coeff * b ^ m.bDeg * s ^ m.sDeg * (β * n + a) ^ m.nDeg :=
              Nat.mul_le_mul_left _ hpow
    simp only [rEval]
    calc w * (m.coeff * b ^ m.bDeg * s ^ m.sDeg * n ^ m.nDeg + rEval R b s n) +
          (m.coeff * 0 ^ m.bDeg * s ^ m.sDeg * a ^ m.nDeg + rEval R 0 s a)
        = (w * (m.coeff * b ^ m.bDeg * s ^ m.sDeg * n ^ m.nDeg) +
            m.coeff * 0 ^ m.bDeg * s ^ m.sDeg * a ^ m.nDeg) +
            (w * rEval R b s n + rEval R 0 s a) := by ring
      _ ≤ _ := Nat.add_le_add key (ih hR')

/-- `y`-free wrappers: orientation is the univariate comparison `W(s, 0) < R(0, s, a)`. -/
theorem orientsSucc_iff_wZero (W : List WMono) (R : List RMono) (β a : Nat)
    (h1 : ¬ HasYSquare W) (h2 : ¬ HasYPayload W) (hw : wLin W 0 = 0) :
    OrientsSucc W R β a ↔ ∀ s, wEval W s 0 < rEval R 0 s a := by
  constructor
  · intro h s
    have hs := h 0 s 0
    rw [wEval_normal W h1 h2, hw, zero_mul, zero_add, mul_zero, zero_add] at hs
    exact hs
  · intro h b s n
    rw [wEval_normal W h1 h2, hw, zero_mul, zero_add]
    exact lt_of_lt_of_le (h s) (rEval_mono R (Nat.zero_le b) le_rfl (Nat.le_add_left a (β * n)))

/-- Wrappers `y + C(s)` with `β ≥ 1`: orientation is the univariate comparison
`W(s, 0) + R(0, s, 0) < R(0, s, a)`. -/
theorem orientsSucc_iff_wOne (W : List WMono) (R : List RMono) {β : Nat} (hβ : 1 ≤ β)
    (a : Nat) (h1 : ¬ HasYSquare W) (h2 : ¬ HasYPayload W) (hw : wLin W 0 = 1) :
    OrientsSucc W R β a ↔ ∀ s, wEval W s 0 + rEval R 0 s 0 < rEval R 0 s a := by
  constructor
  · intro h s
    have hs := h 0 s 0
    rw [wEval_normal W h1 h2, hw, one_mul, mul_zero, zero_add] at hs
    omega
  · intro h b s n
    rw [wEval_normal W h1 h2, hw, one_mul]
    have hsm := rEval_supermod R hβ b s n a
    have hs := h s
    omega

/-- Wrappers `w * y + C(s)` over recursors with every counter degree `k ≥ 1` and
`w ≤ β ^ k`: orientation is the univariate comparison `W(s, 0) < R(0, s, a)`. -/
theorem orientsSucc_iff_high (W : List WMono) (R : List RMono) (β a : Nat)
    (h1 : ¬ HasYSquare W) (h2 : ¬ HasYPayload W) (hR : AllHigh R β (wLin W 0)) :
    OrientsSucc W R β a ↔ ∀ s, wEval W s 0 < rEval R 0 s a := by
  constructor
  · intro h s
    have hs := h 0 s 0
    rw [wEval_normal W h1 h2, rEval_zero_counter_of_allHigh R hR, mul_zero, zero_add,
      mul_zero, zero_add] at hs
    exact hs
  · intro h b s n
    rw [wEval_normal W h1 h2]
    exact lt_of_lt_of_le (Nat.add_lt_add_left (h s) _) (rEval_high R hR b s n a)

/-! ## Exclusions with failing triples -/

/-- `(X + a) ^ k * (X - k * a) ≤ X ^ (k + 1)` over the naturals. -/
theorem pow_add_mul_sub_le (X a : Nat) : ∀ k : Nat, (X + a) ^ k * (X - k * a) ≤ X ^ (k + 1)
  | 0 => by simp
  | k + 1 => by
    have ih := pow_add_mul_sub_le X a k
    rcases Nat.lt_or_ge X ((k + 1) * a) with h | h
    · rw [Nat.sub_eq_zero_of_le h.le, mul_zero]
      exact Nat.zero_le _
    · obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le h
      have e1 : (k + 1) * a + t - (k + 1) * a = t := Nat.add_sub_cancel_left _ _
      have e2 : (k + 1) * a + t - k * a = a + t := by
        rw [show (k + 1) * a = k * a + a by ring, Nat.add_assoc, Nat.add_sub_cancel_left]
      rw [e1]
      rw [e2] at ih
      have hstep : ((k + 1) * a + t + a) * t ≤ ((k + 1) * a + t) * (a + t) := by
        have e3 : ((k + 1) * a + t) * (a + t) = ((k + 1) * a + t + a) * t + (k + 1) * a * a := by
          ring
        rw [e3]
        exact Nat.le_add_right _ _
      calc ((k + 1) * a + t + a) ^ (k + 1) * t
          = ((k + 1) * a + t + a) ^ k * (((k + 1) * a + t + a) * t) := by ring
        _ ≤ ((k + 1) * a + t + a) ^ k * (((k + 1) * a + t) * (a + t)) :=
          Nat.mul_le_mul_left _ hstep
        _ = ((k + 1) * a + t) * (((k + 1) * a + t + a) ^ k * (a + t)) := by ring
        _ ≤ ((k + 1) * a + t) * ((k + 1) * a + t) ^ (k + 1) := Nat.mul_le_mul_left _ ih
        _ = ((k + 1) * a + t) ^ (k + 1 + 1) := by ring

/-- For `X ≥ M * k * a`: `(M - 1) * (X + a) ^ k ≤ M * X ^ k`. -/
theorem ratio_pow_le {M X a k : Nat} (h : M * k * a ≤ X) :
    (M - 1) * (X + a) ^ k ≤ M * X ^ k := by
  rcases Nat.eq_zero_or_pos X with hX | hX
  · subst hX
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      simp
    · rcases Nat.eq_zero_or_pos a with ha | ha
      · subst ha
        simp [Nat.zero_pow hk]
      · have hM : M = 0 := by
          by_contra hM
          have hpos : 0 < M * k * a := Nat.mul_pos (Nat.mul_pos (Nat.pos_of_ne_zero hM) hk) ha
          omega
        subst hM
        simp
  · have base := pow_add_mul_sub_le X a k
    have hsub : (M - 1) * X ≤ M * (X - k * a) := by
      rcases Nat.eq_zero_or_pos M with hM | hM
      · subst hM
        simp
      · obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
        have e1 : (M' + 1) * k * a = M' * k * a + k * a := by ring
        have hka : k * a ≤ X := by omega
        obtain ⟨v, hv⟩ := Nat.exists_eq_add_of_le hka
        rw [hv] at h ⊢
        rw [Nat.add_sub_cancel, Nat.add_sub_cancel_left]
        have e2 : M' * (k * a + v) = M' * k * a + M' * v := by ring
        have e3 : (M' + 1) * v = M' * v + v := by ring
        omega
    have h1 : (M - 1) * (X + a) ^ k * X ≤ M * X ^ k * X := by
      calc (M - 1) * (X + a) ^ k * X = (M - 1) * X * (X + a) ^ k := by ring
        _ ≤ M * (X - k * a) * (X + a) ^ k := Nat.mul_le_mul_right _ hsub
        _ = M * ((X + a) ^ k * (X - k * a)) := by ring
        _ ≤ M * X ^ (k + 1) := Nat.mul_le_mul_left _ base
        _ = M * X ^ k * X := by ring
    exact Nat.le_of_mul_le_mul_right h1 hX

theorem rEval_ratio_aux (R : List RMono) {β M a N d : Nat} (hβ : 1 ≤ β)
    (hd : ∀ m ∈ R, 0 < m.coeff → m.nDeg ≤ d) (hN : M * d * a ≤ N) (b s : Nat) :
    (M - 1) * rEval R b s (β * N + a) ≤ M * β ^ d * rEval R b s N := by
  induction R with
  | nil => simp [rEval]
  | cons m R ih =>
    have ih' := ih (fun m' hm' hc => hd m' (List.mem_cons_of_mem _ hm') hc)
    have key : (M - 1) * (m.coeff * b ^ m.bDeg * s ^ m.sDeg * (β * N + a) ^ m.nDeg) ≤
        M * β ^ d * (m.coeff * b ^ m.bDeg * s ^ m.sDeg * N ^ m.nDeg) := by
      rcases Nat.eq_zero_or_pos m.coeff with hc | hc
      · simp [hc]
      · have hk : m.nDeg ≤ d := hd m (List.mem_cons_self ..) hc
        have hX : M * m.nDeg * a ≤ β * N :=
          le_trans (Nat.mul_le_mul_right a (Nat.mul_le_mul_left M hk))
            (le_trans hN (Nat.le_mul_of_pos_left N hβ))
        have hr : (M - 1) * (β * N + a) ^ m.nDeg ≤ M * (β * N) ^ m.nDeg := ratio_pow_le hX
        have hb : β ^ m.nDeg ≤ β ^ d := Nat.pow_le_pow_right hβ hk
        calc (M - 1) * (m.coeff * b ^ m.bDeg * s ^ m.sDeg * (β * N + a) ^ m.nDeg)
            = m.coeff * b ^ m.bDeg * s ^ m.sDeg * ((M - 1) * (β * N + a) ^ m.nDeg) := by ring
          _ ≤ m.coeff * b ^ m.bDeg * s ^ m.sDeg * (M * (β * N) ^ m.nDeg) :=
            Nat.mul_le_mul_left _ hr
          _ = m.coeff * b ^ m.bDeg * s ^ m.sDeg * N ^ m.nDeg * M * β ^ m.nDeg := by
            rw [mul_pow]
            ring
          _ ≤ m.coeff * b ^ m.bDeg * s ^ m.sDeg * N ^ m.nDeg * M * β ^ d :=
            Nat.mul_le_mul_left _ hb
          _ = M * β ^ d * (m.coeff * b ^ m.bDeg * s ^ m.sDeg * N ^ m.nDeg) := by ring
    simp only [rEval]
    calc (M - 1) * (m.coeff * b ^ m.bDeg * s ^ m.sDeg * (β * N + a) ^ m.nDeg +
          rEval R b s (β * N + a))
        = (M - 1) * (m.coeff * b ^ m.bDeg * s ^ m.sDeg * (β * N + a) ^ m.nDeg) +
          (M - 1) * rEval R b s (β * N + a) := by ring
      _ ≤ M * β ^ d * (m.coeff * b ^ m.bDeg * s ^ m.sDeg * N ^ m.nDeg) +
          M * β ^ d * rEval R b s N := Nat.add_le_add key ih'
      _ = M * β ^ d * (m.coeff * b ^ m.bDeg * s ^ m.sDeg * N ^ m.nDeg + rEval R b s N) := by
        ring

/-- Growth of `R` along `N ↦ β N + a` for `N ≥ M * d * a`, with `d` the largest counter
degree. -/
theorem rEval_ratio (R : List RMono) {β M a N : Nat} (hβ : 1 ≤ β)
    (hN : M * nDegMax R * a ≤ N) (b s : Nat) :
    (M - 1) * rEval R b s (β * N + a) ≤ M * β ^ nDegMax R * rEval R b s N :=
  rEval_ratio_aux R hβ (fun _ hm hc => nDeg_le_nDegMax R hm hc) hN b s

/-- Counter of the failing triple for the leading-coefficient exclusion. -/
def leadFailN (R : List RMono) (β a : Nat) : Nat := (β ^ nDegMax R + 1) * nDegMax R * a

/-- A `y`-coefficient of at least `β ^ d + 1` at payload `s` fails the successor rule at
`(0, s, leadFailN R β a)`. -/
theorem leading_excludes (W : List WMono) (R : List RMono) {β : Nat} (hβ : 1 ≤ β) (a s : Nat)
    (hw : β ^ nDegMax R + 1 ≤ wLin W s) :
    rEval R 0 s (β * leadFailN R β a + a) ≤ wEval W s (rEval R 0 s (leadFailN R β a)) := by
  have hpos : 0 < β ^ nDegMax R := pow_pos (by omega) _
  have hr := rEval_ratio R (β := β) (M := β ^ nDegMax R + 1) (a := a) (N := leadFailN R β a)
    hβ (le_refl _) 0 s
  rw [Nat.add_sub_cancel] at hr
  have h1 : rEval R 0 s (β * leadFailN R β a + a) ≤
      (β ^ nDegMax R + 1) * rEval R 0 s (leadFailN R β a) := by
    refine Nat.le_of_mul_le_mul_left ?_ hpos
    calc β ^ nDegMax R * rEval R 0 s (β * leadFailN R β a + a)
        ≤ (β ^ nDegMax R + 1) * β ^ nDegMax R * rEval R 0 s (leadFailN R β a) := hr
      _ = β ^ nDegMax R * ((β ^ nDegMax R + 1) * rEval R 0 s (leadFailN R β a)) := by ring
  calc rEval R 0 s (β * leadFailN R β a + a)
      ≤ (β ^ nDegMax R + 1) * rEval R 0 s (leadFailN R β a) := h1
    _ ≤ wLin W s * rEval R 0 s (leadFailN R β a) := Nat.mul_le_mul_right _ hw
    _ ≤ wEval W s (rEval R 0 s (leadFailN R β a)) := wEval_ge_wLin_mul W s _

/-- A monomial `c * s ^ j * y` with `j ≥ 1` fails the successor rule at
`(0, β ^ d + 1, leadFailN R β a)`. -/
theorem yPayload_excludes (W : List WMono) (R : List RMono) (hW : HasYPayload W) {β : Nat}
    (hβ : 1 ≤ β) (a : Nat) :
    rEval R 0 (β ^ nDegMax R + 1) (β * leadFailN R β a + a) ≤
      wEval W (β ^ nDegMax R + 1) (rEval R 0 (β ^ nDegMax R + 1) (leadFailN R β a)) := by
  apply leading_excludes W R hβ a
  obtain ⟨m, hm, hc, hy, hs⟩ := hW
  have h1 := wLin_ge_mem W hm hy (β ^ nDegMax R + 1)
  have h2 : β ^ nDegMax R + 1 ≤ (β ^ nDegMax R + 1) ^ m.sDeg := by
    calc β ^ nDegMax R + 1 = (β ^ nDegMax R + 1) ^ 1 := (pow_one _).symm
      _ ≤ (β ^ nDegMax R + 1) ^ m.sDeg := Nat.pow_le_pow_right (by omega) hs
  have h3 : (β ^ nDegMax R + 1) ^ m.sDeg ≤ m.coeff * (β ^ nDegMax R + 1) ^ m.sDeg :=
    Nat.le_mul_of_pos_left _ hc
  omega

theorem wEval_ge_sq (W : List WMono) (hW : HasYSquare W) (y : Nat) : y * y ≤ wEval W 1 y := by
  obtain ⟨m, hm, hc, hy⟩ := hW
  have h1 := wEval_ge_mem W hm 1 y
  rw [one_pow, mul_one] at h1
  rcases Nat.eq_zero_or_pos y with h0 | h0
  · subst h0
    simp
  · have h2 : y * y ≤ y ^ m.yDeg := by
      rw [← pow_two]
      exact Nat.pow_le_pow_right h0 hy
    have h3 : y ^ m.yDeg ≤ m.coeff * y ^ m.yDeg := Nat.le_mul_of_pos_left _ hc
    omega

theorem rEval_ge_counter (R : List RMono) (hR : 1 ≤ nDegMax R) {N : Nat} (hN : 1 ≤ N) :
    N ≤ rEval R 1 1 N := by
  obtain ⟨m, hm, hc, hk⟩ := exists_growing_of_nDegMax R hR
  have h1 := rEval_ge_mem R hm 1 1 N
  simp only [one_pow, mul_one] at h1
  have h2 : N ≤ N ^ m.nDeg := by
    calc N = N ^ 1 := (pow_one N).symm
      _ ≤ N ^ m.nDeg := Nat.pow_le_pow_right hN hk
  have h3 : N ^ m.nDeg ≤ m.coeff * N ^ m.nDeg := Nat.le_mul_of_pos_left _ hc
  omega

/-- Counter of the failing triple for the `y`-square exclusion. -/
def ySquareFailN (R : List RMono) (β a : Nat) : Nat :=
  if nDegMax R = 0 then 0 else 2 * nDegMax R * a + 2 * β ^ nDegMax R + 1

/-- A monomial of `y`-degree at least two fails the successor rule at
`(1, 1, ySquareFailN R β a)`, for every slope `β ≥ 1` and offset `a`. -/
theorem ySquare_excludes (W : List WMono) (R : List RMono) (hW : HasYSquare W) {β : Nat}
    (hβ : 1 ≤ β) (a : Nat) :
    rEval R 1 1 (β * ySquareFailN R β a + a) ≤ wEval W 1 (rEval R 1 1 (ySquareFailN R β a)) := by
  have hsq := wEval_ge_sq W hW
  unfold ySquareFailN
  split_ifs with hd
  · rw [rEval_counter_const R hd 1 1 (β * 0 + a) 0]
    have h1 := hsq (rEval R 1 1 0)
    have h2 : rEval R 1 1 0 ≤ rEval R 1 1 0 * rEval R 1 1 0 := Nat.le_mul_self _
    omega
  · have hd1 : 1 ≤ nDegMax R := by omega
    have hr := rEval_ratio R (β := β) (M := 2) (a := a)
      (N := 2 * nDegMax R * a + 2 * β ^ nDegMax R + 1) hβ (by omega) 1 1
    have hg := rEval_ge_counter R hd1 (N := 2 * nDegMax R * a + 2 * β ^ nDegMax R + 1)
      (by omega)
    have h1 : rEval R 1 1 (β * (2 * nDegMax R * a + 2 * β ^ nDegMax R + 1) + a) ≤
        2 * β ^ nDegMax R * rEval R 1 1 (2 * nDegMax R * a + 2 * β ^ nDegMax R + 1) := by
      simpa using hr
    have h2 : 2 * β ^ nDegMax R * rEval R 1 1 (2 * nDegMax R * a + 2 * β ^ nDegMax R + 1) ≤
        rEval R 1 1 (2 * nDegMax R * a + 2 * β ^ nDegMax R + 1) *
          rEval R 1 1 (2 * nDegMax R * a + 2 * β ^ nDegMax R + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    exact le_trans h1 (le_trans h2 (hsq _))

/-! ## Univariate comparison -/

/-- Coefficient of `x ^ k` in a univariate monomial list. -/
def coeffAt : List UMono → Nat → Nat
  | [], _ => 0
  | m :: p, k => (if m.deg = k then m.coeff else 0) + coeffAt p k

/-- Largest degree of a univariate monomial list. -/
def uDeg : List UMono → Nat
  | [] => 0
  | m :: p => max m.deg (uDeg p)

theorem uEval_eq_sum (p : List UMono) {D : Nat} (hD : uDeg p < D) (x : Nat) :
    uEval p x = ∑ k ∈ Finset.range D, coeffAt p k * x ^ k := by
  induction p with
  | nil => simp [uEval, coeffAt]
  | cons m p ih =>
    simp only [uDeg] at hD
    have hm : m.deg < D := lt_of_le_of_lt (le_max_left _ _) hD
    have hp : uDeg p < D := lt_of_le_of_lt (le_max_right _ _) hD
    simp only [uEval, coeffAt, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, ih hp]
    rw [Finset.sum_ite_eq]
    simp [Finset.mem_range, hm]

/-- Leading coefficient of the coefficient sequence `c 0, ..., c (D - 1)`. -/
def leadCoeff : (Nat → Int) → Nat → Int
  | _, 0 => 0
  | c, D + 1 =>
      if leadCoeff (fun j => c (j + 1)) D = 0 then c 0 else leadCoeff (fun j => c (j + 1)) D

theorem horner_split (c : Nat → Int) (D : Nat) (x : Int) :
    ∑ j ∈ Finset.range (D + 1), c j * x ^ j =
      c 0 + x * ∑ j ∈ Finset.range D, c (j + 1) * x ^ j := by
  rw [Finset.sum_range_succ', Finset.mul_sum]
  simp only [pow_zero, mul_one, pow_succ]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Beyond the sum of the absolute coefficients, a polynomial has the sign of its leading
coefficient. -/
theorem horner_sign : ∀ (D : Nat) (c : Nat → Int) (x : Int),
    (∑ j ∈ Finset.range D, |c j|) < x →
    (leadCoeff c D = 0 → ∑ j ∈ Finset.range D, c j * x ^ j = 0) ∧
    (0 < leadCoeff c D → 0 < ∑ j ∈ Finset.range D, c j * x ^ j) ∧
    (leadCoeff c D < 0 → ∑ j ∈ Finset.range D, c j * x ^ j < 0)
  | 0, c, x, _ => by simp [leadCoeff]
  | D + 1, c, x, hx => by
    rw [Finset.sum_range_succ'] at hx
    have hrest : 0 ≤ ∑ j ∈ Finset.range D, |c (j + 1)| :=
      Finset.sum_nonneg (fun j _ => abs_nonneg _)
    have habs := abs_nonneg (c 0)
    have hx' : ∑ j ∈ Finset.range D, |c (j + 1)| < x := by linarith
    have ih := horner_sign D (fun j => c (j + 1)) x hx'
    have hc : |c 0| < x := by linarith
    have hc' := abs_lt.1 hc
    have hxpos : 0 < x := by linarith
    rw [horner_split]
    by_cases hl : leadCoeff (fun j => c (j + 1)) D = 0
    · have h0 := ih.1 hl
      have hL : leadCoeff c (D + 1) = c 0 := by simp [leadCoeff, hl]
      rw [hL, h0, mul_zero, add_zero]
      exact ⟨id, id, id⟩
    · have hL : leadCoeff c (D + 1) = leadCoeff (fun j => c (j + 1)) D := by
        simp [leadCoeff, hl]
      rw [hL]
      refine ⟨fun h => absurd h hl, fun h => ?_, fun h => ?_⟩
      · have hp := ih.2.1 h
        have h1 : (1 : Int) ≤ ∑ j ∈ Finset.range D, c (j + 1) * x ^ j := by
          simpa using hp
        nlinarith [mul_le_mul_of_nonneg_left h1 hxpos.le]
      · have hn := ih.2.2 h
        have h1 : ∑ j ∈ Finset.range D, c (j + 1) * x ^ j ≤ -1 := by
          simpa using Int.le_sub_one_of_lt hn
        nlinarith [mul_le_mul_of_nonneg_left h1 hxpos.le]

/-- Coefficient difference `Q_k - P_k`. -/
def diffCoeff (P Q : List UMono) (k : Nat) : Int := (coeffAt Q k : Int) - (coeffAt P k : Int)

theorem diff_sum_eq (P Q : List UMono) {D : Nat} (hP : uDeg P < D) (hQ : uDeg Q < D)
    (x : Nat) :
    ∑ k ∈ Finset.range D, diffCoeff P Q k * (x : Int) ^ k =
      (uEval Q x : Int) - (uEval P x : Int) := by
  rw [uEval_eq_sum Q hQ x, uEval_eq_sum P hP x]
  push_cast
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [diffCoeff]
  ring

theorem diff_abs_sum_le (P Q : List UMono) {D : Nat} (hP : uDeg P < D) (hQ : uDeg Q < D) :
    ∑ k ∈ Finset.range D, |diffCoeff P Q k| ≤ (uEval P 1 : Int) + (uEval Q 1 : Int) := by
  have hPe := uEval_eq_sum P hP 1
  have hQe := uEval_eq_sum Q hQ 1
  simp only [one_pow, mul_one] at hPe hQe
  rw [hPe, hQe]
  push_cast
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro k _
  have h1 : (0 : Int) ≤ (coeffAt P k : Int) := Nat.cast_nonneg _
  have h2 : (0 : Int) ≤ (coeffAt Q k : Int) := Nat.cast_nonneg _
  rw [diffCoeff, abs_le]
  constructor <;> linarith

/-- Search bound of the univariate check. -/
def checkBound (P Q : List UMono) : Nat := uEval P 1 + uEval Q 1 + 1

/-- Executable check of `∀ x, P x < Q x`. -/
def ltAllB (P Q : List UMono) : Bool :=
  (List.range (checkBound P Q + 1)).all fun x => decide (uEval P x < uEval Q x)

/-- The univariate check is sound and complete. -/
theorem ltAllB_iff (P Q : List UMono) : ltAllB P Q = true ↔ ∀ x, uEval P x < uEval Q x := by
  constructor
  · intro h x
    unfold ltAllB at h
    rw [List.all_eq_true] at h
    by_cases hx : x ≤ checkBound P Q
    · have hx' := h x (List.mem_range.2 (by omega))
      simpa using hx'
    · obtain ⟨D, hPD, hQD⟩ : ∃ D, uDeg P < D ∧ uDeg Q < D :=
        ⟨max (uDeg P) (uDeg Q) + 1, Nat.lt_succ_of_le (le_max_left _ _),
          Nat.lt_succ_of_le (le_max_right _ _)⟩
      have hbound := diff_abs_sum_le P Q hPD hQD
      have hBcast : ((checkBound P Q : Nat) : Int) = (uEval P 1 : Int) + (uEval Q 1 : Int) + 1 := by
        simp [checkBound]
      have hBpos : (∑ k ∈ Finset.range D, |diffCoeff P Q k|) < ((checkBound P Q : Nat) : Int) := by
        rw [hBcast]
        linarith
      have hB_check : uEval P (checkBound P Q) < uEval Q (checkBound P Q) := by
        have hB' := h (checkBound P Q) (List.mem_range.2 (by omega))
        simpa using hB'
      have hB_int : (uEval P (checkBound P Q) : Int) < (uEval Q (checkBound P Q) : Int) := by
        exact_mod_cast hB_check
      have hsignB := horner_sign D (diffCoeff P Q) ((checkBound P Q : Nat) : Int) hBpos
      rw [diff_sum_eq P Q hPD hQD (checkBound P Q)] at hsignB
      have hlead : 0 < leadCoeff (diffCoeff P Q) D := by
        rcases lt_trichotomy (leadCoeff (diffCoeff P Q) D) 0 with hl | hl | hl
        · have := hsignB.2.2 hl
          linarith
        · have := hsignB.1 hl
          linarith
        · exact hl
      have hxB : (∑ k ∈ Finset.range D, |diffCoeff P Q k|) < ((x : Nat) : Int) := by
        have hlt : ((checkBound P Q : Nat) : Int) < ((x : Nat) : Int) := by
          exact_mod_cast (by omega : checkBound P Q < x)
        linarith
      have hsignx := horner_sign D (diffCoeff P Q) ((x : Nat) : Int) hxB
      rw [diff_sum_eq P Q hPD hQD x] at hsignx
      have hpos := hsignx.2.1 hlead
      have hint : (uEval P x : Int) < (uEval Q x : Int) := by linarith
      exact_mod_cast hint
  · intro h
    unfold ltAllB
    rw [List.all_eq_true]
    intro x _
    simpa using h x

/-- The first point up to the search bound where `P x < Q x` fails. -/
def firstFail (P Q : List UMono) : Nat :=
  ((List.range (checkBound P Q + 1)).find? fun x => !decide (uEval P x < uEval Q x)).getD 0

theorem firstFail_spec {P Q : List UMono} (h : ltAllB P Q = false) :
    uEval Q (firstFail P Q) ≤ uEval P (firstFail P Q) := by
  unfold firstFail
  cases hf : (List.range (checkBound P Q + 1)).find?
      (fun x => !decide (uEval P x < uEval Q x)) with
  | none =>
    exfalso
    rw [List.find?_eq_none] at hf
    have htrue : ltAllB P Q = true := by
      unfold ltAllB
      rw [List.all_eq_true]
      intro x hx
      have hx' := hf x hx
      simpa using hx'
    rw [htrue] at h
    exact Bool.noConfusion h
  | some x =>
    have hx := List.find?_some hf
    simp only [Option.getD_some]
    simp only [Bool.not_eq_true', decide_eq_false_iff_not, not_lt] at hx
    exact hx

/-! ## The decision -/

/-- Verdict for the successor rule under `succ n = β * n + a`: `some v` decides, `none` marks the
class left open. -/
def decideSuccAff (W : List WMono) (R : List RMono) (β a : Nat) : Option Bool :=
  if HasYSquare W then some false
  else if HasYPayload W then some false
  else if wLin W 0 = 0 then some (ltAllB (wAtY0 W) (rAtBN R 0 a))
  else if wLin W 0 = 1 then some (ltAllB (wAtY0 W ++ rAtBN R 0 0) (rAtBN R 0 a))
  else if β ^ nDegMax R < wLin W 0 then some false
  else if AllHigh R β (wLin W 0) then some (ltAllB (wAtY0 W) (rAtBN R 0 a))
  else none

/-- Base, payload and counter of a failing triple for each rejecting branch. -/
def failSuccAff (W : List WMono) (R : List RMono) (β a : Nat) : Nat × Nat × Nat :=
  if HasYSquare W then (1, 1, ySquareFailN R β a)
  else if HasYPayload W then (0, β ^ nDegMax R + 1, leadFailN R β a)
  else if wLin W 0 = 0 then (0, firstFail (wAtY0 W) (rAtBN R 0 a), 0)
  else if wLin W 0 = 1 then (0, firstFail (wAtY0 W ++ rAtBN R 0 0) (rAtBN R 0 a), 0)
  else if β ^ nDegMax R < wLin W 0 then (0, 0, leadFailN R β a)
  else if AllHigh R β (wLin W 0) then (0, firstFail (wAtY0 W) (rAtBN R 0 a), 0)
  else (0, 0, 0)

/-- A rejection comes with a triple at which the successor rule does not decrease. -/
theorem failSuccAff_spec {W : List WMono} {R : List RMono} {β a : Nat} (hβ : 1 ≤ β)
    (h : decideSuccAff W R β a = some false) {b s n : Nat}
    (ht : failSuccAff W R β a = (b, s, n)) :
    rEval R b s (β * n + a) ≤ wEval W s (rEval R b s n) := by
  unfold decideSuccAff at h
  unfold failSuccAff at ht
  split_ifs at h ht with h1 h2 h3 h4 h5 h6
  · cases ht
    exact ySquare_excludes W R h1 hβ a
  · cases ht
    exact yPayload_excludes W R h2 hβ a
  · cases ht
    have hf : ltAllB (wAtY0 W) (rAtBN R 0 a) = false := Option.some.inj h
    have hff := firstFail_spec hf
    rw [uEval_rAtBN, uEval_wAtY0] at hff
    rw [wEval_normal W h1 h2, h3, zero_mul, zero_add, mul_zero, zero_add]
    exact hff
  · cases ht
    have hf : ltAllB (wAtY0 W ++ rAtBN R 0 0) (rAtBN R 0 a) = false := Option.some.inj h
    have hff := firstFail_spec hf
    simp only [uEval_append, uEval_wAtY0, uEval_rAtBN] at hff
    rw [wEval_normal W h1 h2, h4, one_mul, mul_zero, zero_add]
    omega
  · cases ht
    exact leading_excludes W R hβ a 0 h5
  · cases ht
    have hf : ltAllB (wAtY0 W) (rAtBN R 0 a) = false := Option.some.inj h
    have hff := firstFail_spec hf
    rw [uEval_rAtBN, uEval_wAtY0] at hff
    rw [rEval_zero_counter_of_allHigh R h6 0, mul_zero, zero_add]
    exact hff

/-- Where the decision returns a value, the value is correct. -/
theorem decideSuccAff_spec {W : List WMono} {R : List RMono} {β a : Nat} (hβ : 1 ≤ β)
    {v : Bool} (h : decideSuccAff W R β a = some v) : v = true ↔ OrientsSucc W R β a := by
  cases v with
  | false =>
    simp only [Bool.false_eq_true, false_iff]
    intro hor
    rcases ht : failSuccAff W R β a with ⟨b, s, n⟩
    exact (Nat.not_le.2 (hor b s n)) (failSuccAff_spec hβ h ht)
  | true =>
    simp only [true_iff]
    unfold decideSuccAff at h
    split_ifs at h with h1 h2 h3 h4 h5 h6
    · cases h
    · cases h
    · have ht : ltAllB (wAtY0 W) (rAtBN R 0 a) = true := Option.some.inj h
      rw [ltAllB_iff] at ht
      simp only [uEval_wAtY0, uEval_rAtBN] at ht
      exact (orientsSucc_iff_wZero W R β a h1 h2 h3).2 ht
    · have ht : ltAllB (wAtY0 W ++ rAtBN R 0 0) (rAtBN R 0 a) = true := Option.some.inj h
      rw [ltAllB_iff] at ht
      simp only [uEval_append, uEval_wAtY0, uEval_rAtBN] at ht
      exact (orientsSucc_iff_wOne W R hβ a h1 h2 h4).2 ht
    · cases h
    · have ht : ltAllB (wAtY0 W) (rAtBN R 0 a) = true := Option.some.inj h
      rw [ltAllB_iff] at ht
      simp only [uEval_wAtY0, uEval_rAtBN] at ht
      exact (orientsSucc_iff_high W R β a h1 h2 h6).2 ht

/-- The class left open by the decision, stated exactly. -/
theorem decideSuccAff_eq_none_iff (W : List WMono) (R : List RMono) (β a : Nat) :
    decideSuccAff W R β a = none ↔
      ¬ HasYSquare W ∧ ¬ HasYPayload W ∧ 2 ≤ wLin W 0 ∧ wLin W 0 ≤ β ^ nDegMax R ∧
        ¬ AllHigh R β (wLin W 0) := by
  constructor
  · intro h
    unfold decideSuccAff at h
    split_ifs at h with h1 h2 h3 h4 h5 h6
    exact ⟨h1, h2, by omega, by omega, h6⟩
  · rintro ⟨h1, h2, hw, hl, h6⟩
    have h3 : ¬ wLin W 0 = 0 := by omega
    have h4 : ¬ wLin W 0 = 1 := by omega
    have h5 : ¬ β ^ nDegMax R < wLin W 0 := by omega
    simp [decideSuccAff, h1, h2, h3, h4, h5, h6]

/-- For the unit successor the decision always returns a value. -/
theorem decideSuccAff_unit_ne_none (W : List WMono) (R : List RMono) (a : Nat) :
    decideSuccAff W R 1 a ≠ none := by
  intro h
  obtain ⟨-, -, hw, hl, -⟩ := (decideSuccAff_eq_none_iff W R 1 a).1 h
  rw [one_pow] at hl
  omega

/-! ## Unit successor, zero rule and both root rules -/

/-- Decision of the successor rule under the unit successor `succ n = n + a`. -/
def decideSuccUnit (W : List WMono) (R : List RMono) (a : Nat) : Bool :=
  (decideSuccAff W R 1 a).getD false

/-- T-DEC-1 for the successor rule: the unit-successor decision is sound and complete. -/
theorem decideSuccUnit_iff (W : List WMono) (R : List RMono) (a : Nat) :
    decideSuccUnit W R a = true ↔
      ∀ b s n, wEval W s (rEval R b s n) < rEval R b s (n + a) := by
  have hunit : OrientsSucc W R 1 a ↔ ∀ b s n, wEval W s (rEval R b s n) < rEval R b s (n + a) := by
    simp only [OrientsSucc, one_mul]
  rw [← hunit]
  unfold decideSuccUnit
  rcases hv : decideSuccAff W R 1 a with _ | v
  · exact absurd hv (decideSuccAff_unit_ne_none W R a)
  · simpa using decideSuccAff_spec (le_refl 1) hv

/-- A unit-successor rejection comes with a failing triple. -/
theorem failSuccUnit_spec {W : List WMono} {R : List RMono} {a : Nat}
    (h : decideSuccUnit W R a = false) {b s n : Nat} (ht : failSuccAff W R 1 a = (b, s, n)) :
    rEval R b s (n + a) ≤ wEval W s (rEval R b s n) := by
  have hs : decideSuccAff W R 1 a = some false := by
    unfold decideSuccUnit at h
    rcases hv : decideSuccAff W R 1 a with _ | v
    · exact absurd hv (decideSuccAff_unit_ne_none W R a)
    · rw [hv] at h
      simp only [Option.getD_some] at h
      rw [h]
  simpa using failSuccAff_spec (le_refl 1) hs ht

/-- Decision of the zero rule `recur b s zero → b` with zero interpreted as `z`. -/
def decideZero (R : List RMono) (z : Nat) : Bool := ltAllB [⟨1, 1⟩] (rAtSN R 0 z)

theorem decideZero_iff (R : List RMono) (z : Nat) : decideZero R z = true ↔ OrientsZero R z := by
  unfold decideZero OrientsZero
  rw [ltAllB_iff]
  simp only [uEval_rAtSN, uEval, one_mul, pow_one, add_zero]
  constructor
  · intro h b s
    exact lt_of_lt_of_le (h b) (rEval_mono R le_rfl (Nat.zero_le s) le_rfl)
  · intro h b
    exact h b 0

/-- A zero-rule rejection comes with a failing base. -/
theorem decideZero_false_witness {R : List RMono} {z : Nat} (h : decideZero R z = false) :
    rEval R (firstFail [⟨1, 1⟩] (rAtSN R 0 z)) 0 z ≤ firstFail [⟨1, 1⟩] (rAtSN R 0 z) := by
  have hff := firstFail_spec h
  simpa [uEval_rAtSN, uEval] using hff

/-- The constructor-local polynomial interpretation of the free schema. -/
def polyInterpretation (z β a : Nat) (W : List WMono) (R : List RMono) : Interpretation Nat where
  zero := z
  succ n := β * n + a
  wrap s y := wEval W s y
  recur b s n := rEval R b s n

theorem rootRuleOrients_iff (z β a : Nat) (W : List WMono) (R : List RMono) :
    RootRuleOrients (polyInterpretation z β a W R) (· < ·) ↔
      OrientsZero R z ∧ OrientsSucc W R β a := by
  constructor
  · intro h
    exact ⟨fun b s => h.recurZero b s, fun b s n => h.recurSucc b s n⟩
  · rintro ⟨h0, hs⟩
    exact ⟨fun b s => h0 b s, fun b s n => hs b s n⟩

/-- Decision of both root rules under the unit successor. -/
def decideRootUnit (z a : Nat) (W : List WMono) (R : List RMono) : Bool :=
  decideZero R z && decideSuccUnit W R a

/-- T-DEC-1: for natural-coefficient polynomial interpretations with unit successor, root
orientation of the free recursor is decided by `decideRootUnit`. -/
theorem decideRootUnit_iff (z a : Nat) (W : List WMono) (R : List RMono) :
    decideRootUnit z a W R = true ↔ RootRuleOrients (polyInterpretation z 1 a W R) (· < ·) := by
  rw [rootRuleOrients_iff, decideRootUnit, Bool.and_eq_true, decideZero_iff, decideSuccUnit_iff]
  simp only [OrientsSucc, one_mul]

/-! ## Instances and controls -/

/-- The wrapper `s + y + 1` of the coupled region. -/
def regionW : List WMono := [⟨1, 1, 0⟩, ⟨1, 0, 1⟩, ⟨1, 0, 0⟩]

/-- The recursor `(n + 1) * (α * s + b + β)` of the coupled region, expanded. -/
def regionR (α β : Nat) : List RMono :=
  [⟨α, 0, 1, 1⟩, ⟨1, 1, 0, 1⟩, ⟨β, 0, 0, 1⟩, ⟨α, 0, 1, 0⟩, ⟨1, 1, 0, 0⟩, ⟨β, 0, 0, 0⟩]

theorem wEval_regionW (s y : Nat) : wEval regionW s y = PolynomialRegion.wrapperEval s y := by
  simp [regionW, wEval, PolynomialRegion.wrapperEval]
  ring

theorem rEval_regionR (α β b s n : Nat) :
    rEval (regionR α β) b s n = PolynomialRegion.recursorEval α β b s n := by
  simp [regionR, rEval, PolynomialRegion.recursorEval]
  ring

/-- The P2.4 region is the output of the decision: on `W = s + y + 1` and
`R = (n + 1) * (α * s + b + β)` with `z = 0` and unit successor, `decideRootUnit` accepts
exactly when `α ≥ 1` and `β ≥ 2`. The derivation runs through `orientsSucc_iff_wOne`. -/
theorem region_decides (α β : Nat) :
    decideRootUnit 0 1 regionW (regionR α β) = true ↔ 1 ≤ α ∧ 2 ≤ β := by
  have h1 : ¬ HasYSquare regionW := by decide
  have h2 : ¬ HasYPayload regionW := by decide
  have hw : wLin regionW 0 = 1 := by decide
  rw [decideRootUnit, Bool.and_eq_true, decideZero_iff, decideSuccUnit_iff]
  have hsucc : (∀ b s n, wEval regionW s (rEval (regionR α β) b s n) <
      rEval (regionR α β) b s (n + 1)) ↔
      ∀ s, wEval regionW s 0 + rEval (regionR α β) 0 s 0 < rEval (regionR α β) 0 s 1 := by
    have hc := orientsSucc_iff_wOne regionW (regionR α β) (le_refl 1) 1 h1 h2 hw
    simpa [OrientsSucc] using hc
  have hres : ∀ s, (wEval regionW s 0 + rEval (regionR α β) 0 s 0 < rEval (regionR α β) 0 s 1 ↔
      s + 1 < α * s + β) := by
    intro s
    rw [wEval_regionW, rEval_regionR, rEval_regionR]
    simp only [PolynomialRegion.wrapperEval, PolynomialRegion.recursorEval]
    constructor <;> intro hh <;> nlinarith
  have hzero : OrientsZero (regionR α β) 0 ↔ ∀ b s, b < α * s + b + β := by
    unfold OrientsZero
    refine forall_congr' fun b => forall_congr' fun s => ?_
    rw [rEval_regionR]
    simp only [PolynomialRegion.recursorEval]
    constructor <;> intro hh <;> nlinarith
  rw [hsucc, hzero]
  simp only [hres]
  constructor
  · rintro ⟨_, h⟩
    have h0 := h 0
    have hb := h β
    refine ⟨?_, by omega⟩
    rcases Nat.eq_zero_or_pos α with hα | hα
    · subst hα
      omega
    · exact hα
  · rintro ⟨hα, hβ⟩
    refine ⟨fun b s => by omega, fun s => ?_⟩
    have := Nat.le_mul_of_pos_left s hα
    omega

/-- The decision's verdict on the coupled family agrees with `PolynomialRegion.OrientsBoth`. -/
theorem region_decides_agrees (α β : Nat) :
    decideRootUnit 0 1 regionW (regionR α β) = true ↔ PolynomialRegion.OrientsBoth α β := by
  rw [region_decides, PolynomialRegion.orientsBoth_iff_region]

theorem forall_linear_lt_iff (A B C D : Nat) :
    (∀ s, A + B * s < C + D * s) ↔ A < C ∧ B ≤ D := by
  constructor
  · intro h
    refine ⟨by simpa using h 0, ?_⟩
    by_contra hBD
    push_neg at hBD
    have hC := h C
    have hle : D * C + C ≤ B * C := by
      calc D * C + C = (D + 1) * C := by ring
        _ ≤ B * C := Nat.mul_le_mul_right _ hBD
    omega
  · rintro ⟨hAC, hBD⟩ s
    have := Nat.mul_le_mul_right s hBD
    omega

/-- The affine wrapper `α + βw * s + γ * y`. -/
def affineW (α βw γ : Nat) : List WMono := [⟨α, 0, 0⟩, ⟨βw, 1, 0⟩, ⟨γ, 0, 1⟩]

/-- The multilinear recursor with one coefficient per subset of `{b, s, n}`. -/
def multilinearR (r0 rb rs rn rbs rbn rsn rbsn : Nat) : List RMono :=
  [⟨r0, 0, 0, 0⟩, ⟨rb, 1, 0, 0⟩, ⟨rs, 0, 1, 0⟩, ⟨rn, 0, 0, 1⟩,
    ⟨rbs, 1, 1, 0⟩, ⟨rbn, 1, 0, 1⟩, ⟨rsn, 0, 1, 1⟩, ⟨rbsn, 1, 1, 1⟩]

theorem wEval_affineW_zero (α βw γ s : Nat) : wEval (affineW α βw γ) s 0 = α + βw * s := by
  simp [affineW, wEval]

theorem rEval_multilinearR (r0 rb rs rn rbs rbn rsn rbsn s n : Nat) :
    rEval (multilinearR r0 rb rs rn rbs rbn rsn rbsn) 0 s n =
      (r0 + rn * n) + (rs + rsn * n) * s := by
  simp [multilinearR, rEval]
  ring

/-- Exact verdict of the decision on affine wrappers over multilinear recursors with unit
successor: orientation holds exactly for `γ = 0` with `α < r0 + rn * a` and
`βw ≤ rs + rsn * a`, or for `γ = 1` with `α < rn * a` and `βw ≤ rsn * a`. -/
theorem multilinear_affine_classification (α βw γ r0 rb rs rn rbs rbn rsn rbsn a : Nat) :
    decideSuccUnit (affineW α βw γ) (multilinearR r0 rb rs rn rbs rbn rsn rbsn) a = true ↔
      (γ = 0 ∧ α < r0 + rn * a ∧ βw ≤ rs + rsn * a) ∨
        (γ = 1 ∧ α < rn * a ∧ βw ≤ rsn * a) := by
  have h1 : ¬ HasYSquare (affineW α βw γ) := by
    simp [HasYSquare, affineW]
  have h2 : ¬ HasYPayload (affineW α βw γ) := by
    simp [HasYPayload, affineW]
  have hw : wLin (affineW α βw γ) 0 = γ := by
    simp [wLin, affineW]
  have hunit : (∀ b s n, wEval (affineW α βw γ) s
        (rEval (multilinearR r0 rb rs rn rbs rbn rsn rbsn) b s n) <
        rEval (multilinearR r0 rb rs rn rbs rbn rsn rbsn) b s (n + a)) ↔
      OrientsSucc (affineW α βw γ) (multilinearR r0 rb rs rn rbs rbn rsn rbsn) 1 a := by
    simp only [OrientsSucc, one_mul]
  rw [decideSuccUnit_iff, hunit]
  rcases Nat.lt_or_ge γ 2 with hγ | hγ
  · rcases Nat.lt_or_ge γ 1 with hγ1 | hγ1
    · have hγ0 : γ = 0 := by omega
      rw [orientsSucc_iff_wZero _ _ 1 a h1 h2 (by rw [hw, hγ0])]
      have key : (∀ s, wEval (affineW α βw γ) s 0 <
          rEval (multilinearR r0 rb rs rn rbs rbn rsn rbsn) 0 s a) ↔
          ∀ s, α + βw * s < (r0 + rn * a) + (rs + rsn * a) * s :=
        forall_congr' fun s => by rw [wEval_affineW_zero, rEval_multilinearR]
      rw [key, forall_linear_lt_iff]
      constructor
      · intro hh
        exact Or.inl ⟨hγ0, hh⟩
      · rintro (hh | hh)
        · exact hh.2
        · omega
    · have hγ1' : γ = 1 := by omega
      rw [orientsSucc_iff_wOne _ _ (le_refl 1) a h1 h2 (by rw [hw, hγ1'])]
      have key : (∀ s, wEval (affineW α βw γ) s 0 +
          rEval (multilinearR r0 rb rs rn rbs rbn rsn rbsn) 0 s 0 <
          rEval (multilinearR r0 rb rs rn rbs rbn rsn rbsn) 0 s a) ↔
          ∀ s, (α + r0) + (βw + rs) * s < (r0 + rn * a) + (rs + rsn * a) * s :=
        forall_congr' fun s => by
          rw [wEval_affineW_zero, rEval_multilinearR, rEval_multilinearR,
            show α + βw * s + (r0 + rn * 0 + (rs + rsn * 0) * s) =
              (α + r0) + (βw + rs) * s by ring]
      rw [key, forall_linear_lt_iff]
      constructor
      · rintro ⟨hA, hB⟩
        exact Or.inr ⟨hγ1', by omega, by omega⟩
      · rintro (hh | hh)
        · omega
        · exact ⟨by omega, by omega⟩
  · constructor
    · intro hor
      exfalso
      have hf := leading_excludes (affineW α βw γ) (multilinearR r0 rb rs rn rbs rbn rsn rbsn)
        (le_refl 1) a 0 (by rw [one_pow, hw]; omega)
      have hl := hor 0 0 (leadFailN (multilinearR r0 rb rs rn rbs rbn rsn rbsn) 1 a)
      omega
    · rintro (hh | hh) <;> omega

/-- Retentive affine interpretations (`βw ≥ 1`, `γ ≥ 1`) over affine recursors are rejected
under the unit successor. -/
theorem affine_retentive_rejected (α βw γ r0 rb rs rn a : Nat) (hβw : 1 ≤ βw) (hγ : 1 ≤ γ) :
    decideSuccUnit (affineW α βw γ) (multilinearR r0 rb rs rn 0 0 0 0) a = false := by
  have hc := multilinear_affine_classification α βw γ r0 rb rs rn 0 0 0 0 a
  cases hd : decideSuccUnit (affineW α βw γ) (multilinearR r0 rb rs rn 0 0 0 0) a with
  | false => rfl
  | true =>
    rw [hd] at hc
    have hv := hc.1 rfl
    omega

/-- Roadmap control: the doubled wrapper `2 * y` with successor `2 * n + 1` and recursor
`n ^ 2` is decided and orients. -/
theorem doubled_wrapper_decided :
    decideSuccAff [⟨2, 0, 1⟩] [⟨1, 0, 0, 2⟩] 2 1 = some true := by
  decide

theorem doubled_wrapper_orients : OrientsSucc [⟨2, 0, 1⟩] [⟨1, 0, 0, 2⟩] 2 1 :=
  (decideSuccAff_spec (by decide) doubled_wrapper_decided).1 rfl

/-- Under the unit successor the doubled wrapper is rejected for every recursor and offset. -/
theorem doubled_wrapper_unit_rejected (R : List RMono) (a : Nat) :
    decideSuccUnit [⟨2, 0, 1⟩] R a = false := by
  have h1 : ¬ HasYSquare [(⟨2, 0, 1⟩ : WMono)] := by decide
  have h2 : ¬ HasYPayload [(⟨2, 0, 1⟩ : WMono)] := by decide
  have hw : wLin [(⟨2, 0, 1⟩ : WMono)] 0 = 2 := by decide
  simp [decideSuccUnit, decideSuccAff, h1, h2, hw]

/-- The wrapper `2 * y + s + 1`. -/
def residualW : List WMono := [⟨1, 0, 0⟩, ⟨1, 1, 0⟩, ⟨2, 0, 1⟩]

/-- The recursor `(b + s + 2) * (n + 1) ^ 2`, expanded. -/
def residualR : List RMono :=
  [⟨1, 1, 0, 2⟩, ⟨2, 1, 0, 1⟩, ⟨1, 1, 0, 0⟩, ⟨1, 0, 1, 2⟩, ⟨2, 0, 1, 1⟩, ⟨1, 0, 1, 0⟩,
    ⟨2, 0, 0, 2⟩, ⟨4, 0, 0, 1⟩, ⟨2, 0, 0, 0⟩]

/-- The recursor `n ^ 2 + 1`. -/
def residualRFail : List RMono := [⟨1, 0, 0, 2⟩, ⟨1, 0, 0, 0⟩]

theorem wEval_residualW (s y : Nat) : wEval residualW s y = 2 * y + s + 1 := by
  simp [residualW, wEval]
  ring

theorem rEval_residualR (b s n : Nat) : rEval residualR b s n = (b + s + 2) * (n + 1) ^ 2 := by
  simp [residualR, rEval]
  ring

/-- A member of the open class for `β = 2` that orients the successor rule. -/
theorem residual_orienting_member :
    decideSuccAff residualW residualR 2 1 = none ∧ OrientsSucc residualW residualR 2 1 := by
  refine ⟨by decide, fun b s n => ?_⟩
  rw [wEval_residualW, rEval_residualR, rEval_residualR]
  have hX : b + s + 2 ≤ (b + s + 2) * (n + 1) ^ 2 :=
    Nat.le_mul_of_pos_right _ (by positivity)
  have e : (b + s + 2) * (2 * n + 1 + 1) ^ 2 = 4 * ((b + s + 2) * (n + 1) ^ 2) := by ring
  rw [e]
  omega

/-- A member of the open class for `β = 2` that does not orient the successor rule. -/
theorem residual_nonorienting_member :
    decideSuccAff residualW residualRFail 2 1 = none ∧
      ¬ OrientsSucc residualW residualRFail 2 1 := by
  refine ⟨by decide, fun h => ?_⟩
  have h0 := h 0 0 0
  exact absurd h0 (by decide)

/-! ## Transport to arbitrary signatures (P2.10) -/

/-- Over any first-order signature, a signature interpretation whose schema part is a
polynomial interpretation with unit successor orients every root step of the signature schema
exactly when `decideRootUnit` accepts; the inert operation is arbitrary. -/
theorem sig_decideRootUnit_iff {ι : Type u} {arity : ι → Nat}
    (I : SignatureGeneric.SigInterpretation ι arity Nat) {z a : Nat} {W : List WMono}
    {R : List RMono} (hI : I.toInterpretation = polyInterpretation z 1 a W R) :
    decideRootUnit z a W R = true ↔
      ∀ (ρ : Fin 3 → Nat) (t u : SignatureGeneric.SigTerm ι arity (Fin 3)),
        SignatureGeneric.SigRootStep t u → I.eval ρ u < I.eval ρ t := by
  rw [decideRootUnit_iff, ← hI]
  constructor
  · intro h ρ t u hs
    exact SignatureGeneric.sig_eval_rootStep_decreases I h ρ hs
  · intro h
    refine ⟨fun b s => ?_, fun b s n => ?_⟩
    · have hz := h ![b, s, 0] (.recur (.var 0) (.var 1) .zero) (.var 0) (.recurZero _ _)
      simpa [SignatureGeneric.SigInterpretation.eval] using hz
    · have hs := h ![b, s, n] (.recur (.var 0) (.var 1) (.succ (.var 2)))
        (.wrap (.var 1) (.recur (.var 0) (.var 1) (.var 2))) (.recurSucc _ _ _)
      simpa [SignatureGeneric.SigInterpretation.eval] using hs

/-! ## The restricted-quadratic verdict -/

/-- The restricted-quadratic recursor `r0 + rb * b + rs * s + rn * n + q * n ^ 2`. -/
def quadraticR (r0 rb rs rn q : Nat) : List RMono :=
  [⟨r0, 0, 0, 0⟩, ⟨rb, 1, 0, 0⟩, ⟨rs, 0, 1, 0⟩, ⟨rn, 0, 0, 1⟩, ⟨q, 0, 0, 2⟩]

theorem wEval_affineW (α βw γ s y : Nat) : wEval (affineW α βw γ) s y = α + βw * s + γ * y := by
  simp [affineW, wEval]
  ring

theorem rEval_quadraticR_base (r0 rb rs rn q s : Nat) :
    rEval (quadraticR r0 rb rs rn q) 0 s 0 = r0 + rs * s := by
  simp [quadraticR, rEval]

theorem rEval_quadraticR (r0 rb rs rn q s n : Nat) :
    rEval (quadraticR r0 rb rs rn q) 0 s n = r0 + rs * s + (rn * n + q * n ^ 2) := by
  simp [quadraticR, rEval]
  ring

/-- Retentive affine wrappers (`βw ≥ 1`, `γ ≥ 1`) over restricted-quadratic recursors are rejected
under the unit successor: the successor gain `rn * a + q * a ^ 2` does not grow with the payload,
and the payload `s = rn * a + q * a ^ 2` fails the rule. -/
theorem quadratic_retentive_rejected (α βw γ r0 rb rs rn q a : Nat) (hβw : 1 ≤ βw) (hγ : 1 ≤ γ) :
    decideSuccUnit (affineW α βw γ) (quadraticR r0 rb rs rn q) a = false := by
  cases hd : decideSuccUnit (affineW α βw γ) (quadraticR r0 rb rs rn q) a with
  | false => rfl
  | true =>
    exfalso
    have hor := (decideSuccUnit_iff _ _ a).1 hd
    have h := hor 0 (rn * a + q * a ^ 2) 0
    rw [wEval_affineW, rEval_quadraticR_base, Nat.zero_add, rEval_quadraticR] at h
    have h1 : rn * a + q * a ^ 2 ≤ βw * (rn * a + q * a ^ 2) := Nat.le_mul_of_pos_left _ hβw
    have h2 : r0 + rs * (rn * a + q * a ^ 2) ≤ γ * (r0 + rs * (rn * a + q * a ^ 2)) :=
      Nat.le_mul_of_pos_left _ hγ
    omega

end OperatorKO7.Methods.OrientationClosure.PolynomialOrientationDecision
