import OperatorKO7.Meta.Methods.OrientationClosure.CertificateLanguage

/-!
# An exact checker for polynomial certificates

Theorem 6.7 of the Orientation Boundary paper states that the polynomial checker accepts a
certificate exactly when the interpretation orients both root rules and is strictly monotone in
every wrapper and recursor argument. The checker `checkPoly` of `CertificateLanguage` tests for a
positive linear monomial in each argument, and `checkPoly_iff_needs_multilinear` shows that it
reaches the equivalence on multilinear certificates only.

A natural-coefficient polynomial is strictly increasing in one argument, at every value of the
other arguments, exactly when it has a positive monomial that is a pure power of that argument: at
the value zero of the other arguments only the pure monomials survive. The checker below tests for
such monomials. It accepts exactly the certificates that orient both root rules and are strictly
monotone in every argument, on every polynomial certificate, and it agrees with `checkPoly` on
multilinear certificates.
-/

set_option autoImplicit false

namespace OperatorKO7.Methods.OrientationClosure.AuditUpgrades.ExactPolynomialChecker

open OperatorKO7.Methods.OrientationClosure.SchemaCore
open OperatorKO7.Methods.OrientationClosure.InterpretationLaws
open OperatorKO7.Methods.OrientationClosure.PolynomialOrientationDecision
open OperatorKO7.Methods.OrientationClosure.CertificateLanguage
open OperatorKO7.Methods.OrientationClosure.DependencyPairSoundness
open OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs

/-! ## The pure-power test -/

/-- Each wrapper and recursor argument has a positive monomial that is a pure power of it. -/
def PurePowers (W : List WMono) (R : List RMono) : Prop :=
  (∃ m ∈ W, 1 ≤ m.coeff ∧ 1 ≤ m.sDeg ∧ m.yDeg = 0) ∧
    (∃ m ∈ W, 1 ≤ m.coeff ∧ m.sDeg = 0 ∧ 1 ≤ m.yDeg) ∧
    (∃ m ∈ R, 1 ≤ m.coeff ∧ 1 ≤ m.bDeg ∧ m.sDeg = 0 ∧ m.nDeg = 0) ∧
    (∃ m ∈ R, 1 ≤ m.coeff ∧ m.bDeg = 0 ∧ 1 ≤ m.sDeg ∧ m.nDeg = 0) ∧
    (∃ m ∈ R, 1 ≤ m.coeff ∧ m.bDeg = 0 ∧ m.sDeg = 0 ∧ 1 ≤ m.nDeg)

/-- Executable form of `PurePowers` (`purePowers_iff`). -/
def purePowers (W : List WMono) (R : List RMono) : Bool :=
  W.any (fun m => decide (1 ≤ m.coeff ∧ 1 ≤ m.sDeg ∧ m.yDeg = 0)) &&
    W.any (fun m => decide (1 ≤ m.coeff ∧ m.sDeg = 0 ∧ 1 ≤ m.yDeg)) &&
    R.any (fun m => decide (1 ≤ m.coeff ∧ 1 ≤ m.bDeg ∧ m.sDeg = 0 ∧ m.nDeg = 0)) &&
    R.any (fun m => decide (1 ≤ m.coeff ∧ m.bDeg = 0 ∧ 1 ≤ m.sDeg ∧ m.nDeg = 0)) &&
    R.any (fun m => decide (1 ≤ m.coeff ∧ m.bDeg = 0 ∧ m.sDeg = 0 ∧ 1 ≤ m.nDeg))

theorem purePowers_iff (W : List WMono) (R : List RMono) :
    purePowers W R = true ↔ PurePowers W R := by
  simp only [purePowers, PurePowers, Bool.and_eq_true, List.any_eq_true, decide_eq_true_eq,
    and_assoc]

/-! ## Strict monotonicity from pure powers -/

theorem wEval_strict_s_pure (W : List WMono) {s s' : Nat} (y : Nat) (hs : s < s')
    (hW : ∃ m ∈ W, 1 ≤ m.coeff ∧ 1 ≤ m.sDeg ∧ m.yDeg = 0) : wEval W s y < wEval W s' y := by
  induction W with
  | nil =>
    obtain ⟨m, hm, -⟩ := hW
    simp at hm
  | cons m p ih =>
    simp only [wEval]
    obtain ⟨m', hm', hc, hsd, hyd⟩ := hW
    rcases List.mem_cons.1 hm' with heq | hp
    · rw [heq] at hc hsd hyd
      have hpow : s ^ m.sDeg < s' ^ m.sDeg := Nat.pow_lt_pow_left hs (by omega)
      have h1 : m.coeff * s ^ m.sDeg * y ^ m.yDeg < m.coeff * s' ^ m.sDeg * y ^ m.yDeg := by
        rw [hyd, pow_zero, mul_one, mul_one]
        nlinarith
      exact Nat.add_lt_add_of_lt_of_le h1 (wEval_mono p hs.le le_rfl)
    · have h1 : m.coeff * s ^ m.sDeg * y ^ m.yDeg ≤ m.coeff * s' ^ m.sDeg * y ^ m.yDeg :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hs.le _))
      exact Nat.add_lt_add_of_le_of_lt h1 (ih ⟨m', hp, hc, hsd, hyd⟩)

theorem wEval_strict_y_pure (W : List WMono) (s : Nat) {y y' : Nat} (hy : y < y')
    (hW : ∃ m ∈ W, 1 ≤ m.coeff ∧ m.sDeg = 0 ∧ 1 ≤ m.yDeg) : wEval W s y < wEval W s y' := by
  induction W with
  | nil =>
    obtain ⟨m, hm, -⟩ := hW
    simp at hm
  | cons m p ih =>
    simp only [wEval]
    obtain ⟨m', hm', hc, hsd, hyd⟩ := hW
    rcases List.mem_cons.1 hm' with heq | hp
    · rw [heq] at hc hsd hyd
      have hpow : y ^ m.yDeg < y' ^ m.yDeg := Nat.pow_lt_pow_left hy (by omega)
      have h1 : m.coeff * s ^ m.sDeg * y ^ m.yDeg < m.coeff * s ^ m.sDeg * y' ^ m.yDeg := by
        rw [hsd, pow_zero, mul_one]
        nlinarith
      exact Nat.add_lt_add_of_lt_of_le h1 (wEval_mono p le_rfl hy.le)
    · have h1 : m.coeff * s ^ m.sDeg * y ^ m.yDeg ≤ m.coeff * s ^ m.sDeg * y' ^ m.yDeg :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hy.le _)
      exact Nat.add_lt_add_of_le_of_lt h1 (ih ⟨m', hp, hc, hsd, hyd⟩)

theorem rEval_strict_b_pure (R : List RMono) {b b' : Nat} (s n : Nat) (hb : b < b')
    (hR : ∃ m ∈ R, 1 ≤ m.coeff ∧ 1 ≤ m.bDeg ∧ m.sDeg = 0 ∧ m.nDeg = 0) :
    rEval R b s n < rEval R b' s n := by
  induction R with
  | nil =>
    obtain ⟨m, hm, -⟩ := hR
    simp at hm
  | cons m p ih =>
    simp only [rEval]
    obtain ⟨m', hm', hc, hbd, hsd, hnd⟩ := hR
    rcases List.mem_cons.1 hm' with heq | hp
    · rw [heq] at hc hbd hsd hnd
      have hpow : b ^ m.bDeg < b' ^ m.bDeg := Nat.pow_lt_pow_left hb (by omega)
      have h1 : m.coeff * b ^ m.bDeg * s ^ m.sDeg * n ^ m.nDeg <
          m.coeff * b' ^ m.bDeg * s ^ m.sDeg * n ^ m.nDeg := by
        rw [hsd, hnd, pow_zero, pow_zero, mul_one, mul_one]
        nlinarith
      exact Nat.add_lt_add_of_lt_of_le h1 (rEval_mono p hb.le le_rfl le_rfl)
    · have h1 : m.coeff * b ^ m.bDeg * s ^ m.sDeg * n ^ m.nDeg ≤
          m.coeff * b' ^ m.bDeg * s ^ m.sDeg * n ^ m.nDeg :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
          (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hb.le _)))
      exact Nat.add_lt_add_of_le_of_lt h1 (ih ⟨m', hp, hc, hbd, hsd, hnd⟩)

theorem rEval_strict_s_pure (R : List RMono) (b : Nat) {s s' : Nat} (n : Nat) (hs : s < s')
    (hR : ∃ m ∈ R, 1 ≤ m.coeff ∧ m.bDeg = 0 ∧ 1 ≤ m.sDeg ∧ m.nDeg = 0) :
    rEval R b s n < rEval R b s' n := by
  induction R with
  | nil =>
    obtain ⟨m, hm, -⟩ := hR
    simp at hm
  | cons m p ih =>
    simp only [rEval]
    obtain ⟨m', hm', hc, hbd, hsd, hnd⟩ := hR
    rcases List.mem_cons.1 hm' with heq | hp
    · rw [heq] at hc hbd hsd hnd
      have hpow : s ^ m.sDeg < s' ^ m.sDeg := Nat.pow_lt_pow_left hs (by omega)
      have h1 : m.coeff * b ^ m.bDeg * s ^ m.sDeg * n ^ m.nDeg <
          m.coeff * b ^ m.bDeg * s' ^ m.sDeg * n ^ m.nDeg := by
        rw [hbd, hnd, pow_zero, pow_zero, mul_one, mul_one]
        nlinarith
      exact Nat.add_lt_add_of_lt_of_le h1 (rEval_mono p le_rfl hs.le le_rfl)
    · have h1 : m.coeff * b ^ m.bDeg * s ^ m.sDeg * n ^ m.nDeg ≤
          m.coeff * b ^ m.bDeg * s' ^ m.sDeg * n ^ m.nDeg :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hs.le _))
      exact Nat.add_lt_add_of_le_of_lt h1 (ih ⟨m', hp, hc, hbd, hsd, hnd⟩)

theorem rEval_strict_n_pure (R : List RMono) (b s : Nat) {n n' : Nat} (hn : n < n')
    (hR : ∃ m ∈ R, 1 ≤ m.coeff ∧ m.bDeg = 0 ∧ m.sDeg = 0 ∧ 1 ≤ m.nDeg) :
    rEval R b s n < rEval R b s n' := by
  induction R with
  | nil =>
    obtain ⟨m, hm, -⟩ := hR
    simp at hm
  | cons m p ih =>
    simp only [rEval]
    obtain ⟨m', hm', hc, hbd, hsd, hnd⟩ := hR
    rcases List.mem_cons.1 hm' with heq | hp
    · rw [heq] at hc hbd hsd hnd
      have hpow : n ^ m.nDeg < n' ^ m.nDeg := Nat.pow_lt_pow_left hn (by omega)
      have h1 : m.coeff * b ^ m.bDeg * s ^ m.sDeg * n ^ m.nDeg <
          m.coeff * b ^ m.bDeg * s ^ m.sDeg * n' ^ m.nDeg := by
        rw [hbd, hsd, pow_zero, pow_zero, mul_one, mul_one]
        nlinarith
      exact Nat.add_lt_add_of_lt_of_le h1 (rEval_mono p le_rfl le_rfl hn.le)
    · have h1 : m.coeff * b ^ m.bDeg * s ^ m.sDeg * n ^ m.nDeg ≤
          m.coeff * b ^ m.bDeg * s ^ m.sDeg * n' ^ m.nDeg :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hn.le _)
      exact Nat.add_lt_add_of_le_of_lt h1 (ih ⟨m', hp, hc, hbd, hsd, hnd⟩)

theorem purePowers_strictContextLaws {z a : Nat} {W : List WMono} {R : List RMono}
    (h : PurePowers W R) : StrictContextLaws (polyInterpretation z 1 a W R) (· < ·) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y hxy
    show 1 * x + a < 1 * y + a
    omega
  · intro x y w hxy
    exact wEval_strict_s_pure W w hxy h1
  · intro w x y hxy
    exact wEval_strict_y_pure W w hxy h2
  · intro x y s n hxy
    exact rEval_strict_b_pure R s n hxy h3
  · intro b x y n hxy
    exact rEval_strict_s_pure R b n hxy h4
  · intro b s x y hxy
    exact rEval_strict_n_pure R b s hxy h5

/-! ## Flatness without pure powers -/

theorem wEval_flat_s (W : List WMono)
    (hno : ∀ m ∈ W, ¬ (1 ≤ m.coeff ∧ 1 ≤ m.sDeg ∧ m.yDeg = 0)) (s s' : Nat) :
    wEval W s 0 = wEval W s' 0 := by
  induction W with
  | nil => rfl
  | cons m p ih =>
    simp only [wEval]
    rw [ih (fun m' hm' => hno m' (by simp [hm']))]
    have hm := hno m (by simp)
    congr 1
    by_cases hy : m.yDeg = 0
    · by_cases hc : m.coeff = 0
      · simp [hc]
      · have hsd : m.sDeg = 0 := by
          by_contra hsd
          exact hm ⟨by omega, by omega, hy⟩
        simp [hsd]
    · have h0 : (0 : Nat) ^ m.yDeg = 0 := Nat.zero_pow (Nat.pos_of_ne_zero hy)
      simp [h0]

theorem wEval_flat_y (W : List WMono)
    (hno : ∀ m ∈ W, ¬ (1 ≤ m.coeff ∧ m.sDeg = 0 ∧ 1 ≤ m.yDeg)) (y y' : Nat) :
    wEval W 0 y = wEval W 0 y' := by
  induction W with
  | nil => rfl
  | cons m p ih =>
    simp only [wEval]
    rw [ih (fun m' hm' => hno m' (by simp [hm']))]
    have hm := hno m (by simp)
    congr 1
    by_cases hs : m.sDeg = 0
    · by_cases hc : m.coeff = 0
      · simp [hc]
      · have hyd : m.yDeg = 0 := by
          by_contra hyd
          exact hm ⟨by omega, hs, by omega⟩
        simp [hyd]
    · have h0 : (0 : Nat) ^ m.sDeg = 0 := Nat.zero_pow (Nat.pos_of_ne_zero hs)
      simp [h0]

theorem rEval_flat_b (R : List RMono)
    (hno : ∀ m ∈ R, ¬ (1 ≤ m.coeff ∧ 1 ≤ m.bDeg ∧ m.sDeg = 0 ∧ m.nDeg = 0)) (b b' : Nat) :
    rEval R b 0 0 = rEval R b' 0 0 := by
  induction R with
  | nil => rfl
  | cons m p ih =>
    simp only [rEval]
    rw [ih (fun m' hm' => hno m' (by simp [hm']))]
    have hm := hno m (by simp)
    congr 1
    by_cases hs : m.sDeg = 0
    · by_cases hn : m.nDeg = 0
      · by_cases hc : m.coeff = 0
        · simp [hc]
        · have hbd : m.bDeg = 0 := by
            by_contra hbd
            exact hm ⟨by omega, by omega, hs, hn⟩
          simp [hbd]
      · have h0 : (0 : Nat) ^ m.nDeg = 0 := Nat.zero_pow (Nat.pos_of_ne_zero hn)
        simp [h0]
    · have h0 : (0 : Nat) ^ m.sDeg = 0 := Nat.zero_pow (Nat.pos_of_ne_zero hs)
      simp [h0]

theorem rEval_flat_s (R : List RMono)
    (hno : ∀ m ∈ R, ¬ (1 ≤ m.coeff ∧ m.bDeg = 0 ∧ 1 ≤ m.sDeg ∧ m.nDeg = 0)) (s s' : Nat) :
    rEval R 0 s 0 = rEval R 0 s' 0 := by
  induction R with
  | nil => rfl
  | cons m p ih =>
    simp only [rEval]
    rw [ih (fun m' hm' => hno m' (by simp [hm']))]
    have hm := hno m (by simp)
    congr 1
    by_cases hb : m.bDeg = 0
    · by_cases hn : m.nDeg = 0
      · by_cases hc : m.coeff = 0
        · simp [hc]
        · have hsd : m.sDeg = 0 := by
            by_contra hsd
            exact hm ⟨by omega, hb, by omega, hn⟩
          simp [hsd]
      · have h0 : (0 : Nat) ^ m.nDeg = 0 := Nat.zero_pow (Nat.pos_of_ne_zero hn)
        simp [h0]
    · have h0 : (0 : Nat) ^ m.bDeg = 0 := Nat.zero_pow (Nat.pos_of_ne_zero hb)
      simp [h0]

theorem rEval_flat_n (R : List RMono)
    (hno : ∀ m ∈ R, ¬ (1 ≤ m.coeff ∧ m.bDeg = 0 ∧ m.sDeg = 0 ∧ 1 ≤ m.nDeg)) (n n' : Nat) :
    rEval R 0 0 n = rEval R 0 0 n' := by
  induction R with
  | nil => rfl
  | cons m p ih =>
    simp only [rEval]
    rw [ih (fun m' hm' => hno m' (by simp [hm']))]
    have hm := hno m (by simp)
    congr 1
    by_cases hb : m.bDeg = 0
    · by_cases hs : m.sDeg = 0
      · by_cases hc : m.coeff = 0
        · simp [hc]
        · have hnd : m.nDeg = 0 := by
            by_contra hnd
            exact hm ⟨by omega, hb, hs, by omega⟩
          simp [hnd]
      · have h0 : (0 : Nat) ^ m.sDeg = 0 := Nat.zero_pow (Nat.pos_of_ne_zero hs)
        simp [h0]
    · have h0 : (0 : Nat) ^ m.bDeg = 0 := Nat.zero_pow (Nat.pos_of_ne_zero hb)
      simp [h0]

/--
Proves: a unit-successor polynomial interpretation of the free recursor is strictly monotone in
every constructor argument exactly when each wrapper and recursor argument has a positive monomial
that is a pure power of it.
Does not prove: anything about orientation; that is `decideRootUnit_iff`.
Relation: the strict order of `Nat`, read through every one-hole constructor context.
Closure: every constructor argument.
Strategy: pure powers give strict growth; without one, the polynomial is constant in that argument
at the value zero of the other arguments.
Trust: Lean kernel.
Scope: every natural-coefficient polynomial certificate with unit successor slope.
-/
theorem purePowers_iff_strictContextLaws (z a : Nat) (W : List WMono) (R : List RMono) :
    PurePowers W R ↔ StrictContextLaws (polyInterpretation z 1 a W R) (· < ·) := by
  constructor
  · exact purePowers_strictContextLaws
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · by_contra hno
      have hflat := wEval_flat_s W (fun m hm hc => hno ⟨m, hm, hc⟩) 0 1
      have hlt := h.wrapLeft (x := 0) (y := 1) (z := 0) (by norm_num)
      change wEval W 0 0 < wEval W 1 0 at hlt
      omega
    · by_contra hno
      have hflat := wEval_flat_y W (fun m hm hc => hno ⟨m, hm, hc⟩) 0 1
      have hlt := h.wrapRight (z := 0) (x := 0) (y := 1) (by norm_num)
      change wEval W 0 0 < wEval W 0 1 at hlt
      omega
    · by_contra hno
      have hflat := rEval_flat_b R (fun m hm hc => hno ⟨m, hm, hc⟩) 0 1
      have hlt := h.recurBase (x := 0) (y := 1) (s := 0) (n := 0) (by norm_num)
      change rEval R 0 0 0 < rEval R 1 0 0 at hlt
      omega
    · by_contra hno
      have hflat := rEval_flat_s R (fun m hm hc => hno ⟨m, hm, hc⟩) 0 1
      have hlt := h.recurStep (b := 0) (x := 0) (y := 1) (n := 0) (by norm_num)
      change rEval R 0 0 0 < rEval R 0 1 0 at hlt
      omega
    · by_contra hno
      have hflat := rEval_flat_n R (fun m hm hc => hno ⟨m, hm, hc⟩) 0 1
      have hlt := h.recurCounter (b := 0) (s := 0) (x := 0) (y := 1) (by norm_num)
      change rEval R 0 0 0 < rEval R 0 0 1 at hlt
      omega

/-! ## The exact checker -/

/-- The exact polynomial checker: the unit-slope decision of both root rules and the pure-power
test. -/
def checkPolyExact (z a : Nat) (W : List WMono) (R : List RMono) : Bool :=
  decideRootUnit z a W R && purePowers W R

/--
Proves: on every polynomial certificate with unit successor slope, the exact checker accepts
exactly when the interpretation orients both root rules of the free recursor and is strictly
monotone in every constructor argument.
Does not prove: anything at successor slopes above one.
Relation: `RootStep` of the free recursor for orientation; every constructor context for the laws.
Closure: root for orientation; every constructor argument for monotonicity.
Strategy: `decideRootUnit_iff` and `purePowers_iff_strictContextLaws`.
Trust: Lean kernel.
Scope: every natural-coefficient polynomial certificate with unit successor slope.
-/
theorem checkPolyExact_iff (z a : Nat) (W : List WMono) (R : List RMono) :
    checkPolyExact z a W R = true ↔
      RootRuleOrients (polyInterpretation z 1 a W R) (· < ·) ∧
        StrictContextLaws (polyInterpretation z 1 a W R) (· < ·) := by
  rw [checkPolyExact, Bool.and_eq_true, decideRootUnit_iff, purePowers_iff,
    purePowers_iff_strictContextLaws z a W R]

theorem checkPolyExact_sound {z a : Nat} {W : List WMono} {R : List RMono}
    (h : checkPolyExact z a W R = true) (ν : Type) :
    WellFounded (fun u t : FreeTerm ν => ContextStep t u) := by
  obtain ⟨hroot, hlaws⟩ := (checkPolyExact_iff z a W R).1 h
  exact contextStep_reverse_wellFounded hroot hlaws Nat.lt_wfRel.wf (fun _ => 0)

theorem checkPolyExact_eq_checkPoly_of_multilinear {W : List WMono} {R : List RMono}
    (hml : Multilinear W R) (z a : Nat) : checkPolyExact z a W R = checkPoly z a W R := by
  rw [Bool.eq_iff_iff, checkPolyExact_iff, checkPoly_iff_orients_strictContextLaws hml]

theorem squareWrapper_accepted_exact :
    checkPolyExact 0 1 squareWrapperW squareWrapperR = true :=
  (checkPolyExact_iff 0 1 squareWrapperW squareWrapperR).2
    ⟨squareWrapper_orients, squareWrapper_strictContextLaws⟩

/-! ## The certificate language with the exact checker -/

/-- The certificate checker with the exact polynomial branch. -/
def checkExact : Certificate → Bool
  | .poly z a W R => checkPolyExact z a W R
  | .matrix d M => check (.matrix d M)
  | .kbo K => check (.kbo K)
  | .dpSubterm proj => check (.dpSubterm proj)

theorem checkExact_sound : ∀ c : Certificate, checkExact c = true → Proves c
  | .poly z a W R, h => checkPolyExact_sound (z := z) (a := a) (W := W) (R := R) h Nat
  | .matrix d M, h => check_sound (.matrix d M) h
  | .kbo K, h => check_sound (.kbo K) h
  | .dpSubterm proj, h => check_sound (.dpSubterm proj) h

theorem affine_multilinear (α βw γ r0 rb rs rn : Nat) :
    Multilinear (affineW α βw γ) (multilinearR r0 rb rs rn 0 0 0 0) := by
  refine ⟨?_, ?_⟩
  · intro m hm _
    simp only [affineW, List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with rfl | rfl | rfl <;> simp
  · intro m hm _
    simp only [multilinearR, List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem region_multilinear : Multilinear regionW (regionR 1 2) :=
  (multilinearB_iff _ _).1 (by decide)

/--
Proves: Theorem 6.7 of the Orientation Boundary paper with the exact polynomial checker: no
affine polynomial certificate that keeps both wrapper arguments, no matrix certificate and no
Knuth-Bendix certificate is accepted; the counter-projection dependency-pair certificate and the
coupled polynomial certificate are accepted; every accepted certificate proves termination of the
free recursor; on every polynomial certificate the checker accepts exactly the interpretations that
orient both root rules and are strictly monotone in every argument; on multilinear certificates it
agrees with `check`; and it accepts the square-wrapper certificate that `check` rejects.
Does not prove: acceptance of any matrix or Knuth-Bendix certificate.
Relation: `ContextStep` of the free recursor (`Proves`), `RootStep` for orientation.
Closure: every constructor context for termination; root for orientation.
Strategy: the exact equivalence `checkPolyExact_iff`, and the theorems of `CertificateLanguage` for
the other three kinds.
Trust: Lean kernel.
Scope: the four certificate kinds over the two rules of the free recursor; polynomial certificates
with unit successor slope.
-/
theorem certificate_boundary_exact :
    (∀ z a α βw γ r0 rb rs rn : Nat, 1 ≤ βw → 1 ≤ γ →
        checkExact (.poly z a (affineW α βw γ) (multilinearR r0 rb rs rn 0 0 0 0)) = false) ∧
      (∀ (d : Nat) (M : MatrixCert d), checkExact (.matrix d M) = false) ∧
      (∀ K : KBOCert, checkExact (.kbo K) = false) ∧
      checkExact (.dpSubterm freeProj) = true ∧
      checkExact (.poly 0 1 regionW (regionR 1 2)) = true ∧
      (∀ c : Certificate, checkExact c = true → Proves c) ∧
      (∀ (z a : Nat) (W : List WMono) (R : List RMono),
        checkExact (.poly z a W R) = true ↔
          RootRuleOrients (polyInterpretation z 1 a W R) (· < ·) ∧
            StrictContextLaws (polyInterpretation z 1 a W R) (· < ·)) ∧
      (∀ (z a : Nat) (W : List WMono) (R : List RMono), Multilinear W R →
        checkExact (.poly z a W R) = check (.poly z a W R)) ∧
      checkExact (.poly 0 1 squareWrapperW squareWrapperR) = true ∧
      check (.poly 0 1 squareWrapperW squareWrapperR) = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_, checkExact_sound, ?_, ?_, squareWrapper_accepted_exact,
    squareWrapper_rejected⟩
  · intro z a α βw γ r0 rb rs rn hβw hγ
    show checkPolyExact z a (affineW α βw γ) (multilinearR r0 rb rs rn 0 0 0 0) = false
    rw [checkPolyExact_eq_checkPoly_of_multilinear (affine_multilinear α βw γ r0 rb rs rn)]
    exact affine_certificate_rejected z a α βw γ r0 rb rs rn hβw hγ
  · intro d M
    exact matrix_certificate_rejected d M
  · intro K
    exact kbo_certificate_rejected K
  · exact counter_certificate_accepted
  · show checkPolyExact 0 1 regionW (regionR 1 2) = true
    rw [checkPolyExact_eq_checkPoly_of_multilinear region_multilinear]
    exact region_certificate_accepted
  · intro z a W R
    exact checkPolyExact_iff z a W R
  · intro z a W R hml
    exact checkPolyExact_eq_checkPoly_of_multilinear hml z a

end OperatorKO7.Methods.OrientationClosure.AuditUpgrades.ExactPolynomialChecker
