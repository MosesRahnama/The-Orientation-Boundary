import OperatorKO7.Meta.Methods.OrientationClosure.PolynomialOrientationDecision
import OperatorKO7.Meta.Methods.OrientationClosure.CouplingTheorem
import OperatorKO7.Meta.Methods.OrientationClosure.MethodRowsDependencyPairs
import OperatorKO7.Meta.Methods.OrientationClosure.MethodRowsKBO
import Mathlib.Tactic

/-!
# The orientation boundary in a certificate language

Certificates for termination of the free recursor come in four kinds, as in the certification
format of termination tools: a natural-coefficient polynomial interpretation with successor
`n ↦ n + a`, a matrix interpretation of any dimension, a Knuth-Bendix order, and dependency pairs
with the subterm criterion for a projection. `check` is an executable checker.

* Polynomial certificates. The checker is the decision procedure of T-DEC-1 together with a test
  for positive linear monomials in every argument. An accepted certificate proves termination of
  the contextual relation (`checkPoly_sound`) and is an interpretation that orients both root
  rules and is strictly monotone in every argument (`checkPoly_orients_strictContextLaws`). On the
  multilinear class, where every positive monomial has degree at most one in each variable, the
  monomial test is equivalent to strict monotonicity (`linearMonomials_iff_strictContextLaws`), so
  the checker accepts exactly the interpretations that orient both root rules and are strictly
  monotone in every argument (`checkPoly_iff_orients_strictContextLaws`). The multilinear
  certificate `W = s + y + 1`, `R = 2n + sn + b + 1` orients both rules, is rejected, and is
  constant in `s` at counter `0` (`multilinearControl_rejected`,
  `multilinearControl_not_strictContextLaws`), so orientation alone does not characterize
  acceptance on the multilinear class (`orients_not_iff_checkPoly_on_multilinear`). Outside the
  class the wrapper `s ^ 2 + y + 1` gives an orienting, strictly monotone certificate that the
  checker rejects (`squareWrapper_rejected`, `checkPoly_iff_needs_multilinear`). On certificates
  that pass the monomial test, the checker accepts if and only if the interpretation orients both
  root rules (`checkPoly_complete`).
* No certificate of a direct class is accepted: retentive affine polynomial certificates, by the
  coupling inequality of P3.1 on the value schema (`affine_certificate_rejected`); matrix
  certificates, by the same inequality on the top-left entries (`matrix_certificate_rejected`);
  Knuth-Bendix certificates, by the variable condition of the successor rule
  (`kbo_certificate_rejected`, from `succRule_not_kboGt`).
* The Knuth-Bendix checker computes the order. `kboGtB` decides the Knuth-Bendix comparison
  `MethodRowsKBO.Gt (kboCore K)` built from the certificate's weights and precedence
  (`kboGtB_iff`), `kboAdmissibleB` decides the admissibility laws of those weights and that
  precedence (`kboAdmissibleB_iff`), and `checkKBO` accepts exactly the admissible certificates
  whose order orients both root rules (`checkKBO_iff`). The comparison reads the weights, the
  precedence and the lexicographic case (`kboWitness_lex`, `kboPrecHigh_orients`,
  `kboPrecLow_rejects`).
* The dependency-pair checker accepts a projection if and only if the subterm criterion holds for
  it, which happens if and only if it selects the counter (`checkDP_iff`); the counter projection
  is accepted and proves termination (`checkDP_sound`).
* The coupled polynomial certificate `(n + 1)(s + b + 2)` with wrapper `s + y + 1` is accepted
  (`region_certificate_accepted`).
-/

set_option autoImplicit false

namespace OperatorKO7.Methods.OrientationClosure.CertificateLanguage

open OperatorKO7.Meta.Rewriting
open OperatorKO7.StepDuplicating
open OperatorKO7.Methods.OrientationClosure.SchemaCore
open OperatorKO7.Methods.OrientationClosure.InterpretationLaws
open OperatorKO7.Methods.OrientationClosure.PolynomialOrientationDecision
open OperatorKO7.Methods.OrientationClosure.CouplingTheorem
open OperatorKO7.Methods.OrientationClosure.DependencyPairSoundness
open OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs

/-! ## Certificates -/

/-- A matrix interpretation of dimension `d + 1`: a constant vector and one matrix per argument
position for every free symbol. -/
structure MatrixCert (d : Nat) where
  const : FreeSym → Fin (d + 1) → Nat
  mat : FreeSym → Nat → Matrix (Fin (d + 1)) (Fin (d + 1)) Nat

/-- A Knuth-Bendix certificate: symbol weights, the variable weight and a precedence, read as
`f ≻ g` exactly when `prec g < prec f` (`kboCore`). -/
structure KBOCert where
  weight : FreeSym → Nat
  varWeight : Nat
  prec : FreeSym → Nat

/-- Certificates for termination of the free recursor. -/
inductive Certificate where
  | poly (z a : Nat) (W : List WMono) (R : List RMono)
  | matrix (d : Nat) (M : MatrixCert d)
  | kbo (K : KBOCert)
  | dpSubterm (proj : FreeSym → Nat)

/-! ## Polynomial certificates -/

/-- The wrapper has positive linear monomials in `s` and in `y`; the recursor has positive linear
monomials in `b`, in `s` and in `n`. -/
def linearMonomials (W : List WMono) (R : List RMono) : Bool :=
  W.any (fun m => decide (1 ≤ m.coeff) && m.sDeg == 1 && m.yDeg == 0) &&
    W.any (fun m => decide (1 ≤ m.coeff) && m.sDeg == 0 && m.yDeg == 1) &&
    R.any (fun m => decide (1 ≤ m.coeff) && m.bDeg == 1 && m.sDeg == 0 && m.nDeg == 0) &&
    R.any (fun m => decide (1 ≤ m.coeff) && m.bDeg == 0 && m.sDeg == 1 && m.nDeg == 0) &&
    R.any (fun m => decide (1 ≤ m.coeff) && m.bDeg == 0 && m.sDeg == 0 && m.nDeg == 1)

/-- The polynomial checker: the T-DEC-1 decision of both root rules and the monomial test. -/
def checkPoly (z a : Nat) (W : List WMono) (R : List RMono) : Bool :=
  decideRootUnit z a W R && linearMonomials W R

theorem wEval_mono (W : List WMono) {s s' y y' : Nat} (hs : s ≤ s') (hy : y ≤ y') :
    wEval W s y ≤ wEval W s' y' := by
  induction W with
  | nil => simp [wEval]
  | cons m p ih =>
    simp only [wEval]
    exact Nat.add_le_add
      (Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hs _)) (Nat.pow_le_pow_left hy _)) ih

theorem wEval_strict_s (W : List WMono) {s s' : Nat} (y : Nat) (hs : s < s')
    (hW : ∃ m ∈ W, 1 ≤ m.coeff ∧ m.sDeg = 1 ∧ m.yDeg = 0) : wEval W s y < wEval W s' y := by
  induction W with
  | nil =>
    obtain ⟨m, hm, -⟩ := hW
    simp at hm
  | cons m p ih =>
    simp only [wEval]
    obtain ⟨m', hm', hc, hsd, hyd⟩ := hW
    rcases List.mem_cons.1 hm' with heq | hp
    · rw [heq] at hc hsd hyd
      have h1 : m.coeff * s ^ m.sDeg * y ^ m.yDeg < m.coeff * s' ^ m.sDeg * y ^ m.yDeg := by
        rw [hsd, hyd, pow_one, pow_zero, mul_one, mul_one]
        nlinarith
      exact Nat.add_lt_add_of_lt_of_le h1 (wEval_mono p hs.le le_rfl)
    · have h1 : m.coeff * s ^ m.sDeg * y ^ m.yDeg ≤ m.coeff * s' ^ m.sDeg * y ^ m.yDeg :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hs.le _))
      exact Nat.add_lt_add_of_le_of_lt h1 (ih ⟨m', hp, hc, hsd, hyd⟩)

theorem wEval_strict_y (W : List WMono) (s : Nat) {y y' : Nat} (hy : y < y')
    (hW : ∃ m ∈ W, 1 ≤ m.coeff ∧ m.sDeg = 0 ∧ m.yDeg = 1) : wEval W s y < wEval W s y' := by
  induction W with
  | nil =>
    obtain ⟨m, hm, -⟩ := hW
    simp at hm
  | cons m p ih =>
    simp only [wEval]
    obtain ⟨m', hm', hc, hsd, hyd⟩ := hW
    rcases List.mem_cons.1 hm' with heq | hp
    · rw [heq] at hc hsd hyd
      have h1 : m.coeff * s ^ m.sDeg * y ^ m.yDeg < m.coeff * s ^ m.sDeg * y' ^ m.yDeg := by
        rw [hsd, hyd, pow_one, pow_zero, mul_one]
        nlinarith
      exact Nat.add_lt_add_of_lt_of_le h1 (wEval_mono p le_rfl hy.le)
    · have h1 : m.coeff * s ^ m.sDeg * y ^ m.yDeg ≤ m.coeff * s ^ m.sDeg * y' ^ m.yDeg :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hy.le _)
      exact Nat.add_lt_add_of_le_of_lt h1 (ih ⟨m', hp, hc, hsd, hyd⟩)

theorem rEval_strict_b (R : List RMono) {b b' : Nat} (s n : Nat) (hb : b < b')
    (hR : ∃ m ∈ R, 1 ≤ m.coeff ∧ m.bDeg = 1 ∧ m.sDeg = 0 ∧ m.nDeg = 0) :
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
      have h1 : m.coeff * b ^ m.bDeg * s ^ m.sDeg * n ^ m.nDeg <
          m.coeff * b' ^ m.bDeg * s ^ m.sDeg * n ^ m.nDeg := by
        rw [hbd, hsd, hnd, pow_one, pow_zero, pow_zero, mul_one, mul_one]
        nlinarith
      exact Nat.add_lt_add_of_lt_of_le h1 (rEval_mono p hb.le le_rfl le_rfl)
    · have h1 : m.coeff * b ^ m.bDeg * s ^ m.sDeg * n ^ m.nDeg ≤
          m.coeff * b' ^ m.bDeg * s ^ m.sDeg * n ^ m.nDeg :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
          (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hb.le _)))
      exact Nat.add_lt_add_of_le_of_lt h1 (ih ⟨m', hp, hc, hbd, hsd, hnd⟩)

theorem rEval_strict_s (R : List RMono) (b : Nat) {s s' : Nat} (n : Nat) (hs : s < s')
    (hR : ∃ m ∈ R, 1 ≤ m.coeff ∧ m.bDeg = 0 ∧ m.sDeg = 1 ∧ m.nDeg = 0) :
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
      have h1 : m.coeff * b ^ m.bDeg * s ^ m.sDeg * n ^ m.nDeg <
          m.coeff * b ^ m.bDeg * s' ^ m.sDeg * n ^ m.nDeg := by
        rw [hbd, hsd, hnd, pow_one, pow_zero, pow_zero, mul_one, mul_one]
        nlinarith
      exact Nat.add_lt_add_of_lt_of_le h1 (rEval_mono p le_rfl hs.le le_rfl)
    · have h1 : m.coeff * b ^ m.bDeg * s ^ m.sDeg * n ^ m.nDeg ≤
          m.coeff * b ^ m.bDeg * s' ^ m.sDeg * n ^ m.nDeg :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hs.le _))
      exact Nat.add_lt_add_of_le_of_lt h1 (ih ⟨m', hp, hc, hbd, hsd, hnd⟩)

theorem rEval_strict_n (R : List RMono) (b s : Nat) {n n' : Nat} (hn : n < n')
    (hR : ∃ m ∈ R, 1 ≤ m.coeff ∧ m.bDeg = 0 ∧ m.sDeg = 0 ∧ m.nDeg = 1) :
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
      have h1 : m.coeff * b ^ m.bDeg * s ^ m.sDeg * n ^ m.nDeg <
          m.coeff * b ^ m.bDeg * s ^ m.sDeg * n' ^ m.nDeg := by
        rw [hbd, hsd, hnd, pow_one, pow_zero, pow_zero, mul_one, mul_one]
        nlinarith
      exact Nat.add_lt_add_of_lt_of_le h1 (rEval_mono p le_rfl le_rfl hn.le)
    · have h1 : m.coeff * b ^ m.bDeg * s ^ m.sDeg * n ^ m.nDeg ≤
          m.coeff * b ^ m.bDeg * s ^ m.sDeg * n' ^ m.nDeg :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hn.le _)
      exact Nat.add_lt_add_of_le_of_lt h1 (ih ⟨m', hp, hc, hbd, hsd, hnd⟩)

/-- The monomial test gives strict monotonicity in every argument. -/
theorem poly_strictContextLaws {z a : Nat} {W : List WMono} {R : List RMono}
    (h : linearMonomials W R = true) :
    StrictContextLaws (polyInterpretation z 1 a W R) (· < ·) := by
  simp only [linearMonomials, Bool.and_eq_true, List.any_eq_true, decide_eq_true_eq,
    beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨m1, hm1, ⟨hc1, hs1⟩, hy1⟩, ⟨m2, hm2, ⟨hc2, hs2⟩, hy2⟩⟩, ⟨m3, hm3, ⟨⟨hc3, hb3⟩, hs3⟩, hn3⟩⟩,
    ⟨m4, hm4, ⟨⟨hc4, hb4⟩, hs4⟩, hn4⟩⟩, ⟨m5, hm5, ⟨⟨hc5, hb5⟩, hs5⟩, hn5⟩⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y hxy
    show 1 * x + a < 1 * y + a
    omega
  · intro x y w hxy
    exact wEval_strict_s W w hxy ⟨m1, hm1, hc1, hs1, hy1⟩
  · intro w x y hxy
    exact wEval_strict_y W w hxy ⟨m2, hm2, hc2, hs2, hy2⟩
  · intro x y s n hxy
    exact rEval_strict_b R s n hxy ⟨m3, hm3, hc3, hb3, hs3, hn3⟩
  · intro b x y n hxy
    exact rEval_strict_s R b n hxy ⟨m4, hm4, hc4, hb4, hs4, hn4⟩
  · intro b s x y hxy
    exact rEval_strict_n R b s hxy ⟨m5, hm5, hc5, hb5, hs5, hn5⟩

/-- Soundness: an accepted polynomial certificate proves termination of the contextual relation. -/
theorem checkPoly_sound {z a : Nat} {W : List WMono} {R : List RMono}
    (h : checkPoly z a W R = true) (ν : Type) :
    WellFounded (fun u t : FreeTerm ν => ContextStep t u) := by
  simp only [checkPoly, Bool.and_eq_true] at h
  exact contextStep_reverse_wellFounded ((decideRootUnit_iff z a W R).1 h.1)
    (poly_strictContextLaws h.2) Nat.lt_wfRel.wf (fun _ => 0)

/-- Completeness: on certificates that pass the monomial test, the checker accepts exactly the
interpretations that orient both root rules. -/
theorem checkPoly_complete {z a : Nat} {W : List WMono} {R : List RMono}
    (hm : linearMonomials W R = true) :
    checkPoly z a W R = true ↔ RootRuleOrients (polyInterpretation z 1 a W R) (· < ·) := by
  rw [checkPoly, hm, Bool.and_true, decideRootUnit_iff]

/-! ### Acceptance on the multilinear class

`linearMonomials` asks for a positive pure linear monomial in each wrapper and recursor argument,
and every such interpretation is strictly monotone in every argument (`poly_strictContextLaws`).
On the multilinear class the converse holds: a multilinear polynomial without a positive pure
monomial in one argument takes equal values at `0` and `1` in that argument at the value `0` of
the other arguments (`wEval_flat_s`, `wEval_flat_y`, `rEval_flat_b`, `rEval_flat_s`,
`rEval_flat_n`). -/

/-- The multilinear class of polynomial certificates: every monomial with a positive coefficient
has degree at most one in each variable.

Proves: nothing; a predicate on monomial lists.
Does not prove: orientation or monotonicity.
Relation: not applicable.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: monomials with coefficient `0` are unrestricted; they contribute `0` to every value. -/
def Multilinear (W : List WMono) (R : List RMono) : Prop :=
  (∀ m ∈ W, 1 ≤ m.coeff → m.sDeg ≤ 1 ∧ m.yDeg ≤ 1) ∧
    ∀ m ∈ R, 1 ≤ m.coeff → m.bDeg ≤ 1 ∧ m.sDeg ≤ 1 ∧ m.nDeg ≤ 1

/-- Executable membership test for the multilinear class (`multilinearB_iff`).

Proves: nothing; a Boolean test.
Does not prove: orientation or monotonicity.
Relation: not applicable.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: the monomial lists of a polynomial certificate. -/
def multilinearB (W : List WMono) (R : List RMono) : Bool :=
  W.all (fun m => decide (m.coeff = 0) || (decide (m.sDeg ≤ 1) && decide (m.yDeg ≤ 1))) &&
    R.all (fun m => decide (m.coeff = 0) ||
      (decide (m.bDeg ≤ 1) && decide (m.sDeg ≤ 1) && decide (m.nDeg ≤ 1)))

/-- The Boolean test decides the multilinear class.

Proves: `multilinearB W R = true ↔ Multilinear W R`.
Does not prove: orientation or monotonicity.
Relation: not applicable.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: every pair of monomial lists. -/
theorem multilinearB_iff (W : List WMono) (R : List RMono) :
    multilinearB W R = true ↔ Multilinear W R := by
  simp only [multilinearB, Multilinear, Bool.and_eq_true, Bool.or_eq_true, List.all_eq_true,
    decide_eq_true_eq]
  constructor
  · rintro ⟨hW, hR⟩
    refine ⟨fun m hm hc => ?_, fun m hm hc => ?_⟩
    · rcases hW m hm with h0 | h
      · omega
      · exact h
    · rcases hR m hm with h0 | h
      · omega
      · exact ⟨h.1.1, h.1.2, h.2⟩
  · rintro ⟨hW, hR⟩
    refine ⟨fun m hm => ?_, fun m hm => ?_⟩
    · by_cases hc : m.coeff = 0
      · exact Or.inl hc
      · exact Or.inr (hW m hm (Nat.one_le_iff_ne_zero.2 hc))
    · by_cases hc : m.coeff = 0
      · exact Or.inl hc
      · have h := hR m hm (Nat.one_le_iff_ne_zero.2 hc)
        exact Or.inr ⟨⟨h.1, h.2.1⟩, h.2.2⟩

/-- On the multilinear class, a wrapper without a positive monomial `c * s` takes the same value
at `s = 0` and at `s = 1` with `y = 0`.

Proves: `wEval W 1 0 = wEval W 0 0` under the two hypotheses.
Does not prove: equality at other arguments.
Relation: not applicable (polynomial evaluation).
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: wrapper lists with every positive monomial of degree at most one in `s` and in `y`. -/
theorem wEval_flat_s (W : List WMono) (hW : ∀ m ∈ W, 1 ≤ m.coeff → m.sDeg ≤ 1 ∧ m.yDeg ≤ 1)
    (hno : ¬ ∃ m ∈ W, 1 ≤ m.coeff ∧ m.sDeg = 1 ∧ m.yDeg = 0) :
    wEval W 1 0 = wEval W 0 0 := by
  induction W with
  | nil => rfl
  | cons m p ih =>
    simp only [wEval]
    have hp := ih (fun m' hm' => hW m' (List.mem_cons_of_mem _ hm'))
      (fun ⟨m', hm', h⟩ => hno ⟨m', List.mem_cons_of_mem _ hm', h⟩)
    rw [hp]
    congr 1
    by_cases hc : m.coeff = 0
    · simp [hc]
    · have hd := hW m List.mem_cons_self (Nat.one_le_iff_ne_zero.2 hc)
      have hn : ¬ (m.sDeg = 1 ∧ m.yDeg = 0) := fun h =>
        hno ⟨m, List.mem_cons_self, Nat.one_le_iff_ne_zero.2 hc, h.1, h.2⟩
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hd.2 with hy | hy
      · have hs : m.sDeg = 0 := by omega
        simp [hs, hy]
      · simp [hy]

/-- On the multilinear class, a wrapper without a positive monomial `c * y` takes the same value
at `y = 0` and at `y = 1` with `s = 0`.

Proves: `wEval W 0 1 = wEval W 0 0` under the two hypotheses.
Does not prove: equality at other arguments.
Relation: not applicable (polynomial evaluation).
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: wrapper lists with every positive monomial of degree at most one in `s` and in `y`. -/
theorem wEval_flat_y (W : List WMono) (hW : ∀ m ∈ W, 1 ≤ m.coeff → m.sDeg ≤ 1 ∧ m.yDeg ≤ 1)
    (hno : ¬ ∃ m ∈ W, 1 ≤ m.coeff ∧ m.sDeg = 0 ∧ m.yDeg = 1) :
    wEval W 0 1 = wEval W 0 0 := by
  induction W with
  | nil => rfl
  | cons m p ih =>
    simp only [wEval]
    have hp := ih (fun m' hm' => hW m' (List.mem_cons_of_mem _ hm'))
      (fun ⟨m', hm', h⟩ => hno ⟨m', List.mem_cons_of_mem _ hm', h⟩)
    rw [hp]
    congr 1
    by_cases hc : m.coeff = 0
    · simp [hc]
    · have hd := hW m List.mem_cons_self (Nat.one_le_iff_ne_zero.2 hc)
      have hn : ¬ (m.sDeg = 0 ∧ m.yDeg = 1) := fun h =>
        hno ⟨m, List.mem_cons_self, Nat.one_le_iff_ne_zero.2 hc, h.1, h.2⟩
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hd.1 with hs | hs
      · have hy : m.yDeg = 0 := by omega
        simp [hs, hy]
      · simp [hs]

/-- On the multilinear class, a recursor without a positive monomial `c * b` takes the same value
at `b = 0` and at `b = 1` with `s = n = 0`.

Proves: `rEval R 1 0 0 = rEval R 0 0 0` under the two hypotheses.
Does not prove: equality at other arguments.
Relation: not applicable (polynomial evaluation).
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: recursor lists with every positive monomial of degree at most one in each variable. -/
theorem rEval_flat_b (R : List RMono)
    (hR : ∀ m ∈ R, 1 ≤ m.coeff → m.bDeg ≤ 1 ∧ m.sDeg ≤ 1 ∧ m.nDeg ≤ 1)
    (hno : ¬ ∃ m ∈ R, 1 ≤ m.coeff ∧ m.bDeg = 1 ∧ m.sDeg = 0 ∧ m.nDeg = 0) :
    rEval R 1 0 0 = rEval R 0 0 0 := by
  induction R with
  | nil => rfl
  | cons m p ih =>
    simp only [rEval]
    have hp := ih (fun m' hm' => hR m' (List.mem_cons_of_mem _ hm'))
      (fun ⟨m', hm', h⟩ => hno ⟨m', List.mem_cons_of_mem _ hm', h⟩)
    rw [hp]
    congr 1
    by_cases hc : m.coeff = 0
    · simp [hc]
    · have hd := hR m List.mem_cons_self (Nat.one_le_iff_ne_zero.2 hc)
      have hn : ¬ (m.bDeg = 1 ∧ m.sDeg = 0 ∧ m.nDeg = 0) := fun h =>
        hno ⟨m, List.mem_cons_self, Nat.one_le_iff_ne_zero.2 hc, h⟩
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hd.2.1 with hs | hs
      · rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hd.2.2 with hn' | hn'
        · have hb : m.bDeg = 0 := by omega
          simp [hb, hs, hn']
        · simp [hn']
      · simp [hs]

/-- On the multilinear class, a recursor without a positive monomial `c * s` takes the same value
at `s = 0` and at `s = 1` with `b = n = 0`.

Proves: `rEval R 0 1 0 = rEval R 0 0 0` under the two hypotheses.
Does not prove: equality at other arguments.
Relation: not applicable (polynomial evaluation).
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: recursor lists with every positive monomial of degree at most one in each variable. -/
theorem rEval_flat_s (R : List RMono)
    (hR : ∀ m ∈ R, 1 ≤ m.coeff → m.bDeg ≤ 1 ∧ m.sDeg ≤ 1 ∧ m.nDeg ≤ 1)
    (hno : ¬ ∃ m ∈ R, 1 ≤ m.coeff ∧ m.bDeg = 0 ∧ m.sDeg = 1 ∧ m.nDeg = 0) :
    rEval R 0 1 0 = rEval R 0 0 0 := by
  induction R with
  | nil => rfl
  | cons m p ih =>
    simp only [rEval]
    have hp := ih (fun m' hm' => hR m' (List.mem_cons_of_mem _ hm'))
      (fun ⟨m', hm', h⟩ => hno ⟨m', List.mem_cons_of_mem _ hm', h⟩)
    rw [hp]
    congr 1
    by_cases hc : m.coeff = 0
    · simp [hc]
    · have hd := hR m List.mem_cons_self (Nat.one_le_iff_ne_zero.2 hc)
      have hn : ¬ (m.bDeg = 0 ∧ m.sDeg = 1 ∧ m.nDeg = 0) := fun h =>
        hno ⟨m, List.mem_cons_self, Nat.one_le_iff_ne_zero.2 hc, h⟩
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hd.1 with hb | hb
      · rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hd.2.2 with hn' | hn'
        · have hs : m.sDeg = 0 := by omega
          simp [hb, hs, hn']
        · simp [hn']
      · simp [hb]

/-- On the multilinear class, a recursor without a positive monomial `c * n` takes the same value
at `n = 0` and at `n = 1` with `b = s = 0`.

Proves: `rEval R 0 0 1 = rEval R 0 0 0` under the two hypotheses.
Does not prove: equality at other arguments.
Relation: not applicable (polynomial evaluation).
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: recursor lists with every positive monomial of degree at most one in each variable. -/
theorem rEval_flat_n (R : List RMono)
    (hR : ∀ m ∈ R, 1 ≤ m.coeff → m.bDeg ≤ 1 ∧ m.sDeg ≤ 1 ∧ m.nDeg ≤ 1)
    (hno : ¬ ∃ m ∈ R, 1 ≤ m.coeff ∧ m.bDeg = 0 ∧ m.sDeg = 0 ∧ m.nDeg = 1) :
    rEval R 0 0 1 = rEval R 0 0 0 := by
  induction R with
  | nil => rfl
  | cons m p ih =>
    simp only [rEval]
    have hp := ih (fun m' hm' => hR m' (List.mem_cons_of_mem _ hm'))
      (fun ⟨m', hm', h⟩ => hno ⟨m', List.mem_cons_of_mem _ hm', h⟩)
    rw [hp]
    congr 1
    by_cases hc : m.coeff = 0
    · simp [hc]
    · have hd := hR m List.mem_cons_self (Nat.one_le_iff_ne_zero.2 hc)
      have hn : ¬ (m.bDeg = 0 ∧ m.sDeg = 0 ∧ m.nDeg = 1) := fun h =>
        hno ⟨m, List.mem_cons_self, Nat.one_le_iff_ne_zero.2 hc, h⟩
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hd.1 with hb | hb
      · rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hd.2.1 with hs | hs
        · have hn' : m.nDeg = 0 := by omega
          simp [hb, hs, hn']
        · simp [hs]
      · simp [hb]

/-- On the multilinear class, strict monotonicity in every argument forces the positive linear
monomials of the monomial test.

Proves: `Multilinear W R → StrictContextLaws (polyInterpretation z 1 a W R) (· < ·) →
linearMonomials W R = true`.
Does not prove: the implication outside the multilinear class (`squareWrapper_strictContextLaws`
with `squareWrapper_not_linearMonomials` is the failing instance).
Relation: not applicable (interpretation laws).
Closure: every constructor context (the laws).
Strategy: not applicable.
Trust: kernel-only.
Scope: unit successor slope; the multilinear class. -/
theorem linearMonomials_of_strictContextLaws {z a : Nat} {W : List WMono} {R : List RMono}
    (hml : Multilinear W R) (h : StrictContextLaws (polyInterpretation z 1 a W R) (· < ·)) :
    linearMonomials W R = true := by
  simp only [linearMonomials, Bool.and_eq_true, List.any_eq_true, decide_eq_true_eq,
    beq_iff_eq]
  have hs : ∃ m ∈ W, 1 ≤ m.coeff ∧ m.sDeg = 1 ∧ m.yDeg = 0 := by
    by_contra hno
    have := h.wrapLeft 0 (show (0 : Nat) < 1 from Nat.zero_lt_one)
    simp only [polyInterpretation] at this
    rw [wEval_flat_s W hml.1 hno] at this
    exact lt_irrefl _ this
  have hy : ∃ m ∈ W, 1 ≤ m.coeff ∧ m.sDeg = 0 ∧ m.yDeg = 1 := by
    by_contra hno
    have := h.wrapRight 0 (show (0 : Nat) < 1 from Nat.zero_lt_one)
    simp only [polyInterpretation] at this
    rw [wEval_flat_y W hml.1 hno] at this
    exact lt_irrefl _ this
  have hb : ∃ m ∈ R, 1 ≤ m.coeff ∧ m.bDeg = 1 ∧ m.sDeg = 0 ∧ m.nDeg = 0 := by
    by_contra hno
    have := h.recurBase 0 0 (show (0 : Nat) < 1 from Nat.zero_lt_one)
    simp only [polyInterpretation] at this
    rw [rEval_flat_b R hml.2 hno] at this
    exact lt_irrefl _ this
  have hs' : ∃ m ∈ R, 1 ≤ m.coeff ∧ m.bDeg = 0 ∧ m.sDeg = 1 ∧ m.nDeg = 0 := by
    by_contra hno
    have := h.recurStep 0 0 (show (0 : Nat) < 1 from Nat.zero_lt_one)
    simp only [polyInterpretation] at this
    rw [rEval_flat_s R hml.2 hno] at this
    exact lt_irrefl _ this
  have hn : ∃ m ∈ R, 1 ≤ m.coeff ∧ m.bDeg = 0 ∧ m.sDeg = 0 ∧ m.nDeg = 1 := by
    by_contra hno
    have := h.recurCounter 0 0 (show (0 : Nat) < 1 from Nat.zero_lt_one)
    simp only [polyInterpretation] at this
    rw [rEval_flat_n R hml.2 hno] at this
    exact lt_irrefl _ this
  obtain ⟨m1, hm1, c1, s1, y1⟩ := hs
  obtain ⟨m2, hm2, c2, s2, y2⟩ := hy
  obtain ⟨m3, hm3, c3, b3, s3, n3⟩ := hb
  obtain ⟨m4, hm4, c4, b4, s4, n4⟩ := hs'
  obtain ⟨m5, hm5, c5, b5, s5, n5⟩ := hn
  exact ⟨⟨⟨⟨⟨m1, hm1, ⟨c1, s1⟩, y1⟩, ⟨m2, hm2, ⟨c2, s2⟩, y2⟩⟩, ⟨m3, hm3, ⟨⟨c3, b3⟩, s3⟩, n3⟩⟩,
    ⟨m4, hm4, ⟨⟨c4, b4⟩, s4⟩, n4⟩⟩, ⟨m5, hm5, ⟨⟨c5, b5⟩, s5⟩, n5⟩⟩

/-- On the multilinear class, the monomial test is strict monotonicity in every argument.

Proves: `Multilinear W R → (linearMonomials W R = true ↔
StrictContextLaws (polyInterpretation z 1 a W R) (· < ·))`.
Does not prove: the equivalence outside the multilinear class.
Relation: not applicable (interpretation laws).
Closure: every constructor context (the laws).
Strategy: not applicable.
Trust: kernel-only.
Scope: unit successor slope; the multilinear class. -/
theorem linearMonomials_iff_strictContextLaws {z a : Nat} {W : List WMono} {R : List RMono}
    (hml : Multilinear W R) :
    linearMonomials W R = true ↔ StrictContextLaws (polyInterpretation z 1 a W R) (· < ·) :=
  ⟨poly_strictContextLaws, linearMonomials_of_strictContextLaws hml⟩

/-- An accepted polynomial certificate orients both root rules and is strictly monotone in every
argument.

Proves: `checkPoly z a W R = true → RootRuleOrients ... ∧ StrictContextLaws ...` for every
certificate.
Does not prove: the converse (`checkPoly_iff_orients_strictContextLaws` on the multilinear class).
Relation: `RootStep` of the free recursor (orientation) and the constructor laws.
Closure: root for orientation; every constructor context for the laws.
Strategy: full.
Trust: kernel-only.
Scope: natural-coefficient polynomial certificates with successor `n ↦ n + a`. -/
theorem checkPoly_orients_strictContextLaws {z a : Nat} {W : List WMono} {R : List RMono}
    (h : checkPoly z a W R = true) :
    RootRuleOrients (polyInterpretation z 1 a W R) (· < ·) ∧
      StrictContextLaws (polyInterpretation z 1 a W R) (· < ·) := by
  simp only [checkPoly, Bool.and_eq_true] at h
  exact ⟨(decideRootUnit_iff z a W R).1 h.1, poly_strictContextLaws h.2⟩

/-- On the multilinear class, the polynomial checker accepts exactly the interpretations that
orient both root rules and are strictly monotone in every argument.

Proves: `Multilinear W R → (checkPoly z a W R = true ↔
RootRuleOrients (polyInterpretation z 1 a W R) (· < ·) ∧
StrictContextLaws (polyInterpretation z 1 a W R) (· < ·))`.
Does not prove: the equivalence outside the multilinear class (`checkPoly_iff_needs_multilinear`).
Relation: `RootStep` of the free recursor (orientation) and the constructor laws.
Closure: root for orientation; every constructor context for the laws.
Strategy: full.
Trust: kernel-only.
Scope: natural-coefficient polynomial certificates with successor `n ↦ n + a`. -/
theorem checkPoly_iff_orients_strictContextLaws {z a : Nat} {W : List WMono} {R : List RMono}
    (hml : Multilinear W R) :
    checkPoly z a W R = true ↔
      RootRuleOrients (polyInterpretation z 1 a W R) (· < ·) ∧
        StrictContextLaws (polyInterpretation z 1 a W R) (· < ·) := by
  rw [checkPoly, Bool.and_eq_true, decideRootUnit_iff, linearMonomials_iff_strictContextLaws hml]

/-! ### Controls for the multilinear class -/

/-- The multilinear recursor `2n + sn + b + 1`, with no pure monomial in `s`.

Proves: nothing; a monomial list.
Does not prove: anything by itself.
Relation: not applicable.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: the control of `orients_not_iff_checkPoly_on_multilinear`, with wrapper `regionW`,
`z = 0` and `a = 1`. -/
def multilinearControlR : List RMono := [⟨2, 0, 0, 1⟩, ⟨1, 0, 1, 1⟩, ⟨1, 1, 0, 0⟩, ⟨1, 0, 0, 0⟩]

/-- The control certificate is multilinear.

Proves: `Multilinear regionW multilinearControlR`.
Does not prove: orientation.
Relation: not applicable.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only; evaluation by `decide`.
Scope: the control certificate. -/
theorem multilinearControl_multilinear : Multilinear regionW multilinearControlR :=
  (multilinearB_iff _ _).1 (by decide)

/-- The control certificate orients both root rules.

Proves: `RootRuleOrients (polyInterpretation 0 1 1 regionW multilinearControlR) (· < ·)`.
Does not prove: strict monotonicity (`multilinearControl_not_strictContextLaws`).
Relation: `RootStep` of the free recursor.
Closure: root.
Strategy: full.
Trust: kernel-only; the decision of T-DEC-1 evaluated by `decide`.
Scope: the control certificate. -/
theorem multilinearControl_orients :
    RootRuleOrients (polyInterpretation 0 1 1 regionW multilinearControlR) (· < ·) :=
  (decideRootUnit_iff 0 1 regionW multilinearControlR).1 (by decide)

/-- The polynomial checker rejects the control certificate.

Proves: `checkPoly 0 1 regionW multilinearControlR = false`.
Does not prove: failure of orientation (the certificate orients both rules).
Relation: not applicable (Boolean checker).
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only; evaluation by `decide`.
Scope: the control certificate. -/
theorem multilinearControl_rejected : checkPoly 0 1 regionW multilinearControlR = false := by
  decide

/-- At counter `0` the control recursor does not depend on the step argument `s`.

Proves: `rEval multilinearControlR b 1 0 = rEval multilinearControlR b 0 0` for every `b`.
Does not prove: anything at other counters.
Relation: not applicable (polynomial evaluation).
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: the control recursor. -/
theorem multilinearControl_step_flat (b : Nat) :
    rEval multilinearControlR b 1 0 = rEval multilinearControlR b 0 0 := by
  simp [multilinearControlR, rEval]

/-- The control certificate is not strictly monotone in the step argument of `recur`.

Proves: `¬ StrictContextLaws (polyInterpretation 0 1 1 regionW multilinearControlR) (· < ·)`.
Does not prove: failure of root orientation.
Relation: not applicable (interpretation laws).
Closure: every constructor context (the laws).
Strategy: not applicable.
Trust: kernel-only.
Scope: the control certificate; the failing instance is `s = 0` against `s = 1` at `b = n = 0`. -/
theorem multilinearControl_not_strictContextLaws :
    ¬ StrictContextLaws (polyInterpretation 0 1 1 regionW multilinearControlR) (· < ·) := by
  intro h
  have := h.recurStep 0 0 (show (0 : Nat) < 1 from Nat.zero_lt_one)
  simp only [polyInterpretation] at this
  rw [multilinearControl_step_flat] at this
  exact lt_irrefl _ this

/-- Orientation alone does not characterize acceptance on the multilinear class: the multilinear
control orients both root rules and the checker rejects it.

Proves: `¬ ∀ z a W R, Multilinear W R → (checkPoly z a W R = true ↔
RootRuleOrients (polyInterpretation z 1 a W R) (· < ·))`.
Does not prove: anything about strictly monotone certificates
(`checkPoly_iff_orients_strictContextLaws` covers them).
Relation: `RootStep` of the free recursor.
Closure: root.
Strategy: full.
Trust: kernel-only.
Scope: the multilinear class with unit successor slope. -/
theorem orients_not_iff_checkPoly_on_multilinear :
    ¬ ∀ (z a : Nat) (W : List WMono) (R : List RMono), Multilinear W R →
      (checkPoly z a W R = true ↔ RootRuleOrients (polyInterpretation z 1 a W R) (· < ·)) := by
  intro h
  have := (h 0 1 regionW multilinearControlR multilinearControl_multilinear).2
    multilinearControl_orients
  rw [multilinearControl_rejected] at this
  exact Bool.false_ne_true this

/-- The wrapper `s ^ 2 + y + 1`: strictly monotone in `s` with no pure monomial in `s`.

Proves: nothing; a monomial list.
Does not prove: anything by itself.
Relation: not applicable.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: the control of `checkPoly_iff_needs_multilinear`. -/
def squareWrapperW : List WMono := [⟨1, 2, 0⟩, ⟨1, 0, 1⟩, ⟨1, 0, 0⟩]

/-- The recursor `(n + 1)(s ^ 2 + b + 2) + s`, expanded.

Proves: nothing; a monomial list.
Does not prove: anything by itself.
Relation: not applicable.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: the control of `checkPoly_iff_needs_multilinear`. -/
def squareWrapperR : List RMono :=
  [⟨1, 0, 2, 1⟩, ⟨1, 1, 0, 1⟩, ⟨2, 0, 0, 1⟩, ⟨1, 0, 2, 0⟩, ⟨1, 1, 0, 0⟩, ⟨2, 0, 0, 0⟩,
    ⟨1, 0, 1, 0⟩]

/-- The square-wrapper certificate orients both root rules.

Proves: `RootRuleOrients (polyInterpretation 0 1 1 squareWrapperW squareWrapperR) (· < ·)`.
Does not prove: acceptance by the checker (`squareWrapper_rejected`).
Relation: `RootStep` of the free recursor.
Closure: root.
Strategy: full.
Trust: kernel-only; the decision of T-DEC-1 evaluated by `decide`.
Scope: the square-wrapper certificate. -/
theorem squareWrapper_orients :
    RootRuleOrients (polyInterpretation 0 1 1 squareWrapperW squareWrapperR) (· < ·) :=
  (decideRootUnit_iff 0 1 squareWrapperW squareWrapperR).1 (by decide)

/-- The square-wrapper certificate is strictly monotone in every argument.

Proves: `StrictContextLaws (polyInterpretation 0 1 1 squareWrapperW squareWrapperR) (· < ·)`.
Does not prove: membership in the multilinear class (`squareWrapper_not_multilinear`).
Relation: not applicable (interpretation laws).
Closure: every constructor context (the laws).
Strategy: not applicable.
Trust: kernel-only.
Scope: the square-wrapper certificate. -/
theorem squareWrapper_strictContextLaws :
    StrictContextLaws (polyInterpretation 0 1 1 squareWrapperW squareWrapperR) (· < ·) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y hxy
    show 1 * x + 1 < 1 * y + 1
    omega
  · intro x y w hxy
    show wEval squareWrapperW x w < wEval squareWrapperW y w
    have hsq : x ^ 2 < y ^ 2 := Nat.pow_lt_pow_left hxy (by decide)
    simp only [squareWrapperW, wEval, pow_zero, pow_one, one_mul, mul_one, add_zero]
    omega
  · intro w x y hxy
    exact wEval_strict_y squareWrapperW w hxy ⟨⟨1, 0, 1⟩, by simp [squareWrapperW], le_rfl, rfl, rfl⟩
  · intro x y s n hxy
    exact rEval_strict_b squareWrapperR s n hxy
      ⟨⟨1, 1, 0, 0⟩, by simp [squareWrapperR], le_rfl, rfl, rfl, rfl⟩
  · intro b x y n hxy
    exact rEval_strict_s squareWrapperR b n hxy
      ⟨⟨1, 0, 1, 0⟩, by simp [squareWrapperR], le_rfl, rfl, rfl, rfl⟩
  · intro b s x y hxy
    exact rEval_strict_n squareWrapperR b s hxy
      ⟨⟨2, 0, 0, 1⟩, by simp [squareWrapperR], by decide, rfl, rfl, rfl⟩

/-- The square wrapper has no pure linear monomial in `s`, so the monomial test fails.

Proves: `linearMonomials squareWrapperW squareWrapperR = false`.
Does not prove: failure of strict monotonicity (`squareWrapper_strictContextLaws`).
Relation: not applicable (Boolean test).
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only; evaluation by `decide`.
Scope: the square-wrapper certificate. -/
theorem squareWrapper_not_linearMonomials :
    linearMonomials squareWrapperW squareWrapperR = false := by
  decide

/-- The square-wrapper certificate lies outside the multilinear class.

Proves: `¬ Multilinear squareWrapperW squareWrapperR`.
Does not prove: anything about orientation.
Relation: not applicable.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only; evaluation by `decide`.
Scope: the square-wrapper certificate. -/
theorem squareWrapper_not_multilinear : ¬ Multilinear squareWrapperW squareWrapperR := by
  rw [← multilinearB_iff]
  decide

/-- The polynomial checker rejects the square-wrapper certificate.

Proves: `checkPoly 0 1 squareWrapperW squareWrapperR = false`.
Does not prove: failure of orientation or of strict monotonicity (both hold).
Relation: not applicable (Boolean checker).
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only; evaluation by `decide`.
Scope: the square-wrapper certificate. -/
theorem squareWrapper_rejected : checkPoly 0 1 squareWrapperW squareWrapperR = false := by
  decide

/-- The multilinear hypothesis of `checkPoly_iff_orients_strictContextLaws` is load-bearing: the
square-wrapper certificate orients both root rules, is strictly monotone in every argument, and the
checker rejects it.

Proves: `¬ ∀ z a W R, (checkPoly z a W R = true ↔
RootRuleOrients (polyInterpretation z 1 a W R) (· < ·) ∧
StrictContextLaws (polyInterpretation z 1 a W R) (· < ·))`.
Does not prove: anything on the multilinear class.
Relation: `RootStep` of the free recursor and the constructor laws.
Closure: root for orientation; every constructor context for the laws.
Strategy: full.
Trust: kernel-only.
Scope: natural-coefficient polynomial certificates with unit successor slope. -/
theorem checkPoly_iff_needs_multilinear :
    ¬ ∀ (z a : Nat) (W : List WMono) (R : List RMono),
      (checkPoly z a W R = true ↔
        RootRuleOrients (polyInterpretation z 1 a W R) (· < ·) ∧
          StrictContextLaws (polyInterpretation z 1 a W R) (· < ·)) := by
  intro h
  have := (h 0 1 squareWrapperW squareWrapperR).2
    ⟨squareWrapper_orients, squareWrapper_strictContextLaws⟩
  rw [squareWrapper_rejected] at this
  exact Bool.false_ne_true this

/-- The value schema of a unit-successor polynomial interpretation. -/
abbrev valueSchema (z a : Nat) (W : List WMono) (R : List RMono) : StepDuplicatingSchema where
  T := Nat
  base := z
  succ n := 1 * n + a
  wrap := wEval W
  recur := rEval R

/-- Retentive affine polynomial certificates are rejected, by the coupling inequality on the value
schema: retention of the wrapper arguments forces the counter gain above every payload value, and
an affine recursor has a gain independent of the payload. -/
theorem affine_certificate_rejected (z a α βw γ r0 rb rs rn : Nat) (hβw : 1 ≤ βw) (hγ : 1 ≤ γ) :
    checkPoly z a (affineW α βw γ) (multilinearR r0 rb rs rn 0 0 0 0) = false := by
  cases h : checkPoly z a (affineW α βw γ) (multilinearR r0 rb rs rn 0 0 0 0) with
  | false => rfl
  | true =>
    exfalso
    simp only [checkPoly, Bool.and_eq_true] at h
    have hroot := (decideRootUnit_iff z a _ _).1 h.1
    have hret : ∀ x y : Nat, α + x + y ≤ wEval (affineW α βw γ) x y := by
      intro x y
      simp [affineW, wEval]
      nlinarith
    have hc := retained_wrapper_forces_payload_coupled_gain
      (S := valueSchema z a (affineW α βw γ) (multilinearR r0 rb rs rn 0 0 0 0)) id α
      (fun x y => hret x y) (fun b s n => hroot.recurSucc b s n)
    have key := hc 0 (rn * a) 0
    simp only [counterGainZ, id] at key
    simp only [rEval_multilinearR] at key
    have hα0 : (0 : Int) ≤ (α : Int) := by positivity
    push_cast at key
    ring_nf at key
    linarith

/-- The coupled certificate of the P2.4 region is accepted. -/
theorem region_certificate_accepted : checkPoly 0 1 regionW (regionR 1 2) = true := by
  rw [checkPoly, (region_decides 1 2).2 ⟨le_rfl, le_rfl⟩, Bool.true_and]
  decide

/-! ## Matrix certificates -/

/-- Entrywise comparison `B ≤ A` of natural matrices. -/
def matGe {k : Nat} (A B : Matrix (Fin k) (Fin k) Nat) : Bool := decide (∀ i j, B i j ≤ A i j)

/-- The matrix checker (Endrullis, Waldmann and Zantema 2008): positive top-left entries of the
argument matrices, the coefficient conditions of the successor rule for `b`, `s` and `n`, and the
strict condition on the first entry of the constant vectors. -/
def checkMatrix (d : Nat) (M : MatrixCert d) : Bool :=
  decide (1 ≤ M.mat .succ 0 0 0) && decide (1 ≤ M.mat .wrap 0 0 0) &&
    decide (1 ≤ M.mat .wrap 1 0 0) && decide (1 ≤ M.mat .recur 0 0 0) &&
    decide (1 ≤ M.mat .recur 1 0 0) && decide (1 ≤ M.mat .recur 2 0 0) &&
    matGe (M.mat .recur 0) (M.mat .wrap 1 * M.mat .recur 0) &&
    matGe (M.mat .recur 1) (M.mat .wrap 0 + M.mat .wrap 1 * M.mat .recur 1) &&
    matGe (M.mat .recur 2 * M.mat .succ 0) (M.mat .wrap 1 * M.mat .recur 2) &&
    decide (M.const .wrap 0 + (M.mat .wrap 1).mulVec (M.const .recur) 0 <
      M.const .recur 0 + (M.mat .recur 2).mulVec (M.const .succ) 0)

/-- No matrix certificate is accepted: at the top-left entry the step argument occurs once on the
left and twice on the right, and positive entries make the right side larger. -/
theorem matrix_certificate_rejected (d : Nat) (M : MatrixCert d) : checkMatrix d M = false := by
  cases h : checkMatrix d M with
  | false => rfl
  | true =>
    exfalso
    simp only [checkMatrix, matGe, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨-, hw0⟩, hw1⟩, -⟩, -⟩, -⟩, -⟩, hs⟩, -⟩, -⟩ := h
    have key := hs 0 0
    rw [Matrix.add_apply, Matrix.mul_apply] at key
    have hsum : M.mat .wrap 1 0 0 * M.mat .recur 1 0 0 ≤
        ∑ j, M.mat .wrap 1 0 j * M.mat .recur 1 j 0 :=
      Finset.single_le_sum (f := fun j => M.mat .wrap 1 0 j * M.mat .recur 1 j 0)
        (fun j _ => Nat.zero_le _) (Finset.mem_univ 0)
    have h3 := Nat.mul_le_mul_right (M.mat .recur 1 0 0) hw1
    linarith

/-! ## Knuth-Bendix certificates -/

mutual
/-- Occurrences of the variable `x`. -/
def varCount (x : Nat) : Term FreeSym Nat → Nat
  | .var y => if y = x then 1 else 0
  | .app _ args => varCountList x args
/-- Occurrences of the variable `x` in a list of terms. -/
def varCountList (x : Nat) : List (Term FreeSym Nat) → Nat
  | [] => 0
  | t :: ts => varCount x t + varCountList x ts
end

/-- The variable condition: no listed variable occurs more often on the right than on the left. -/
def varCondition (r : Rule FreeSym Nat) (xs : List Nat) : Bool :=
  xs.all fun x => decide (varCount x r.rhs ≤ varCount x r.lhs)

theorem succRule_varCondition_fails : varCondition succRule [0, 1, 2] = false := by
  decide

/-! ### The Knuth-Bendix order of a certificate

A certificate determines one instance of the shared first-order Knuth-Bendix core of
`MethodRowsKBO` over the free symbols: arities `freeArity`, variable weight, symbol weights, unit
subterm coefficients (the standard order of Knuth and Bendix 1970), the precedence `f ≻ g` exactly
when `K.prec g < K.prec f`, and lexicographic status. The comparison `MethodRowsKBO.Gt` of that
core has the clauses of the variable condition and the weight, the variable case, the precedence
case and the lexicographic case; `kboGtB` computes it (`kboGtB_iff`), and `kboAdmissibleB` computes
the admissibility laws `MethodRowsKBO.KBOCore.Laws` of the core (`kboAdmissibleB_iff`). -/

/-- The Knuth-Bendix order data of a certificate in the shared core of `MethodRowsKBO`.

Proves: nothing; a definition.
Does not prove: admissibility (`kboAdmissibleB_iff`).
Relation: the order `MethodRowsKBO.Gt (kboCore K)` on `FTerm`.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: the four free symbols with arities `freeArity`; unit subterm coefficients; lexicographic
status for every symbol; precedence `f ≻ g` exactly when `K.prec g < K.prec f`. -/
def kboCore (K : KBOCert) : MethodRowsKBO.KBOCore FreeSym Nat where
  arOK f n := n = freeArity f
  w0 := K.varWeight
  weight := K.weight
  coeff _ _ := 1
  prec f g := K.prec g < K.prec f
  status _ := .lex

mutual
/-- The variables of a term, one entry per occurrence, left to right.

Proves: nothing; a definition.
Does not prove: anything about rewriting.
Relation: not applicable.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: first-order terms over the free symbols. -/
def termVars : FTerm → List Nat
  | .var x => [x]
  | .app _ args => termVarsList args
/-- The variables of a list of terms, one entry per occurrence, left to right.

Proves: nothing; a definition.
Does not prove: anything about rewriting.
Relation: not applicable.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: argument lists over the free symbols. -/
def termVarsList : List FTerm → List Nat
  | [] => []
  | t :: ts => termVars t ++ termVarsList ts
end

/-- With unit subterm coefficients, the weighted occurrence count of `MethodRowsKBO` is the
occurrence count `varCount`.

Proves: `MethodRowsKBO.cnt (fun _ _ => 1) x t = varCount x t` for every term.
Does not prove: anything for other coefficients.
Relation: not applicable.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: first-order terms over the free symbols. -/
theorem cnt_eq_varCount (x : Nat) : ∀ t : FTerm,
    MethodRowsKBO.cnt (fun (_ : FreeSym) (_ : Nat) => 1) x t = varCount x t := by
  intro t
  induction t using Term.rec' with
  | hvar y => simp [MethodRowsKBO.cnt_var, varCount]
  | happ f args ih =>
      rw [MethodRowsKBO.cnt_app, varCount]
      suffices h : ∀ (l : List FTerm), (∀ a ∈ l,
          MethodRowsKBO.cnt (fun (_ : FreeSym) (_ : Nat) => 1) x a = varCount x a) →
          ∀ i, MethodRowsKBO.evL (fun (_ : FreeSym) (_ : Nat) => 1) (fun _ => (0 : Nat))
            (fun y => if y = x then 1 else 0) f i l = varCountList x l from h args ih 0
      intro l hl
      induction l with
      | nil => intro i; rfl
      | cons a as ihl =>
          intro i
          rw [MethodRowsKBO.evL_cons, varCountList, ihl (fun b hb => hl b (by simp [hb])) (i + 1)]
          have := hl a (by simp)
          simp only [MethodRowsKBO.cnt] at this
          rw [one_smul, this]

/-- A variable that does not occur in a term has occurrence count `0`.

Proves: `x ∉ termVars t → varCount x t = 0`.
Does not prove: anything about occurring variables.
Relation: not applicable.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: first-order terms over the free symbols. -/
theorem varCount_eq_zero_of_not_mem (x : Nat) : ∀ t : FTerm,
    x ∉ termVars t → varCount x t = 0 := by
  intro t
  induction t using Term.rec' with
  | hvar y =>
      intro h
      simp only [termVars, List.mem_singleton] at h
      simp [varCount, Ne.symm h]
  | happ f args ih =>
      intro h
      rw [varCount]
      rw [termVars] at h
      suffices hs : ∀ (l : List FTerm), (∀ a ∈ l, x ∉ termVars a → varCount x a = 0) →
          x ∉ termVarsList l → varCountList x l = 0 from hs args ih h
      intro l hl hx
      induction l with
      | nil => rfl
      | cons a as ihl =>
          rw [termVarsList, List.mem_append, not_or] at hx
          rw [varCountList, hl a (by simp) hx.1, ihl (fun b hb => hl b (by simp [hb])) hx.2]

/-- The variable condition of the Knuth-Bendix order, tested on the variables of the smaller
side: no variable occurs more often in `t` than in `s`.

Proves: nothing; a Boolean test (`kboVCB_iff`).
Does not prove: the weight condition.
Relation: not applicable.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: first-order terms over the free symbols. -/
def kboVCB (s t : FTerm) : Bool :=
  (termVars t).all fun x => decide (varCount x t ≤ varCount x s)

/-- The test `kboVCB` decides the variable condition `MethodRowsKBO.KBOCore.VC` of the core of
every certificate.

Proves: `kboVCB s t = true ↔ (kboCore K).VC s t`.
Does not prove: anything about weights.
Relation: not applicable.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: every certificate and every pair of terms. -/
theorem kboVCB_iff (K : KBOCert) (s t : FTerm) : kboVCB s t = true ↔ (kboCore K).VC s t := by
  simp only [kboVCB, List.all_eq_true, decide_eq_true_eq, MethodRowsKBO.KBOCore.VC]
  constructor
  · intro h x
    show MethodRowsKBO.cnt (fun (_ : FreeSym) (_ : Nat) => 1) x t ≤
      MethodRowsKBO.cnt (fun (_ : FreeSym) (_ : Nat) => 1) x s
    rw [cnt_eq_varCount, cnt_eq_varCount]
    by_cases hx : x ∈ termVars t
    · exact h x hx
    · rw [varCount_eq_zero_of_not_mem x t hx]
      exact Nat.zero_le _
  · intro h x _
    have := h x
    change MethodRowsKBO.cnt (fun (_ : FreeSym) (_ : Nat) => 1) x t ≤
      MethodRowsKBO.cnt (fun (_ : FreeSym) (_ : Nat) => 1) x s at this
    rwa [cnt_eq_varCount, cnt_eq_varCount] at this

mutual
/-- The Knuth-Bendix comparison `s ≻ t` of a certificate, computed: the variable condition, then
a heavier left side, or equal weights with a variable on the right, a larger root in the
precedence, or the same root and a lexicographically larger argument list.

Proves: nothing; a Boolean comparison. Its meaning is `kboGtB_iff`.
Does not prove: admissibility of the certificate.
Relation: the order `MethodRowsKBO.Gt (kboCore K)` on `FTerm`.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: first-order terms over the free symbols; weights `(kboCore K).wt`. -/
def kboGtB (K : KBOCert) : FTerm → FTerm → Bool
  | .var x, t => kboVCB (.var x) t && decide ((kboCore K).wt t < (kboCore K).wt (.var x))
  | .app f ss, t =>
      kboVCB (.app f ss) t &&
        (decide ((kboCore K).wt t < (kboCore K).wt (.app f ss)) ||
          (decide ((kboCore K).wt (.app f ss) = (kboCore K).wt t) &&
            match t with
            | .var _ => true
            | .app g ts => if f = g then kboLexB K ss ts else decide (K.prec g < K.prec f)))
/-- The lexicographic extension of `kboGtB` to argument lists of equal length: the first
position with different arguments carries a `kboGtB` decrease.

Proves: nothing; a Boolean comparison (`kboLexB_sound`, `kboLexB_complete`).
Does not prove: anything for lists of different length (the result is `false`).
Relation: the lexicographic case of `MethodRowsKBO.Gt (kboCore K)`.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: argument lists over the free symbols. -/
def kboLexB (K : KBOCert) : List FTerm → List FTerm → Bool
  | [], _ => false
  | _ :: _, [] => false
  | a :: as, b :: bs =>
      (kboGtB K a b && as.length == bs.length) || (decide (a = b) && kboLexB K as bs)
end

/-- Soundness of the lexicographic comparison: an accepted pair of lists has equal length and a
first differing position with a Knuth-Bendix decrease, given soundness on the left elements.

Proves: `kboLexB K ss ts = true → ss.length = ts.length ∧ ∃ i, ss.take i = ts.take i ∧
Gt (kboCore K) ss[i] ts[i]`, under soundness of `kboGtB` on the elements of `ss`.
Does not prove: completeness (`kboLexB_complete`).
Relation: the lexicographic case of `MethodRowsKBO.Gt (kboCore K)`.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: argument lists over the free symbols. -/
theorem kboLexB_sound (K : KBOCert) : ∀ (ss ts : List FTerm),
    (∀ a ∈ ss, ∀ b, kboGtB K a b = true → MethodRowsKBO.Gt (kboCore K) a b) →
    kboLexB K ss ts = true →
      ss.length = ts.length ∧ ∃ i, ∃ (hi : i < ss.length) (hti : i < ts.length),
        ss.take i = ts.take i ∧ MethodRowsKBO.Gt (kboCore K) ss[i] ts[i]
  | [], ts, _, h => by simp [kboLexB] at h
  | _ :: _, [], _, h => by simp [kboLexB] at h
  | a :: as, b :: bs, ih, h => by
      simp only [kboLexB, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
      rcases h with ⟨hab, hlen⟩ | ⟨rfl, hrest⟩
      · refine ⟨by simp [hlen], 0, by simp, by simp, by simp, ?_⟩
        simpa using ih a (by simp) b hab
      · obtain ⟨hlen, i, hi, hti, hpre, hgt⟩ :=
          kboLexB_sound K as bs (fun c hc d hd => ih c (by simp [hc]) d hd) hrest
        refine ⟨by simp [hlen], i + 1, by simp [hi], by simp [hti], by simp [hpre], ?_⟩
        simpa using hgt

/-- Soundness of the computed comparison: an accepted pair is in the Knuth-Bendix order of the
certificate.

Proves: `kboGtB K s t = true → MethodRowsKBO.Gt (kboCore K) s t`.
Does not prove: admissibility of `K`.
Relation: `MethodRowsKBO.Gt (kboCore K)` on `FTerm`.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: every certificate and every pair of terms. -/
theorem kboGtB_sound (K : KBOCert) : ∀ (s t : FTerm),
    kboGtB K s t = true → MethodRowsKBO.Gt (kboCore K) s t := by
  intro s
  induction s using Term.rec' with
  | hvar x =>
      intro t h
      simp only [kboGtB, Bool.and_eq_true, decide_eq_true_eq] at h
      exact MethodRowsKBO.Gt.weight ((kboVCB_iff K _ _).1 h.1) h.2
  | happ f ss ih =>
      intro t h
      simp only [kboGtB, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
      obtain ⟨hvc, hw⟩ := h
      have hvc' := (kboVCB_iff K _ _).1 hvc
      rcases hw with hlt | ⟨heq, hrest⟩
      · exact MethodRowsKBO.Gt.weight hvc' hlt
      · cases t with
        | var y => exact MethodRowsKBO.Gt.varR hvc' heq
        | app g ts =>
            by_cases hfg : f = g
            · subst hfg
              simp only [if_true] at hrest
              obtain ⟨hlen, i, hi, hti, hpre, hgt⟩ := kboLexB_sound K ss ts ih hrest
              exact MethodRowsKBO.Gt.lex hvc' heq rfl hlen i hi hti hpre hgt
            · simp only [hfg, if_false, decide_eq_true_eq] at hrest
              exact MethodRowsKBO.Gt.prec hvc' heq hrest

/-- Completeness of the lexicographic comparison: equal lengths, an equal prefix of length `i`
and an accepted comparison at position `i` give acceptance.

Proves: `ss.length = ts.length → ss.take i = ts.take i → kboGtB K ss[i] ts[i] = true →
kboLexB K ss ts = true`.
Does not prove: soundness (`kboLexB_sound`).
Relation: the lexicographic case of `MethodRowsKBO.Gt (kboCore K)`.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: argument lists over the free symbols. -/
theorem kboLexB_complete (K : KBOCert) : ∀ (i : Nat) (ss ts : List FTerm)
    (hi : i < ss.length) (hti : i < ts.length),
    ss.length = ts.length → ss.take i = ts.take i → kboGtB K ss[i] ts[i] = true →
      kboLexB K ss ts = true
  | _, [], _, hi, _, _, _, _ => by simp at hi
  | _, _ :: _, [], _, hti, _, _, _ => by simp at hti
  | 0, a :: as, b :: bs, _, _, hlen, _, hgt => by
      simp only [List.getElem_cons_zero] at hgt
      simp only [kboLexB, hgt, Bool.true_and, Bool.or_eq_true, beq_iff_eq]
      left
      simpa using hlen
  | i + 1, a :: as, b :: bs, hi, hti, hlen, hpre, hgt => by
      simp only [List.take_succ_cons, List.cons.injEq] at hpre
      obtain ⟨rfl, hpre'⟩ := hpre
      simp only [List.getElem_cons_succ] at hgt
      have hrest := kboLexB_complete K i as bs (by simpa using hi) (by simpa using hti)
        (by simpa using hlen) hpre' hgt
      simp [kboLexB, hrest]

/-- Completeness of the computed comparison: every pair in the Knuth-Bendix order of the
certificate is accepted.

Proves: `MethodRowsKBO.Gt (kboCore K) s t → kboGtB K s t = true`.
Does not prove: admissibility of `K`.
Relation: `MethodRowsKBO.Gt (kboCore K)` on `FTerm`.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: every certificate; the multiset clause of the core is excluded because every symbol has
lexicographic status. -/
theorem kboGtB_complete (K : KBOCert) {s t : FTerm}
    (h : MethodRowsKBO.Gt (kboCore K) s t) : kboGtB K s t = true := by
  induction h with
  | weight hvc hw =>
      rename_i s t
      have hv := (kboVCB_iff K s t).2 hvc
      cases s with
      | var x => simp [kboGtB, hv, hw]
      | app f ss => simp [kboGtB, hv, hw]
  | varR hvc hw =>
      have hv := (kboVCB_iff K _ _).2 hvc
      simp [kboGtB, hv, hw]
  | prec hvc hw hp =>
      rename_i f g ss ts
      have hv := (kboVCB_iff K _ _).2 hvc
      have hfg : f ≠ g := by
        rintro rfl
        exact lt_irrefl _ hp
      have hp' : K.prec g < K.prec f := hp
      simp [kboGtB, hv, hw, hfg, hp']
  | lex hvc hw hst hlen i hi hti hpre hgt ih =>
      rename_i f ss ts
      have hv := (kboVCB_iff K _ _).2 hvc
      have hl := kboLexB_complete K i ss ts hi hti hlen hpre ih
      simp [kboGtB, hv, hw, hl]
  | mul hvc hw hst =>
      simp [kboCore] at hst

/-- The computed comparison is the Knuth-Bendix order of the certificate.

Proves: `kboGtB K s t = true ↔ MethodRowsKBO.Gt (kboCore K) s t`.
Does not prove: admissibility of `K` (`kboAdmissibleB_iff`).
Relation: `MethodRowsKBO.Gt (kboCore K)` on `FTerm`.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: every certificate and every pair of terms. -/
theorem kboGtB_iff (K : KBOCert) (s t : FTerm) :
    kboGtB K s t = true ↔ MethodRowsKBO.Gt (kboCore K) s t :=
  ⟨kboGtB_sound K s t, kboGtB_complete K⟩

/-- The admissibility test of a certificate (Knuth and Bendix 1970): positive variable weight,
the constant `zero` at least as heavy as a variable, and a weight-zero `succ` above every other
symbol in the precedence.

Proves: nothing; a Boolean test (`kboAdmissibleB_iff`).
Does not prove: orientation of any rule.
Relation: not applicable.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: the four free symbols; `succ` is the only unary symbol. -/
def kboAdmissibleB (K : KBOCert) : Bool :=
  decide (0 < K.varWeight) && decide (K.varWeight ≤ K.weight .zero) &&
    (decide (K.weight .succ ≠ 0) ||
      (decide (K.prec .zero < K.prec .succ) && decide (K.prec .wrap < K.prec .succ) &&
        decide (K.prec .recur < K.prec .succ)))

/-- The free symbol of arity `0` is `zero`.

Proves: `0 = freeArity f → f = .zero`.
Does not prove: anything about other arities.
Relation: not applicable.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: the four free symbols. -/
theorem eq_zero_of_freeArity_eq_zero {f : FreeSym} (h : 0 = freeArity f) : f = .zero := by
  cases f <;> simp_all [freeArity]

/-- The free symbol of arity `1` is `succ`.

Proves: `1 = freeArity f → f = .succ`.
Does not prove: anything about other arities.
Relation: not applicable.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: the four free symbols. -/
theorem eq_succ_of_freeArity_eq_one {f : FreeSym} (h : 1 = freeArity f) : f = .succ := by
  cases f <;> simp_all [freeArity]

/-- The admissibility test decides the admissibility laws of the core.

Proves: `kboAdmissibleB K = true ↔ (kboCore K).Laws`.
Does not prove: orientation of any rule.
Relation: not applicable.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: every certificate; the precedence of a certificate is always irreflexive, transitive and
well founded. -/
theorem kboAdmissibleB_iff (K : KBOCert) : kboAdmissibleB K = true ↔ (kboCore K).Laws := by
  constructor
  · intro h
    simp only [kboAdmissibleB, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hw0, hz⟩, hs⟩ := h
    exact
      { w0_pos := hw0
        weight_nonneg := fun _ => Nat.zero_le _
        const_ge := fun f hf => by
          have := eq_zero_of_freeArity_eq_zero hf
          subst this
          exact hz
        coeff_pos := fun _ _ => le_rfl
        special_unary := fun f hf _ n hn => by
          show n = 1
          exact hn.trans hf.symm
        special_max := fun f hf hw g hg => by
          have hfs := eq_succ_of_freeArity_eq_one hf
          subst hfs
          rcases hs with hne | ⟨⟨hz', hw'⟩, hr'⟩
          · exact absurd hw hne
          · show K.prec g < K.prec .succ
            cases g with
            | zero => exact hz'
            | succ => exact absurd rfl hg
            | wrap => exact hw'
            | recur => exact hr'
        prec_irrefl := fun f => lt_irrefl (K.prec f)
        prec_trans := fun f g h hfg hgh => lt_trans hgh hfg
        prec_wf := (InvImage.wf K.prec wellFounded_lt) }
  · intro hL
    simp only [kboAdmissibleB, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
    refine ⟨⟨hL.w0_pos, hL.const_ge .zero rfl⟩, ?_⟩
    by_cases hw : K.weight .succ = 0
    · right
      have hm := hL.special_max .succ rfl hw
      exact ⟨⟨hm .zero (by decide), hm .wrap (by decide)⟩, hm .recur (by decide)⟩
    · left
      exact hw

/-- The Knuth-Bendix checker (Knuth and Bendix 1970): admissibility of the certificate
(`kboAdmissibleB`) and the Knuth-Bendix comparison of the left- and right-hand side of each root
rule (`kboGtB`), computed from the certificate's weights and precedence.

Proves: nothing; a Boolean checker. Its meaning is `checkKBO_iff`.
Does not prove: termination by itself; every certificate is rejected (`kbo_certificate_rejected`).
Relation: the order `MethodRowsKBO.Gt (kboCore K)` on `FTerm`.
Closure: not applicable (comparison of the two sides of each rule).
Strategy: not applicable.
Trust: kernel-only.
Scope: the two root rules `zeroRule` and `succRule` of `freeRecursorTRS`. -/
def checkKBO (K : KBOCert) : Bool :=
  kboAdmissibleB K && kboGtB K zeroRule.lhs zeroRule.rhs && kboGtB K succRule.lhs succRule.rhs

/-- The Knuth-Bendix checker accepts exactly the admissible certificates whose order orients
both root rules.

Proves: `checkKBO K = true ↔ (kboCore K).Laws ∧ Gt (kboCore K) zeroRule.lhs zeroRule.rhs ∧
Gt (kboCore K) succRule.lhs succRule.rhs`.
Does not prove: termination; no certificate satisfies the right side
(`kbo_certificate_rejected`).
Relation: `MethodRowsKBO.Gt (kboCore K)` on the two rule sides.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: every certificate. -/
theorem checkKBO_iff (K : KBOCert) :
    checkKBO K = true ↔ (kboCore K).Laws ∧
      MethodRowsKBO.Gt (kboCore K) zeroRule.lhs zeroRule.rhs ∧
        MethodRowsKBO.Gt (kboCore K) succRule.lhs succRule.rhs := by
  rw [checkKBO, Bool.and_eq_true, Bool.and_eq_true, kboAdmissibleB_iff, kboGtB_iff, kboGtB_iff,
    and_assoc]

/-- No Knuth-Bendix order of a certificate orients the successor rule: the step argument `1`
occurs once on the left and twice on the right, against the variable condition that every clause
of the order carries.

Proves: `¬ MethodRowsKBO.Gt (kboCore K) succRule.lhs succRule.rhs` for every certificate.
Does not prove: anything about the zero rule (`kboWitness_orients_zeroRule` orients it).
Relation: `MethodRowsKBO.Gt (kboCore K)`.
Closure: not applicable (the rule sides themselves).
Strategy: not applicable.
Trust: kernel-only.
Scope: every certificate, admissible or not. -/
theorem succRule_not_kboGt (K : KBOCert) :
    ¬ MethodRowsKBO.Gt (kboCore K) succRule.lhs succRule.rhs := by
  intro h
  have hvc := MethodRowsKBO.gt_vc (kboCore K) h 1
  change MethodRowsKBO.cnt (fun (_ : FreeSym) (_ : Nat) => 1) 1 succRule.rhs ≤
    MethodRowsKBO.cnt (fun (_ : FreeSym) (_ : Nat) => 1) 1 succRule.lhs at hvc
  rw [cnt_eq_varCount, cnt_eq_varCount] at hvc
  exact absurd hvc (by decide)

/-- No Knuth-Bendix certificate is accepted: the checker computes the order of the certificate,
and that order violates the variable condition on the successor rule, where the step argument
occurs once on the left and twice on the right.

Proves: `checkKBO K = false` for every certificate.
Does not prove: rejection of the zero rule (admissible certificates orient it).
Relation: `MethodRowsKBO.Gt (kboCore K)` on the successor rule.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: every certificate; the proof goes through `checkKBO_iff` and `succRule_not_kboGt`. -/
theorem kbo_certificate_rejected (K : KBOCert) : checkKBO K = false := by
  cases h : checkKBO K with
  | false => rfl
  | true => exact absurd ((checkKBO_iff K).1 h).2.2 (succRule_not_kboGt K)

/-! ### Witnesses for the Knuth-Bendix comparison -/

/-- An admissible certificate: unit weights, variable weight `1`, precedence
`recur ≻ wrap ≻ succ ≻ zero`.

Proves: nothing; a certificate.
Does not prove: anything by itself.
Relation: not applicable.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: the witnesses of this section. -/
def kboWitness : KBOCert where
  weight _ := 1
  varWeight := 1
  prec
    | .zero => 0
    | .succ => 1
    | .wrap => 2
    | .recur => 3

/-- The witness certificate is admissible.

Proves: `kboAdmissibleB kboWitness = true`.
Does not prove: orientation of the successor rule.
Relation: not applicable.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only; evaluation by `decide`.
Scope: the witness certificate. -/
theorem kboWitness_admissible : kboAdmissibleB kboWitness = true := by decide

/-- The order of the witness certificate orients the zero rule.

Proves: `kboGtB kboWitness zeroRule.lhs zeroRule.rhs = true`.
Does not prove: orientation of the successor rule.
Relation: `MethodRowsKBO.Gt (kboCore kboWitness)` through `kboGtB_iff`.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only; evaluation by `decide`.
Scope: the witness certificate. -/
theorem kboWitness_orients_zeroRule : kboGtB kboWitness zeroRule.lhs zeroRule.rhs = true := by
  decide

/-- The order of the witness certificate does not orient the successor rule.

Proves: `kboGtB kboWitness succRule.lhs succRule.rhs = false`.
Does not prove: anything beyond the witness (`succRule_not_kboGt` covers every certificate).
Relation: `MethodRowsKBO.Gt (kboCore kboWitness)` through `kboGtB_iff`.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only; evaluation by `decide`.
Scope: the witness certificate. -/
theorem kboWitness_rejects_succRule : kboGtB kboWitness succRule.lhs succRule.rhs = false := by
  decide

/-- The term `wrap(succ(x), x)`.

Proves: nothing; a term.
Does not prove: anything by itself.
Relation: not applicable.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: the lexicographic witness. -/
def kboLexLeft : FTerm := .app .wrap [.app .succ [.var 0], .var 0]

/-- The term `wrap(x, succ(x))`.

Proves: nothing; a term.
Does not prove: anything by itself.
Relation: not applicable.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: the lexicographic witness. -/
def kboLexRight : FTerm := .app .wrap [.var 0, .app .succ [.var 0]]

/-- The lexicographic case: equal weights and the same root, decided by the first argument.

Proves: `kboGtB kboWitness kboLexLeft kboLexRight = true`.
Does not prove: anything for other certificates.
Relation: `MethodRowsKBO.Gt (kboCore kboWitness)` through `kboGtB_iff`.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only; evaluation by `decide`.
Scope: the witness certificate. -/
theorem kboWitness_lex : kboGtB kboWitness kboLexLeft kboLexRight = true := by decide

/-- The lexicographic case in the other direction is rejected.

Proves: `kboGtB kboWitness kboLexRight kboLexLeft = false`.
Does not prove: anything for other certificates.
Relation: `MethodRowsKBO.Gt (kboCore kboWitness)` through `kboGtB_iff`.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only; evaluation by `decide`.
Scope: the witness certificate. -/
theorem kboWitness_lex_reverse : kboGtB kboWitness kboLexRight kboLexLeft = false := by decide

/-- The term `wrap(x, y)`.

Proves: nothing; a term.
Does not prove: anything by itself.
Relation: not applicable.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: the precedence witness. -/
def kboPrecLeft : FTerm := .app .wrap [.var 0, .var 1]

/-- The term `recur(x, y, zero)`.

Proves: nothing; a term.
Does not prove: anything by itself.
Relation: not applicable.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: the precedence witness. -/
def kboPrecRight : FTerm := .app .recur [.var 0, .var 1, .app .zero []]

/-- A certificate with `w(wrap) = w(recur) + w(zero)` and `wrap ≻ recur`.

Proves: nothing; a certificate.
Does not prove: anything by itself.
Relation: not applicable.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: the precedence witness. -/
def kboPrecHigh : KBOCert where
  weight
    | .wrap => 2
    | _ => 1
  varWeight := 1
  prec
    | .zero => 0
    | .succ => 1
    | .wrap => 3
    | .recur => 2

/-- The same weights with `recur ≻ wrap`.

Proves: nothing; a certificate.
Does not prove: anything by itself.
Relation: not applicable.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: the precedence witness. -/
def kboPrecLow : KBOCert where
  weight
    | .wrap => 2
    | _ => 1
  varWeight := 1
  prec
    | .zero => 0
    | .succ => 1
    | .wrap => 2
    | .recur => 3

/-- The precedence case: equal weights and different roots, decided by the precedence
`wrap ≻ recur`.

Proves: `kboGtB kboPrecHigh kboPrecLeft kboPrecRight = true`.
Does not prove: anything for other certificates.
Relation: `MethodRowsKBO.Gt (kboCore kboPrecHigh)` through `kboGtB_iff`.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only; evaluation by `decide`.
Scope: the certificate `kboPrecHigh`. -/
theorem kboPrecHigh_orients : kboGtB kboPrecHigh kboPrecLeft kboPrecRight = true := by decide

/-- The same pair under the precedence `recur ≻ wrap` is rejected, so the comparison reads the
precedence of the certificate.

Proves: `kboGtB kboPrecLow kboPrecLeft kboPrecRight = false`.
Does not prove: anything for other certificates.
Relation: `MethodRowsKBO.Gt (kboCore kboPrecLow)` through `kboGtB_iff`.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only; evaluation by `decide`.
Scope: the certificate `kboPrecLow`. -/
theorem kboPrecLow_rejects : kboGtB kboPrecLow kboPrecLeft kboPrecRight = false := by decide

/-! ## Dependency-pair certificates -/

/-- The dependency-pair checker: the subterm criterion of the unique dependency pair
`recur(b, s, succ n) → recur(b, s, n)` at the projection `proj`. -/
def checkDP (proj : FreeSym → Nat) : Bool := proj .recur == 2

theorem subtermCriterion_of_proj {proj : FreeSym → Nat} (hproj : proj .recur = 2) :
    SubtermCriterion freeRecursorTRS proj := by
  intro rule hrule f largs hl g targs hsub hdef
  rw [freeRecursorTRS_defined_iff] at hdef
  subst hdef
  simp only [freeRecursorTRS, List.mem_cons, List.not_mem_nil, or_false] at hrule
  rcases hrule with rfl | rfl
  · simp only [zeroRule] at hsub
    exact absurd hsub not_isSubterm_app_var
  · have ht := succRule_rhs_recur_subterm hsub
    subst ht
    simp only [succRule, Term.app.injEq] at hl
    obtain ⟨rfl, rfl⟩ := hl
    rw [hproj]
    exact ⟨Term.app FreeSym.succ [Term.var 2], Term.var 2, rfl, rfl,
      ProperSubterm.arg FreeSym.succ [Term.var 2] List.mem_cons_self (IsSubterm.refl _)⟩

/-- The checker accepts a projection if and only if the subterm criterion holds for it. -/
theorem checkDP_iff (proj : FreeSym → Nat) :
    checkDP proj = true ↔ SubtermCriterion freeRecursorTRS proj := by
  constructor
  · intro h
    exact subtermCriterion_of_proj (by simpa [checkDP] using h)
  · intro hsc
    have hsub : IsSubterm (Term.app FreeSym.recur [Term.var 0, Term.var 1, Term.var 2])
        succRule.rhs :=
      IsSubterm.arg FreeSym.wrap _ (by simp) (IsSubterm.refl _)
    obtain ⟨l0, t0, hl0, ht0, hprop⟩ := hsc succRule (by simp [freeRecursorTRS]) FreeSym.recur
      [Term.var 0, Term.var 1, Term.app FreeSym.succ [Term.var 2]] rfl FreeSym.recur
      [Term.var 0, Term.var 1, Term.var 2] hsub ((freeRecursorTRS_defined_iff _).2 rfl)
    simp only [checkDP, beq_iff_eq]
    generalize proj FreeSym.recur = k at hl0 ht0
    match k, hl0, ht0 with
    | 0, hl0, ht0 =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hl0 ht0
      subst hl0
      subst ht0
      cases hprop
    | 1, hl0, ht0 =>
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hl0 ht0
      subst hl0
      subst ht0
      cases hprop
    | 2, _, _ => rfl
    | k + 3, hl0, _ => simp at hl0

/-- Soundness: an accepted dependency-pair certificate proves termination of the free recursor. -/
theorem checkDP_sound {proj : FreeSym → Nat} (h : checkDP proj = true) : FreeTerminates :=
  terminating_of_subtermCriterion freeRecursorTRS freeRecursorTRS_vars ((checkDP_iff proj).1 h)

theorem counter_certificate_accepted : checkDP freeProj = true := rfl

/-! ## The checker and the boundary -/

/-- The executable checker. -/
def check : Certificate → Bool
  | .poly z a W R => checkPoly z a W R
  | .matrix d M => checkMatrix d M
  | .kbo K => checkKBO K
  | .dpSubterm proj => checkDP proj

/-- What an accepted certificate proves: termination of the free recursor, in the term encoding of
its method (constructor terms for interpretations and orders, first-order rewrite terms for
dependency pairs). -/
def Proves : Certificate → Prop
  | .poly .. => WellFounded (fun u t : FreeTerm Nat => ContextStep t u)
  | .matrix .. => WellFounded (fun u t : FreeTerm Nat => ContextStep t u)
  | .kbo .. => WellFounded (fun u t : FreeTerm Nat => ContextStep t u)
  | .dpSubterm _ => FreeTerminates

theorem check_sound : ∀ c : Certificate, check c = true → Proves c
  | .poly _ _ _ _, h => checkPoly_sound h Nat
  | .matrix d M, h => by
    simp [check, matrix_certificate_rejected] at h
  | .kbo K, h => by
    simp [check, kbo_certificate_rejected] at h
  | .dpSubterm _, h => checkDP_sound h

/-- The orientation boundary in the certificate language. No retentive affine polynomial, matrix
or Knuth-Bendix certificate is accepted; the counter-projection dependency-pair certificate and the
coupled polynomial certificate are accepted; every accepted certificate proves termination; on
certificates that pass the monomial test the polynomial checker accepts exactly the orienting
interpretations; on multilinear certificates it accepts exactly the interpretations that orient
both root rules and are strictly monotone in every argument; and the Knuth-Bendix checker accepts
exactly the admissible certificates whose order orients both root rules.

Proves: the conjunction of `affine_certificate_rejected`, `matrix_certificate_rejected`,
`kbo_certificate_rejected`, `counter_certificate_accepted`, `region_certificate_accepted`,
`check_sound`, `checkPoly_complete`, `checkPoly_iff_orients_strictContextLaws` and
`checkKBO_iff`.
Does not prove: acceptance of any matrix or Knuth-Bendix certificate; the polynomial equivalence
outside the multilinear class (`checkPoly_iff_needs_multilinear`).
Relation: `ContextStep` of the free recursor (`Proves`), `RootStep` for orientation,
`MethodRowsKBO.Gt (kboCore K)` for the Knuth-Bendix kind.
Closure: every constructor context for termination; root for orientation.
Strategy: full.
Trust: kernel-only.
Scope: the four certificate kinds over the two rules of the free recursor; polynomial certificates
with unit successor slope. -/
theorem certificate_boundary :
    (∀ z a α βw γ r0 rb rs rn : Nat, 1 ≤ βw → 1 ≤ γ →
        check (.poly z a (affineW α βw γ) (multilinearR r0 rb rs rn 0 0 0 0)) = false) ∧
      (∀ (d : Nat) (M : MatrixCert d), check (.matrix d M) = false) ∧
      (∀ K : KBOCert, check (.kbo K) = false) ∧
      check (.dpSubterm freeProj) = true ∧
      check (.poly 0 1 regionW (regionR 1 2)) = true ∧
      (∀ c : Certificate, check c = true → Proves c) ∧
      (∀ (z a : Nat) (W : List WMono) (R : List RMono), linearMonomials W R = true →
        (check (.poly z a W R) = true ↔ RootRuleOrients (polyInterpretation z 1 a W R) (· < ·))) ∧
      (∀ (z a : Nat) (W : List WMono) (R : List RMono), Multilinear W R →
        (check (.poly z a W R) = true ↔
          RootRuleOrients (polyInterpretation z 1 a W R) (· < ·) ∧
            StrictContextLaws (polyInterpretation z 1 a W R) (· < ·))) ∧
      (∀ K : KBOCert, check (.kbo K) = true ↔ (kboCore K).Laws ∧
        MethodRowsKBO.Gt (kboCore K) zeroRule.lhs zeroRule.rhs ∧
          MethodRowsKBO.Gt (kboCore K) succRule.lhs succRule.rhs) :=
  ⟨fun z a α βw γ r0 rb rs rn hβw hγ => affine_certificate_rejected z a α βw γ r0 rb rs rn hβw hγ,
    fun d M => matrix_certificate_rejected d M, fun K => kbo_certificate_rejected K,
    counter_certificate_accepted, region_certificate_accepted, check_sound,
    fun _ _ _ _ hm => checkPoly_complete hm,
    fun _ _ _ _ hml => checkPoly_iff_orients_strictContextLaws hml,
    fun K => checkKBO_iff K⟩

end OperatorKO7.Methods.OrientationClosure.CertificateLanguage
