import Mathlib

/-!
# QM-law mechanization: DERIVED monogamy of overlap + DERIVED qubit entropic-uncertainty floor
(SP2-119, SP2-120; audit close 2026-06-11)

This module closes the two named PROVEN targets left by the 2026-06-10 QM-law audit
(`qm-laws-lean-audit-2026-06-10.md`). The audit reclassified SP2-91 (CKW monogamy) and SP2-92
(Maassen-Uffink entropic uncertainty) from PROVEN to ESTABLISHED because their cataloged anchors
carried the named inequality as an ASSUMED structure field. Here both laws get a GENUINE finite
cousin whose bound is DERIVED, with no assumed-inequality field anywhere:

* **SP2-119 (monogamy of overlap, Bessel-derived).** For any normalized state `a` and any
  orthonormal partner pair `b, c`: the squared overlaps sum to at most one,
  `‖⟪b,a⟫‖² + ‖⟪c,a⟫‖² ≤ 1` (`overlap_monogamy`). Hence maximal overlap with one partner forces
  ZERO overlap with the other (`maximal_overlap_excludes`), and double-maximal sharing is
  impossible (`no_double_maximal`). DERIVED from Bessel's inequality
  (`Orthonormal.sum_inner_products_le`), not assumed. The exact CKW concurrence/tangle monogamy
  stays the named external fence (it needs concurrence, which has no Mathlib support).

* **SP2-120 (qubit entropic-uncertainty floor, derived).** For ANY normalized qubit amplitude
  pair `(a, b)` (hypothesis only `normSq a + normSq b = 1`), the Shannon entropies of the two
  COMPLEMENTARY readouts, the Z-readout `p_Z = normSq a` and the X-readout
  `p_X = normSq (a+b) / 2`, satisfy the DERIVED floor
  `H(p_Z) + H(p_X) ≥ log (16/9)` (`qubit_entropic_floor`).
  Derivation chain, every step proved here: (1) the Bloch constraint `x² + z² ≤ 1` is DERIVED
  from normalization (`bloch_constraint`, via the Brahmagupta-Fibonacci identity
  `x² + y² = 4·normSq a·normSq b`); (2) each readout entropy is bounded below by its collision
  entropy via two-point Jensen for the concave `log` (`binEntropy_ge_collision`,
  riding `strictConcaveOn_log_Ioi`); (3) the two collision floors combine over the Bloch disk by
  an AM-GM product bound (`(1+z²)(1+x²) ≤ 9/4`). The sharp Maassen-Uffink constant `log 2`
  (= `-2 log c` at the qubit overlap `c = 1/√2`) stays the named external fence: it needs a
  quadratic lower bound on `Real.binEntropy` that Mathlib does not currently carry; the derived
  floor `log (16/9)` is about 83 percent of the sharp constant in bits and is genuinely positive.

Claim typing (binding):
* PROVEN (the theorems below): the overlap-monogamy bound and the entropic floor are derived.
* ANALOGY (docstring only, never asserted by a theorem): the entanglement-monogamy and
  Maassen-Uffink identifications; `Z`/`X` as physical measurement bases.

## Audit slots
- Relation: NA (no rewriting relation). Inner-product and real-entropy arithmetic on Mathlib
  carriers (the SP2-107 pure-Mathlib-anchor precedent).
- Closure: `propext`, `Classical.choice`, `Quot.sound`; verified per headline by `#print axioms`.
- Trust: no `sorry`/`admit`/`axiom`/`native_decide`/`bv_decide`/`@[csimp]`/`implemented_by`/
  `unsafe`/`partial`/`opaque`. No structure carries an assumed inequality field.
- Non-vacuity (R5): the monogamy bound is EXACTLY attained on the standard qubit basis
  (`overlap_monogamy_witness_tight`), and the entropic floor is realized on the basis state
  `(1, 0)` with strictly positive floor (`qubit_entropic_floor_witness`, `floor_pos`).
- Scope: finite/discrete carriers; the two derived bounds only. QM readings are ANALOGY.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.ReverseBridge.QMLaw_MonogamyEntropicDerived

open Real

/-! ## SP2-119: monogamy of overlap, derived from Bessel's inequality -/

/-- **SP2-119 (PROVEN, derived monogamy of overlap).** A normalized state's squared overlaps with
the two members of an orthonormal pair sum to at most one. DERIVED from Bessel's inequality; no
assumed bound.

QM ANALOGY (docstring only, not asserted): a state cannot be strongly correlated with two
orthogonal partners at once; the finite overlap face of entanglement monogamy. The exact CKW
concurrence/tangle monogamy is the named external fence (parent row SP2-91, ESTABLISHED). -/
theorem overlap_monogamy {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {b c a : E} (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) (hbc : inner ℂ b c = 0) (ha : ‖a‖ = 1) :
    ‖inner ℂ b a‖ ^ 2 + ‖inner ℂ c a‖ ^ 2 ≤ 1 := by
  have hv : Orthonormal ℂ (![b, c]) := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j
    · simpa using by rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ), hb]; norm_num
    · simpa using hbc
    · simpa using (inner_eq_zero_symm).mp hbc
    · simpa using by rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ), hc]; norm_num
  have hB := hv.sum_inner_products_le (s := Finset.univ) a
  simpa [Fin.sum_univ_two, ha] using hB

/-- **SP2-119 (PROVEN, exclusion form).** Maximal overlap with one orthonormal partner forces
ZERO overlap with the other: the monogamy is sharp at the top. -/
theorem maximal_overlap_excludes {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {b c a : E} (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) (hbc : inner ℂ b c = 0) (ha : ‖a‖ = 1)
    (hmax : ‖inner ℂ b a‖ = 1) : inner ℂ c a = 0 := by
  have h := overlap_monogamy hb hc hbc ha
  rw [hmax] at h
  have hsq : ‖inner ℂ c a‖ ^ 2 ≤ 0 := by nlinarith
  have h0 : ‖inner ℂ c a‖ = 0 := by nlinarith [norm_nonneg (inner ℂ c a), sq_nonneg ‖inner ℂ c a‖]
  exact norm_eq_zero.mp h0

/-- **SP2-119 (PROVEN, no-double-maximal form).** No normalized state has maximal overlap with
BOTH members of an orthonormal pair: the derived counterpart of "monogamy blocks double-maximal
sharing" (whose previous anchor assumed its bound). -/
theorem no_double_maximal {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {b c a : E} (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) (hbc : inner ℂ b c = 0) (ha : ‖a‖ = 1) :
    ¬ (‖inner ℂ b a‖ = 1 ∧ ‖inner ℂ c a‖ = 1) := by
  rintro ⟨h1, h2⟩
  have h := overlap_monogamy hb hc hbc ha
  rw [h1, h2] at h
  norm_num at h

/-- **R5 non-vacuity (SP2-119), tight witness.** On the standard qubit basis the monogamy bound
is attained EXACTLY: the state `e₀` has full overlap with `e₀` and zero with `e₁`, summing to the
bound `1`. So the inequality is sharp, not loose, and the carrier is inhabited. -/
theorem overlap_monogamy_witness_tight :
    ‖inner ℂ (EuclideanSpace.single (0 : Fin 2) (1 : ℂ))
        (EuclideanSpace.single (0 : Fin 2) (1 : ℂ))‖ ^ 2
      + ‖inner ℂ (EuclideanSpace.single (1 : Fin 2) (1 : ℂ))
          (EuclideanSpace.single (0 : Fin 2) (1 : ℂ))‖ ^ 2 = 1 := by
  rw [EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_left]
  simp [EuclideanSpace.single_apply]

/-! ## SP2-120: qubit entropic-uncertainty floor, derived -/

/-- Collision-entropy floor for the binary Shannon entropy, by two-point Jensen for the concave
`Real.log`: `-log (p² + (1-p)²) ≤ binEntropy p` on `[0,1]`. DERIVED (rides
`strictConcaveOn_log_Ioi`); the totalization edge cases `p = 0, 1` close by direct evaluation. -/
theorem binEntropy_ge_collision (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    -Real.log (p ^ 2 + (1 - p) ^ 2) ≤ Real.binEntropy p := by
  rcases eq_or_lt_of_le hp0 with h0 | hp0'
  · rw [← h0]
    norm_num
  rcases eq_or_lt_of_le hp1 with h1 | hp1'
  · rw [h1]
    norm_num
  have hq0' : (0 : ℝ) < 1 - p := by linarith
  have hcc := strictConcaveOn_log_Ioi.concaveOn
  have hjen := hcc.2 (Set.mem_Ioi.mpr hp0') (Set.mem_Ioi.mpr hq0')
    (le_of_lt hp0') (le_of_lt hq0') (by ring : p + (1 - p) = 1)
  simp only [smul_eq_mul] at hjen
  have hform : p * p + (1 - p) * (1 - p) = p ^ 2 + (1 - p) ^ 2 := by ring
  rw [hform] at hjen
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  simp only [Real.negMulLog]
  nlinarith [hjen]

/-- The per-readout floor in Bloch form: for `t ∈ [-1, 1]`,
`log 2 - log (1 + t²) ≤ binEntropy ((1 + t)/2)`. The collision value at probability `(1+t)/2`
is `(1 + t²)/2`. -/
theorem binEntropy_bloch_floor (t : ℝ) (h1 : -1 ≤ t) (h2 : t ≤ 1) :
    Real.log 2 - Real.log (1 + t ^ 2) ≤ Real.binEntropy ((1 + t) / 2) := by
  have hp0 : (0 : ℝ) ≤ (1 + t) / 2 := by linarith
  have hp1 : (1 + t) / 2 ≤ 1 := by linarith
  have hc := binEntropy_ge_collision ((1 + t) / 2) hp0 hp1
  have hcoll : ((1 + t) / 2) ^ 2 + (1 - (1 + t) / 2) ^ 2 = (1 + t ^ 2) / 2 := by ring
  rw [hcoll] at hc
  have hpos : (0 : ℝ) < 1 + t ^ 2 := by positivity
  rw [Real.log_div (ne_of_gt hpos) (by norm_num)] at hc
  linarith

/-- **The Bloch constraint, DERIVED from normalization.** For any amplitudes with
`normSq a + normSq b = 1`, the X- and Z-coordinates `x = 2(Re a·Re b + Im a·Im b)` and
`z = normSq a - normSq b` satisfy `x² + z² ≤ 1`. The slack is exactly the Y-coordinate:
`x² + y² = 4·normSq a·normSq b` (Brahmagupta-Fibonacci), so `x² + z² = 1 - y² ≤ 1`. -/
theorem bloch_constraint (a b : ℂ) (hn : Complex.normSq a + Complex.normSq b = 1) :
    (2 * (a.re * b.re + a.im * b.im)) ^ 2 + (Complex.normSq a - Complex.normSq b) ^ 2 ≤ 1 := by
  have hna : Complex.normSq a = a.re ^ 2 + a.im ^ 2 := by
    rw [Complex.normSq_apply]; ring
  have hnb : Complex.normSq b = b.re ^ 2 + b.im ^ 2 := by
    rw [Complex.normSq_apply]; ring
  have key : (2 * (a.re * b.re + a.im * b.im)) ^ 2 + (2 * (a.re * b.im - a.im * b.re)) ^ 2
      = 4 * Complex.normSq a * Complex.normSq b := by
    rw [hna, hnb]; ring
  nlinarith [sq_nonneg (2 * (a.re * b.im - a.im * b.re)), key, hn]

/-- The X-readout probability in Bloch form: `normSq (a+b) / 2 = (1 + x)/2`. -/
theorem xReadout_eq (a b : ℂ) (hn : Complex.normSq a + Complex.normSq b = 1) :
    Complex.normSq (a + b) / 2 = (1 + 2 * (a.re * b.re + a.im * b.im)) / 2 := by
  have hadd : Complex.normSq (a + b)
      = Complex.normSq a + Complex.normSq b + 2 * (a.re * b.re + a.im * b.im) := by
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im]
    ring
  rw [hadd, hn]

/-- **SP2-120 (PROVEN, derived qubit entropic-uncertainty floor).** For ANY normalized qubit
amplitude pair, the summed Shannon entropies of the two complementary readouts (`Z`-readout
`normSq a`, `X`-readout `normSq (a+b)/2`) are at least `log (16/9) > 0`: both complementary
readouts cannot be sharp together. Every input is DERIVED: the Bloch constraint from
normalization, the per-readout collision floor from Jensen, the product bound by AM-GM.

QM ANALOGY (docstring only, not asserted): the Maassen-Uffink entropic uncertainty relation for
the qubit `Z`/`X` pair. The sharp constant `log 2 = -2 log c` at `c = 1/√2` is the named external
fence (needs a quadratic `binEntropy` lower bound absent from Mathlib); this floor is
`log (16/9) ≈ 0.83` bits of the sharp `1` bit. Parents SP2-17 and SP2-92 stay ESTABLISHED. -/
theorem qubit_entropic_floor (a b : ℂ) (hn : Complex.normSq a + Complex.normSq b = 1) :
    Real.log (16 / 9) ≤ Real.binEntropy (Complex.normSq a)
      + Real.binEntropy (Complex.normSq (a + b) / 2) := by
  set x : ℝ := 2 * (a.re * b.re + a.im * b.im) with hxdef
  set z : ℝ := Complex.normSq a - Complex.normSq b with hzdef
  have hna : (0 : ℝ) ≤ Complex.normSq a := Complex.normSq_nonneg a
  have hnb : (0 : ℝ) ≤ Complex.normSq b := Complex.normSq_nonneg b
  have hpZ : Complex.normSq a = (1 + z) / 2 := by rw [hzdef]; linarith
  have hpX : Complex.normSq (a + b) / 2 = (1 + x) / 2 := by
    rw [xReadout_eq a b hn]
  have hcon : x ^ 2 + z ^ 2 ≤ 1 := bloch_constraint a b hn
  have hz1 : -1 ≤ z := by rw [hzdef]; linarith
  have hz2 : z ≤ 1 := by rw [hzdef]; linarith
  have hx2 : x ^ 2 ≤ 1 := by nlinarith [sq_nonneg z]
  have hx1a : -1 ≤ x := by nlinarith
  have hx1b : x ≤ 1 := by nlinarith
  have hZ := binEntropy_bloch_floor z hz1 hz2
  have hX := binEntropy_bloch_floor x hx1a hx1b
  rw [← hpZ] at hZ
  rw [← hpX] at hX
  have hzpos : (0 : ℝ) < 1 + z ^ 2 := by positivity
  have hxpos : (0 : ℝ) < 1 + x ^ 2 := by positivity
  have hprod : (1 + z ^ 2) * (1 + x ^ 2) ≤ 9 / 4 := by
    nlinarith [sq_nonneg (z ^ 2 - x ^ 2), sq_nonneg z, sq_nonneg x, sq_nonneg (x * z), hcon]
  have hlog : Real.log (1 + z ^ 2) + Real.log (1 + x ^ 2) ≤ Real.log (9 / 4) := by
    rw [← Real.log_mul (ne_of_gt hzpos) (ne_of_gt hxpos)]
    exact Real.log_le_log (by positivity) hprod
  have h169 : Real.log (16 / 9) = 2 * Real.log 2 - Real.log (9 / 4) := by
    rw [show (16 : ℝ) / 9 = 2 ^ 2 / (9 / 4) by norm_num,
      Real.log_div (by norm_num) (by norm_num), Real.log_pow]
    push_cast
    ring
  linarith

/-! ## Non-vacuity (R5 witnesses) -/

/-- **R5 non-vacuity (SP2-120).** The floor is realized on the concrete basis state `(1, 0)`:
`H(Z) = 0`, `H(X) = log 2`, and `log (16/9) ≤ log 2`. The bounded set is inhabited. -/
theorem qubit_entropic_floor_witness :
    Real.log (16 / 9) ≤ Real.binEntropy (Complex.normSq 1)
      + Real.binEntropy (Complex.normSq (1 + 0) / 2) :=
  qubit_entropic_floor 1 0 (by simp)

/-- **R5 non-vacuity (SP2-120), positivity.** The derived floor is strictly positive, so the
entropic-uncertainty statement has genuine content (the trivial floor `0` is strictly beaten). -/
theorem floor_pos : 0 < Real.log (16 / 9) :=
  Real.log_pos (by norm_num)

-- Axiom inventory (must be a subset of `{propext, Classical.choice, Quot.sound}`).
#print axioms overlap_monogamy
#print axioms maximal_overlap_excludes
#print axioms no_double_maximal
#print axioms overlap_monogamy_witness_tight
#print axioms binEntropy_ge_collision
#print axioms binEntropy_bloch_floor
#print axioms bloch_constraint
#print axioms qubit_entropic_floor
#print axioms qubit_entropic_floor_witness
#print axioms floor_pos

end OperatorKO7.Meta.ReverseBridge.QMLaw_MonogamyEntropicDerived
