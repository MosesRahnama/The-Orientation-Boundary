import OperatorKO7.Meta.UUET.FiniteSignedAmplitudeBorn

set_option autoImplicit false

/-!
# UUET finite complex/phase amplitude Born carrier (U-62)

This extends the signed-real amplitude carrier (U-61) to a finite *complex/phase*
amplitude, using a lightweight real-pair representation `CAmp = (re, im)` with
`normSq = re^2 + im^2` (no heavy `Complex` import). A two-branch complex amplitude
pair gives Born weights

 `cWeightA = normSq A / (normSq A + normSq B)`,
 `cWeightB = normSq B / (normSq A + normSq B)`.

What is proven: the denominator is strictly positive (amplitudes not both zero),
the weights are nonnegative and normalized, and they are *gauge invariant*: the
weights depend only on the two `normSq` values (`cWeightA_eq_of_normSq_eq`), and
`normSq` is invariant under the global sign flip `(re, im) -> (-re, -im)`
(`CAmp.normSq_neg`) and under a finite rotation `(c, s)` with `c^2 + s^2 = 1`
(`CAmp.normSq_rotate`). The carrier reduces to the U-61 signed-real case when the
imaginary parts vanish (`cWeightA_reduces_to_signed`), and a dual-boundary theorem
links a committed terminal record to a normalized two-branch Born ledger
(`complexBorn_terminal_record_ledger`). A phase-bearing witness `(1+i, 1)` gives
`cWeightA = 2/3`, showing that the finite carrier records squared modulus from
both real and imaginary coordinates. This is a richer carrier than sign-flip
invariance alone, not a uniqueness claim about probability-weight
representations.

Scope and honesty: FINITE STRUCTURAL Lean over real pairs. The `normSq` ratio is
the finite `|.|^2` Born form; this is NOT Hilbert-space quantum mechanics (no
complex Hilbert space, no state vector, no Born postulate). The reading as physical
Born probabilities is a structural model, not a Lean claim. No `sorry`, `admit`,
new `axiom`, `native_decide`, `bv_decide`, `@[csimp]`, `unsafe`, `partial`, or
`opaque`. Headline declarations are `#print axioms`-checked against the baseline
whitelist `{propext, Classical.choice, Quot.sound}`.
-/

namespace OperatorKO7.Meta.UUET

noncomputable section

/-- A finite complex amplitude as a real pair `(re, im)`. -/
structure CAmp where
  re : ℝ
  im : ℝ

namespace CAmp

/-- The squared modulus `re^2 + im^2`. -/
def normSq (z : CAmp) : ℝ := z.re ^ 2 + z.im ^ 2

theorem normSq_nonneg (z : CAmp) : 0 ≤ z.normSq := by
  unfold normSq; positivity

/-- `normSq` is invariant under the global sign flip `(re, im) -> (-re, -im)`. -/
theorem normSq_neg (z : CAmp) :
    (CAmp.mk (-z.re) (-z.im)).normSq = z.normSq := by
  simp only [normSq]; ring

/-- A finite rotation of an amplitude by `(c, s)`. -/
def rotate (z : CAmp) (c s : ℝ) : CAmp :=
  CAmp.mk (c * z.re - s * z.im) (s * z.re + c * z.im)

/-- `normSq` is invariant under a finite rotation with `c^2 + s^2 = 1`. -/
theorem normSq_rotate (z : CAmp) (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) :
    (z.rotate c s).normSq = z.normSq := by
  simp only [rotate, normSq]
  have hexp :
      (c * z.re - s * z.im) ^ 2 + (s * z.re + c * z.im) ^ 2
        = (c ^ 2 + s ^ 2) * (z.re ^ 2 + z.im ^ 2) := by ring
  rw [hexp, h, one_mul]

end CAmp

/-- A finite two-branch complex amplitude pair, not both branches zero. -/
structure ComplexBranchPair where
  A : CAmp
  B : CAmp
  ne_zero : ¬ (A.normSq = 0 ∧ B.normSq = 0)

namespace ComplexBranchPair

/-- The total weight `normSq A + normSq B`. -/
def total (p : ComplexBranchPair) : ℝ := p.A.normSq + p.B.normSq

theorem total_pos (p : ComplexBranchPair) : 0 < p.total := by
  unfold total
  rcases not_and_or.mp p.ne_zero with hA | hB
  · have hA' : 0 < p.A.normSq := (p.A.normSq_nonneg).lt_of_ne (Ne.symm hA)
    have hB' := p.B.normSq_nonneg
    linarith
  · have hB' : 0 < p.B.normSq := (p.B.normSq_nonneg).lt_of_ne (Ne.symm hB)
    have hA' := p.A.normSq_nonneg
    linarith

theorem total_ne_zero (p : ComplexBranchPair) : p.total ≠ 0 := p.total_pos.ne'

end ComplexBranchPair

/-- The complex Born weight of branch A. -/
def cWeightA (p : ComplexBranchPair) : ℝ := p.A.normSq / p.total

/-- The complex Born weight of branch B. -/
def cWeightB (p : ComplexBranchPair) : ℝ := p.B.normSq / p.total

theorem cWeightA_nonneg (p : ComplexBranchPair) : 0 ≤ cWeightA p :=
  div_nonneg p.A.normSq_nonneg p.total_pos.le

theorem cWeightB_nonneg (p : ComplexBranchPair) : 0 ≤ cWeightB p :=
  div_nonneg p.B.normSq_nonneg p.total_pos.le

/-- **Normalization.** The two complex Born weights sum to one. -/
theorem cWeights_normalized (p : ComplexBranchPair) :
    cWeightA p + cWeightB p = 1 := by
  unfold cWeightA cWeightB
  rw [div_add_div_same]
  exact div_self p.total_ne_zero

/-- **Gauge invariance (master).** The complex Born weight of branch A depends only
on the two `normSq` values: any amplitude transformation preserving both `normSq`
values leaves the weight unchanged. -/
theorem cWeightA_eq_of_normSq_eq (p p' : ComplexBranchPair)
    (hA : p'.A.normSq = p.A.normSq) (hB : p'.B.normSq = p.B.normSq) :
    cWeightA p' = cWeightA p := by
  unfold cWeightA ComplexBranchPair.total
  rw [hA, hB]

/-- **Reduction to the signed-real case.** A complex pair whose amplitudes are the
real embedding of a signed amplitude `s` has the same Born weight as `s`. -/
theorem cWeightA_reduces_to_signed (s : SignedAmplitude) (p : ComplexBranchPair)
    (hA : p.A = CAmp.mk s.a 0) (hB : p.B = CAmp.mk s.b 0) :
    cWeightA p = weightA s := by
  unfold cWeightA ComplexBranchPair.total weightA SignedAmplitude.norm2
  rw [hA, hB]
  simp [CAmp.normSq]

/-- **Dual-boundary theorem.** A committed terminal record (U-27) together with a
complex amplitude carrier yields a normalized, nonnegative two-branch Born ledger,
and the committed record has zero entanglement magnitude (a separable classical
record). -/
theorem complexBorn_terminal_record_ledger
    (s : OperationalCompletenessState) (h : terminalRecordLicensed s)
    (p : ComplexBranchPair) :
    cWeightA p + cWeightB p = 1
      ∧ 0 ≤ cWeightA p
      ∧ 0 ≤ cWeightB p
      ∧ entanglementMagnitude (descentLicensedOf s) (distinctionLicensedOf s) = 0 :=
  ⟨cWeights_normalized p, cWeightA_nonneg p, cWeightB_nonneg p,
    entanglementMagnitude_collapses_on_terminal_record s h⟩

/-- The balanced complex pair `(1, i)`: equal `normSq`, weights `(1/2, 1/2)`. -/
def balancedComplex : ComplexBranchPair where
  A := CAmp.mk 1 0
  B := CAmp.mk 0 1
  ne_zero := by norm_num [CAmp.normSq]

theorem balancedComplex_cWeightA : cWeightA balancedComplex = 1 / 2 := by
  unfold cWeightA ComplexBranchPair.total balancedComplex CAmp.normSq; norm_num

/-- The collapsed complex pair `(1, 0)`: all weight on branch A. -/
def collapsedComplex : ComplexBranchPair where
  A := CAmp.mk 1 0
  B := CAmp.mk 0 0
  ne_zero := by norm_num [CAmp.normSq]

theorem collapsedComplex_cWeightA : cWeightA collapsedComplex = 1 := by
  unfold cWeightA ComplexBranchPair.total collapsedComplex CAmp.normSq; norm_num

theorem collapsedComplex_cWeightB : cWeightB collapsedComplex = 0 := by
  unfold cWeightB ComplexBranchPair.total collapsedComplex CAmp.normSq; norm_num

/-- A phase-bearing pair `(1 + i, 1)`: `normSq A = 2`, `normSq B = 1`, weight
`2/3`. The imaginary coordinate contributes to `normSq A`, which is not captured
by sign-flip invariance alone. -/
def phaseComplex : ComplexBranchPair where
  A := CAmp.mk 1 1
  B := CAmp.mk 1 0
  ne_zero := by norm_num [CAmp.normSq]

theorem phaseComplex_cWeightA : cWeightA phaseComplex = 2 / 3 := by
  unfold cWeightA ComplexBranchPair.total phaseComplex CAmp.normSq; norm_num

/-- Non-vacuity: balanced `(1/2)`, collapsed `(1, 0)`, the phase-bearing `2/3`
witness, and the global normalization and nonnegativity. -/
theorem finiteComplexAmplitudeBorn_nonvacuous :
    cWeightA balancedComplex = 1 / 2
      ∧ cWeightA collapsedComplex = 1
      ∧ cWeightB collapsedComplex = 0
      ∧ cWeightA phaseComplex = 2 / 3
      ∧ (∀ p : ComplexBranchPair, cWeightA p + cWeightB p = 1)
      ∧ (∀ p : ComplexBranchPair, 0 ≤ cWeightA p) :=
  ⟨balancedComplex_cWeightA, collapsedComplex_cWeightA, collapsedComplex_cWeightB,
    phaseComplex_cWeightA, cWeights_normalized, cWeightA_nonneg⟩

#print axioms CAmp.normSq_neg
#print axioms CAmp.normSq_rotate
#print axioms ComplexBranchPair.total_pos
#print axioms cWeights_normalized
#print axioms cWeightA_eq_of_normSq_eq
#print axioms cWeightA_reduces_to_signed
#print axioms complexBorn_terminal_record_ledger
#print axioms phaseComplex_cWeightA
#print axioms finiteComplexAmplitudeBorn_nonvacuous

end

end OperatorKO7.Meta.UUET
