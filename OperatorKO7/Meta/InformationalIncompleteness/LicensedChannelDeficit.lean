import OperatorKO7.Meta.InformationalIncompleteness.ShannonFinite
import OperatorKO7.Meta.InformationalIncompleteness.ConditionalEntropy
import OperatorKO7.Meta.InformationalIncompleteness.QueryInterface

/-!
# The licensed-channel information deficit and the informational circular reference

This module formalises, for an arbitrary information system, the **licensed-channel information deficit**:
the conditional mutual information of a target with a licensed channel given the querant's direct surface,
`deficit = I(target ; C | W0) = H(target | W0) - H(target | W0, C)`.

The deficit measures how much a licensed channel reduces the querant's residual uncertainty about a target
beyond what the direct surface `W0` (the information the querant already holds) commits. Its zero case is the
**informational circular reference**: a non-vacuous query whose answer carries no information about the
target beyond what the querant already had returns vacuous. The motivating instance is domain-independent:
a genuine query to an object layer, "what is the step-duplicating recursor rule?", returned to the querant
the querant's own prior writings, presented as authority. The query was non-vacuous when issued
(`H(target | W0) > 0`), but the answer was a copy of the querant's own committed information (`W0`), so it
carried no new information about the target: the non-vacuous query returned vacuous.

Load-bearing structural facts:

* `deficit_nonneg` — the deficit is well defined and `≥ 0` (per-`W0`-cell concave Jensen, reusing the
  conditioning inequality `condEntropy_le_H_mixture`).
* `circular_reference_zero_deficit` — if the channel carries no target information beyond `W0` (its target
  conditional does not depend on the channel cell; the answer is informationally a copy of `W0`), then the
  deficit is zero. This is the conditional shadow of the diagonal-entropy lemma (a redundant copy of what
  one already holds carries no independent information) and is the formal content of the informational
  circular reference: the non-vacuous query returns vacuous.
* `positive_deficit_requires_exogeny` — contrapositive: a nonzero deficit forces a genuinely exogenous
  channel (the target conditional must vary across channel cells).

Honesty: this is finite classical information theory. The objects are domain-independent. Particular
readings (in foundations of computation, the AI self-retrieval circular reference; in markets, the
licensed-channel deficit as a price premium / alpha) are interpretations carried in prose and never in a
theorem; the market instantiation is developed in the Boundary Premium Program, not here. The module
formalises the DEFINITION of the deficit and the STRUCTURAL theorems about it; it does not assert that any
particular channel has positive deficit on any particular data. No rewriting relation. Trust: no
`sorry`/`admit`/`axiom`/`native_decide`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace OperatorKO7.Meta.InformationalIncompleteness.LicensedChannelDeficit

open OperatorKO7.Meta.InformationalIncompleteness.ShannonFinite
open OperatorKO7.Meta.InformationalIncompleteness.ConditionalEntropy
open OperatorKO7.Meta.InformationalIncompleteness.QueryInterface

variable {X W Cn : Type} [Fintype X] [Fintype W] [Fintype Cn]

/-- `H(target | W0)`: per-`W0`-cell entropy of the channel-marginalised target conditional.
`μ w` is the weight of direct-surface cell `w`, `ν w c` the conditional weight of channel cell `c`, and
`r w c` the target conditional given `(w, c)`. -/
noncomputable def condEntropyDirect (μ : W → ℝ) (ν : W → Cn → ℝ) (r : W → Cn → X → ℝ) : ℝ :=
  ∑ w, μ w * H (fun x => ∑ c, ν w c * r w c x)

/-- `H(target | W0, C)`: per-`(W0,C)`-cell entropy of the target conditional. -/
noncomputable def condEntropyLicensed (μ : W → ℝ) (ν : W → Cn → ℝ) (r : W → Cn → X → ℝ) : ℝ :=
  ∑ w, μ w * (∑ c, ν w c * H (r w c))

/-- **Licensed-channel information deficit** = the conditional mutual information
`I(target ; C | W0) = H(target | W0) - H(target | W0, C)`: how much the licensed channel `C` reduces the
querant's residual uncertainty about the target beyond the direct surface `W0`. -/
noncomputable def deficit (μ : W → ℝ) (ν : W → Cn → ℝ) (r : W → Cn → X → ℝ) : ℝ :=
  condEntropyDirect μ ν r - condEntropyLicensed μ ν r

/--
Proves: the deficit is nonnegative (`I(target ; C | W0) ≥ 0`). A licensed channel never increases the
  conditional entropy of the target. The proof is the conditioning inequality `condEntropy_le_H_mixture`
  (concave Jensen for `negMulLog`) applied in each direct-surface cell, then a nonnegative-weighted sum.
Does not prove: strict positivity (that is the exogenous-channel case / an empirical question).
Relation: not applicable. Closure: not applicable. Trust: kernel-only.
Scope: every finite `X, W, Cn`, weights `μ ≥ 0`, channel weights `ν ≥ 0` with `∑_c ν w c = 1`, and
  nonnegative conditionals `r`.
-/
theorem deficit_nonneg (μ : W → ℝ) (ν : W → Cn → ℝ) (r : W → Cn → X → ℝ)
    (hμ0 : ∀ w, 0 ≤ μ w)
    (hν0 : ∀ w c, 0 ≤ ν w c) (hν1 : ∀ w, ∑ c, ν w c = 1)
    (hr0 : ∀ w c x, 0 ≤ r w c x) :
    0 ≤ deficit μ ν r := by
  unfold deficit condEntropyDirect condEntropyLicensed
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_nonneg
  intro w _
  have hbracket : (∑ c, ν w c * H (r w c)) ≤ H (fun x => ∑ c, ν w c * r w c x) := by
    have h := condEntropy_le_H_mixture (lam := ν w) (q := r w) (hν0 w) (hν1 w) (fun c x => hr0 w c x)
    simpa [condEntropy, mixture] using h
  have hrw : μ w * H (fun x => ∑ c, ν w c * r w c x) - μ w * (∑ c, ν w c * H (r w c))
      = μ w * (H (fun x => ∑ c, ν w c * r w c x) - (∑ c, ν w c * H (r w c))) := by ring
  rw [hrw]
  exact mul_nonneg (hμ0 w) (by linarith)

/--
Proves: the informational circular reference. If the channel carries no target information beyond `W0` (the
  target conditional `r w c` does not depend on the channel cell `c`; equivalently the answer is
  informationally a copy of what `W0` already fixes), then the deficit is zero. This is the conditional
  shadow of the diagonal-entropy lemma: a redundant copy of what the querant already holds carries no
  independent information, so the non-vacuous query returns vacuous. The motivating instance is the
  self-retrieval circular reference: a query whose answer is the querant's own committed information.
Does not prove: that a given empirical channel is of this form (that is observed, not proved).
Relation: not applicable. Closure: not applicable. Trust: kernel-only.
Scope: every finite `X, W, Cn`, channel weights with `∑_c ν w c = 1`, and channel-constant conditional `s`.
-/
theorem circular_reference_zero_deficit (μ : W → ℝ) (ν : W → Cn → ℝ) (r : W → Cn → X → ℝ)
    (hν1 : ∀ w, ∑ c, ν w c = 1)
    (s : W → X → ℝ) (hconst : ∀ w c, r w c = s w) :
    deficit μ ν r = 0 := by
  unfold deficit condEntropyDirect condEntropyLicensed
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_eq_zero
  intro w _
  have hmix : (fun x => ∑ c, ν w c * r w c x) = s w := by
    funext x
    calc ∑ c, ν w c * r w c x = ∑ c, ν w c * s w x := by
            refine Finset.sum_congr rfl (fun c _ => ?_); rw [hconst w c]
      _ = (∑ c, ν w c) * s w x := by rw [← Finset.sum_mul]
      _ = s w x := by rw [hν1 w, one_mul]
  have hlic : (∑ c, ν w c * H (r w c)) = H (s w) := by
    calc ∑ c, ν w c * H (r w c) = ∑ c, ν w c * H (s w) := by
            refine Finset.sum_congr rfl (fun c _ => ?_); rw [hconst w c]
      _ = (∑ c, ν w c) * H (s w) := by rw [← Finset.sum_mul]
      _ = H (s w) := by rw [hν1 w, one_mul]
  rw [hmix, hlic]; ring

/--
Proves: contrapositive of `circular_reference_zero_deficit`. If the deficit is nonzero then the channel
  cannot be a redundant copy of the direct surface: its target conditional must genuinely depend on the
  channel cell. A positive licensed deficit forces a genuinely exogenous channel.
Does not prove: a quantitative lower bound. Relation/Closure: not applicable. Trust: kernel-only.
Scope: as `circular_reference_zero_deficit`.
-/
theorem positive_deficit_requires_exogeny (μ : W → ℝ) (ν : W → Cn → ℝ) (r : W → Cn → X → ℝ)
    (hν1 : ∀ w, ∑ c, ν w c = 1) (hd : deficit μ ν r ≠ 0) :
    ¬ ∃ s : W → X → ℝ, ∀ w c, r w c = s w := by
  rintro ⟨s, hs⟩
  exact hd (circular_reference_zero_deficit μ ν r hν1 s hs)

/-! ## Quantitative bracket: the deficit lies between zero and the residual uncertainty.

The echo vacuum (`circular_reference_zero_deficit`) is not an isolated zero; it is the lower end of a
quantitative interval. A licensed channel can reduce the querant's residual uncertainty about the target
by at most the total residual uncertainty `H(target | W0)` the querant started with, so the deficit is
sandwiched: `0 ≤ deficit ≤ H(target | W0)`. The lower end is achieved exactly by a channel that is a
redundant copy of `W0` (the echo vacuum, `circular_reference_zero_deficit`); the upper end is achieved
exactly by a channel that leaves no residual entropy in any cell (a fully resolving channel,
`deficit_eq_condEntropyDirect_of_zero_residual`). -/

/--
Proves: the per-`(W0,C)`-cell conditional entropy `H(target | W0, C)` (`condEntropyLicensed`) is
  nonnegative when the target conditionals are sub-distributions (`0 ≤ r w c x ≤ 1`). Each cell entropy
  is `≥ 0` by `H_nonneg`, then a nonnegative-weighted double sum.
Does not prove: strict positivity. Relation: not applicable. Closure: not applicable. Trust: kernel-only.
Scope: every finite `X, W, Cn`, weights `μ ≥ 0`, channel weights `ν ≥ 0`, sub-distribution conditionals.
-/
theorem condEntropyLicensed_nonneg (μ : W → ℝ) (ν : W → Cn → ℝ) (r : W → Cn → X → ℝ)
    (hμ0 : ∀ w, 0 ≤ μ w) (hν0 : ∀ w c, 0 ≤ ν w c)
    (hr0 : ∀ w c x, 0 ≤ r w c x) (hr1 : ∀ w c x, r w c x ≤ 1) :
    0 ≤ condEntropyLicensed μ ν r := by
  unfold condEntropyLicensed
  apply Finset.sum_nonneg
  intro w _
  apply mul_nonneg (hμ0 w)
  apply Finset.sum_nonneg
  intro c _
  exact mul_nonneg (hν0 w c) (H_nonneg (r w c) (hr0 w c) (hr1 w c))

/--
Proves: the deficit is at most the residual uncertainty `H(target | W0)` (`condEntropyDirect`): a
  licensed channel reduces the target uncertainty by at most what was there. Since
  `deficit = condEntropyDirect - condEntropyLicensed` and `condEntropyLicensed ≥ 0`.
Does not prove: that the bound is achieved for a given channel (that is the zero-residual case).
Relation: not applicable. Closure: not applicable. Trust: kernel-only.
Scope: weights `μ ≥ 0`, channel weights `ν ≥ 0`, sub-distribution conditionals.
-/
theorem deficit_le_condEntropyDirect (μ : W → ℝ) (ν : W → Cn → ℝ) (r : W → Cn → X → ℝ)
    (hμ0 : ∀ w, 0 ≤ μ w) (hν0 : ∀ w c, 0 ≤ ν w c)
    (hr0 : ∀ w c x, 0 ≤ r w c x) (hr1 : ∀ w c x, r w c x ≤ 1) :
    deficit μ ν r ≤ condEntropyDirect μ ν r := by
  have h := condEntropyLicensed_nonneg μ ν r hμ0 hν0 hr0 hr1
  unfold deficit
  linarith

/--
Proves: the two-sided quantitative bracket `0 ≤ deficit ≤ H(target | W0)`. The licensed channel's
  information gain about the target is bounded below by zero (the echo vacuum) and above by the
  querant's residual uncertainty before consulting the channel. This sharpens the qualitative echo
  vacuum into a quantitative interval whose bottom is the vacuum.
Relation: not applicable. Closure: not applicable. Trust: kernel-only.
Scope: weights `μ ≥ 0`, channel weights `ν ≥ 0` with `∑_c ν w c = 1`, sub-distribution conditionals.
-/
theorem deficit_bracket (μ : W → ℝ) (ν : W → Cn → ℝ) (r : W → Cn → X → ℝ)
    (hμ0 : ∀ w, 0 ≤ μ w) (hν0 : ∀ w c, 0 ≤ ν w c) (hν1 : ∀ w, ∑ c, ν w c = 1)
    (hr0 : ∀ w c x, 0 ≤ r w c x) (hr1 : ∀ w c x, r w c x ≤ 1) :
    0 ≤ deficit μ ν r ∧ deficit μ ν r ≤ condEntropyDirect μ ν r :=
  ⟨deficit_nonneg μ ν r hμ0 hν0 hν1 hr0,
   deficit_le_condEntropyDirect μ ν r hμ0 hν0 hr0 hr1⟩

/--
Proves: the upper bound is achieved exactly when the licensed channel leaves no residual entropy in any
  cell (`H(r w c) = 0` for all `w, c`, a fully resolving / determinate channel): then
  `deficit = H(target | W0)`. The channel extracts ALL of the querant's residual uncertainty as deficit,
  so the bracket's upper end is tight.
Does not prove: that a given empirical channel resolves the target (that is observed, not proved).
Relation: not applicable. Closure: not applicable. Trust: kernel-only.
-/
theorem deficit_eq_condEntropyDirect_of_zero_residual (μ : W → ℝ) (ν : W → Cn → ℝ)
    (r : W → Cn → X → ℝ) (hres : ∀ w c, H (r w c) = 0) :
    deficit μ ν r = condEntropyDirect μ ν r := by
  have hlic : condEntropyLicensed μ ν r = 0 := by
    unfold condEntropyLicensed
    apply Finset.sum_eq_zero
    intro w _
    have hinner : (∑ c, ν w c * H (r w c)) = 0 := by
      apply Finset.sum_eq_zero
      intro c _
      rw [hres w c, mul_zero]
    rw [hinner, mul_zero]
  unfold deficit
  rw [hlic, sub_zero]

/-! ## R5 non-vacuity witnesses. -/

/-- R5 (positive deficit): a one-cell direct surface (`W = Fin 1`), a binary target (`X = Fin 2`), and a
binary channel (`Cn = Fin 2`) that perfectly reveals the target. The licensed conditional entropy is zero
while the direct conditional entropy is the binary-uniform entropy, so the deficit is positive. -/
theorem deficit_witness_pos :
    0 < deficit (W := Fin 1) (Cn := Fin 2) (X := Fin 2)
      (fun _ => 1) (fun _ _ => (1 : ℝ) / 2) (fun _ c => pointMass c) := by
  have hdir : condEntropyDirect (W := Fin 1) (Cn := Fin 2) (X := Fin 2)
      (fun _ => 1) (fun _ _ => (1 : ℝ) / 2) (fun _ c => pointMass c)
      = H (fun _ : Fin 2 => (1 : ℝ) / 2) := by
    unfold condEntropyDirect
    rw [Fin.sum_univ_one, one_mul]
    congr 1
    funext x
    fin_cases x <;> simp [pointMass]
  have hlic : condEntropyLicensed (W := Fin 1) (Cn := Fin 2) (X := Fin 2)
      (fun _ => 1) (fun _ _ => (1 : ℝ) / 2) (fun _ c => pointMass c) = 0 := by
    unfold condEntropyLicensed
    simp [H_pointMass]
  unfold deficit
  rw [hdir, hlic, sub_zero]
  exact query_confession_condEntropy_pos (fun _ => (1 : ℝ) / 2)
    (fun _ => by norm_num) (by rw [Fin.sum_univ_two]; norm_num)
    (0 : Fin 2) (1 : Fin 2) (by decide) (by norm_num) (by norm_num)

/-- R5 (circular reference / vacuous return): the same one-cell direct surface and binary channel, but the
channel conditional is constant across channel cells (the answer is a redundant copy of `W0`). Then the
deficit is zero by `circular_reference_zero_deficit`: the non-vacuous query returns vacuous. -/
theorem circular_reference_witness_zero :
    deficit (W := Fin 1) (Cn := Fin 2) (X := Fin 2)
      (fun _ => 1) (fun _ _ => (1 : ℝ) / 2) (fun _ _ => fun _ => (1 : ℝ) / 2) = 0 :=
  circular_reference_zero_deficit _ _ _
    (fun _ => by rw [Fin.sum_univ_two]; norm_num)
    (fun _ => fun _ => (1 : ℝ) / 2) (fun _ _ => rfl)

/-- R5 (upper bound achieved): the perfectly revealing binary channel of `deficit_witness_pos` leaves
zero residual entropy in every cell (each conditional is a point mass), so its deficit equals the full
residual uncertainty `H(target | W0)` (the binary-uniform entropy). The upper end of the bracket is
tight. -/
theorem deficit_witness_saturates_upper :
    deficit (W := Fin 1) (Cn := Fin 2) (X := Fin 2)
      (fun _ => 1) (fun _ _ => (1 : ℝ) / 2) (fun _ c => pointMass c)
    = condEntropyDirect (W := Fin 1) (Cn := Fin 2) (X := Fin 2)
      (fun _ => 1) (fun _ _ => (1 : ℝ) / 2) (fun _ c => pointMass c) :=
  deficit_eq_condEntropyDirect_of_zero_residual _ _ _ (fun _ c => H_pointMass c)

/-! ## Headline axiom audit (subset of {propext, Classical.choice, Quot.sound}). -/

#print axioms deficit_nonneg
#print axioms circular_reference_zero_deficit
#print axioms positive_deficit_requires_exogeny
#print axioms condEntropyLicensed_nonneg
#print axioms deficit_le_condEntropyDirect
#print axioms deficit_bracket
#print axioms deficit_eq_condEntropyDirect_of_zero_residual
#print axioms deficit_witness_pos
#print axioms circular_reference_witness_zero
#print axioms deficit_witness_saturates_upper

end OperatorKO7.Meta.InformationalIncompleteness.LicensedChannelDeficit
