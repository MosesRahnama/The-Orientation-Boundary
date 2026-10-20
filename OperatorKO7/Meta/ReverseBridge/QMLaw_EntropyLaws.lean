import Mathlib
import OperatorKO7.Meta.InformationalIncompleteness.ShannonFinite
import OperatorKO7.Meta.InformationalIncompleteness.ConditionalEntropy

/-!
# QM-law mechanization: finite entropy laws (Workstream B, MIN-127)

Finite sharpenings of two ESTABLISHED catalog rows on the framework's own Shannon substrate
(`ShannonFinite.H`, `ConditionalEntropy.condEntropy`):

1. **SP2-26 cousin (von Neumann entropy, finite face).** The finite (diagonal / spectral) entropy is
   `H` of the spectrum (`DiagonalEntropy.diagonal_entropy_eq` is the existing diagonal bridge); here we
   prove the LAW PACKAGE: the Gibbs inequality (`gibbs_inequality`, from `log x ≤ x - 1`), the maximum
   `H p ≤ log |α|` (`H_le_log_card`), and exact attainment by the uniform (maximally mixed) state
   (`H_uniform`). With `ShannonFinite.H_nonneg`, the finite entropy is nonnegative and maximized exactly
   by the maximally mixed state.

2. **SP2-27 cousin (strong subadditivity, finite Shannon face).** The full finite Shannon SSA:
   `H(ACB) + H(B) ≤ H(AB) + H(CB)` (`shannon_strong_subadditivity`), assembled from the entropy chain
   rule (`entropy_chain_rule`, proven here) and conditional subadditivity (`condEntropy_subadditive`,
   from `entropy_subadditive`, itself from Gibbs against the product reference).

   QM ANALOGY (docstring only, never asserted): the von Neumann entropy of a finite quantum state is the
   Shannon entropy of its spectrum; SSA of von Neumann entropy (Lieb-Ruskai) restricted to mutually
   commuting (simultaneously diagonal) states IS this finite Shannon SSA. The general non-commuting
   Lieb-Ruskai theorem needs operator convexity machinery Mathlib does not currently provide and stays on
   the ESTABLISHED parent row (a named external dependency, not mechanized here).

## Honest scope (the fence)

Finite alphabets only; all distribution hypotheses are explicit per theorem. `Real.log` is total in
Mathlib (`log 0 = 0`), so the Gibbs inequality carries the EXPLICIT absolute-continuity hypothesis
(`q i = 0 → p i = 0`); without it the totalized statement is false (the `S23` totalization guard).
Quantum (non-commuting) SSA is NOT proven here.

## Audit slots
- Relation: NA (no rewriting relation). Real-arithmetic inequalities and identities on finite sums.
- Closure: `propext`, `Classical.choice`, `Quot.sound`; verified by `#print axioms` at the foot.
- Trust: no `sorry`/`admit`/`axiom`/`native_decide`/`@[csimp]`/`unsafe`/`partial`/`opaque`.
- Non-vacuity (R5): max-entropy saturated by the concrete uniform distribution on `Bool`
  (`H_uniform_bool_saturates`); SSA instantiated at a concrete uniform model (`ssa_witness`).
- Scope: finite carriers; explicit hypotheses; QM reading is ANALOGY, docstring-only.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.ReverseBridge.QMLaw_EntropyLaws

open OperatorKO7.Meta.InformationalIncompleteness.ShannonFinite
open OperatorKO7.Meta.InformationalIncompleteness.ConditionalEntropy

/-! ## 1. The Gibbs inequality (from `log x ≤ x - 1`) -/

/-- `negMulLog` splits multiplicatively, TOTALLY (every zero case checked; uses Mathlib's total
`log` with `log 0 = 0`): `negMulLog (a b) = b · negMulLog a + a · negMulLog b`. -/
theorem negMulLog_mul_total (a b : ℝ) :
    Real.negMulLog (a * b) = b * Real.negMulLog a + a * Real.negMulLog b := by
  rcases eq_or_ne a 0 with ha | ha
  · subst ha; simp [Real.negMulLog]
  rcases eq_or_ne b 0 with hb | hb
  · subst hb; simp [Real.negMulLog]
  simp only [Real.negMulLog, Real.log_mul ha hb]
  ring

/-- Per-term Gibbs bound: for `a, b ≥ 0` with `b = 0 → a = 0`,
`negMulLog a + a · log b ≤ b - a`. The single-letter face of `log x ≤ x - 1`. -/
theorem gibbs_term (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : b = 0 → a = 0) :
    Real.negMulLog a + a * Real.log b ≤ b - a := by
  rcases eq_or_lt_of_le ha with ha0 | hapos
  · rw [← ha0]
    simp [Real.negMulLog]
    linarith [hb]
  · have hbne : b ≠ 0 := fun h => absurd (hab h) (ne_of_gt hapos)
    have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hbne)
    have hane : a ≠ 0 := ne_of_gt hapos
    have hdiv : 0 < b / a := div_pos hbpos hapos
    have hlog : Real.log (b / a) ≤ b / a - 1 := Real.log_le_sub_one_of_pos hdiv
    have hmul : a * Real.log (b / a) ≤ a * (b / a - 1) :=
      mul_le_mul_of_nonneg_left hlog ha
    have hsplit : a * Real.log (b / a) = a * Real.log b - a * Real.log a := by
      rw [Real.log_div hbne hane]; ring
    have hrhs : a * (b / a - 1) = b - a := by
      field_simp
    rw [hsplit, hrhs] at hmul
    simp only [Real.negMulLog]
    linarith

/--
**Gibbs inequality (PROVEN).** For a probability distribution `p` and a sub-distribution reference `q`
that dominates it (`q i = 0 → p i = 0`, the explicit absolute-continuity hypothesis demanded by the
totalized `log`), the entropy is bounded by the cross entropy: `H p ≤ -∑ i, p i · log (q i)`. -/
theorem gibbs_inequality {α : Type} [Fintype α] (p q : α → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∑ i, q i ≤ 1)
    (habs : ∀ i, q i = 0 → p i = 0) :
    H p ≤ -∑ i, p i * Real.log (q i) := by
  have hsum : ∑ i, (Real.negMulLog (p i) + p i * Real.log (q i)) ≤ ∑ i, (q i - p i) :=
    Finset.sum_le_sum fun i _ => gibbs_term (p i) (q i) (hp0 i) (hq0 i) (habs i)
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hp1] at hsum
  have hH : (∑ i, Real.negMulLog (p i)) = H p := rfl
  rw [hH] at hsum
  linarith

/-! ## 2. SP2-26 cousin: the finite entropy maximum and the maximally mixed state -/

/--
**SP2-26 cousin (PROVEN, finite entropy maximum).** Every probability distribution on a finite nonempty
alphabet has entropy at most `log |α|`: `H p ≤ log (card α)`. From Gibbs against the uniform reference.

QM ANALOGY (docstring only, not asserted): the von Neumann entropy of a `d`-dimensional state is at most
`log d`, with the bound set by the maximally mixed state. -/
theorem H_le_log_card {α : Type} [Fintype α] [Nonempty α] (p : α → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1) :
    H p ≤ Real.log (Fintype.card α) := by
  have hcard : (0 : ℝ) < (Fintype.card α : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hgibbs := gibbs_inequality p (fun _ => (Fintype.card α : ℝ)⁻¹) hp0 hp1
    (fun _ => inv_nonneg.mpr hcard.le)
    (by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [mul_inv_cancel₀ (ne_of_gt hcard)])
    (fun i h => absurd h (inv_ne_zero (ne_of_gt hcard)))
  have hcross : -∑ i, p i * Real.log ((Fintype.card α : ℝ)⁻¹)
      = Real.log (Fintype.card α) := by
    rw [Real.log_inv]
    rw [← Finset.sum_mul, hp1]
    ring
  rwa [hcross] at hgibbs

/--
**SP2-26 cousin (PROVEN, the maximally mixed state attains the maximum).** The uniform distribution on a
finite nonempty alphabet has entropy exactly `log |α|`. -/
theorem H_uniform {α : Type} [Fintype α] [Nonempty α] :
    H (fun _ : α => (Fintype.card α : ℝ)⁻¹) = Real.log (Fintype.card α) := by
  have hcard : (0 : ℝ) < (Fintype.card α : ℝ) := by
    exact_mod_cast Fintype.card_pos
  unfold H
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simp only [Real.negMulLog, Real.log_inv]
  field_simp

/-- **R5 non-vacuity (SP2-26 cousin).** The uniform distribution on `Bool` saturates the maximum:
`H = log 2`, and `log 2 > 0`, so the maximum is attained at a concrete nontrivial value. -/
theorem H_uniform_bool_saturates :
    H (fun _ : Bool => (2 : ℝ)⁻¹) = Real.log 2 ∧ 0 < Real.log 2 := by
  constructor
  · have h := H_uniform (α := Bool)
    simpa using h
  · exact Real.log_pos (by norm_num)

/-! ## 3. Marginals and subadditivity -/

variable {A C : Type} [Fintype A] [Fintype C]

/-- First marginal of a joint distribution on `A × C`. -/
noncomputable def margFst (p : A × C → ℝ) : A → ℝ := fun a => ∑ c, p (a, c)

/-- Second marginal of a joint distribution on `A × C`. -/
noncomputable def margSnd (p : A × C → ℝ) : C → ℝ := fun c => ∑ a, p (a, c)

omit [Fintype A] in
theorem margFst_nonneg (p : A × C → ℝ) (hp0 : ∀ x, 0 ≤ p x) (a : A) : 0 ≤ margFst p a :=
  Finset.sum_nonneg fun c _ => hp0 (a, c)

omit [Fintype C] in
theorem margSnd_nonneg (p : A × C → ℝ) (hp0 : ∀ x, 0 ≤ p x) (c : C) : 0 ≤ margSnd p c :=
  Finset.sum_nonneg fun a _ => hp0 (a, c)

theorem margFst_sum (p : A × C → ℝ) (hp1 : ∑ x, p x = 1) : ∑ a, margFst p a = 1 := by
  unfold margFst
  rw [← Fintype.sum_prod_type]
  exact hp1

theorem margSnd_sum (p : A × C → ℝ) (hp1 : ∑ x, p x = 1) : ∑ c, margSnd p c = 1 := by
  unfold margSnd
  rw [Finset.sum_comm, ← Fintype.sum_prod_type]
  exact hp1

omit [Fintype A] in
/-- The joint mass is dominated by its first marginal. -/
theorem le_margFst (p : A × C → ℝ) (hp0 : ∀ x, 0 ≤ p x) (a : A) (c : C) :
    p (a, c) ≤ margFst p a :=
  Finset.single_le_sum (fun c' _ => hp0 (a, c')) (Finset.mem_univ c)

omit [Fintype C] in
/-- The joint mass is dominated by its second marginal. -/
theorem le_margSnd (p : A × C → ℝ) (hp0 : ∀ x, 0 ≤ p x) (a : A) (c : C) :
    p (a, c) ≤ margSnd p c :=
  Finset.single_le_sum (fun a' _ => hp0 (a', c)) (Finset.mem_univ a)

/--
**Subadditivity (PROVEN).** The entropy of a finite joint distribution is at most the sum of the
entropies of its marginals: `H p ≤ H (margFst p) + H (margSnd p)`. From Gibbs against the product of the
marginals.

QM ANALOGY (docstring only, not asserted): the entropy of a bipartite state is at most the sum of the
entropies of its parts. -/
theorem entropy_subadditive (p : A × C → ℝ)
    (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1) :
    H p ≤ H (margFst p) + H (margSnd p) := by
  set q : A × C → ℝ := fun x => margFst p x.1 * margSnd p x.2 with hq
  have hq0 : ∀ x, 0 ≤ q x := fun x =>
    mul_nonneg (margFst_nonneg p hp0 x.1) (margSnd_nonneg p hp0 x.2)
  have hq1 : ∑ x, q x ≤ 1 := by
    have : ∑ x : A × C, q x = (∑ a, margFst p a) * (∑ c, margSnd p c) := by
      rw [Fintype.sum_prod_type]
      rw [← Finset.sum_mul_sum]
    rw [this, margFst_sum p hp1, margSnd_sum p hp1, one_mul]
  have habs : ∀ x, q x = 0 → p x = 0 := by
    rintro ⟨a, c⟩ hx
    rcases mul_eq_zero.mp hx with h | h
    · exact le_antisymm (h ▸ le_margFst p hp0 a c) (hp0 (a, c))
    · exact le_antisymm (h ▸ le_margSnd p hp0 a c) (hp0 (a, c))
  have hgibbs := gibbs_inequality p q hp0 hp1 hq0 hq1 habs
  -- Split the cross entropy into the two marginal entropies.
  have hsplit : ∀ x : A × C,
      p x * Real.log (q x)
        = p x * Real.log (margFst p x.1) + p x * Real.log (margSnd p x.2) := by
    rintro ⟨a, c⟩
    rcases eq_or_ne (p (a, c)) 0 with hpz | hpz
    · rw [hpz]; ring
    · have hppos : 0 < p (a, c) := lt_of_le_of_ne (hp0 (a, c)) (Ne.symm hpz)
      have hfne : margFst p a ≠ 0 :=
        ne_of_gt (lt_of_lt_of_le hppos (le_margFst p hp0 a c))
      have hsne : margSnd p c ≠ 0 :=
        ne_of_gt (lt_of_lt_of_le hppos (le_margSnd p hp0 a c))
      show p (a, c) * Real.log (margFst p a * margSnd p c) = _
      rw [Real.log_mul hfne hsne]
      ring
  have hcross : ∑ x, p x * Real.log (q x)
      = (∑ x : A × C, p x * Real.log (margFst p x.1))
        + (∑ x : A × C, p x * Real.log (margSnd p x.2)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => hsplit x
  have hfst : ∑ x : A × C, p x * Real.log (margFst p x.1) = -H (margFst p) := by
    rw [Fintype.sum_prod_type]
    dsimp only
    unfold H
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_mul]
    show margFst p a * Real.log (margFst p a) = -Real.negMulLog (margFst p a)
    simp [Real.negMulLog]
  have hsnd : ∑ x : A × C, p x * Real.log (margSnd p x.2) = -H (margSnd p) := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    dsimp only
    unfold H
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Finset.sum_mul]
    show margSnd p c * Real.log (margSnd p c) = -Real.negMulLog (margSnd p c)
    simp [Real.negMulLog]
  rw [hcross, hfst, hsnd] at hgibbs
  linarith

/-! ## 4. The chain rule -/

/-- The joint distribution assembled from weights `lam` on `Y` and conditionals `q y` on `X`,
indexed `(x, y)`. -/
noncomputable def jointDist {X Y : Type} [Fintype X] [Fintype Y]
    (lam : Y → ℝ) (q : Y → X → ℝ) : X × Y → ℝ :=
  fun p => lam p.2 * q p.2 p.1

/--
**Entropy chain rule (PROVEN).** `H(X, Y) = H(Y) + H(X | Y)` for the joint assembled from weights and
per-cell conditionals, with per-cell normalization `∑ x, q y x = 1`. Total (no positivity needed): the
multiplicative split of `negMulLog` is checked through every zero case. -/
theorem entropy_chain_rule {X Y : Type} [Fintype X] [Fintype Y]
    (lam : Y → ℝ) (q : Y → X → ℝ) (hq1 : ∀ y, ∑ x, q y x = 1) :
    H (jointDist lam q) = H lam + condEntropy lam q := by
  unfold H jointDist condEntropy
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  have hterm : ∀ y, ∑ x, Real.negMulLog (lam y * q y x)
      = Real.negMulLog (lam y) + lam y * H (q y) := by
    intro y
    have : ∀ x, Real.negMulLog (lam y * q y x)
        = q y x * Real.negMulLog (lam y) + lam y * Real.negMulLog (q y x) :=
      fun x => negMulLog_mul_total (lam y) (q y x)
    rw [Finset.sum_congr rfl fun x _ => this x, Finset.sum_add_distrib]
    rw [← Finset.sum_mul, hq1 y, one_mul, ← Finset.mul_sum]
    rfl
  rw [Finset.sum_congr rfl fun y _ => hterm y, Finset.sum_add_distrib]

/-! ## 5. Conditional subadditivity and strong subadditivity -/

variable {B : Type} [Fintype B]

/--
**Conditional subadditivity (PROVEN).** Averaging the per-cell subadditivity over the conditioning
variable: `H(A C | B) ≤ H(A | B) + H(C | B)`. -/
theorem condEntropy_subadditive (lam : B → ℝ) (r : B → A × C → ℝ)
    (hlam0 : ∀ b, 0 ≤ lam b)
    (hr0 : ∀ b x, 0 ≤ r b x) (hr1 : ∀ b, ∑ x, r b x = 1) :
    condEntropy lam r
      ≤ condEntropy lam (fun b => margFst (r b)) + condEntropy lam (fun b => margSnd (r b)) := by
  unfold condEntropy
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun b _ => ?_
  have hsub := entropy_subadditive (r b) (hr0 b) (hr1 b)
  calc lam b * H (r b) ≤ lam b * (H (margFst (r b)) + H (margSnd (r b))) :=
        mul_le_mul_of_nonneg_left hsub (hlam0 b)
    _ = lam b * H (margFst (r b)) + lam b * H (margSnd (r b)) := by ring

/--
**SP2-27 cousin (PROVEN, finite Shannon strong subadditivity).** For any weights `lam` on `B` and
per-cell joint conditionals `r b` on `A × C`:

`H(A C B) + H(B) ≤ H(A B) + H(C B)`,

with each joint assembled by `jointDist`. Assembled from the chain rule (three times) and conditional
subadditivity; the genuine content is Gibbs against the product reference inside each `B`-cell.

QM ANALOGY (docstring only, not asserted): strong subadditivity of von Neumann entropy (Lieb-Ruskai)
restricted to simultaneously diagonal (mutually commuting) states IS this statement; the general
non-commuting case needs operator convexity (Lieb's theorem) that Mathlib does not currently provide and
stays ESTABLISHED on the parent row. -/
theorem shannon_strong_subadditivity (lam : B → ℝ) (r : B → A × C → ℝ)
    (hlam0 : ∀ b, 0 ≤ lam b)
    (hr0 : ∀ b x, 0 ≤ r b x) (hr1 : ∀ b, ∑ x, r b x = 1) :
    H (jointDist lam r) + H lam
      ≤ H (jointDist lam (fun b => margFst (r b)))
        + H (jointDist lam (fun b => margSnd (r b))) := by
  have hA1 : ∀ b, ∑ a, margFst (r b) a = 1 := fun b => margFst_sum (r b) (hr1 b)
  have hC1 : ∀ b, ∑ c, margSnd (r b) c = 1 := fun b => margSnd_sum (r b) (hr1 b)
  rw [entropy_chain_rule lam r hr1,
      entropy_chain_rule lam (fun b => margFst (r b)) hA1,
      entropy_chain_rule lam (fun b => margSnd (r b)) hC1]
  have hsub := condEntropy_subadditive lam r hlam0 hr0 hr1
  linarith

/-- **R5 non-vacuity (SP2-27 cousin).** The SSA hypotheses are inhabited by a concrete uniform model
(`B = A = C = Bool`, uniform weights, uniform per-cell joints), so the theorem is non-vacuous. -/
theorem ssa_witness :
    H (jointDist (fun _ : Bool => (2 : ℝ)⁻¹) (fun _ : Bool => fun _ : Bool × Bool => (4 : ℝ)⁻¹))
        + H (fun _ : Bool => (2 : ℝ)⁻¹)
      ≤ H (jointDist (fun _ : Bool => (2 : ℝ)⁻¹)
            (fun b => margFst ((fun _ : Bool => fun _ : Bool × Bool => (4 : ℝ)⁻¹) b)))
        + H (jointDist (fun _ : Bool => (2 : ℝ)⁻¹)
            (fun b => margSnd ((fun _ : Bool => fun _ : Bool × Bool => (4 : ℝ)⁻¹) b))) := by
  apply shannon_strong_subadditivity
  · intro _; norm_num
  · intro _ _; norm_num
  · intro b
    rw [Fintype.sum_prod_type]
    simp
    norm_num

/-! ### Axiom audits -/

#print axioms negMulLog_mul_total
#print axioms gibbs_term
#print axioms gibbs_inequality
#print axioms H_le_log_card
#print axioms H_uniform
#print axioms H_uniform_bool_saturates
#print axioms entropy_subadditive
#print axioms entropy_chain_rule
#print axioms condEntropy_subadditive
#print axioms shannon_strong_subadditivity
#print axioms ssa_witness

end OperatorKO7.Meta.ReverseBridge.QMLaw_EntropyLaws
