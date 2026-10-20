import OperatorKO7.Meta.BoundaryObserver.ProtocolDynkin
import OperatorKO7.Meta.BoundaryObserver.PairResolution
import OperatorKO7.Meta.BoundaryObserver.BurdenGibbs
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# The sequential probability ratio test

Manuscript: Corollary `cor:sequential-reading-cost` and the sequential test of
Example `ex:ruin-walk` of the Observation-Boundary Principle.

The label `true` reads with the row `P` and `false` with the row `Q`, both of full support. The
test reads until the log-likelihood ratio of the transcript leaves `(-A, A)` and returns the label
of the exit side. Wald's identity holds at every horizon through the drift identity. With
`|ln (P(y)/Q(y))| ≤ ℓ`, the test stops with probability one, errs with conditional chance at most
`e^{-A}` under each label, and has conditional expected count at most `(A + ℓ)/D(P ‖ Q)` under
`true` and `(A + ℓ)/D(Q ‖ P)` under `false` at every horizon. Concavity of the logarithm gives
`D(P ‖ Q) ≥ -2 ln BC(P, Q) ≥ Δ/2`. For the binary symmetric rows of bias `ε`, `ℓ ≥ 4ε`,
`D = 2εℓ` and `Δ = 8ε²`; thresholds at `kℓ` are the biased ruin walk with barriers at distance
`k`, whose error is at most `e^{-4εk}` at expected count at most `(k + 1)/(2ε)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped BigOperators
open Filter Topology
open OperatorKO7.Meta.BoundaryObserver.ProtocolResolution
open OperatorKO7.Meta.BoundaryObserver.TranscriptLaw
open OperatorKO7.Meta.BoundaryObserver.ProtocolDynkin
open OperatorKO7.Meta.BoundaryGeneral.CountableRoleExchange

namespace OperatorKO7.Meta.BoundaryObserver.SequentialRatioTest

variable {Y : Type} [Fintype Y]

/-- The log-likelihood ratio of one output. -/
noncomputable def llr (P Q : FiniteLaw Y) (y : Y) : ℝ := Real.log (P.mass y / Q.mass y)

/-- The log-likelihood ratio of a transcript. -/
noncomputable def transcriptLLR (P Q : FiniteLaw Y) (h : List (Unit × Y)) : ℝ :=
  (h.map (fun ay => llr P Q ay.2)).sum

theorem transcriptLLR_nil (P Q : FiniteLaw Y) : transcriptLLR P Q [] = 0 := by
  simp [transcriptLLR]

theorem transcriptLLR_append (P Q : FiniteLaw Y) (h : List (Unit × Y)) (a : Unit) (y : Y) :
    transcriptLLR P Q (h ++ [(a, y)]) = transcriptLLR P Q h + llr P Q y := by
  simp [transcriptLLR, List.map_append, List.sum_append]

/-- The test reads until the log-likelihood ratio leaves `(-A, A)`. -/
noncomputable def sprtStop (P Q : FiniteLaw Y) (A : ℝ) (h : List (Unit × Y)) : Bool :=
  decide (transcriptLLR P Q h ≤ -A ∨ A ≤ transcriptLLR P Q h)

theorem sprtStop_false_iff (P Q : FiniteLaw Y) (A : ℝ) (h : List (Unit × Y)) :
    sprtStop P Q A h = false ↔ -A < transcriptLLR P Q h ∧ transcriptLLR P Q h < A := by
  unfold sprtStop
  rw [decide_eq_false_iff_not, not_or, not_le, not_le]

/-- The one-point law of the single reading. -/
noncomputable def unitLaw : FiniteLaw Unit where
  mass _ := 1
  nonnegative _ := zero_le_one
  total := by simp

/-- **The sequential probability ratio test** as a finite protocol. -/
noncomputable def sprt (P Q : FiniteLaw Y) (A : ℝ) (prior : FiniteLaw Bool) :
    FiniteProtocol Bool Unit Y where
  prior := prior
  policy _ := unitLaw
  observation _ _ z := if z then P else Q
  stop := sprtStop P Q A
  cost _ _ := 1
  cost_nonnegative _ _ := zero_le_one

/-- The divergence `D(P ‖ Q) = ∑ P ln (P/Q)`. -/
noncomputable def kl (P Q : Y → ℝ) : ℝ := ∑ y, P y * Real.log (P y / Q y)

theorem kl_eq_role (P Q : Y → ℝ) : kl P Q = countableRoleDivergence P Q :=
  (countableRoleDivergence_fintype P Q).symm

/-- Distinct rows of full support have positive divergence. -/
theorem kl_pos (P Q : FiniteLaw Y) (hQ : ∀ y, 0 < Q.mass y) (hne : P.mass ≠ Q.mass) :
    0 < kl P.mass Q.mass := by
  rw [kl_eq_role]
  have h0 := BurdenGibbs.finite_divergence_nonneg P.mass Q.mass P.nonnegative hQ P.total Q.total
  have hz := BurdenGibbs.finite_divergence_eq_zero_iff P.mass Q.mass P.nonnegative hQ P.total
    Q.total
  rcases h0.eq_or_lt with h | h
  · exact absurd (hz.1 h.symm) hne
  · exact h

theorem llr_neg (P Q : FiniteLaw Y) (y : Y) : llr Q P y = -llr P Q y := by
  unfold llr
  rw [← Real.log_inv, inv_div]

section Wald

variable (P Q : FiniteLaw Y) (A : ℝ) (prior : FiniteLaw Bool)

theorem sprt_prior_mass (z : Bool) : (sprt P Q A prior).prior.mass z = prior.mass z := rfl

theorem drift_true (F : List (Unit × Y) → ℝ) (h : List (Unit × Y)) :
    ∑ a, ∑ y, ((sprt P Q A prior).policy h).mass a * ((sprt P Q A prior).observation h a true).mass y *
      F (h ++ [(a, y)]) = ∑ y, P.mass y * F (h ++ [((), y)]) := by
  simp [sprt, unitLaw]

theorem drift_false (F : List (Unit × Y) → ℝ) (h : List (Unit × Y)) :
    ∑ a, ∑ y, ((sprt P Q A prior).policy h).mass a *
      ((sprt P Q A prior).observation h a false).mass y * F (h ++ [(a, y)]) =
      ∑ y, Q.mass y * F (h ++ [((), y)]) := by
  simp [sprt, unitLaw]

theorem llr_sum_true (h : List (Unit × Y)) :
    ∑ y, P.mass y * transcriptLLR P Q (h ++ [((), y)]) = transcriptLLR P Q h + kl P.mass Q.mass := by
  simp only [transcriptLLR_append, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, P.total,
    one_mul]
  rfl

theorem llr_sum_false (h : List (Unit × Y)) :
    ∑ y, Q.mass y * transcriptLLR P Q (h ++ [((), y)]) =
      transcriptLLR P Q h + -kl Q.mass P.mass := by
  simp only [transcriptLLR_append, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, Q.total,
    one_mul]
  congr 1
  unfold kl
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  have := llr_neg P Q y
  unfold llr at this ⊢
  rw [this]
  ring

/-- **Wald's identity at every horizon** under the row `P`. -/
theorem wald_identity (n : ℕ) :
    ∑ h ∈ historySet (Unit × Y) n, stoppedMass (sprt P Q A prior) n true h * transcriptLLR P Q h =
      kl P.mass Q.mass * activeBelow (sprt P Q A prior) true n := by
  have h := protocol_dynkin (sprt P Q A prior) true (transcriptLLR P Q) (kl P.mass Q.mass)
    (fun h _ => by rw [drift_true P Q A prior (transcriptLLR P Q) h, llr_sum_true]) n
  rw [transcriptLLR_nil, mul_zero, zero_add] at h
  exact h

/-- Wald's identity under the row `Q`, with drift `-D(Q ‖ P)`. -/
theorem wald_identity_false (n : ℕ) :
    ∑ h ∈ historySet (Unit × Y) n, stoppedMass (sprt P Q A prior) n false h * transcriptLLR P Q h =
      -kl Q.mass P.mass * activeBelow (sprt P Q A prior) false n := by
  have h := protocol_dynkin (sprt P Q A prior) false (transcriptLLR P Q) (-kl Q.mass P.mass)
    (fun h _ => by rw [drift_false P Q A prior (transcriptLLR P Q) h, llr_sum_false]) n
  rw [transcriptLLR_nil, mul_zero, zero_add] at h
  exact h

end Wald

section Bounds

variable (P Q : FiniteLaw Y) (hP : ∀ y, 0 < P.mass y) (hQ : ∀ y, 0 < Q.mass y)
  (ℓ : ℝ) (hℓ : ∀ y, |llr P Q y| ≤ ℓ) (A : ℝ) (hA : 0 ≤ A) (prior : FiniteLaw Bool)

include hℓ in
theorem ell_nonneg [Nonempty Y] : 0 ≤ ℓ := by
  obtain ⟨y⟩ := (inferInstance : Nonempty Y)
  exact (abs_nonneg _).trans (hℓ y)

include hℓ hA in
/-- **The expected count under `true`** at every horizon is at most `(A + ℓ)/D(P ‖ Q)` times the
prior mass. -/
theorem activeBelow_true_le [Nonempty Y] (hD : 0 < kl P.mass Q.mass) (n : ℕ) :
    activeBelow (sprt P Q A prior) true n ≤ prior.mass true * (A + ℓ) / kl P.mass Q.mass := by
  have hl := ell_nonneg P Q ℓ hℓ
  have hdyn := protocol_dynkin (sprt P Q A prior) true
    (fun h => min (A + ℓ) (transcriptLLR P Q h)) (kl P.mass Q.mass) (fun h hs => by
      have hs' := (sprtStop_false_iff P Q A h).1 hs
      rw [drift_true P Q A prior (fun h => min (A + ℓ) (transcriptLLR P Q h)) h]
      have hchild : ∀ y, min (A + ℓ) (transcriptLLR P Q (h ++ [((), y)])) =
          transcriptLLR P Q (h ++ [((), y)]) := fun y => by
        apply min_eq_right
        rw [transcriptLLR_append]
        have := (abs_le.1 (hℓ y)).2
        linarith
      simp only [hchild]
      rw [llr_sum_true, min_eq_right (by linarith)]) n
  have hV0 : min (A + ℓ) (transcriptLLR P Q []) = 0 := by
    rw [transcriptLLR_nil]
    exact min_eq_right (by linarith)
  rw [hV0, mul_zero, zero_add] at hdyn
  have hle : ∑ h ∈ historySet (Unit × Y) n,
      stoppedMass (sprt P Q A prior) n true h * min (A + ℓ) (transcriptLLR P Q h) ≤
      (A + ℓ) * prior.mass true := by
    rw [← sprt_prior_mass P Q A prior true,
      ← historySet_stoppedMass_target_marginal (sprt P Q A prior) n true, Finset.mul_sum]
    refine Finset.sum_le_sum fun h _ => ?_
    rw [mul_comm (A + ℓ)]
    exact mul_le_mul_of_nonneg_left (min_le_left _ _) (stoppedMass_nonnegative _ n true h)
  rw [le_div_iff₀ hD]
  linarith

include hℓ hA in
/-- The expected count under `false` at every horizon is at most `(A + ℓ)/D(Q ‖ P)` times the
prior mass. -/
theorem activeBelow_false_le [Nonempty Y] (hD : 0 < kl Q.mass P.mass) (n : ℕ) :
    activeBelow (sprt P Q A prior) false n ≤ prior.mass false * (A + ℓ) / kl Q.mass P.mass := by
  have hl := ell_nonneg P Q ℓ hℓ
  have hdyn := protocol_dynkin (sprt P Q A prior) false
    (fun h => max (-(A + ℓ)) (transcriptLLR P Q h)) (-kl Q.mass P.mass) (fun h hs => by
      have hs' := (sprtStop_false_iff P Q A h).1 hs
      rw [drift_false P Q A prior (fun h => max (-(A + ℓ)) (transcriptLLR P Q h)) h]
      have hchild : ∀ y, max (-(A + ℓ)) (transcriptLLR P Q (h ++ [((), y)])) =
          transcriptLLR P Q (h ++ [((), y)]) := fun y => by
        apply max_eq_right
        rw [transcriptLLR_append]
        have := (abs_le.1 (hℓ y)).1
        linarith
      simp only [hchild]
      rw [llr_sum_false, max_eq_right (by linarith)]) n
  have hV0 : max (-(A + ℓ)) (transcriptLLR P Q []) = 0 := by
    rw [transcriptLLR_nil]
    exact max_eq_right (by linarith)
  rw [hV0, mul_zero, zero_add] at hdyn
  have hge : -(A + ℓ) * prior.mass false ≤ ∑ h ∈ historySet (Unit × Y) n,
      stoppedMass (sprt P Q A prior) n false h * max (-(A + ℓ)) (transcriptLLR P Q h) := by
    rw [← sprt_prior_mass P Q A prior false,
      ← historySet_stoppedMass_target_marginal (sprt P Q A prior) n false, Finset.mul_sum]
    refine Finset.sum_le_sum fun h _ => ?_
    rw [mul_comm (-(A + ℓ))]
    exact mul_le_mul_of_nonneg_left (le_max_left _ _) (stoppedMass_nonnegative _ n false h)
  rw [le_div_iff₀ hD]
  linarith

include hℓ hA hP hQ in
/-- **The test stops with probability one** under each label. -/
theorem sprt_stops [Nonempty Y] (hne : P.mass ≠ Q.mass) (z : Bool) :
    Tendsto (fun n => activeMass (sprt P Q A prior) n z) atTop (𝓝 0) := by
  cases z
  · exact activeMass_tendsto_zero_of_bounded _ false _
      (activeBelow_false_le P Q ℓ hℓ A hA prior (kl_pos Q P hP (Ne.symm hne)))
  · exact activeMass_tendsto_zero_of_bounded _ true _
      (activeBelow_true_le P Q ℓ hℓ A hA prior (kl_pos P Q hQ hne))

include hP hQ in
/-- The likelihood-ratio change of measure: `m_false(h) π(true) = e^{-Λ(h)} m_true(h) π(false)`. -/
theorem likelihood_ratio (h : List (Unit × Y)) :
    prefixMass (sprt P Q A prior) false h * prior.mass true =
      Real.exp (-transcriptLLR P Q h) * prefixMass (sprt P Q A prior) true h * prior.mass false := by
  induction h using List.reverseRecOn with
  | nil =>
    simp only [prefixMass_nil, transcriptLLR_nil, neg_zero, Real.exp_zero, one_mul]
    change prior.mass false * prior.mass true = prior.mass true * prior.mass false
    ring
  | append_singleton h ay ih =>
    obtain ⟨a, y⟩ := ay
    rw [prefixMass_append, prefixMass_append, transcriptLLR_append]
    by_cases hs : (sprt P Q A prior).stop h = true
    · simp [hs]
    · rw [if_neg hs, if_neg hs]
      have he : Real.exp (-(transcriptLLR P Q h + llr P Q y)) =
          Real.exp (-transcriptLLR P Q h) * (Q.mass y / P.mass y) := by
        rw [neg_add, Real.exp_add, llr, ← Real.log_inv, inv_div,
          Real.exp_log (div_pos (hQ y) (hP y))]
      rw [he]
      simp only [sprt, unitLaw, if_true, Bool.false_eq_true, if_false, mul_one]
      have hPy : P.mass y ≠ 0 := (hP y).ne'
      calc prefixMass (sprt P Q A prior) false h * Q.mass y * prior.mass true
          = (prefixMass (sprt P Q A prior) false h * prior.mass true) * Q.mass y := by ring
        _ = (Real.exp (-transcriptLLR P Q h) * prefixMass (sprt P Q A prior) true h *
              prior.mass false) * Q.mass y := by rw [ih]
        _ = Real.exp (-transcriptLLR P Q h) * (Q.mass y / P.mass y) *
              (prefixMass (sprt P Q A prior) true h * P.mass y) * prior.mass false := by
          field_simp
          ring

/-- The mass of the transcripts that exit at the upper threshold by horizon `n`. -/
noncomputable def upperMass (z : Bool) (n : ℕ) : ℝ :=
  ∑ h ∈ historySet (Unit × Y) n,
    if A ≤ transcriptLLR P Q h then prefixMass (sprt P Q A prior) z h else 0

/-- The mass of the transcripts that exit at the lower threshold by horizon `n`. -/
noncomputable def lowerMass (z : Bool) (n : ℕ) : ℝ :=
  ∑ h ∈ historySet (Unit × Y) n,
    if transcriptLLR P Q h ≤ -A then prefixMass (sprt P Q A prior) z h else 0

theorem upperMass_le_prior (z : Bool) (n : ℕ) : upperMass P Q A prior z n ≤ prior.mass z := by
  have h := transcript_sum_le_prior (sprt P Q A prior) z (historySet (Unit × Y) n)
  refine le_trans (Finset.sum_le_sum fun h _ => ?_) h
  unfold transcriptMass
  split_ifs with h1 h2 h2
  · exact le_rfl
  · exact absurd (by unfold sprt sprtStop; simp [h1]) h2
  · exact prefixMass_nonnegative _ z h
  · exact le_rfl

theorem lowerMass_le_prior (z : Bool) (n : ℕ) : lowerMass P Q A prior z n ≤ prior.mass z := by
  have h := transcript_sum_le_prior (sprt P Q A prior) z (historySet (Unit × Y) n)
  refine le_trans (Finset.sum_le_sum fun h _ => ?_) h
  unfold transcriptMass
  split_ifs with h1 h2 h2
  · exact le_rfl
  · exact absurd (by unfold sprt sprtStop; simp [h1]) h2
  · exact prefixMass_nonnegative _ z h
  · exact le_rfl

include hP hQ in
/-- **The error under `false`**: the upper exits carry at most `e^{-A}` of the prior mass. -/
theorem error_false_le (htrue : 0 < prior.mass true) (n : ℕ) :
    upperMass P Q A prior false n ≤ Real.exp (-A) * prior.mass false := by
  have hkey : upperMass P Q A prior false n * prior.mass true ≤
      Real.exp (-A) * upperMass P Q A prior true n * prior.mass false := by
    unfold upperMass
    rw [Finset.sum_mul, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_le_sum fun h _ => ?_
    split_ifs with hA'
    · rw [likelihood_ratio P Q hP hQ A prior h]
      have hm := prefixMass_nonnegative (sprt P Q A prior) true h
      have hpf := prior.nonnegative false
      have he : Real.exp (-transcriptLLR P Q h) ≤ Real.exp (-A) := Real.exp_le_exp.2 (by linarith)
      have := mul_le_mul_of_nonneg_right he (mul_nonneg hm hpf)
      linarith
    · simp
  have hu := upperMass_le_prior P Q A prior true n
  have hpf := prior.nonnegative false
  have hstep : Real.exp (-A) * upperMass P Q A prior true n * prior.mass false ≤
      Real.exp (-A) * prior.mass false * prior.mass true := by
    have := mul_le_mul_of_nonneg_left hu (mul_nonneg (Real.exp_pos (-A)).le hpf)
    nlinarith
  have := hkey.trans hstep
  exact le_of_mul_le_mul_right this htrue

include hP hQ in
/-- **The error under `true`**: the lower exits carry at most `e^{-A}` of the prior mass. -/
theorem error_true_le (hfalse : 0 < prior.mass false) (n : ℕ) :
    lowerMass P Q A prior true n ≤ Real.exp (-A) * prior.mass true := by
  have hkey : lowerMass P Q A prior true n * prior.mass false ≤
      Real.exp (-A) * lowerMass P Q A prior false n * prior.mass true := by
    unfold lowerMass
    rw [Finset.sum_mul, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_le_sum fun h _ => ?_
    split_ifs with hA'
    · have hl := likelihood_ratio P Q hP hQ A prior h
      have hm := prefixMass_nonnegative (sprt P Q A prior) true h
      have hpf := prior.nonnegative false
      have hpt := prior.nonnegative true
      -- `m_true π_false = e^{Λ} m_false π_true`, with `e^{Λ} ≤ e^{-A}` on the lower exits
      have hexp : Real.exp (transcriptLLR P Q h) ≤ Real.exp (-A) := Real.exp_le_exp.2 hA'
      have hrel : prefixMass (sprt P Q A prior) true h * prior.mass false =
          Real.exp (transcriptLLR P Q h) * prefixMass (sprt P Q A prior) false h *
            prior.mass true := by
        have hexp1 : Real.exp (transcriptLLR P Q h) * Real.exp (-transcriptLLR P Q h) = 1 := by
          rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
        calc prefixMass (sprt P Q A prior) true h * prior.mass false
            = (Real.exp (transcriptLLR P Q h) * Real.exp (-transcriptLLR P Q h)) *
                prefixMass (sprt P Q A prior) true h * prior.mass false := by rw [hexp1, one_mul]
          _ = Real.exp (transcriptLLR P Q h) * (Real.exp (-transcriptLLR P Q h) *
                prefixMass (sprt P Q A prior) true h * prior.mass false) := by ring
          _ = Real.exp (transcriptLLR P Q h) * (prefixMass (sprt P Q A prior) false h *
                prior.mass true) := by rw [← hl]
          _ = _ := by ring
      rw [hrel]
      have hmf := prefixMass_nonnegative (sprt P Q A prior) false h
      have := mul_le_mul_of_nonneg_right hexp (mul_nonneg hmf hpt)
      linarith
    · simp
  have hl := lowerMass_le_prior P Q A prior false n
  have hpt := prior.nonnegative true
  have hstep : Real.exp (-A) * lowerMass P Q A prior false n * prior.mass true ≤
      Real.exp (-A) * prior.mass true * prior.mass false := by
    have := mul_le_mul_of_nonneg_left hl (mul_nonneg (Real.exp_pos (-A)).le hpt)
    nlinarith
  have := hkey.trans hstep
  exact le_of_mul_le_mul_right this hfalse

end Bounds

/-! ## The divergence and the coefficient -/

/-- **Concavity of the logarithm:** `D(P ‖ Q) ≥ -2 ln BC(P, Q)`. -/
theorem kl_ge_neg_two_log_bc (P Q : FiniteLaw Y) (hP : ∀ y, 0 < P.mass y) (hQ : ∀ y, 0 < Q.mass y) :
    -2 * Real.log (PairResolution.bhattacharyya P.mass Q.mass) ≤ kl P.mass Q.mass := by
  have hj := (strictConcaveOn_log_Ioi).concaveOn.le_map_sum (t := Finset.univ) (w := P.mass)
    (p := fun y => Real.sqrt (Q.mass y / P.mass y)) (fun y _ => (hP y).le) P.total
    (fun y _ => Set.mem_Ioi.2 (Real.sqrt_pos.2 (div_pos (hQ y) (hP y))))
  simp only [smul_eq_mul] at hj
  have hsum : ∑ y, P.mass y * Real.sqrt (Q.mass y / P.mass y) =
      PairResolution.bhattacharyya P.mass Q.mass := by
    unfold PairResolution.bhattacharyya
    refine Finset.sum_congr rfl fun y _ => ?_
    have hp := hP y
    have hq := hQ y
    have hsP : Real.sqrt (P.mass y) * Real.sqrt (P.mass y) = P.mass y := Real.mul_self_sqrt hp.le
    have hsPpos : 0 < Real.sqrt (P.mass y) := Real.sqrt_pos.2 hp
    rw [Real.sqrt_div hq.le, Real.sqrt_mul hp.le, mul_div_assoc', div_eq_iff hsPpos.ne']
    linear_combination (-(Real.sqrt (Q.mass y))) * hsP
  have hterm : ∀ y, P.mass y * Real.log (Real.sqrt (Q.mass y / P.mass y)) =
      -(1 / 2) * (P.mass y * Real.log (P.mass y / Q.mass y)) := by
    intro y
    have hneg : Real.log (Q.mass y / P.mass y) = -Real.log (P.mass y / Q.mass y) := by
      rw [← Real.log_inv, inv_div]
    rw [Real.log_sqrt (div_pos (hQ y) (hP y)).le, hneg]
    ring
  rw [hsum] at hj
  simp only [hterm] at hj
  rw [← Finset.mul_sum] at hj
  unfold kl
  linarith

/-- `-2 ln BC(P, Q) ≥ Δ/2`: the coefficient bound of the pair-resolution theorem. -/
theorem neg_two_log_bc_ge (P Q : FiniteLaw Y) (hbc : 0 < PairResolution.bhattacharyya P.mass Q.mass) :
    BoundarySingularity.discrimination P.mass Q.mass / 2 ≤
      -2 * Real.log (PairResolution.bhattacharyya P.mass Q.mass) := by
  have hb := PairResolution.bhattacharyya_le_one_sub_quarter_discrimination P.mass Q.mass
    P.nonnegative Q.nonnegative P.total Q.total
  have hlog : Real.log (PairResolution.bhattacharyya P.mass Q.mass) ≤
      PairResolution.bhattacharyya P.mass Q.mass - 1 := Real.log_le_sub_one_of_pos hbc
  linarith

/-! ## The binary symmetric rows -/

/-- The binary symmetric row of bias `ε`: the up step `true` has chance `1/2 + ε`. -/
noncomputable def biasRow (ε : ℝ) (hε : |ε| < 1 / 2) : FiniteLaw Bool where
  mass y := if y then 1 / 2 + ε else 1 / 2 - ε
  nonnegative y := by
    cases y <;> simp <;> linarith [(abs_lt.1 hε).1, (abs_lt.1 hε).2]
  total := by rw [Fintype.sum_bool]; simp; ring

theorem biasRow_pos (ε : ℝ) (hε : |ε| < 1 / 2) (y : Bool) : 0 < (biasRow ε hε).mass y := by
  cases y <;> simp [biasRow] <;> linarith [(abs_lt.1 hε).1, (abs_lt.1 hε).2]

theorem neg_abs_lt (ε : ℝ) (hε : |ε| < 1 / 2) : |-ε| < 1 / 2 := by rwa [abs_neg]

/-- The step of the binary symmetric rows: `ℓ = ln ((1 + 2ε)/(1 - 2ε))`. -/
noncomputable def biasStep (ε : ℝ) : ℝ := Real.log ((1 + 2 * ε) / (1 - 2 * ε))

/-- `ℓ ≥ 4ε`, from the series of `ln (1 + x) - ln (1 - x)` at `x = 2ε`. -/
theorem biasStep_ge (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε < 1 / 2) : 4 * ε ≤ biasStep ε := by
  have hx : |2 * ε| < 1 := by rw [abs_of_nonneg (by linarith)]; linarith
  have hs := Real.hasSum_log_sub_log_of_abs_lt_one hx
  have hterm : ∀ k : ℕ, 0 ≤ (2 : ℝ) * (1 / (2 * k + 1)) * (2 * ε) ^ (2 * k + 1) := fun k => by
    positivity
  have hle := le_hasSum hs 0 (fun k _ => hterm k)
  simp only [Nat.cast_zero, mul_zero, zero_add, div_one, mul_one, pow_one] at hle
  unfold biasStep
  rw [Real.log_div (by linarith) (by linarith)]
  linarith

theorem biasRows_llr (ε : ℝ) (hε : |ε| < 1 / 2) (y : Bool) :
    llr (biasRow ε hε) (biasRow (-ε) (neg_abs_lt ε hε)) y = if y then biasStep ε else -biasStep ε := by
  have h1 := (abs_lt.1 hε).1
  have h2 := (abs_lt.1 hε).2
  have hp' : (1 : ℝ) / 2 - -ε ≠ 0 := ne_of_gt (by linarith)
  have hm' : (1 : ℝ) / 2 + -ε ≠ 0 := ne_of_gt (by linarith)
  have hP2 : (1 : ℝ) + 2 * ε ≠ 0 := ne_of_gt (by linarith)
  have hM2 : (1 : ℝ) - 2 * ε ≠ 0 := ne_of_gt (by linarith)
  cases y
  · show Real.log ((1 / 2 - ε) / (1 / 2 - -ε)) = -Real.log ((1 + 2 * ε) / (1 - 2 * ε))
    rw [← Real.log_inv, inv_div]
    congr 1
    rw [div_eq_div_iff hp' hP2]
    ring
  · show Real.log ((1 / 2 + ε) / (1 / 2 + -ε)) = Real.log ((1 + 2 * ε) / (1 - 2 * ε))
    congr 1
    rw [div_eq_div_iff hm' hM2]
    ring

/-- For the binary symmetric rows, `D(P ‖ Q) = D(Q ‖ P) = 2εℓ`. -/
theorem biasRows_kl (ε : ℝ) (hε : |ε| < 1 / 2) :
    kl (biasRow ε hε).mass (biasRow (-ε) (neg_abs_lt ε hε)).mass = 2 * ε * biasStep ε ∧
    kl (biasRow (-ε) (neg_abs_lt ε hε)).mass (biasRow ε hε).mass = 2 * ε * biasStep ε := by
  have hl := biasRows_llr ε hε
  have hl' : ∀ y, llr (biasRow (-ε) (neg_abs_lt ε hε)) (biasRow ε hε) y =
      -(if y then biasStep ε else -biasStep ε) := fun y => by rw [llr_neg, hl]
  refine ⟨?_, ?_⟩
  · unfold kl
    rw [Fintype.sum_bool]
    have ht := hl true
    have hf := hl false
    unfold llr at ht hf
    rw [ht, hf]
    simp [biasRow]
    ring
  · unfold kl
    rw [Fintype.sum_bool]
    have ht := hl' true
    have hf := hl' false
    unfold llr at ht hf
    rw [ht, hf]
    simp [biasRow]
    ring

/-- For the binary symmetric rows, the discrimination is `Δ = 8ε²`. -/
theorem biasRows_discrimination (ε : ℝ) (hε : |ε| < 1 / 2) :
    BoundarySingularity.discrimination (biasRow ε hε).mass (biasRow (-ε) (neg_abs_lt ε hε)).mass =
      8 * ε ^ 2 := by
  unfold BoundarySingularity.discrimination
  rw [Fintype.sum_bool]
  simp [biasRow]
  ring

/-- **The biased ruin walk as a sequential test.** With step chances `1/2 ± ε` under the two labels
and thresholds at `k ℓ`, the barriers at distance `k` of the walk, the error under each label is
at most `e^{-4εk}` and the expected count under each label is at most `(k + 1)/(2ε)` at every
horizon. -/
theorem biased_walk_test (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 2) (k : ℕ) (prior : FiniteLaw Bool)
    (hpt : 0 < prior.mass true) (hpf : 0 < prior.mass false) (n : ℕ) :
    upperMass (biasRow ε (by rw [abs_of_pos hε0]; exact hε1))
        (biasRow (-ε) (neg_abs_lt ε (by rw [abs_of_pos hε0]; exact hε1))) (k * biasStep ε) prior
        false n ≤ Real.exp (-(4 * ε * k)) * prior.mass false ∧
    lowerMass (biasRow ε (by rw [abs_of_pos hε0]; exact hε1))
        (biasRow (-ε) (neg_abs_lt ε (by rw [abs_of_pos hε0]; exact hε1))) (k * biasStep ε) prior
        true n ≤ Real.exp (-(4 * ε * k)) * prior.mass true ∧
    activeBelow (sprt (biasRow ε (by rw [abs_of_pos hε0]; exact hε1))
        (biasRow (-ε) (neg_abs_lt ε (by rw [abs_of_pos hε0]; exact hε1))) (k * biasStep ε) prior)
        true n ≤ prior.mass true * (k + 1) / (2 * ε) ∧
    activeBelow (sprt (biasRow ε (by rw [abs_of_pos hε0]; exact hε1))
        (biasRow (-ε) (neg_abs_lt ε (by rw [abs_of_pos hε0]; exact hε1))) (k * biasStep ε) prior)
        false n ≤ prior.mass false * (k + 1) / (2 * ε) := by
  have hε : |ε| < 1 / 2 := by rw [abs_of_pos hε0]; exact hε1
  set P := biasRow ε hε
  set Q := biasRow (-ε) (neg_abs_lt ε hε)
  have hP := biasRow_pos ε hε
  have hQ := biasRow_pos (-ε) (neg_abs_lt ε hε)
  have hstep := biasStep_ge ε hε0.le hε1
  have hℓpos : 0 < biasStep ε := by linarith
  have hℓ : ∀ y, |llr P Q y| ≤ biasStep ε := fun y => by
    rw [biasRows_llr ε hε y]
    cases y <;> simp [abs_of_pos hℓpos]
  have hA : (0 : ℝ) ≤ k * biasStep ε := by positivity
  have hexp : Real.exp (-(k * biasStep ε)) ≤ Real.exp (-(4 * ε * k)) := by
    apply Real.exp_le_exp.2
    have : (4 * ε) * k ≤ biasStep ε * k := mul_le_mul_of_nonneg_right hstep (Nat.cast_nonneg k)
    linarith
  obtain ⟨hklPQ, hklQP⟩ := biasRows_kl ε hε
  have hD : 0 < kl P.mass Q.mass := by rw [hklPQ]; positivity
  have hD' : 0 < kl Q.mass P.mass := by rw [hklQP]; positivity
  have hcount : ∀ m : ℝ, 0 ≤ m → m * (k * biasStep ε + biasStep ε) / (2 * ε * biasStep ε) =
      m * (k + 1) / (2 * ε) := fun m _ => by
    field_simp
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := error_false_le P Q hP hQ (k * biasStep ε) prior hpt n
    have := mul_le_mul_of_nonneg_right hexp (prior.nonnegative false)
    linarith
  · have h := error_true_le P Q hP hQ (k * biasStep ε) prior hpf n
    have := mul_le_mul_of_nonneg_right hexp (prior.nonnegative true)
    linarith
  · have h := activeBelow_true_le P Q (biasStep ε) hℓ (k * biasStep ε) hA prior hD n
    rw [hklPQ, hcount _ (prior.nonnegative true)] at h
    exact h
  · have h := activeBelow_false_le P Q (biasStep ε) hℓ (k * biasStep ε) hA prior hD' n
    rw [hklQP, hcount _ (prior.nonnegative false)] at h
    exact h

end OperatorKO7.Meta.BoundaryObserver.SequentialRatioTest
