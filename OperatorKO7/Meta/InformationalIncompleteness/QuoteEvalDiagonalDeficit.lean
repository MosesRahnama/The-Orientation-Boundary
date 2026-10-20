import OperatorKO7.Meta.InformationalIncompleteness.LicensedChannelDeficit
import OperatorKO7.Meta.DistinctionBoundary.GodelQuoteEvalPeak

/-!
# The quotation peak is the echo vacuum on the self-evaluation face

The querant already holds that `quote (merge void void)` converges to `void`.
The two raw branches are evaluation and under-quotation. The channel report
about the evaluated value is a redundant copy of that direct-surface fact, so
the licensed-channel deficit is zero. The rewrite face of the same diagonal is
the nonjoinable quote/eval peak.
-/

set_option autoImplicit false

open scoped BigOperators

namespace OperatorKO7.Meta.InformationalIncompleteness.QuoteEvalDiagonalDeficit

open OperatorKO7 Trace
open OperatorKO7.Meta.InformationalIncompleteness.ShannonFinite
open OperatorKO7.Meta.InformationalIncompleteness.LicensedChannelDeficit
open OperatorKO7.Meta.DistinctionBoundary.GodelPartial

/-- Direct-surface fact the querant already holds. -/
theorem quoted_base_value_already_fixed :
    convergesTo (quote (merge void void)) void void :=
  quote_merge_void_void_converges

theorem quoteEval_step_one_value :
    step 1 (quote (merge void void)) void = some void :=
  rfl

/-- The target outcome is computed from the actual one-step evaluator. `0` is
the convergent value verdict and `1` is the fallback cell. -/
def quoteEvalObservedOutcome : Fin 2 :=
  if step 1 (quote (merge void void)) void = some void then 0 else 1

theorem quoteEvalObservedOutcome_eq_zero :
    quoteEvalObservedOutcome = 0 := by
  simp [quoteEvalObservedOutcome, quoteEval_step_one_value]

/-- The channel posterior is the point mass at the outcome computed by the
actual evaluator. It is channel-constant because the direct surface fixes it. -/
def quoteEvalPosterior : Fin 1 → Fin 2 → Fin 2 → ℝ :=
  fun _ _ => pointMass quoteEvalObservedOutcome

theorem quoteEvalPosterior_calibrated (w : Fin 1) (c : Fin 2) :
    quoteEvalPosterior w c = pointMass (0 : Fin 2) := by
  rw [quoteEvalPosterior, quoteEvalObservedOutcome_eq_zero]

theorem quoteEval_evaluator_and_posterior_agree :
    step 1 (quote (merge void void)) void = some void
      ∧ quoteEvalObservedOutcome = 0
      ∧ ∀ w c, quoteEvalPosterior w c = pointMass (0 : Fin 2) :=
  ⟨quoteEval_step_one_value, quoteEvalObservedOutcome_eq_zero,
    quoteEvalPosterior_calibrated⟩

/-- **The quotation diagonal is the echo vacuum.** Both channel cells report
the already-known value (point mass on `0`). Instance of
`circular_reference_zero_deficit`. -/
theorem quoteEval_diagonal_echo_vacuum :
    deficit (W := Fin 1) (Cn := Fin 2) (X := Fin 2)
      (fun _ => 1) (fun _ _ => (1 : ℝ) / 2) quoteEvalPosterior = 0 :=
  circular_reference_zero_deficit _ _ _
    (fun _ => by rw [Fin.sum_univ_two]; norm_num)
    (fun _ => pointMass quoteEvalObservedOutcome) (fun _ _ => rfl)

/-- **No residual uncertainty.** The direct surface already fixes the evaluated
value, so `H(X | W0) = 0`. -/
theorem quoteEval_diagonal_zero_residual :
    condEntropyDirect (W := Fin 1) (Cn := Fin 2) (X := Fin 2)
      (fun _ => 1) (fun _ _ => (1 : ℝ) / 2) quoteEvalPosterior = 0 := by
  unfold condEntropyDirect
  rw [Fin.sum_univ_one, one_mul]
  have hmarg : (fun x : Fin 2 => ∑ c : Fin 2,
      (1 : ℝ) / 2 * quoteEvalPosterior 0 c x)
      = pointMass quoteEvalObservedOutcome := by
    funext x
    simp only [quoteEvalPosterior, Fin.sum_univ_two]
    ring
  rw [hmarg, H_pointMass]

/-- Information-face vacuum together with the rewrite-face nonjoinable peak. -/
theorem quoteEval_diagonal_echo_vacuum_with_peak :
    deficit (W := Fin 1) (Cn := Fin 2) (X := Fin 2)
        (fun _ => 1) (fun _ _ => (1 : ℝ) / 2) quoteEvalPosterior = 0
      ∧ condEntropyDirect (W := Fin 1) (Cn := Fin 2) (X := Fin 2)
        (fun _ => 1) (fun _ _ => (1 : ℝ) / 2) quoteEvalPosterior = 0
      ∧ step 1 (quote (merge void void)) void = some void
      ∧ quoteEvalObservedOutcome = 0
      ∧ QuoteEvalStep true freezePeakSource (.value void)
      ∧ QuoteEvalStar true freezePeakSource .diverged
      ∧ ¬ QuoteEvalJoin true (.value void) .diverged :=
  ⟨quoteEval_diagonal_echo_vacuum, quoteEval_diagonal_zero_residual,
    quoteEval_step_one_value,
    quoteEvalObservedOutcome_eq_zero,
    quote_eval_nonjoinable_peak.1, quote_eval_nonjoinable_peak.2.1,
    quote_eval_nonjoinable_peak.2.2⟩

end OperatorKO7.Meta.InformationalIncompleteness.QuoteEvalDiagonalDeficit
