import OperatorKO7.Meta.BoundaryObserver.TranscriptLaw

/-!
# The decoder error at a horizon with active histories

Manuscript: Theorem `thm:transcript-information`, part (iv).

A decoder `g` on histories errs on the transcripts of the experiment that runs until it stops with
the mass `fullError`. Stopping at a horizon `n` and deciding from the stopped transcripts, with any
rule `r` on the histories still active at `n`, raises that error by at most the active mass at `n`.
Scoring every active history as an error raises it by exactly the active mass minus the error of the
full decoder on the transcripts that continue the active histories, and never lowers it.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped BigOperators
open OperatorKO7.Meta.BoundaryObserver.ProtocolResolution
open OperatorKO7.Meta.BoundaryObserver.TranscriptLaw

namespace OperatorKO7.Meta.BoundaryObserver.StoppedHorizonError

variable {Z A Y : Type} [Fintype Z] [Fintype A] [Fintype Y] [DecidableEq Z]

/-- The error indicator of deciding `v` at the target `z`. -/
def miss (v z : Z) : ℝ := if v = z then 0 else 1

theorem miss_nonneg (v z : Z) : 0 ≤ miss v z := by
  unfold miss
  split_ifs <;> norm_num

theorem miss_le_one (v z : Z) : miss v z ≤ 1 := by
  unfold miss
  split_ifs <;> norm_num

/-- The active indicator mass of a history at horizon `n`. -/
noncomputable def activeTerm (p : FiniteProtocol Z A Y) (n : ℕ) (z : Z) (h : List (A × Y)) : ℝ :=
  if h.length = n ∧ p.stop h = false then prefixMass p z h else 0

theorem activeTerm_nonneg (p : FiniteProtocol Z A Y) (n : ℕ) (z : Z) (h : List (A × Y)) :
    0 ≤ activeTerm p n z h := by
  unfold activeTerm
  split_ifs
  · exact prefixMass_nonnegative p z h
  · exact le_rfl

/-- The error of `g` on the transcripts of the experiment that runs until it stops. -/
noncomputable def fullError (p : FiniteProtocol Z A Y) (g : List (A × Y) → Z) : ℝ :=
  ∑ z, ∑' h, transcriptMass p z h * miss (g h) z

/-- The error at horizon `n`: the stopped transcripts of length at most `n` decided by `g`, and the
histories active at `n` decided by the rule `r`. -/
noncomputable def horizonError (p : FiniteProtocol Z A Y) (g r : List (A × Y) → Z) (n : ℕ) : ℝ :=
  ∑ z, ((∑ h ∈ historySet (A × Y) n, transcriptMass p z h * miss (g h) z) +
    ∑ h ∈ historySet (A × Y) n, activeTerm p n z h * miss (r h) z)

/-- The error at horizon `n` with every active history scored as an error. -/
noncomputable def horizonErrorAll (p : FiniteProtocol Z A Y) (g : List (A × Y) → Z) (n : ℕ) : ℝ :=
  ∑ z, ((∑ h ∈ historySet (A × Y) n, transcriptMass p z h * miss (g h) z) + activeMass p n z)

/-- The error of the full decoder on the transcripts longer than `n`, the continuations of the
histories active at `n`. -/
noncomputable def activeError (p : FiniteProtocol Z A Y) (g : List (A × Y) → Z) (n : ℕ) : ℝ :=
  ∑ z, ∑' h : ((historySet (A × Y) n : Set (List (A × Y)))ᶜ : Set (List (A × Y))),
    transcriptMass p z h * miss (g h) z

theorem errorTerm_summable (p : FiniteProtocol Z A Y) (g : List (A × Y) → Z) (z : Z) :
    Summable (fun h => transcriptMass p z h * miss (g h) z) :=
  Summable.of_nonneg_of_le (fun h => mul_nonneg (transcriptMass_nonneg p z h) (miss_nonneg _ _))
    (fun h => by
      have := mul_le_mul_of_nonneg_left (miss_le_one (g h) z) (transcriptMass_nonneg p z h)
      linarith)
    (transcriptMass_summable p z)

theorem activeMass_eq_sum (p : FiniteProtocol Z A Y) (n : ℕ) (z : Z) :
    activeMass p n z = ∑ h ∈ historySet (A × Y) n, activeTerm p n z h := rfl

/-- **Part (iv), first clause.** Deciding at horizon `n`, with any rule on the active histories,
raises the error of the full decoder by at most the active mass at `n`. -/
theorem horizonError_le (p : FiniteProtocol Z A Y) (g r : List (A × Y) → Z) (n : ℕ) :
    horizonError p g r n ≤ fullError p g + ∑ z, activeMass p n z := by
  unfold horizonError fullError
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun z _ => add_le_add ?_ ?_
  · exact sum_le_tsum _ (fun h _ => mul_nonneg (transcriptMass_nonneg p z h) (miss_nonneg _ _))
      (errorTerm_summable p g z)
  · rw [activeMass_eq_sum]
    refine Finset.sum_le_sum fun h _ => ?_
    have := mul_le_mul_of_nonneg_left (miss_le_one (r h) z) (activeTerm_nonneg p n z h)
    linarith

/-- **Part (iv), second clause.** Scoring every active history as an error raises the error of
the full decoder by the active mass minus the error of the full decoder on the transcripts that
continue the active histories. -/
theorem horizonErrorAll_eq (p : FiniteProtocol Z A Y) (g : List (A × Y) → Z) (n : ℕ) :
    horizonErrorAll p g n = fullError p g + ∑ z, activeMass p n z - activeError p g n := by
  unfold horizonErrorAll fullError activeError
  have hsplit : ∀ z, ∑' h, transcriptMass p z h * miss (g h) z =
      (∑ h ∈ historySet (A × Y) n, transcriptMass p z h * miss (g h) z) +
        ∑' h : ((historySet (A × Y) n : Set (List (A × Y)))ᶜ : Set (List (A × Y))),
          transcriptMass p z h * miss (g h) z := fun z =>
    ((errorTerm_summable p g z).sum_add_tsum_compl).symm
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  ring

theorem activeError_le (p : FiniteProtocol Z A Y) (g : List (A × Y) → Z) (n : ℕ) :
    activeError p g n ≤ ∑ z, activeMass p n z := by
  unfold activeError
  refine Finset.sum_le_sum fun z _ => ?_
  have hT := (transcriptMass_summable p z).sum_add_tsum_compl (s := historySet (A × Y) n)
  have hle : ∑' h : ((historySet (A × Y) n : Set (List (A × Y)))ᶜ : Set (List (A × Y))),
      transcriptMass p z h * miss (g h) z ≤
      ∑' h : ((historySet (A × Y) n : Set (List (A × Y)))ᶜ : Set (List (A × Y))),
        transcriptMass p z h :=
    Summable.tsum_le_tsum (fun h => by
        have := mul_le_mul_of_nonneg_left (miss_le_one (g h) z) (transcriptMass_nonneg p z h)
        linarith)
      ((errorTerm_summable p g z).subtype _) ((transcriptMass_summable p z).subtype _)
  have htot := transcriptTotal_le_prior p z
  have hact := activeMass_eq p n z
  unfold transcriptTotal at htot
  linarith

/-- Scoring every active history as an error never lowers the error of the full decoder. -/
theorem fullError_le_horizonErrorAll (p : FiniteProtocol Z A Y) (g : List (A × Y) → Z) (n : ℕ) :
    fullError p g ≤ horizonErrorAll p g n := by
  rw [horizonErrorAll_eq]
  linarith [activeError_le p g n]

end OperatorKO7.Meta.BoundaryObserver.StoppedHorizonError
