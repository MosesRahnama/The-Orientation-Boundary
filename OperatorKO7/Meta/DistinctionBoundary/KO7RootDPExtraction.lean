import OperatorKO7.Meta.DependencyPairs_Works
import OperatorKO7.Kernel

set_option autoImplicit false

/-!
# Complete DP extraction against the eight KO7 root rules

Every `Step` is classified by its constructor. The only rule that
extracts a dependency pair is `R_rec_succ`. Soundness: that pair is
exactly `DPPair.rec_succ`. Completeness: no other root rule produces a
`DPPair`. The control TRS `SpuriousPair` is not a KO7 step.

Does not edit `Step` or `SafeStep`.
-/

open OperatorKO7 Trace
open OperatorKO7.MetaDependencyPairs

namespace OperatorKO7.Meta.DistinctionBoundary.KO7RootDPExtraction

def isRecSuccRedex (a b : Trace) : Prop :=
  ∃ bb ss nn : Trace, a = recΔ bb ss (delta nn) ∧ b = app ss (recΔ bb ss nn)

def extractsDP {a b : Trace} (_h : Step a b) : Prop :=
  isRecSuccRedex a b

theorem extractsDP_recSucc (bb ss nn : Trace) :
    extractsDP (Step.R_rec_succ bb ss nn) :=
  ⟨bb, ss, nn, rfl, rfl⟩

theorem extractsDP_iff {a b : Trace} (h : Step a b) :
    extractsDP h ↔ isRecSuccRedex a b :=
  Iff.rfl

theorem dpPair_iff {a c : Trace} :
    DPPair a c ↔
      ∃ bb ss nn : Trace, a = recΔ bb ss (delta nn) ∧ c = recΔ bb ss nn := by
  constructor
  · intro h
    cases h with
    | rec_succ bb ss nn => exact ⟨bb, ss, nn, rfl, rfl⟩
  · rintro ⟨bb, ss, nn, rfl, rfl⟩
    exact DPPair.rec_succ bb ss nn

theorem extraction_sound {a b : Trace} (h : Step a b) (hex : extractsDP h) :
    ∃ c, DPPair a c := by
  cases h with
  | R_rec_succ bb ss nn =>
      exact ⟨recΔ bb ss nn, DPPair.rec_succ bb ss nn⟩
  | R_int_delta t =>
      rcases hex with ⟨_, _, _, h1, _⟩; cases h1
  | R_merge_void_left t =>
      rcases hex with ⟨_, _, _, h1, _⟩; cases h1
  | R_merge_void_right t =>
      rcases hex with ⟨_, _, _, h1, _⟩; cases h1
  | R_merge_cancel t =>
      rcases hex with ⟨_, _, _, h1, _⟩; cases h1
  | R_rec_zero bb ss =>
      rcases hex with ⟨_, _, _, h1, _⟩; cases h1
  | R_eq_refl a =>
      rcases hex with ⟨_, _, _, h1, _⟩; cases h1
  | R_eq_diff a b =>
      rcases hex with ⟨_, _, _, h1, _⟩; cases h1

theorem extraction_complete {a b : Trace} (h : Step a b) :
    (∃ c, DPPair a c) ↔ extractsDP h := by
  constructor
  · intro ⟨c, hc⟩
    cases h with
    | R_rec_succ bb ss nn =>
        exact extractsDP_recSucc bb ss nn
    | R_int_delta t =>
        cases hc
    | R_merge_void_left t =>
        cases hc
    | R_merge_void_right t =>
        cases hc
    | R_merge_cancel t =>
        cases hc
    | R_rec_zero bb ss =>
        cases hc
    | R_eq_refl a =>
        cases hc
    | R_eq_diff a b =>
        cases hc
  · intro hex
    exact extraction_sound h hex

theorem seven_rules_pair_free {a b : Trace} (h : Step a b)
    (hne : ¬ extractsDP h) : ¬ ∃ c, DPPair a c := by
  intro hc
  exact hne ((extraction_complete h).mp hc)

theorem processor_rank_decrease {a c : Trace} (h : DPPair a c) :
    dpRank c < dpRank a :=
  dpPair_decreases h

theorem processor_wf : WellFounded DPPairRev :=
  wf_DPPairRev

inductive SpuriousPair : Trace → Trace → Prop
  | extra : SpuriousPair void (delta void)

theorem spurious_not_step : ¬ Step void (delta void) := by
  intro h
  cases h

theorem spurious_not_dpPair : ¬ DPPair void (delta void) := by
  intro h
  cases h

theorem recSucc_nonvacuous :
    extractsDP (Step.R_rec_succ void void void) :=
  extractsDP_recSucc void void void

/-- Processor soundness on the concrete KO7 system: every extracted DP
is a real `DPPair`, strictly decreases rank, and the DP relation is
well-founded. Completeness identifies extraction with existence of a DP. -/
theorem processor_sound {a b : Trace} (h : Step a b) :
    (extractsDP h ↔ ∃ c, DPPair a c) ∧
      (∀ c, DPPair a c → dpRank c < dpRank a) ∧
      WellFounded DPPairRev :=
  ⟨(extraction_complete h).symm, fun _ hc => processor_rank_decrease hc,
    processor_wf⟩

end OperatorKO7.Meta.DistinctionBoundary.KO7RootDPExtraction
