import OperatorKO7.Meta.BoundaryGeneral.EchoLawInstance
import OperatorKO7.Meta.InformationalIncompleteness.QuoteEvalDiagonalDeficit
import OperatorKO7.Meta.InformationalIncompleteness.EqWDiagonalDeficit

/-!
# Quotation peak as an echo-law episode

`quoteKernelEpisode` uses `QuoteEvalStar true` for raw emissions and `QuoteEvalStar false` for licensed emissions. At `freezePeakSource`, the answer is independent of the object. Raw reachability includes `.value void` and `.diverged`; the frozen licensed relation cannot reach `.diverged`.

The theorems establish the echo hypotheses, false formal legitimacy, and a nonjoinable raw peak. `quoteKernelEpisode_exact_peak` combines the episode result with the quote/eval step to `.value void`, the path to `.diverged`, their nonjoinability, and the frozen-relation result. The earlier `quoteEpisode` definition gives a Boolean model of the same conditions.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.BoundaryGeneral.EchoLawQuoteInstance

open OperatorKO7.Meta.BoundaryGeneral.EchoLaw
open OperatorKO7.Meta.BoundaryGeneral.DistinctionRecord
open OperatorKO7.Meta.BoundaryGeneral.EchoLawInstance
open OperatorKO7.Meta.InformationalIncompleteness.QuoteEvalDiagonalDeficit
open OperatorKO7.Meta.InformationalIncompleteness.EqWDiagonalDeficit
open OperatorKO7.Meta.InformationalIncompleteness.ShannonFinite
open OperatorKO7.Meta.InformationalIncompleteness.LicensedChannelDeficit
open OperatorKO7.Meta.SafeStep.EqWVoidAnomaly
open OperatorKO7.Meta.DistinctionBoundary.GodelPartial
open OperatorKO7 Trace

/-- State `false` is the echo peak. State `true` is informative because its answer depends on the Boolean object. -/
def quoteEpisode : Episode where
  State := Bool
  Object := Bool
  Answer := Bool
  Record := Rec Bool
  null := Rec.void
  nonnull := Rec.nonnull
  answer := fun s o => if s then o else false
  Distinction := fun s => s = true
  rawEmits := fun _ r => r = Rec.void ∨ r = Rec.diff false false
  licensedEmits := fun s r => r = Rec.void ∨ (s = true ∧ r = Rec.diff false false)

def quotePeak : Bool := false

theorem quoteEpisode_echo_at_peak : EchoAt quoteEpisode quotePeak := by
  intro o o'
  simp [quoteEpisode, quotePeak]

theorem quoteEpisode_informative_off_peak :
    InformativeAt quoteEpisode true := by
  refine ⟨false, true, ?_⟩
  simp [quoteEpisode]

theorem quoteEpisode_licensedSound : LicensedSound quoteEpisode := by
  intro s r hr hn
  cases hr with
  | inl h =>
    subst h
    exact absurd hn (by simp [quoteEpisode, Rec.nonnull])
  | inr h =>
    exact h.1

theorem quoteEpisode_objectWitnessed : ObjectWitnessed quoteEpisode := by
  intro s hs
  subst s
  exact quoteEpisode_informative_off_peak

theorem quoteEpisode_null_is_null : ¬ quoteEpisode.nonnull quoteEpisode.null := by
  simp [quoteEpisode, Rec.nonnull]

theorem quoteEpisode_raw_null :
    quoteEpisode.rawEmits quotePeak quoteEpisode.null :=
  Or.inl rfl

/-- The raw relation emits a non-null record at `quotePeak`. -/
theorem quoteEpisode_raw_manufactures :
    ∃ r, quoteEpisode.rawEmits quotePeak r ∧ quoteEpisode.nonnull r :=
  ⟨Rec.diff false false, Or.inr rfl, trivial⟩

theorem quoteEpisode_ffl_at_peak :
    FalseFormalLegitimacyAt quoteEpisode quotePeak :=
  ffl_of_raw_nonnull_at_echo quoteEpisode_licensedSound
    quoteEpisode_objectWitnessed quoteEpisode_echo_at_peak
    quoteEpisode_raw_manufactures

theorem quoteEpisode_no_licensed_record_at_peak :
    ¬ ∃ r, quoteEpisode.licensedEmits quotePeak r ∧ quoteEpisode.nonnull r :=
  no_licensed_nonnull_at_echo quoteEpisode_licensedSound
    quoteEpisode_objectWitnessed quoteEpisode_echo_at_peak

/-- An echo run increases mass and keeps the peak state fixed. -/
def quoteEchoDynamics : EchoDynamics quoteEpisode where
  Trace := Nat × Bool
  mass := Prod.fst
  stateOf := Prod.snd
  step := fun t => (t.1 + 1, t.2)
  mass_grows := fun _ => rfl
  state_fixed := fun _ => rfl

theorem quoteEpisode_trap (n : Nat) :
    quoteEchoDynamics.mass (run quoteEchoDynamics (0, quotePeak) n) = n
      ∧ quoteEchoDynamics.stateOf (run quoteEchoDynamics (0, quotePeak) n) = quotePeak
      ∧ ¬ ∃ r, quoteEpisode.licensedEmits
            (quoteEchoDynamics.stateOf (run quoteEchoDynamics (0, quotePeak) n)) r
          ∧ quoteEpisode.nonnull r := by
  refine ⟨?_, run_state quoteEchoDynamics (0, quotePeak) n, ?_⟩
  · have h := run_mass quoteEchoDynamics (0, quotePeak) n
    simpa [quoteEchoDynamics] using h
  exact no_licensed_nonnull_at_any_run_depth quoteEpisode_licensedSound
    quoteEpisode_objectWitnessed quoteEchoDynamics (0, quotePeak)
    quoteEpisode_echo_at_peak n

/-! ## Episode over `QuoteEvalCfg` -/

/-- Raw emissions use `QuoteEvalStar` with quotation congruence enabled; licensed emissions use it with congruence disabled. The divergent configuration is the non-null record. -/
def quoteKernelEpisode : Episode where
  State := QuoteEvalCfg
  Object := Bool
  Answer := Bool
  Record := QuoteEvalCfg
  null := .value void
  nonnull := fun r => r = .diverged
  answer := fun s o => if s = freezePeakSource then false else o
  Distinction := fun s => s ≠ freezePeakSource
  rawEmits := QuoteEvalStar true
  licensedEmits := QuoteEvalStar false

def quoteKernelPeak : quoteKernelEpisode.State := freezePeakSource

theorem quoteKernelEpisode_echo_at_peak :
    EchoAt quoteKernelEpisode quoteKernelPeak := by
  intro o o'
  simp [quoteKernelEpisode, quoteKernelPeak]

theorem quoteKernelEpisode_informative_off_peak
    {s : quoteKernelEpisode.State} (hs : s ≠ quoteKernelPeak) :
    InformativeAt quoteKernelEpisode s := by
  have hs' : s ≠ freezePeakSource := by
    simpa [quoteKernelPeak] using hs
  refine ⟨false, true, ?_⟩
  simp [quoteKernelEpisode, hs']

/-- With quotation congruence disabled, `freezePeakSource` has no path to `.diverged`. -/
theorem no_frozen_quoteEvalStar_peak_diverged :
    ¬ QuoteEvalStar false freezePeakSource .diverged := by
  intro h
  cases h with
  | tail hstep hstar =>
      cases hstep with
      | underQuote henabled _ => cases henabled
      | evalConverge _ =>
          have hv := star_from_value hstar
          cases hv
      | evalDiverge hd =>
          exact quote_diverge_blocks_join hd quote_merge_void_void_converges

theorem quoteKernelEpisode_licensedSound :
    LicensedSound quoteKernelEpisode := by
  intro s r hr hn
  change r = QuoteEvalCfg.diverged at hn
  subst r
  change s ≠ freezePeakSource
  intro hs
  subst s
  exact no_frozen_quoteEvalStar_peak_diverged hr

theorem quoteKernelEpisode_objectWitnessed :
    ObjectWitnessed quoteKernelEpisode := by
  intro s hs
  exact quoteKernelEpisode_informative_off_peak hs

theorem quoteKernelEpisode_null_is_null :
    ¬ quoteKernelEpisode.nonnull quoteKernelEpisode.null := by
  simp [quoteKernelEpisode]

theorem quoteKernelEpisode_raw_null :
    quoteKernelEpisode.rawEmits quoteKernelPeak quoteKernelEpisode.null :=
  QuoteEvalStar.tail freeze_peak_eval_converge (QuoteEvalStar.refl _)

theorem quoteKernelEpisode_raw_manufactures :
    ∃ r, quoteKernelEpisode.rawEmits quoteKernelPeak r ∧
      quoteKernelEpisode.nonnull r :=
  ⟨.diverged, quote_eval_nonjoinable_peak.2.1, rfl⟩

theorem quoteKernelEpisode_ffl_at_peak :
    FalseFormalLegitimacyAt quoteKernelEpisode quoteKernelPeak :=
  ffl_of_raw_nonnull_at_echo quoteKernelEpisode_licensedSound
    quoteKernelEpisode_objectWitnessed quoteKernelEpisode_echo_at_peak
    quoteKernelEpisode_raw_manufactures

theorem quoteKernelEpisode_no_licensed_record_at_peak :
    ¬ ∃ r, quoteKernelEpisode.licensedEmits quoteKernelPeak r ∧
      quoteKernelEpisode.nonnull r :=
  no_licensed_nonnull_at_echo quoteKernelEpisode_licensedSound
    quoteKernelEpisode_objectWitnessed quoteKernelEpisode_echo_at_peak

/-- At `quoteKernelPeak`, the episode has false formal legitimacy; the enabled relation reaches `.value void` and `.diverged` without joining them, while the disabled relation cannot reach `.diverged`. -/
theorem quoteKernelEpisode_exact_peak :
    FalseFormalLegitimacyAt quoteKernelEpisode quoteKernelPeak
      ∧ QuoteEvalStep true freezePeakSource (.value void)
      ∧ QuoteEvalStar true freezePeakSource .diverged
      ∧ ¬ QuoteEvalJoin true (.value void) .diverged
      ∧ ¬ QuoteEvalStar false freezePeakSource .diverged :=
  ⟨quoteKernelEpisode_ffl_at_peak, quote_eval_nonjoinable_peak.1,
    quote_eval_nonjoinable_peak.2.1, quote_eval_nonjoinable_peak.2.2,
    no_frozen_quoteEvalStar_peak_diverged⟩

/-- Bundles the diagonal conclusions from the equality, quote/eval, and Boolean comparator instances. -/
def three_diagonal_faces :=
  And.intro eqW_diagonal_echo_vacuum_with_fork
    (And.intro quoteEval_diagonal_echo_vacuum_with_peak
      (eqwEpisode_ffl_on_diagonal true))

end OperatorKO7.Meta.BoundaryGeneral.EchoLawQuoteInstance
