import OperatorKO7.Meta.InformationalIncompleteness.ShannonFinite
import OperatorKO7.Meta.InformationalIncompleteness.ConditionalEntropy
import OperatorKO7.Meta.InformationalIncompleteness.QueryInterface
import OperatorKO7.Meta.InformationalIncompleteness.LicensedChannelDeficit

/-!
# Propagation residual, lead, and the first reactor (Boundary Propagation Program, Formal-spec layer)

This module turns the Formal-spec objects of the Boundary Propagation Program
(`docs/paper/Rahnama_Boundary_Propagation_Program.tex`) into Proven-in-Lean declarations on the existing
finite-Shannon substrate. Every object here is an INSTANCE of the audited licensed-channel deficit
`LicensedChannelDeficit.deficit = I(target ; C | surface)`; nothing is re-derived.

The licensed-channel deficit `Def_t(C; Y, h) = I(Y ; C | W0)` measures the payoff information a channel
carries beyond the committed market surface `W0` (the querant's direct surface). The propagation layer asks a
sharper, time-indexed question: after the market record has GROWN to the future committed surface
`W0_{t+s}` (`def:future-w0`, `W0_t ⊆ W0_{t+s}`), how much channel information is still unabsorbed?

* `propagationResidual` (`def:residual`) — `Def_{t,s}(C; Y, h) = I(Y ; C | W0_{t+s})`: the deficit conditioned
  on the GROWN surface. It is `LicensedChannelDeficit.deficit` with the conditioning surface taken to be the
  grown-surface cell index `Ws`.
* `lead` (`def:lead`) — `Lead_t(C; U, u) = I(U ; C | W0)`: the same conditional-MI functional with the payoff
  target `Y` replaced by a committed market-update target `U` (does the channel predict the market's next
  committed record, not merely a payoff label?). It is `LicensedChannelDeficit.deficit` at target type `U`.
* `residual_nonneg` (`prop:nonnegative`, shadow) — the residual is `≥ 0`; reuses `deficit_nonneg`.
* `residual_zero_of_measurable` (`thm:synch-kills`, the SYNCHRONIZATION theorem) — if the channel is
  measurable with respect to the grown surface (the channel is a function of `W0_{t+s}`, i.e. its target
  conditional does not depend on the channel cell once the grown surface is fixed), the residual is zero. This
  is the conditional shadow of `circular_reference_zero_deficit` / the diagonal-entropy lemma
  `diagonal_entropy_eq`: a channel the grown record already determines carries no unabsorbed information, so the
  propagation residual collapses. The market reading: once the witness has synchronized into the committed
  surface, the non-vacuous channel returns vacuous.
* `FirstReactor` (`def:first-reactor`) — the four-condition predicate that makes a channel a trade-facing alpha
  source: positive deficit (carries information beyond `W0`), positive lead (leads a committed market record),
  not a diagonal echo of `W0`, and a propagation window exceeding the strategy's latency. The last two are the
  guards that separate a genuine first reactor from a late echo.

Honesty: this is finite classical information theory, identical in content to the audited
`LicensedChannelDeficit` substrate. The market readings (first-reactor alpha, synchronization, forced flow) are
interpretive labels carried in prose and docstrings, never in a theorem; no theorem here asserts that any real
channel has positive residual or is a first reactor on any data, only the DEFINITIONS and the STRUCTURAL
theorems about them. No rewriting relation. Trust: no `sorry`/`admit`/`axiom`/`native_decide`; every headline
theorem's axiom closure is a subset of `{propext, Classical.choice, Quot.sound}` (audited at the foot of this
file and in the reach gate).
-/

set_option autoImplicit false

open scoped BigOperators

namespace OperatorKO7.Meta.InformationalIncompleteness.PropagationResidual

open OperatorKO7.Meta.InformationalIncompleteness.ShannonFinite
open OperatorKO7.Meta.InformationalIncompleteness.ConditionalEntropy
open OperatorKO7.Meta.InformationalIncompleteness.QueryInterface
open OperatorKO7.Meta.InformationalIncompleteness.LicensedChannelDeficit

variable {Y U W Ws Cn : Type} [Fintype Y] [Fintype U] [Fintype W] [Fintype Ws] [Fintype Cn]

/-- **Propagation residual** `Def_{t,s}(C; Y, h) = I(Y ; C | W0_{t+s})` (`def:residual`): the licensed-channel
deficit conditioned on the GROWN committed surface `W0_{t+s}`, whose cells are indexed by `Ws`. It is exactly
the audited conditional-MI functional `LicensedChannelDeficit.deficit` with the conditioning surface taken to
be the grown surface, so all of its structural theorems specialise. `μs w` is the weight of grown-surface cell
`w`, `νs w c` the conditional channel weight, and `rs w c` the target conditional given `(w, c)`. -/
noncomputable def propagationResidual (μs : Ws → ℝ) (νs : Ws → Cn → ℝ) (rs : Ws → Cn → Y → ℝ) : ℝ :=
  deficit μs νs rs

/-- **Lead score** `Lead_t(C; U, u) = I(U ; C | W0)` (`def:lead`): the same conditional-MI functional as the
deficit, but with the payoff target replaced by a committed market-update target `U` (price move, spread
change, auction print, factor-record update). It is `LicensedChannelDeficit.deficit` at target type `U`, so it
inherits nonnegativity and the circular-reference collapse verbatim. -/
noncomputable def lead (μ : W → ℝ) (ν : W → Cn → ℝ) (rU : W → Cn → U → ℝ) : ℝ :=
  deficit μ ν rU

/--
Proves: the propagation residual is nonnegative (`prop:nonnegative`, conditioned on the grown surface). A
  channel never increases the conditional entropy of the target given the grown record. Reuses
  `LicensedChannelDeficit.deficit_nonneg` directly (the residual IS that deficit).
Does not prove: strict positivity (that is the unsynchronized first-reactor case / an empirical question).
Relation: not applicable. Closure: not applicable. Trust: kernel-only.
Scope: every finite `Y, Ws, Cn`, weights `μs ≥ 0`, channel weights `νs ≥ 0` with `∑_c νs w c = 1`, and
  nonnegative conditionals `rs`.
-/
theorem residual_nonneg (μs : Ws → ℝ) (νs : Ws → Cn → ℝ) (rs : Ws → Cn → Y → ℝ)
    (hμ0 : ∀ w, 0 ≤ μs w)
    (hν0 : ∀ w c, 0 ≤ νs w c) (hν1 : ∀ w, ∑ c, νs w c = 1)
    (hr0 : ∀ w c x, 0 ≤ rs w c x) :
    0 ≤ propagationResidual μs νs rs := by
  unfold propagationResidual
  exact deficit_nonneg μs νs rs hμ0 hν0 hν1 hr0

/--
Proves: nonnegativity of the lead score (`Lead_t(C; U, u) ≥ 0`). Reuses `deficit_nonneg` at target type `U`.
Does not prove: strict positivity (that is the leading-channel case / empirical).
Relation/Closure: not applicable. Trust: kernel-only.
Scope: as `residual_nonneg`, with the committed-update target `U`.
-/
theorem lead_nonneg (μ : W → ℝ) (ν : W → Cn → ℝ) (rU : W → Cn → U → ℝ)
    (hμ0 : ∀ w, 0 ≤ μ w)
    (hν0 : ∀ w c, 0 ≤ ν w c) (hν1 : ∀ w, ∑ c, ν w c = 1)
    (hr0 : ∀ w c u, 0 ≤ rU w c u) :
    0 ≤ lead μ ν rU := by
  unfold lead
  exact deficit_nonneg μ ν rU hμ0 hν0 hν1 hr0

/--
Proves: the SYNCHRONIZATION theorem `thm:synch-kills` (synchronization kills the residual deficit). If the
  channel is measurable with respect to the GROWN surface `W0_{t+s}` (the channel is a function of the grown
  record: its target conditional `rs w c` does not depend on the channel cell `c` once the grown-surface cell
  `w` is fixed, witnessed by `rs w c = s w`), then the propagation residual is zero. This is the conditional
  shadow of `circular_reference_zero_deficit` / the diagonal-entropy lemma `diagonal_entropy_eq`: a channel the
  grown record already determines carries no unabsorbed information. Market reading: once the witness has
  synchronized into the committed surface, the non-vacuous channel returns vacuous, and the propagation window
  has closed.
Does not prove: that a given empirical channel is synchronized at delay `s` (that is observed, not proved);
  the synchronization is the measurability hypothesis `rs w c = s w`, exactly as the paper states it.
Relation: not applicable. Closure: not applicable. Trust: kernel-only.
Scope: every finite `Y, Ws, Cn`, channel weights with `∑_c νs w c = 1`, and grown-surface-measurable channel
  conditional `s`.
-/
theorem residual_zero_of_measurable (μs : Ws → ℝ) (νs : Ws → Cn → ℝ) (rs : Ws → Cn → Y → ℝ)
    (hν1 : ∀ w, ∑ c, νs w c = 1)
    (s : Ws → Y → ℝ) (hmeas : ∀ w c, rs w c = s w) :
    propagationResidual μs νs rs = 0 := by
  unfold propagationResidual
  exact circular_reference_zero_deficit μs νs rs hν1 s hmeas

/--
Proves: contrapositive of `residual_zero_of_measurable`. A nonzero propagation residual forces a channel that
  is NOT measurable with respect to the grown surface: it is not yet synchronized, so its target conditional
  genuinely depends on the channel cell. A positive residual after delay `s` certifies an open propagation
  window. Reuses `positive_deficit_requires_exogeny`.
Does not prove: a quantitative residual lower bound. Relation/Closure: not applicable. Trust: kernel-only.
Scope: as `residual_zero_of_measurable`.
-/
theorem positive_residual_not_synchronized (μs : Ws → ℝ) (νs : Ws → Cn → ℝ) (rs : Ws → Cn → Y → ℝ)
    (hν1 : ∀ w, ∑ c, νs w c = 1) (hr : propagationResidual μs νs rs ≠ 0) :
    ¬ ∃ s : Ws → Y → ℝ, ∀ w c, rs w c = s w := by
  unfold propagationResidual at hr
  exact positive_deficit_requires_exogeny μs νs rs hν1 hr

/-! ## The first-reactor predicate (`def:first-reactor`). -/

/-- A channel is a `DiagonalEcho` of the direct surface `W0` if its target conditional does not depend on the
channel cell (it is informationally a function of `W0` alone: observing it after `W0` adds no state
information, `def:diagonal-echo`). This is exactly the hypothesis under which the deficit is zero. -/
def DiagonalEcho (r : W → Cn → Y → ℝ) : Prop := ∃ s : W → Y → ℝ, ∀ w c, r w c = s w

/--
**First-reactor channel** (`def:first-reactor`): the four-condition predicate that makes a channel a
trade-facing directional-alpha source. Bundles
1. `0 < deficit μ ν r` — it carries payoff information beyond the direct surface `W0`;
2. `0 < lead μ ν rU` — it leads a subsequent committed market record (not merely a payoff label);
3. `¬ DiagonalEcho r` — it is not a redundant copy of `W0` (an open, exogenous channel);
4. `latency < window` — its propagation window exceeds the strategy's latency and execution time, so the edge
   is still open where it is tradable.
Conditions 3 and 4 are the guards separating a genuine first reactor from a late echo. -/
structure FirstReactor (μ : W → ℝ) (ν : W → Cn → ℝ) (r : W → Cn → Y → ℝ) (rU : W → Cn → U → ℝ)
    (window latency : ℝ) : Prop where
  /-- Positive licensed-channel deficit: the channel carries payoff information beyond `W0`. -/
  deficit_pos : 0 < deficit μ ν r
  /-- Positive lead: the channel leads a subsequent committed market record. -/
  lead_pos : 0 < lead μ ν rU
  /-- Not a diagonal echo: the channel is genuinely exogenous to `W0`. -/
  not_echo : ¬ DiagonalEcho r
  /-- The propagation window exceeds the strategy's latency and execution time. -/
  window_gt_latency : latency < window

/--
Proves: a first-reactor channel has positive deficit AND positive lead AND an open (latency-exceeding) window.
  A structural readout of the bundled predicate — the three positive-quantity guarantees a trade-facing route
  requires.
Does not prove: that any empirical channel is a first reactor (that is the held-out test, not a theorem).
Relation/Closure: not applicable. Trust: kernel-only.
Scope: every first-reactor channel.
-/
theorem firstReactor_positive_and_open (μ : W → ℝ) (ν : W → Cn → ℝ) (r : W → Cn → Y → ℝ)
    (rU : W → Cn → U → ℝ) (window latency : ℝ)
    (h : FirstReactor μ ν r rU window latency) :
    0 < deficit μ ν r ∧ 0 < lead μ ν rU ∧ latency < window :=
  ⟨h.deficit_pos, h.lead_pos, h.window_gt_latency⟩

/--
Proves: a first reactor is not synchronized at delay zero. Because a first-reactor channel is not a diagonal
  echo of `W0`, the residual at the direct surface (delay `s = 0`, where the grown surface is `W0` itself) is
  not forced to zero by `residual_zero_of_measurable`; equivalently the channel fails the synchronization
  (measurability) hypothesis at the direct surface. This is the formal separation of a first reactor from a
  late echo at the moment of observation.
Does not prove: positivity of the residual at later delays (the half-life governs that, empirically).
Relation/Closure: not applicable. Trust: kernel-only.
Scope: every first-reactor channel, read at the direct surface.
-/
theorem firstReactor_not_diagonalEcho (μ : W → ℝ) (ν : W → Cn → ℝ) (r : W → Cn → Y → ℝ)
    (rU : W → Cn → U → ℝ) (window latency : ℝ)
    (h : FirstReactor μ ν r rU window latency) :
    ¬ ∃ s : W → Y → ℝ, ∀ w c, r w c = s w :=
  h.not_echo

/-! ## R5 non-vacuity witnesses. -/

/-- R5 (synchronized echo / zero residual): a one-cell grown surface (`Ws = Fin 1`), a binary target
(`Y = Fin 2`), and a binary channel (`Cn = Fin 2`) whose target conditional is constant across channel cells
(the channel is a function of the grown surface, i.e. it has synchronized). Then the propagation residual is
zero by `residual_zero_of_measurable`: synchronization kills the residual deficit. -/
theorem residual_witness_zero :
    propagationResidual (Ws := Fin 1) (Cn := Fin 2) (Y := Fin 2)
      (fun _ => 1) (fun _ _ => (1 : ℝ) / 2) (fun _ _ => fun _ => (1 : ℝ) / 2) = 0 :=
  residual_zero_of_measurable _ _ _
    (fun _ => by rw [Fin.sum_univ_two]; norm_num)
    (fun _ => fun _ => (1 : ℝ) / 2) (fun _ _ => rfl)

/-- R5 (positive lead): a one-cell direct surface (`W = Fin 1`), a binary committed-update target (`U = Fin 2`),
and a binary channel (`Cn = Fin 2`) that perfectly reveals the update (the channel leads the market record).
The lead score is strictly positive: the channel predicts the market's next committed record. Witnesses that
the second first-reactor condition is satisfiable, and that `lead` is a genuine conditional-MI instance (not
identically zero). -/
theorem lead_witness_pos :
    0 < lead (W := Fin 1) (U := Fin 2) (Cn := Fin 2)
      (fun _ => 1) (fun _ _ => (1 : ℝ) / 2) (fun _ c => pointMass c) := by
  unfold lead
  -- `deficit` with a perfectly-revealing channel is the binary-uniform entropy, mirroring `deficit_witness_pos`.
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

/-! ## Headline axiom audit (subset of {propext, Classical.choice, Quot.sound}). -/

#print axioms residual_nonneg
#print axioms lead_nonneg
#print axioms residual_zero_of_measurable
#print axioms positive_residual_not_synchronized
#print axioms firstReactor_positive_and_open
#print axioms firstReactor_not_diagonalEcho
#print axioms residual_witness_zero
#print axioms lead_witness_pos

end OperatorKO7.Meta.InformationalIncompleteness.PropagationResidual
