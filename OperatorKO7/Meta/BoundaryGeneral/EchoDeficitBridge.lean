import OperatorKO7.Meta.BoundaryGeneral.EchoLaw
import OperatorKO7.Meta.InformationalIncompleteness.LicensedChannelDeficit

/-!
# The echo law and the licensed-channel deficit are the same boundary condition

`EchoLaw` states the boundary condition structurally: the answer at a state
ignores the object coordinate. `LicensedChannelDeficit` states it
quantitatively: the licensed channel supplies zero conditional information about
the target. This module proves the two agree, under one named hypothesis.

The hypothesis is `ChannelSufficient`: the target conditional is revised only
through the answer, so the answer is a sufficient statistic for the channel.
That is the honest content of "the channel informs the querant only by what it
answers"; without it a channel cell could move the target law behind the
answer's back and the two readings would legitimately differ.

* `echo_forces_zero_deficit` - structural echo implies quantitative vacuum.
* `positive_deficit_forces_informative_channel` - the converse in its valid
  direction: positive licensed gain forces a channel that reads the object.
  The unrestricted converse is false, since a zero deficit tolerates answer
  variation on null-weight cells.
* `echo_zero_deficit_and_no_licensed_record` - the two faces at one state.

## Claim typing (binding)
* PROVEN: the theorems below.
* SCOPE: `ChannelSufficient` is a declared modelling hypothesis. The reference
  object `o₀` is an explicit parameter, so no channel-cell inhabitation is
  assumed silently.

## Audit slots
- Relation: none. Closure: none. The content is finite information theory over
  the `EchoLaw.Episode` abstraction.
- Trust: no `sorry`/`admit`/`axiom`/`native_decide`; Mathlib baseline.
-/

set_option autoImplicit false

open scoped BigOperators

namespace OperatorKO7.Meta.BoundaryGeneral.EchoDeficitBridge

open OperatorKO7.Meta.BoundaryGeneral.EchoLaw
open OperatorKO7.Meta.InformationalIncompleteness.LicensedChannelDeficit

variable {E : Episode} {X : Type} [Fintype X] [Fintype E.Object]

/-- The target conditional induced by a posterior map reading the answer. The
channel cell is the object coordinate; the direct surface is the single cell of
the state under audit. -/
noncomputable def channelConditional
    (E : Episode) {X : Type} (post : E.Answer → X → ℝ) (s : E.State) :
    Fin 1 → E.Object → X → ℝ :=
  fun _ o x => post (E.answer s o) x

/-- **Channel sufficiency.** The querant revises the target law only through the
answer: the conditional at a channel cell is the posterior of that cell's
answer. Stated as a definition so the hypothesis is visible in every theorem
that consumes it. -/
def ChannelSufficient
    (E : Episode) {X : Type} (post : E.Answer → X → ℝ) (s : E.State)
    (r : Fin 1 → E.Object → X → ℝ) : Prop :=
  r = channelConditional E post s

/-- **Structural echo forces the quantitative vacuum.** If the answer at `s`
ignores the object coordinate and the target conditional is revised only through
the answer, the licensed-channel deficit at `s` is zero: the return carries no
information about the target beyond the direct surface. -/
theorem echo_forces_zero_deficit
    (post : E.Answer → X → ℝ) (s : E.State) (o₀ : E.Object)
    (hecho : EchoAt E s)
    (μ : Fin 1 → ℝ) (ν : Fin 1 → E.Object → ℝ)
    (hν1 : ∀ w, ∑ c, ν w c = 1) :
    deficit μ ν (channelConditional E post s) = 0 := by
  refine circular_reference_zero_deficit μ ν _ hν1
    (fun _ x => post (E.answer s o₀) x) ?_
  intro w c
  funext x
  simp only [channelConditional]
  rw [hecho c o₀]

/-- The same statement for any conditional carrying the sufficiency certificate. -/
theorem echo_forces_zero_deficit_of_sufficient
    (post : E.Answer → X → ℝ) (s : E.State) (o₀ : E.Object)
    (r : Fin 1 → E.Object → X → ℝ) (hsuff : ChannelSufficient E post s r)
    (hecho : EchoAt E s)
    (μ : Fin 1 → ℝ) (ν : Fin 1 → E.Object → ℝ)
    (hν1 : ∀ w, ∑ c, ν w c = 1) :
    deficit μ ν r = 0 := by
  rw [hsuff]
  exact echo_forces_zero_deficit post s o₀ hecho μ ν hν1

/-- **Positive licensed gain forces an exogenous coordinate.** A nonzero deficit
at `s` proves the channel there reads the object. This is the valid direction of
the converse; the unrestricted converse fails, because a zero deficit tolerates
answer variation on cells of zero weight. -/
theorem positive_deficit_forces_informative_channel
    (post : E.Answer → X → ℝ) (s : E.State) (o₀ : E.Object)
    (μ : Fin 1 → ℝ) (ν : Fin 1 → E.Object → ℝ)
    (hν1 : ∀ w, ∑ c, ν w c = 1)
    (hd : deficit μ ν (channelConditional E post s) ≠ 0) :
    InformativeAt E s := by
  refine Classical.byContradiction (fun hni => ?_)
  exact hd (echo_forces_zero_deficit post s o₀
    ((echoAt_iff_not_informativeAt E s).mpr hni) μ ν hν1)

/-- **The two faces at one state.** At an echo state of a distinction-sound,
object-witnessed episode the information face reads zero licensed gain and the
record face emits no licensed non-null record. The quantitative vacuum and the
structural silence are the same event on the same carrier. -/
theorem echo_zero_deficit_and_no_licensed_record
    (hsound : LicensedSound E) (hwit : ObjectWitnessed E)
    (post : E.Answer → X → ℝ) (s : E.State) (o₀ : E.Object)
    (hecho : EchoAt E s)
    (μ : Fin 1 → ℝ) (ν : Fin 1 → E.Object → ℝ)
    (hν1 : ∀ w, ∑ c, ν w c = 1) :
    deficit μ ν (channelConditional E post s) = 0
      ∧ ¬ ∃ r, E.licensedEmits s r ∧ E.nonnull r :=
  ⟨echo_forces_zero_deficit post s o₀ hecho μ ν hν1,
    no_licensed_nonnull_at_echo hsound hwit hecho⟩

/-- **The quantitative diagnosis.** A raw non-null emission at a zero-gain state
is false formal legitimacy, and the deficit witnesses the vacuum that makes it
unwarranted. -/
theorem zero_deficit_raw_emission_is_false_formal_legitimacy
    (hsound : LicensedSound E) (hwit : ObjectWitnessed E)
    (post : E.Answer → X → ℝ) (s : E.State) (o₀ : E.Object)
    (hecho : EchoAt E s)
    (μ : Fin 1 → ℝ) (ν : Fin 1 → E.Object → ℝ)
    (hν1 : ∀ w, ∑ c, ν w c = 1)
    (hraw : ∃ r, E.rawEmits s r ∧ E.nonnull r) :
    deficit μ ν (channelConditional E post s) = 0
      ∧ FalseFormalLegitimacyAt E s :=
  ⟨echo_forces_zero_deficit post s o₀ hecho μ ν hν1,
    ffl_of_raw_nonnull_at_echo hsound hwit hecho hraw⟩

end OperatorKO7.Meta.BoundaryGeneral.EchoDeficitBridge
