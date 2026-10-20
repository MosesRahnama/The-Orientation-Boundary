import OperatorKO7.Meta.BoundaryGeneral.EchoLaw
import OperatorKO7.Meta.InformationalIncompleteness.LicensedChannelDeficit

/-!
# Echo and licensed-channel deficit

`EchoLaw` means that the answer at a state is independent of the object. `LicensedChannelDeficit` measures conditional information the licensed channel provides about the target. Under `ChannelSufficient`, the target conditional depends on the object only through the answer, and `echo_forces_zero_deficit` proves the deficit is zero. The reference object `o₀` remains an explicit parameter.

The implication from positive deficit is one-way: `positive_deficit_forces_informative_channel` proves that a positive deficit requires a channel that reads the object. Zero deficit alone does not imply echo, because answer variation on zero-weight cells can leave the deficit zero. Under `LicensedSound` and `ObjectWitnessed`, an echo state also has no licensed non-null record.

Trust: Mathlib baseline; no `sorry`, `admit`, `axiom`, or `native_decide` occurs in this module.
-/

set_option autoImplicit false

open scoped BigOperators

namespace OperatorKO7.Meta.BoundaryGeneral.EchoDeficitBridge

open OperatorKO7.Meta.BoundaryGeneral.EchoLaw
open OperatorKO7.Meta.InformationalIncompleteness.LicensedChannelDeficit

variable {E : Episode} {X : Type} [Fintype X] [Fintype E.Object]

/-- The target conditional uses the posterior associated with the answer at each object. The direct surface has one cell indexed by `Fin 1`. -/
noncomputable def channelConditional
    (E : Episode) {X : Type} (post : E.Answer → X → ℝ) (s : E.State) :
    Fin 1 → E.Object → X → ℝ :=
  fun _ o x => post (E.answer s o) x

/-- The target conditional is determined by the answer at each object. -/
def ChannelSufficient
    (E : Episode) {X : Type} (post : E.Answer → X → ℝ) (s : E.State)
    (r : Fin 1 → E.Object → X → ℝ) : Prop :=
  r = channelConditional E post s

/-- For normalized object laws, an echo at `s` gives zero deficit for the target conditional induced by the posterior map. -/
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

/-- A positive deficit at `s` implies that the channel reads the object. The unrestricted converse fails because zero deficit can tolerate answer variation on zero-weight cells. -/
theorem positive_deficit_forces_informative_channel
    (post : E.Answer → X → ℝ) (s : E.State) (o₀ : E.Object)
    (μ : Fin 1 → ℝ) (ν : Fin 1 → E.Object → ℝ)
    (hν1 : ∀ w, ∑ c, ν w c = 1)
    (hd : deficit μ ν (channelConditional E post s) ≠ 0) :
    InformativeAt E s := by
  refine Classical.byContradiction (fun hni => ?_)
  exact hd (echo_forces_zero_deficit post s o₀
    ((echoAt_iff_not_informativeAt E s).mpr hni) μ ν hν1)

/-- Under `LicensedSound E` and `ObjectWitnessed E`, an echo at `s` gives zero deficit for normalized object laws and excludes licensed non-null records at `s`. -/
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

/-- Under `LicensedSound E` and `ObjectWitnessed E`, a raw non-null emission at an echo state yields `FalseFormalLegitimacyAt`; normalized target laws have zero deficit. -/
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
