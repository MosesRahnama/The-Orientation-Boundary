import OperatorKO7.Meta.BoundaryGeneral.EchoDeficitBridge
import OperatorKO7.Meta.DistinctionBoundary.MinimalForkQuantitative

/-!
# Evidence-structure overproduction gap

`terminalHartleyEntropy` measures terminal multiplicity in bits. `deficit` measures licensed conditional information in nats; `deficitBits` converts it to bits. `overproductionGap` subtracts licensed bits from terminal bits, and a boundary event means a positive gap.

Zero deficit leaves the full terminal entropy in the gap. For finite carriers and normalized object laws, an echo state gives a gap equal to terminal Hartley entropy. Two or more reachable terminals with zero deficit produce a positive gap. A source-confluent, locally normalizing finite relation raises no boundary event when channel gain is nonnegative.

For `Fork3`, the raw relation with echo evidence has a one-bit gap; the licensed relation has zero gap. The same raw relation has zero gap with resolving evidence. Two terminals alone do not determine the boundary verdict; the verdict depends on the channel.

Scope: caller-supplied finite relations and finite classical conditional information. The result does not assert physical cost or a Landauer bound. `Fork3` is a separate carrier; transport to the KO7 local cone is stated separately.
Trust: kernel-only; no `sorry`, `admit`, `axiom`, or `native_decide` occurs in this module.
-/

set_option autoImplicit false

open scoped BigOperators

namespace OperatorKO7.Meta.BoundaryGeneral.OverproductionGap

open OperatorKO7.Meta.InformationalIncompleteness.ShannonFinite
open OperatorKO7.Meta.InformationalIncompleteness.LicensedChannelDeficit
open OperatorKO7.Meta.DistinctionBoundary.Quantitative
open OperatorKO7.Meta.DistinctionBoundary.MinimalFork
open OperatorKO7.Meta.BoundaryGeneral.EchoLaw
open OperatorKO7.Meta.BoundaryGeneral.EchoDeficitBridge

universe u

noncomputable section

/-! ## Unit reconciliation -/

/-- `Real.log 2` is positive, so it is a legal divisor for the nat-to-bit
conversion. -/
theorem log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

/-- `Real.log 2` is nonzero. -/
theorem log_two_ne_zero : Real.log 2 ≠ 0 := ne_of_gt log_two_pos

/-- The licensed-channel deficit expressed in **bits**. `deficit` is built on
`Real.negMulLog`, hence natural-log units; `terminalHartleyEntropy` is
`Real.logb 2`, hence bits. This is the conversion that makes the two
commensurable. -/
def deficitBits {X W Cn : Type} [Fintype X] [Fintype W] [Fintype Cn]
    (μ : W → ℝ) (ν : W → Cn → ℝ) (r : W → Cn → X → ℝ) : Real :=
  deficit μ ν r / Real.log 2

/-- Conversion preserves the vacuum: zero gain in nats is zero gain in bits. -/
theorem deficitBits_eq_zero_iff {X W Cn : Type} [Fintype X] [Fintype W] [Fintype Cn]
    (μ : W → ℝ) (ν : W → Cn → ℝ) (r : W → Cn → X → ℝ) :
    deficitBits μ ν r = 0 ↔ deficit μ ν r = 0 := by
  unfold deficitBits
  rw [div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · exact h
    · exact absurd h log_two_ne_zero
  · intro h; exact Or.inl h

/-- Conversion preserves sign. -/
theorem deficitBits_nonneg_of_nonneg {X W Cn : Type} [Fintype X] [Fintype W] [Fintype Cn]
    (μ : W → ℝ) (ν : W → Cn → ℝ) (r : W → Cn → X → ℝ)
    (h : 0 ≤ deficit μ ν r) : 0 ≤ deficitBits μ ν r :=
  div_nonneg h (le_of_lt log_two_pos)

/-! ## The gap and the boundary event -/

/-- **The evidence-structure overproduction gap.** Emitted terminal branch
entropy minus licensed information gain, both in bits. -/
def overproductionGap {T : Type u} [Fintype T] (R : T → T → Prop) (source : T)
    {X W Cn : Type} [Fintype X] [Fintype W] [Fintype Cn]
    (μ : W → ℝ) (ν : W → Cn → ℝ) (r : W → Cn → X → ℝ) : Real :=
  terminalHartleyEntropy R source - deficitBits μ ν r

/-- **A boundary event**: the dynamics emit strictly more terminal branch
structure than the licensed channel supplies. -/
def BoundaryEvent {T : Type u} [Fintype T] (R : T → T → Prop) (source : T)
    {X W Cn : Type} [Fintype X] [Fintype W] [Fintype Cn]
    (μ : W → ℝ) (ν : W → Cn → ℝ) (r : W → Cn → X → ℝ) : Prop :=
  0 < overproductionGap R source μ ν r

/-- A zero-gain channel licenses none of the emitted branch entropy, so the gap
is the whole emitted entropy. -/
theorem overproductionGap_eq_hartley_of_zero_deficit
    {T : Type u} [Fintype T] (R : T → T → Prop) (source : T)
    {X W Cn : Type} [Fintype X] [Fintype W] [Fintype Cn]
    (μ : W → ℝ) (ν : W → Cn → ℝ) (r : W → Cn → X → ℝ)
    (hd : deficit μ ν r = 0) :
    overproductionGap R source μ ν r = terminalHartleyEntropy R source := by
  unfold overproductionGap
  rw [(deficitBits_eq_zero_iff μ ν r).mpr hd, sub_zero]

/-- **The general law.** A channel whose target conditional does not depend on
the channel cell (the answer is a redundant copy of the direct surface) leaves
the gap equal to `Real.logb 2` of the terminal multiplicity. -/
theorem echo_multiplicity_forces_gap
    {T : Type u} [Fintype T] (R : T → T → Prop) (source : T)
    {X W Cn : Type} [Fintype X] [Fintype W] [Fintype Cn]
    (μ : W → ℝ) (ν : W → Cn → ℝ) (r : W → Cn → X → ℝ)
    (hν1 : ∀ w, ∑ c, ν w c = 1)
    (s : W → X → ℝ) (hconst : ∀ w c, r w c = s w)
    (m : Nat) (hm : terminalMultiplicity R source = m) :
    overproductionGap R source μ ν r = Real.logb 2 (m : Real) := by
  rw [overproductionGap_eq_hartley_of_zero_deficit R source μ ν r
    (circular_reference_zero_deficit μ ν r hν1 s hconst)]
  unfold terminalHartleyEntropy
  rw [hm]

/-- **The boundary-event law.** Two or more reachable terminals together with a
zero-gain channel is a boundary event. -/
theorem boundary_event_of_zero_deficit_of_two_terminals
    {T : Type u} [Fintype T] (R : T → T → Prop) (source : T)
    {X W Cn : Type} [Fintype X] [Fintype W] [Fintype Cn]
    (μ : W → ℝ) (ν : W → Cn → ℝ) (r : W → Cn → X → ℝ)
    (hd : deficit μ ν r = 0)
    (hmult : 2 ≤ terminalMultiplicity R source) :
    BoundaryEvent R source μ ν r := by
  unfold BoundaryEvent
  rw [overproductionGap_eq_hartley_of_zero_deficit R source μ ν r hd]
  unfold terminalHartleyEntropy
  refine Real.logb_pos (by norm_num) ?_
  have h2 : (2 : Real) ≤ (terminalMultiplicity R source : Real) := by
    exact_mod_cast hmult
  linarith

/-- **The negative direction.** A source-confluent, locally normalizing relation
raises no boundary event against any nonnegative-gain channel: it emits zero
branch entropy, so nothing is unlicensed. -/
theorem no_boundary_event_of_confluentAt
    {T : Type u} [Fintype T] {R : T → T → Prop} {source : T}
    {X W Cn : Type} [Fintype X] [Fintype W] [Fintype Cn]
    (μ : W → ℝ) (ν : W → Cn → ℝ) (r : W → Cn → X → ℝ)
    (hnorm : NormalizingAt R source) (hconf : ConfluentAt R source)
    (hd : 0 ≤ deficit μ ν r) :
    ¬ BoundaryEvent R source μ ν r := by
  unfold BoundaryEvent overproductionGap
  have hzero : terminalHartleyEntropy R source = 0 :=
    (terminalHartleyEntropy_eq_zero_iff_multiplicity_eq_one hnorm).mpr
      (terminalMultiplicity_eq_one_of_confluentAt hnorm hconf)
  have hbits : 0 ≤ deficitBits μ ν r := deficitBits_nonneg_of_nonneg μ ν r hd
  rw [hzero]
  intro hcontra
  linarith

/-! ## Finite unit and channel examples

The examples use one direct-surface cell, a binary channel, and a binary target. -/

/-- The single direct-surface cell, at full weight. -/
def unitSurface : Fin 1 → Real := fun _ => 1

/-- Uniform weights on the binary channel. -/
def uniformChannelWeights : Fin 1 → Fin 2 → Real := fun _ _ => (1 : Real) / 2

/-- Uniform weights sum to one. -/
theorem uniformChannelWeights_sum_one : ∀ w, ∑ c, uniformChannelWeights w c = 1 := by
  intro w
  unfold uniformChannelWeights
  rw [Fin.sum_univ_two]
  norm_num

/-- **The echo channel.** The target conditional is the same in every channel
cell: the answer is a redundant copy of what the direct surface already fixes. -/
def echoChannel : Fin 1 → Fin 2 → Fin 2 → Real := fun _ _ _ => (1 : Real) / 2

/-- **The resolving channel.** Each channel cell determines the target exactly. -/
def resolvingChannel : Fin 1 → Fin 2 → Fin 2 → Real := fun _ c => pointMass c

/-- The echo channel has zero licensed gain. -/
theorem echoChannel_deficit_zero :
    deficit unitSurface uniformChannelWeights echoChannel = 0 :=
  circular_reference_zero_deficit _ _ _ uniformChannelWeights_sum_one
    (fun _ _ => (1 : Real) / 2) (fun _ _ => rfl)

/-- The echo channel has zero licensed gain in bits. -/
theorem echoChannel_deficitBits_zero :
    deficitBits unitSurface uniformChannelWeights echoChannel = 0 :=
  (deficitBits_eq_zero_iff _ _ _).mpr echoChannel_deficit_zero

/-- The uniform binary entropy is `Real.log 2` **nats**. -/
theorem H_uniform_two_eq_log_two : H (fun _ : Fin 2 => (1 : Real) / 2) = Real.log 2 := by
  unfold H
  rw [Fin.sum_univ_two]
  unfold Real.negMulLog
  have hinv : (1 : Real) / 2 = (2 : Real)⁻¹ := by norm_num
  rw [hinv, Real.log_inv]
  ring

/-- The direct conditional entropy of the resolving channel is `Real.log 2`. -/
theorem resolvingChannel_condEntropyDirect_eq_log_two :
    condEntropyDirect unitSurface uniformChannelWeights resolvingChannel = Real.log 2 := by
  unfold condEntropyDirect unitSurface uniformChannelWeights resolvingChannel
  rw [Fin.sum_univ_one, one_mul]
  rw [← H_uniform_two_eq_log_two]
  congr 1
  funext x
  fin_cases x <;> simp [pointMass]

/-- For the resolving binary channel, the raw deficit is `Real.log 2` nats while `deficitBits` is one bit. Subtracting raw deficit from bit-valued Hartley entropy mixes units. -/
theorem resolvingChannel_deficit_eq_log_two :
    deficit unitSurface uniformChannelWeights resolvingChannel = Real.log 2 := by
  have hres : ∀ (w : Fin 1) (c : Fin 2), H (resolvingChannel w c) = 0 :=
    fun _ c => H_pointMass c
  rw [deficit_eq_condEntropyDirect_of_zero_residual
    unitSurface uniformChannelWeights resolvingChannel hres]
  exact resolvingChannel_condEntropyDirect_eq_log_two

/-- The resolving channel supplies exactly one bit. -/
theorem resolvingChannel_deficitBits_eq_one :
    deficitBits unitSurface uniformChannelWeights resolvingChannel = 1 := by
  unfold deficitBits
  rw [resolvingChannel_deficit_eq_log_two]
  exact div_self log_two_ne_zero

/-- The raw deficit and its bit value differ, so the two surfaces are genuinely
in different units. -/
theorem resolvingChannel_deficit_ne_deficitBits :
    deficit unitSurface uniformChannelWeights resolvingChannel
      ≠ deficitBits unitSurface uniformChannelWeights resolvingChannel := by
  rw [resolvingChannel_deficit_eq_log_two, resolvingChannel_deficitBits_eq_one]
  have h : Real.log 2 < 1 := by
    have hb := Real.log_lt_sub_one_of_pos (by norm_num : (0 : Real) < 2)
      (by norm_num : (2 : Real) ≠ 1)
    linarith
  exact ne_of_lt h

/-! ## Fork3 example -/

/-- **The raw fork overproduces exactly one bit against an echo channel.** -/
theorem fork3_raw_overproduction_eq_one :
    overproductionGap Fork3Step Fork3.source unitSurface uniformChannelWeights echoChannel = 1 := by
  unfold overproductionGap
  rw [echoChannel_deficitBits_zero, sub_zero]
  exact fork3_raw_terminalHartleyEntropy_eq_one

/-- **The licensed fork overproduces nothing.** -/
theorem fork3_licensed_overproduction_eq_zero :
    overproductionGap Fork3LicensedStep Fork3.source unitSurface uniformChannelWeights
      echoChannel = 0 := by
  unfold overproductionGap
  rw [echoChannel_deficitBits_zero, sub_zero]
  exact fork3_licensed_terminalHartleyEntropy_eq_zero

/-- The licensed repair removes exactly the unlicensed bit. -/
theorem fork3_overproduction_drop_eq_one :
    overproductionGap Fork3Step Fork3.source unitSurface uniformChannelWeights echoChannel
      - overproductionGap Fork3LicensedStep Fork3.source unitSurface uniformChannelWeights
          echoChannel = 1 := by
  rw [fork3_raw_overproduction_eq_one, fork3_licensed_overproduction_eq_zero, sub_zero]

/-- The raw fork against an echo channel is a boundary event. -/
theorem fork3_raw_boundary_event :
    BoundaryEvent Fork3Step Fork3.source unitSurface uniformChannelWeights echoChannel := by
  unfold BoundaryEvent
  rw [fork3_raw_overproduction_eq_one]
  norm_num

/-- Two reachable terminals do not guarantee a positive gap. The raw `Fork3` relation has gap zero under resolving evidence; the gap measures terminal information minus licensed information, not confluence. -/
theorem fork3_raw_gap_closed_by_resolving_channel :
    overproductionGap Fork3Step Fork3.source unitSurface uniformChannelWeights
      resolvingChannel = 0 := by
  unfold overproductionGap
  rw [fork3_raw_terminalHartleyEntropy_eq_one, resolvingChannel_deficitBits_eq_one, sub_self]

/-- The same relation, two channels, two verdicts. -/
theorem fork3_raw_not_boundary_event_under_resolving_channel :
    ¬ BoundaryEvent Fork3Step Fork3.source unitSurface uniformChannelWeights
      resolvingChannel := by
  unfold BoundaryEvent
  rw [fork3_raw_gap_closed_by_resolving_channel]
  exact lt_irrefl 0

/-! ## Echo-state result -/

/-- For finite episode carriers, normalized object laws, and an echo state, a target conditional derived from the answer gives a gap equal to terminal Hartley entropy for any finite relation. -/
theorem echoAt_forces_gap_eq_hartley
    {E : Episode} {X : Type} [Fintype X] [Fintype E.Object]
    (post : E.Answer → X → Real) (s : E.State) (o₀ : E.Object)
    (hecho : EchoAt E s)
    (μ : Fin 1 → Real) (ν : Fin 1 → E.Object → Real)
    (hν1 : ∀ w, ∑ c, ν w c = 1)
    {T : Type u} [Fintype T] (R : T → T → Prop) (source : T) :
    overproductionGap R source μ ν (channelConditional E post s)
      = terminalHartleyEntropy R source :=
  overproductionGap_eq_hartley_of_zero_deficit R source μ ν _
    (echo_forces_zero_deficit post s o₀ hecho μ ν hν1)

/-- With finite carriers and normalized object laws, an echo state gives a boundary event for any relation with at least two reachable terminals. -/
theorem echoAt_boundary_event_of_two_terminals
    {E : Episode} {X : Type} [Fintype X] [Fintype E.Object]
    (post : E.Answer → X → Real) (s : E.State) (o₀ : E.Object)
    (hecho : EchoAt E s)
    (μ : Fin 1 → Real) (ν : Fin 1 → E.Object → Real)
    (hν1 : ∀ w, ∑ c, ν w c = 1)
    {T : Type u} [Fintype T] (R : T → T → Prop) (source : T)
    (hmult : 2 ≤ terminalMultiplicity R source) :
    BoundaryEvent R source μ ν (channelConditional E post s) :=
  boundary_event_of_zero_deficit_of_two_terminals R source μ ν _
    (echo_forces_zero_deficit post s o₀ hecho μ ν hν1) hmult

/-! ## Combined result -/

/-- The combined result gives zero deficit for echo evidence and one-bit deficit for resolving evidence. Raw `Fork3` with echo evidence has gap one and a boundary event; the licensed relation has gap zero; raw `Fork3` with resolving evidence has gap zero and no boundary event. -/
theorem overproduction_gap_law :
    deficitBits unitSurface uniformChannelWeights echoChannel = 0 ∧
    deficitBits unitSurface uniformChannelWeights resolvingChannel = 1 ∧
    overproductionGap Fork3Step Fork3.source unitSurface uniformChannelWeights echoChannel = 1 ∧
    overproductionGap Fork3LicensedStep Fork3.source unitSurface uniformChannelWeights
      echoChannel = 0 ∧
    BoundaryEvent Fork3Step Fork3.source unitSurface uniformChannelWeights echoChannel ∧
    overproductionGap Fork3Step Fork3.source unitSurface uniformChannelWeights
      resolvingChannel = 0 ∧
    ¬ BoundaryEvent Fork3Step Fork3.source unitSurface uniformChannelWeights resolvingChannel :=
  ⟨echoChannel_deficitBits_zero,
    resolvingChannel_deficitBits_eq_one,
    fork3_raw_overproduction_eq_one,
    fork3_licensed_overproduction_eq_zero,
    fork3_raw_boundary_event,
    fork3_raw_gap_closed_by_resolving_channel,
    fork3_raw_not_boundary_event_under_resolving_channel⟩

end

end OperatorKO7.Meta.BoundaryGeneral.OverproductionGap
