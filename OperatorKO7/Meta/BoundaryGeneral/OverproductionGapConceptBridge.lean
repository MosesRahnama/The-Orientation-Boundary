import OperatorKO7.Meta.BoundaryGeneral.OverproductionGap

/-!
# Concept-level bridges for the overproduction gap

Two cross-concept equivalences stated between named `Prop`-valued predicates, so
the relation layer can read them off the elaborated types:

* `gapBelowEnvelope_iff_licensedGain` joins the gap to the licensed-channel
  deficit of Informational Incompleteness, unconditionally.
* `boundaryEvent_iff_branchingAt` joins the boundary event to strict terminal
  branching of the distinction/quantitative layer, on any zero-gain channel.

Each predicate lives in the namespace of the surface it describes.

Trust: kernel-only. No `sorry`/`admit`/`axiom`/`native_decide`.
-/

set_option autoImplicit false

universe u

/-! ## Distinction/quantitative vocabulary -/

namespace OperatorKO7.Meta.DistinctionBoundary.Quantitative

/-- **Strict terminal branching**: at least two reachable normal forms below the
source. The positive form of non-confluence used by the quantitative layer. -/
def BranchingAt {T : Type u} [Fintype T] (R : T → T → Prop) (source : T) : Prop :=
  2 ≤ terminalMultiplicity R source

/-- Under local normalization, strict branching is exactly the failure of source
confluence. -/
theorem branchingAt_iff_not_confluentAt {T : Type u} [Fintype T]
    {R : T → T → Prop} {source : T} (hnorm : NormalizingAt R source) :
    BranchingAt R source ↔ ¬ ConfluentAt R source := by
  unfold BranchingAt
  rw [confluentAt_iff_terminalMultiplicity_eq_one hnorm]
  have hpos : 0 < terminalMultiplicity R source :=
    terminalMultiplicity_pos_of_normalizingAt hnorm
  omega

end OperatorKO7.Meta.DistinctionBoundary.Quantitative

/-! ## Informational-incompleteness vocabulary -/

namespace OperatorKO7.Meta.InformationalIncompleteness.LicensedChannelDeficit

/-- **Licensed gain**: the audited channel supplies strictly more target
information than the querant's direct surface already fixes. -/
def LicensedGain {X W Cn : Type} [Fintype X] [Fintype W] [Fintype Cn]
    (μ : W → ℝ) (ν : W → Cn → ℝ) (r : W → Cn → X → ℝ) : Prop :=
  0 < deficit μ ν r

end OperatorKO7.Meta.InformationalIncompleteness.LicensedChannelDeficit

/-! ## The bridges -/

namespace OperatorKO7.Meta.BoundaryGeneral.OverproductionGap

open OperatorKO7.Meta.InformationalIncompleteness.LicensedChannelDeficit
open OperatorKO7.Meta.DistinctionBoundary.Quantitative

/-- The gap sits strictly below the emitted terminal envelope: some emitted
branch structure is actually licensed. -/
def GapBelowEnvelope {T : Type u} [Fintype T] (R : T → T → Prop) (source : T)
    {X W Cn : Type} [Fintype X] [Fintype W] [Fintype Cn]
    (μ : W → ℝ) (ν : W → Cn → ℝ) (r : W → Cn → X → ℝ) : Prop :=
  overproductionGap R source μ ν r < terminalHartleyEntropy R source

/-- **Bridge to Informational Incompleteness.** The gap drops strictly below the
emitted envelope exactly when the licensed channel strictly gains over the
direct surface. Unconditional: it is the sign bridge between the two surfaces. -/
theorem gapBelowEnvelope_iff_licensedGain {T : Type u} [Fintype T]
    (R : T → T → Prop) (source : T)
    {X W Cn : Type} [Fintype X] [Fintype W] [Fintype Cn]
    (μ : W → ℝ) (ν : W → Cn → ℝ) (r : W → Cn → X → ℝ) :
    GapBelowEnvelope R source μ ν r ↔ LicensedGain μ ν r := by
  unfold GapBelowEnvelope overproductionGap deficitBits LicensedGain
  rw [sub_lt_self_iff]
  constructor
  · intro h
    rcases div_pos_iff.mp h with ⟨hd, _⟩ | ⟨_, hlog⟩
    · exact hd
    · exact absurd hlog (not_lt.mpr (le_of_lt log_two_pos))
  · intro h
    exact div_pos h log_two_pos

/-- **Bridge to the distinction boundary.** On any zero-gain channel, the
boundary event is exactly strict terminal branching: the gap detects the
two-terminal fork and nothing else. -/
theorem boundaryEvent_iff_branchingAt {T : Type u} [Fintype T]
    (R : T → T → Prop) (source : T)
    {X W Cn : Type} [Fintype X] [Fintype W] [Fintype Cn]
    (μ : W → ℝ) (ν : W → Cn → ℝ) (r : W → Cn → X → ℝ)
    (hd : deficit μ ν r = 0) :
    BoundaryEvent R source μ ν r ↔ BranchingAt R source := by
  unfold BoundaryEvent BranchingAt
  rw [overproductionGap_eq_hartley_of_zero_deficit R source μ ν r hd]
  unfold terminalHartleyEntropy
  constructor
  · intro h
    by_cases hm : terminalMultiplicity R source = 0
    · rw [hm] at h
      norm_num at h
    · have hpos : (0 : ℝ) < (terminalMultiplicity R source : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hm
      have h1 : (1 : ℝ) < (terminalMultiplicity R source : ℝ) :=
        (Real.logb_pos_iff (by norm_num) hpos).mp h
      have h1n : 1 < terminalMultiplicity R source := by exact_mod_cast h1
      omega
  · intro h
    refine Real.logb_pos (by norm_num) ?_
    have h2 : (2 : ℝ) ≤ (terminalMultiplicity R source : ℝ) := by exact_mod_cast h
    linarith

/-- The two bridges in one receipt: the gap's strict-drop face is the licensed
gain of Informational Incompleteness, and its boundary-event face on zero-gain
channels is the strict branching of the distinction layer. -/
theorem omega_concept_bridge_law :
    (∀ {T : Type u} [Fintype T] (R : T → T → Prop) (source : T)
      {X W Cn : Type} [Fintype X] [Fintype W] [Fintype Cn]
      (μ : W → ℝ) (ν : W → Cn → ℝ) (r : W → Cn → X → ℝ),
      (GapBelowEnvelope R source μ ν r ↔ LicensedGain μ ν r)) ∧
    (∀ {T : Type u} [Fintype T] (R : T → T → Prop) (source : T)
      {X W Cn : Type} [Fintype X] [Fintype W] [Fintype Cn]
      (μ : W → ℝ) (ν : W → Cn → ℝ) (r : W → Cn → X → ℝ),
      deficit μ ν r = 0 →
      (BoundaryEvent R source μ ν r ↔ BranchingAt R source)) :=
  by
  constructor
  · intro T _ R source X W Cn _ _ _ μ ν r
    exact gapBelowEnvelope_iff_licensedGain R source μ ν r
  · intro T _ R source X W Cn _ _ _ μ ν r hd
    exact boundaryEvent_iff_branchingAt R source μ ν r hd

end OperatorKO7.Meta.BoundaryGeneral.OverproductionGap
