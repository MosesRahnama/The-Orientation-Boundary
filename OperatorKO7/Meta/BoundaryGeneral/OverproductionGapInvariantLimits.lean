import OperatorKO7.Meta.BoundaryGeneral.OverproductionGapOrder
import OperatorKO7.Meta.BoundaryGeneral.OverproductionGapTransport

/-!
# Limits of Omega as an invariant

Exact coupled transport preserves Omega, but equality of Omega, even together
with equal terminal multiplicity, does not reconstruct the operational carrier.
-/
set_option autoImplicit false

namespace OperatorKO7.Meta.BoundaryGeneral.OverproductionGapInvariantLimits

open OperatorKO7.Meta.BoundaryGeneral.OverproductionGap
open OperatorKO7.Meta.BoundaryGeneral.OverproductionGapOrder
open OperatorKO7.Meta.DistinctionBoundary.Quantitative
open OperatorKO7.Meta.DistinctionBoundary.MinimalFork

inductive LongChainNode where
  | source
  | mid
  | terminal
  deriving DecidableEq, Fintype

inductive LongChainStep : LongChainNode → LongChainNode → Prop where
  | first : LongChainStep .source .mid
  | second : LongChainStep .mid .terminal

theorem longChain_terminal_normal :
    OperatorKO7.Meta.DistinctionBoundary.Quantitative.NormalForm
      LongChainStep .terminal := by
  intro y h
  cases h

theorem longChain_terminalSupport_eq :
    terminalSupport LongChainStep .source = {.terminal} := by
  classical
  ext x
  cases x with
  | source =>
      constructor
      · intro hx
        exact False.elim ((mem_terminalSupport.mp hx).2 .mid LongChainStep.first)
      · simp
  | mid =>
      constructor
      · intro hx
        exact False.elim ((mem_terminalSupport.mp hx).2 .terminal LongChainStep.second)
      · simp
  | terminal =>
      constructor
      · intro _; simp
      · intro _
        exact mem_terminalSupport.mpr
          ⟨reach_trans (reach_step LongChainStep.first) (reach_step LongChainStep.second),
            longChain_terminal_normal⟩

theorem longChain_terminalMultiplicity_eq_one :
    terminalMultiplicity LongChainStep .source = 1 := by
  simp [terminalMultiplicity, longChain_terminalSupport_eq]

theorem longChain_echo_omega_eq_zero :
    overproductionGap LongChainStep .source
      unitSurface uniformChannelWeights echoChannel = 0 := by
  unfold overproductionGap terminalHartleyEntropy
  rw [echoChannel_deficitBits_zero, sub_zero, longChain_terminalMultiplicity_eq_one]
  simp [Real.logb]

theorem shortChain_echo_omega_eq_zero :
    overproductionGap ChainStep ChainNode.source
      unitSurface uniformChannelWeights echoChannel = 0 := by
  unfold overproductionGap
  rw [chain_terminalHartleyEntropy_eq_zero, echoChannel_deficitBits_zero]
  norm_num

theorem chainNode_card_eq_two : Fintype.card ChainNode = 2 := by decide

theorem longChainNode_card_eq_three : Fintype.card LongChainNode = 3 := by decide

/-- No relation isomorphism exists because the carriers have different
cardinality. -/
theorem no_relIso_shortChain_longChain :
    ¬ Nonempty (OperatorKO7.Meta.DistinctionBoundary.MinimalFork.RelIso ChainStep LongChainStep) := by
  rintro ⟨I⟩
  have hcard : Fintype.card ChainNode = Fintype.card LongChainNode :=
    Fintype.card_congr I.toEquiv
  rw [chainNode_card_eq_two, longChainNode_card_eq_three] at hcard
  norm_num at hcard

/-- Equal Omega and equal terminal multiplicity still do not determine the
relation up to isomorphism. -/
theorem omega_and_terminalMultiplicity_not_complete_invariant :
    overproductionGap ChainStep ChainNode.source
        unitSurface uniformChannelWeights echoChannel =
      overproductionGap LongChainStep LongChainNode.source
        unitSurface uniformChannelWeights echoChannel ∧
    terminalMultiplicity ChainStep ChainNode.source =
      terminalMultiplicity LongChainStep LongChainNode.source ∧
    ¬ Nonempty (OperatorKO7.Meta.DistinctionBoundary.MinimalFork.RelIso ChainStep LongChainStep) := by
  rw [shortChain_echo_omega_eq_zero, longChain_echo_omega_eq_zero,
    chain_terminalMultiplicity_eq_one, longChain_terminalMultiplicity_eq_one]
  exact ⟨rfl, rfl, no_relIso_shortChain_longChain⟩

/-- **W26 compiled kill.** Same zero Omega and same singleton terminal support
do not imply a coupled operational isomorphism. -/
theorem omega_complete_invariant_conjecture_false :
    overproductionGap ChainStep ChainNode.source unitSurface uniformChannelWeights echoChannel = 0 ∧
    overproductionGap LongChainStep LongChainNode.source unitSurface uniformChannelWeights echoChannel = 0 ∧
    terminalMultiplicity ChainStep ChainNode.source = 1 ∧
    terminalMultiplicity LongChainStep LongChainNode.source = 1 ∧
    ¬ Nonempty (OperatorKO7.Meta.DistinctionBoundary.MinimalFork.RelIso ChainStep LongChainStep) :=
  ⟨shortChain_echo_omega_eq_zero, longChain_echo_omega_eq_zero,
    chain_terminalMultiplicity_eq_one, longChain_terminalMultiplicity_eq_one,
    no_relIso_shortChain_longChain⟩

end OperatorKO7.Meta.BoundaryGeneral.OverproductionGapInvariantLimits

