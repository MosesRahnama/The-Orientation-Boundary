import OperatorKO7.Meta.OperationalInexpressibility.DirectGrammarBoundary
import OperatorKO7.Meta.BoundaryGeneral.OverproductionGapRoleExchangeGeneral
import OperatorKO7.Meta.Methods.OrientationClosure.ObserverSufficiency
import OperatorKO7.Meta.Methods.OrientationClosure.SourceChainSoundness

/-!
# Confession and distinction as one license event

One theorem collects the parts of a single event on the free recursor. The counter projection
orients the duplicating step and no grammar measure that reads the payload does (operational
inexpressibility, direct-grammar boundary). The dependency-pair evidence at duplication arity `r` is
the deterministic role channel, whose deficit is the binary entropy of the active share, and at
`r = 1` the channel is the two-role resolving channel of the one-bit exchange. The observers that
license a rank of the free recursive calls are exactly those refining the kernel of the call
counter (P3.3), and the call counter drops on every recursive call.

The relation between the channel statements is an equality of channels (`raryDP_evidence_eq_dpChannel`,
`dpChannel_one_eq_roleResolving_two`); between observers it is refinement of one kernel, so every
observer refining the counter kernel licenses the same rank.
-/

set_option autoImplicit false

namespace OperatorKO7.Methods.OrientationClosure.LicenseEvent

open OperatorKO7.Meta.OperationalInexpressibility
open OperatorKO7.Meta.BoundaryGeneral
open OperatorKO7.Methods.OrientationClosure
open OperatorKO7.Methods.OrientationClosure.SchemaCore

/-- The confession and distinction license event on the free recursor. -/
theorem confession_distinction_license_event :
    (type_of% @DirectGrammarBoundary.counter_adequateForDupOrientation) ∧
      (type_of% @DirectGrammarBoundary.no_directGrammar_measure_usesPayload_and_orients) ∧
      (type_of% @OverproductionGapRoleExchangeGeneral.raryDP_evidence_eq_dpChannel) ∧
      (type_of% @OverproductionGapRoleExchangeGeneral.dpChannel_deficitBits_eq_activeShareEntropy) ∧
      (type_of% @OverproductionGapRoleExchangeGeneral.dpChannel_one_eq_roleResolving_two) ∧
      (type_of% @OverproductionGapRoleExchangeGeneral.rary_one_frame_eq_one_bit_exchange) ∧
      (type_of% fun q : FreeTerm Nat → Nat => ObserverSufficiency.freeCall_sufficient_observers Nat q) ∧
      (type_of% (@SourceChainSoundness.freeRecursiveCallPair_rank_decreases Nat)) :=
  ⟨DirectGrammarBoundary.counter_adequateForDupOrientation,
    DirectGrammarBoundary.no_directGrammar_measure_usesPayload_and_orients,
    OverproductionGapRoleExchangeGeneral.raryDP_evidence_eq_dpChannel,
    OverproductionGapRoleExchangeGeneral.dpChannel_deficitBits_eq_activeShareEntropy,
    OverproductionGapRoleExchangeGeneral.dpChannel_one_eq_roleResolving_two,
    OverproductionGapRoleExchangeGeneral.rary_one_frame_eq_one_bit_exchange,
    fun q => ObserverSufficiency.freeCall_sufficient_observers Nat q,
    @SourceChainSoundness.freeRecursiveCallPair_rank_decreases Nat⟩

end OperatorKO7.Methods.OrientationClosure.LicenseEvent
