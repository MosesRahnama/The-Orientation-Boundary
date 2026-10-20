import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import OperatorKO7.Meta.HigherOrderRewriting_SystemTSyntax
import OperatorKO7.Meta.HigherOrderRewriting_TypeCostBoundary
import OperatorKO7.Meta.HigherOrderRewriting_ChannelCapacity
import OperatorKO7.Meta.OperationalInexpressibility.FiberDeficitCore
import OperatorKO7.Meta.OperationalInexpressibility.LiftOrRefuse
import OperatorKO7.Meta.OperationalInexpressibility.ConfusabilityGraph
import OperatorKO7.Meta.OperationalInexpressibility.LicenseCore

/-!
# L22 Church capacity count is the general least-lift law

`least_lift_eq_fiberMultiplicity` is the carrier-free law: the least licensing lift equals the
fiber multiplicity. This module evaluates that law on the Church prefix of System T. The
manuscript claim that the higher-order count is the general law on one fiber anchors here.

Relation: observer-fiber equality of `infer []` against `betaCost (n + 2)` on `Prefix n`.
Closure: the whole subtype carrier `Prefix n` (the first `n + 1` Church applications).
Strategy: leftmost-outermost cost through `betaCost`; least lift via `least_lift_eq_fiberMultiplicity`.
Trust: kernel-only; finite fixtures use `decide`.
Scope: the Church prefix subtype and finite `Fin k` side channels.
-/

set_option autoImplicit false

namespace OperatorKO7.HigherOrderRewritingCapacityLawWeld

open OperatorKO7.HigherOrderRewritingSystemT
open OperatorKO7.HigherOrderRewritingTypeCostBoundary
open OperatorKO7.HigherOrderRewritingChannelCapacity
open OperatorKO7.Meta.OperationalInexpressibility.LiftOrRefuse
open OperatorKO7.Meta.OperationalInexpressibility.FiberDeficit
open OperatorKO7.Meta.OperationalInexpressibility.Confusability
open OperatorKO7.Meta.OperationalInexpressibility.LicenseCriterion

/-! ## NameGate -/

#check @OperatorKO7.HigherOrderRewritingChannelCapacity.churchPrefix
#check @OperatorKO7.HigherOrderRewritingChannelCapacity.churchPrefix_card
#check @OperatorKO7.HigherOrderRewritingChannelCapacity.churchPrefix_typed
#check @OperatorKO7.HigherOrderRewritingChannelCapacity.ChannelLicenses
#check @OperatorKO7.HigherOrderRewritingChannelCapacity.capacity_lower_bound
#check @OperatorKO7.HigherOrderRewritingChannelCapacity.capacity_attained
#check @OperatorKO7.HigherOrderRewritingChannelCapacity.finIndexChannel
#check @OperatorKO7.HigherOrderRewritingChannelCapacity.least_channel_card
#check @OperatorKO7.HigherOrderRewritingChannelCapacity.isChurchApp?
#check @OperatorKO7.HigherOrderRewritingChannelCapacity.churchApp_injective
#check @OperatorKO7.Meta.OperationalInexpressibility.FiberDeficit.fiberVerdicts
#check @OperatorKO7.Meta.OperationalInexpressibility.FiberDeficit.fiberMultiplicity
#check @OperatorKO7.Meta.OperationalInexpressibility.FiberDeficit.additional_channel_card_lower_bound
#check @OperatorKO7.Meta.OperationalInexpressibility.FiberDeficit.exists_optimal_side_channel
#check @OperatorKO7.Meta.OperationalInexpressibility.LiftOrRefuse.LicensedOn
#check @OperatorKO7.Meta.OperationalInexpressibility.LiftOrRefuse.least_lift_eq_fiberMultiplicity
#check @OperatorKO7.Meta.OperationalInexpressibility.LiftOrRefuse.mixed_repair_iff
#check @OperatorKO7.Meta.OperationalInexpressibility.LiftOrRefuse.fiberMultiplicity_const
#check @OperatorKO7.Meta.OperationalInexpressibility.Confusability.augmentObserver
#check @OperatorKO7.Meta.OperationalInexpressibility.LicenseCriterion.Licensed
#check @OperatorKO7.HigherOrderRewritingTypeCostBoundary.betaCost_churchApp
#check @OperatorKO7.HigherOrderRewritingTypeCostBoundary.infer_churchApp
#check @Fintype.card
#check @Fintype.card_coe
#check @Finset.card_image_of_injective
#check @IsLeast

/--
Proves: `Prefix n` is the subtype of System T terms that belong to `churchPrefix n`.
Does not prove: that this subtype exhausts System T.
Relation: membership in `churchPrefix n`.
Closure: finite retained set.
Strategy: not applicable.
Trust: kernel-only.
Scope: every `n : Nat`.
-/
abbrev Prefix (n : Nat) := {t : SysTTerm // t ∈ churchPrefix n}

/--
Proves: `Prefix n` is a finite type, as a subtype of a `Finset`.
Does not prove: a cardinality formula.
Relation: not applicable.
Closure: finite subtype.
Strategy: not applicable.
Trust: kernel-only.
Scope: every `n : Nat`.
-/
instance instFintypePrefix (n : Nat) : Fintype (Prefix n) :=
  Finset.Subtype.fintype (churchPrefix n)

/--
Proves: `churchApp 0` belongs to every Church prefix, so `Prefix n` is inhabited.
Does not prove: a typing or cost fact.
Relation: membership in `churchPrefix n`.
Closure: finite image of `Finset.range (n + 1)`.
Strategy: not applicable.
Trust: kernel-only.
Scope: every `n : Nat`.
-/
theorem churchApp_mem_churchPrefix (n : Nat) : churchApp 0 ∈ churchPrefix n := by
  unfold churchPrefix
  exact Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ n), rfl⟩

/--
Proves: `Prefix n` is nonempty.
Does not prove: a cardinality formula.
Relation: not applicable.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: every `n : Nat`.
-/
instance instNonemptyPrefix (n : Nat) : Nonempty (Prefix n) :=
  ⟨⟨churchApp 0, churchApp_mem_churchPrefix n⟩⟩

/--
Proves: the Church-prefix subtype has exactly `n + 1` values.
Does not prove: a cardinality statement for any larger System T family.
Relation: equality of `Nat`.
Closure: finite subtype of a `Finset`.
Strategy: not applicable.
Trust: kernel-only.
Scope: every `n : Nat`.
-/
theorem prefix_card (n : Nat) : Fintype.card (Prefix n) = n + 1 := by
  rw [Fintype.card_coe, churchPrefix_card]

/--
Proves: the restricted type observer on `Prefix n` is empty-context inference.
Does not prove: completeness of `infer`.
Relation: `infer []`.
Closure: the subtype carrier `Prefix n`.
Strategy: not applicable.
Trust: kernel-only.
Scope: every member of `Prefix n`.
-/
def obs (n : Nat) : Prefix n → Option SysTTy :=
  fun t => infer [] t.1

/--
Proves: the restricted cost target on `Prefix n` is leftmost-outermost beta cost at fuel `n + 2`.
Does not prove: a cost fact outside the prefix, or under another strategy.
Relation: `betaCost (n + 2)`.
Closure: the subtype carrier `Prefix n`.
Strategy: leftmost-outermost.
Trust: kernel-only.
Scope: every member of `Prefix n`.
-/
def cost (n : Nat) : Prefix n → Option Nat :=
  fun t => betaCost (n + 2) t.1

/--
Proves: every prefix state is observed as `some nat`.
Does not prove: a cost fact, or typing of terms outside the prefix.
Relation: `infer []`.
Closure: the subtype carrier `Prefix n`.
Strategy: not applicable.
Trust: kernel-only.
Scope: every member of `Prefix n`.
-/
theorem obs_const (n : Nat) : ∀ t : Prefix n, obs n t = some .nat := by
  intro t
  exact churchPrefix_typed n t.1 t.2

/--
Proves: the restricted cost map is injective on `Prefix n`.
Does not prove: injectivity of `betaCost` on any larger family.
Relation: equality of `Option Nat`.
Closure: the subtype carrier `Prefix n`.
Strategy: leftmost-outermost cost through `betaCost_churchApp`.
Trust: kernel-only.
Scope: every `n : Nat`.
-/
theorem cost_injective (n : Nat) : Function.Injective (cost n) := by
  intro t u htu
  obtain ⟨m, hm, htm⟩ := Finset.mem_image.mp (show t.1 ∈ churchPrefix n from t.2)
  obtain ⟨k, hk, huk⟩ := Finset.mem_image.mp (show u.1 ∈ churchPrefix n from u.2)
  have hmFuel : m + 2 ≤ n + 2 := by
    have := Finset.mem_range.mp hm
    omega
  have hkFuel : k + 2 ≤ n + 2 := by
    have := Finset.mem_range.mp hk
    omega
  have htcost : cost n t = some (m + 2) := by
    unfold cost
    rw [← htm, betaCost_churchApp m (n + 2) hmFuel]
  have hucost : cost n u = some (k + 2) := by
    unfold cost
    rw [← huk, betaCost_churchApp k (n + 2) hkFuel]
  have hmk : m + 2 = k + 2 :=
    Option.some_injective _ (htcost.symm.trans (htu.trans hucost))
  have : m = k := Nat.add_right_cancel hmk
  apply Subtype.ext
  rw [← htm, ← huk, this]

/--
Proves: the fiber multiplicity of the restricted type observer and cost target is `n + 1`.
Does not prove: a multiplicity fact for any observer other than `obs n`, or any target other than `cost n`.
Relation: fiber multiplicity of `obs n` against `cost n`.
Closure: the subtype carrier `Prefix n`; one observer fiber holds every state.
Strategy: rewrite `obs n` to a constant by `funext` and apply `fiberMultiplicity_const`; injectivity of `cost n` gives the cardinality.
Trust: kernel-only.
Scope: every `n : Nat`.
-/
theorem church_fiberMultiplicity (n : Nat) :
    fiberMultiplicity (obs n) (cost n) = n + 1 := by
  have hobs : obs n = fun _ => some .nat := funext (obs_const n)
  rw [hobs, fiberMultiplicity_const (some SysTTy.nat) (cost n)]
  rw [Finset.card_image_of_injective _ (cost_injective n), Finset.card_univ, prefix_card]

/--
Proves: a side channel with `n + 1` symbols licenses cost on `Prefix n`, and every licensing
`Fin k` channel has `n + 1 ≤ k`.
Does not prove: a Shannon-entropy bound, or a fact about observers other than `obs n`.
Relation: `Licensed (augmentObserver (obs n) s) (cost n)`.
Closure: the whole subtype carrier `Prefix n`.
Strategy: `least_lift_eq_fiberMultiplicity` rewritten by `church_fiberMultiplicity`; no direct pigeonhole.
Trust: kernel-only.
Scope: every `n : Nat`, every finite `Fin k` side channel on `Prefix n`.
-/
theorem church_least_lift (n : Nat) :
    (∃ s : Prefix n → Fin (n + 1), Licensed (augmentObserver (obs n) s) (cost n)) ∧
      ∀ (k : Nat) (s : Prefix n → Fin k),
        Licensed (augmentObserver (obs n) s) (cost n) → n + 1 ≤ k := by
  have hlaw := least_lift_eq_fiberMultiplicity (obs n) (cost n)
  rwa [church_fiberMultiplicity] at hlaw

/--
Proves: the L21 predicate `ChannelLicenses n s` on the ambient carrier agrees with `Licensed` of
the restricted observer and cost on `Prefix n`.
Does not prove: licensing outside the prefix, or agreement for a different observer or cost.
Relation: `ChannelLicenses` versus `Licensed (augmentObserver (obs n) _) (cost n)`.
Closure: observer-fiber equality on `churchPrefix n` and on the subtype `Prefix n`.
Strategy: not applicable.
Trust: kernel-only.
Scope: every channel type `C`, every `n`, every `s : SysTTerm → C`.
-/
theorem channelLicenses_iff_licensed {C : Type} (n : Nat) (s : SysTTerm → C) :
    ChannelLicenses n s ↔
      Licensed (augmentObserver (obs n) (fun t => s t.1)) (cost n) := by
  constructor
  · intro h x y hxy
    have hobs :
        ((infer [] x.1, s x.1) : Option SysTTy × C) = (infer [] y.1, s y.1) := by
      simpa [augmentObserver, obs] using hxy
    have hcost :=
      h x.1 (Finset.mem_coe.mpr x.2) y.1 (Finset.mem_coe.mpr y.2) hobs
    simpa [cost] using hcost
  · intro h x hx y hy hxy
    have hx' : x ∈ churchPrefix n := Finset.mem_coe.mp hx
    have hy' : y ∈ churchPrefix n := Finset.mem_coe.mp hy
    have hxy' :
        augmentObserver (obs n) (fun t => s t.1) ⟨x, hx'⟩ =
          augmentObserver (obs n) (fun t => s t.1) ⟨y, hy'⟩ := by
      simpa [augmentObserver, obs] using hxy
    have hcost := h ⟨x, hx'⟩ ⟨y, hy'⟩ hxy'
    simpa [cost] using hcost

/--
Proves: `n + 1` is the least cardinality of a finite `Fin k` ambient channel licensing the prefix
cost, by transporting `church_least_lift` across `channelLicenses_iff_licensed`.
Does not prove: a result about entropy or non-finite channel types.
Relation: `ChannelLicenses n s`.
Closure: finite prefix and finite channel codomain.
Strategy: extend a subtype channel by `fun t => if h : t ∈ churchPrefix n then s ⟨t, h⟩ else ⟨0, _⟩`;
the converse restricts an ambient channel to `Prefix n`. Consumes `church_least_lift`, hence the
general least-lift law.
Trust: kernel-only.
Scope: every `n : Nat`.
-/
theorem least_channel_card_of_general_law (n : Nat) :
    IsLeast {k : Nat | ∃ s : SysTTerm → Fin k, ChannelLicenses n s} (n + 1) := by
  constructor
  · obtain ⟨s, hs⟩ := (church_least_lift n).1
    refine ⟨fun t => if h : t ∈ churchPrefix n then s ⟨t, h⟩ else ⟨0, Nat.zero_lt_succ n⟩, ?_⟩
    rw [channelLicenses_iff_licensed]
    have hrestrict :
        (fun t : Prefix n =>
          if h : t.1 ∈ churchPrefix n then s ⟨t.1, h⟩ else ⟨0, Nat.zero_lt_succ n⟩) = s := by
      funext t
      have ht : t.1 ∈ churchPrefix n := t.2
      simp [ht]
    simpa [hrestrict] using hs
  · intro k hk
    obtain ⟨s, hs⟩ := hk
    exact (church_least_lift n).2 k (fun t => s t.1)
      ((channelLicenses_iff_licensed n s).1 hs)

/--
Proves: the same `IsLeast` statement as L21's `least_channel_card`, obtained from the general law.
Does not prove: proof-term equality with `least_channel_card` (proof irrelevance makes that trivial).
Relation: `ChannelLicenses n s`.
Closure: finite prefix and finite channel codomain.
Strategy: alias of `least_channel_card_of_general_law`; L21 proved this statement directly.
Trust: kernel-only.
Scope: every `n : Nat`.
-/
theorem least_channel_card_general_eq_L21 (n : Nat) :
    IsLeast {k : Nat | ∃ s : SysTTerm → Fin k, ChannelLicenses n s} (n + 1) :=
  least_channel_card_of_general_law n

/--
Proves: the Church-prefix fiber multiplicity at `n = 4` is `5`.
Does not prove: the identity for a different prefix length except through `church_fiberMultiplicity`.
Relation: fiber multiplicity of `obs 4` against `cost 4`.
Closure: finite Finset computation on `Prefix 4`.
Strategy: not applicable.
Trust: kernel-only; `decide` on the finite fiber.
Scope: the instance `n = 4`.
-/
theorem church_fiberMultiplicity_four :
    fiberMultiplicity (obs 4) (cost 4) = 5 := by
  decide

/--
Proves: L21's attained channel `finIndexChannel 4` licenses cost on `Prefix 4` after the bridge.
Does not prove: optimality by itself.
Relation: `Licensed (augmentObserver (obs 4) _) (cost 4)`.
Closure: the subtype carrier `Prefix 4`.
Strategy: `channelLicenses_iff_licensed` applied to `capacity_attained 4`.
Trust: kernel-only.
Scope: the instance `n = 4`.
-/
theorem capacity_attained_four_through_bridge :
    Licensed (augmentObserver (obs 4) (fun t => finIndexChannel 4 t.1)) (cost 4) :=
  (channelLicenses_iff_licensed 4 (finIndexChannel 4)).1 (capacity_attained 4)

end OperatorKO7.HigherOrderRewritingCapacityLawWeld
