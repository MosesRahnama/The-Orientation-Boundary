import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import OperatorKO7.Meta.HigherOrderRewriting_SystemTSyntax
import OperatorKO7.Meta.HigherOrderRewriting_TypeCostBoundary
import OperatorKO7.Meta.HigherOrderRewriting_ChannelCapacity
import OperatorKO7.Meta.HigherOrderRewriting_CapacityLawWeld
import OperatorKO7.Meta.HigherOrderRewriting_IndexedLicense
import OperatorKO7.Meta.OperationalInexpressibility.LiftOrRefuse
import OperatorKO7.Meta.OperationalInexpressibility.LicenseCore
import OperatorKO7.Meta.OperationalInexpressibility.FiberDeficitCore
import OperatorKO7.Meta.OperationalInexpressibility.ConfusabilityGraph

/-!
# L48 The quantitative face of the type-cost boundary on the Church prefix

The capacity theorem of L21 and L22 is a cardinality: the least licensing channel on the first
`n + 1` Church applications has `n + 1` values. This module states the same fact in the four
quantitative forms the observer framework uses, each on the subtype carrier `Prefix n` of L22.

1. Bits. The fixed-width code deficit `fiberDeficit` of the type observer against the cost is
   `Nat.clog 2 (n + 1)`, the ceiling of the base-two logarithm of the capacity, with the
   two-sided power sandwich. The hidden-progress quantity `log2 (n + 1)` of the Orientation
   Boundary equals the base-two logarithm of the fiber multiplicity, as a real number.
2. The repair curve. Under the uniform prior on `Prefix n`, a side channel with `k` values can
   license the cost on a retained set of at most `k` terms, so the refused mass is at least
   `1 - k / (n + 1)`, and this is attained by retaining the first `k` Church applications.
   The curve is linear in `k` and reaches zero at the capacity `k = n + 1`.
3. Bayes risk. A decoder that reads the type alone is correct on at most one term of `Prefix n`,
   so under the uniform prior its refused mass is at least `n / (n + 1)`, attained by the
   constant decoder that answers the cost of `churchApp 0`.
4. Sufficiency. On the full Church family the indexed observer of L2 is a sufficient statistic
   for the cost (it licenses the cost), the Church index alone is sufficient, and the type is a
   garbling of both in the sense of observer refinement, which is the Blackwell order of the
   observer framework at the deterministic level.

Units. Items 2 and 3 are rational masses in `[0, 1]`; item 1 carries a natural-number bit count
and a real-number logarithm; the capacity itself is a count. No quantity here is a Shannon
entropy: the entropy bound `H(P | q) <= log m` of the observer framework is not restated.

Relation: observer-fiber equality of `obs n` (the type) against `cost n` (leftmost-outermost
beta cost at fuel `n + 2`) on `Prefix n`; `LicensedOn` and `refusedMass` of
`OperationalInexpressibility.LiftOrRefuse`.
Closure: the finite subtype carrier `Prefix n`; one observer fiber holds every state.
Strategy: leftmost-outermost cost through `betaCost`.
Trust: kernel-only; finite fixtures use `decide` and `norm_num`.
Scope: the Church prefix of System T under the uniform prior, and the Church family for item 4.
-/

set_option autoImplicit false

namespace OperatorKO7.HigherOrderRewritingQuantitativeFace

open OperatorKO7.HigherOrderRewritingSystemT
open OperatorKO7.HigherOrderRewritingTypeCostBoundary
open OperatorKO7.HigherOrderRewritingChannelCapacity
open OperatorKO7.HigherOrderRewritingCapacityLawWeld
open OperatorKO7.Meta.OperationalInexpressibility.LiftOrRefuse
open OperatorKO7.Meta.OperationalInexpressibility.FiberDeficit
open OperatorKO7.Meta.OperationalInexpressibility.Confusability
open OperatorKO7.Meta.OperationalInexpressibility.LicenseCriterion
open OperatorKO7.Meta.OperationalInexpressibility.ObserverKernel

/-! ## NameGate -/

#check @OperatorKO7.HigherOrderRewritingCapacityLawWeld.Prefix
#check @OperatorKO7.HigherOrderRewritingCapacityLawWeld.obs
#check @OperatorKO7.HigherOrderRewritingCapacityLawWeld.cost
#check @OperatorKO7.HigherOrderRewritingCapacityLawWeld.obs_const
#check @OperatorKO7.HigherOrderRewritingCapacityLawWeld.cost_injective
#check @OperatorKO7.HigherOrderRewritingCapacityLawWeld.prefix_card
#check @OperatorKO7.HigherOrderRewritingCapacityLawWeld.church_fiberMultiplicity
#check @OperatorKO7.HigherOrderRewritingChannelCapacity.churchApp_injective
#check @OperatorKO7.HigherOrderRewritingChannelCapacity.indexChannel
#check @OperatorKO7.HigherOrderRewritingChannelCapacity.isChurchApp?_churchApp
#check @OperatorKO7.HigherOrderRewritingIndexedLicense.indexedObserver
#check @OperatorKO7.HigherOrderRewritingIndexedLicense.churchIndex
#check @OperatorKO7.HigherOrderRewritingIndexedLicense.churchIndex_churchApp
#check @OperatorKO7.HigherOrderRewritingIndexedLicense.ChurchFamily
#check @OperatorKO7.HigherOrderRewritingIndexedLicense.indexed_observer_licensedOn_church
#check @OperatorKO7.HigherOrderRewritingIndexedLicense.plain_observer_not_licensedOn_church
#check @OperatorKO7.Meta.OperationalInexpressibility.LiftOrRefuse.LicensedOn
#check @OperatorKO7.Meta.OperationalInexpressibility.LiftOrRefuse.refusedMass
#check @OperatorKO7.Meta.OperationalInexpressibility.LiftOrRefuse.correctFinset
#check @OperatorKO7.Meta.OperationalInexpressibility.FiberDeficit.fiberDeficit
#check @OperatorKO7.Meta.OperationalInexpressibility.FiberDeficit.fiberMultiplicity
#check @OperatorKO7.Meta.OperationalInexpressibility.Confusability.augmentObserver
#check @OperatorKO7.Meta.OperationalInexpressibility.LicenseCriterion.ObserverRefines
#check @Nat.le_pow_iff_clog_le
#check @Nat.pow_lt_iff_lt_clog
#check @Nat.clog_pos
#check @Finset.card_le_card_of_injOn
#check @Finset.sum_ite
#check @Finset.card_univ_diff

/-! ## 1. Bits -/

/--
Proves: the fixed-width code deficit of the type observer against the prefix cost is the ceiling
of the base-two logarithm of `n + 1`.
Does not prove: a Shannon-entropy statement; `fiberDeficit` is a fixed-length code capacity.
Relation: `fiberDeficit (obs n) (cost n)`.
Closure: the subtype carrier `Prefix n`.
Strategy: leftmost-outermost cost; the identity is `church_fiberMultiplicity` under `Nat.clog`.
Trust: kernel-only.
Scope: every `n : Nat`.
-/
theorem church_fiberDeficit (n : Nat) :
    fiberDeficit (obs n) (cost n) = Nat.clog 2 (n + 1) := by
  unfold fiberDeficit
  rw [church_fiberMultiplicity]

/--
Proves: for `1 ≤ n`, the capacity `n + 1` lies strictly above `2 ^ (bits - 1)` and at most
`2 ^ bits`, where `bits` is the code deficit; so the deficit is the least number of binary digits
that index every cost value in the fiber.
Does not prove: anything at `n = 0`, where the deficit is zero and `bits - 1` truncates.
Relation: `fiberDeficit (obs n) (cost n)` against `n + 1`.
Closure: the subtype carrier `Prefix n`.
Strategy: not applicable.
Trust: kernel-only; `Nat.pow_lt_iff_lt_clog` and `Nat.le_pow_iff_clog_le`.
Scope: every `n` with `1 ≤ n`.
-/
theorem church_bits_sandwich (n : Nat) (hn : 1 ≤ n) :
    2 ^ (fiberDeficit (obs n) (cost n) - 1) < n + 1 ∧
      n + 1 ≤ 2 ^ fiberDeficit (obs n) (cost n) := by
  rw [church_fiberDeficit]
  have hb : (1 : Nat) < 2 := by norm_num
  have hpos : 0 < Nat.clog 2 (n + 1) := Nat.clog_pos hb (by omega)
  constructor
  · exact (Nat.pow_lt_iff_lt_clog hb).2 (by omega)
  · exact (Nat.le_pow_iff_clog_le hb).2 le_rfl

/--
Proves: nothing by itself; names the hidden-progress quantity `log2 (n + 1)` of the Orientation
Boundary as a real number.
Does not prove: a relation to the code deficit without the theorem below.
Relation: not applicable.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only; noncomputable through `Real.logb`.
Scope: every `n : Nat`.
-/
noncomputable def hiddenProgressBits (n : Nat) : ℝ := Real.logb 2 ((n : ℝ) + 1)

/--
Proves: the hidden-progress quantity `log2 (n + 1)` equals the base-two logarithm of the fiber
multiplicity of the type observer against the prefix cost.
Does not prove: equality with the integer code deficit, which is the ceiling of this value.
Relation: `fiberMultiplicity (obs n) (cost n)` cast to `ℝ`.
Closure: the subtype carrier `Prefix n`.
Strategy: not applicable.
Trust: kernel-only.
Scope: every `n : Nat`.
-/
theorem hiddenProgress_eq_logb_fiberMultiplicity (n : Nat) :
    hiddenProgressBits n = Real.logb 2 ((fiberMultiplicity (obs n) (cost n) : Nat) : ℝ) := by
  simp [hiddenProgressBits, church_fiberMultiplicity]

/-! ## 2. The uniform prior and the repair curve -/

/--
Proves: nothing by itself; the uniform prior on the `n + 1` states of `Prefix n`.
Does not prove: normalization without `uniformPrior_sum_one`.
Relation: not applicable.
Closure: the subtype carrier `Prefix n`.
Strategy: not applicable.
Trust: kernel-only.
Scope: every `n : Nat`.
-/
def uniformPrior (n : Nat) : Prefix n → ℚ := fun _ => 1 / ((n : ℚ) + 1)

/--
Proves: the uniform prior is nonnegative at every state.
Does not prove: normalization.
Relation: not applicable.
Closure: the subtype carrier `Prefix n`.
Strategy: not applicable.
Trust: kernel-only.
Scope: every `n : Nat`.
-/
theorem uniformPrior_nonneg (n : Nat) : ∀ x, 0 ≤ uniformPrior n x := by
  intro x
  unfold uniformPrior
  positivity

/--
Proves: the uniform prior sums to one over `Prefix n`.
Does not prove: anything about another carrier.
Relation: not applicable.
Closure: the subtype carrier `Prefix n`, of cardinality `n + 1` by `prefix_card`.
Strategy: not applicable.
Trust: kernel-only.
Scope: every `n : Nat`.
-/
theorem uniformPrior_sum_one (n : Nat) : ∑ x, uniformPrior n x = 1 := by
  unfold uniformPrior
  rw [Finset.sum_const, Finset.card_univ, prefix_card, nsmul_eq_mul]
  have h : ((n : ℚ) + 1) ≠ 0 := by positivity
  push_cast
  field_simp

/--
Proves: under the uniform prior the refused mass of a retained set `S` is the number of states
outside `S` divided by `n + 1`.
Does not prove: anything about a non-uniform prior.
Relation: `refusedMass (uniformPrior n) S`.
Closure: the subtype carrier `Prefix n`.
Strategy: not applicable.
Trust: kernel-only.
Scope: every `n : Nat` and every `S : Finset (Prefix n)`.
-/
theorem refusedMass_uniform (n : Nat) (S : Finset (Prefix n)) :
    refusedMass (uniformPrior n) S = ((n + 1 - S.card : Nat) : ℚ) / ((n : ℚ) + 1) := by
  unfold refusedMass uniformPrior
  rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul,
    Finset.filter_not, Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.card_univ_diff,
    prefix_card]
  ring

/--
Proves: a side channel with `k` values that licenses the prefix cost on a retained set `S`
(jointly with the type) retains at most `k` states.
Does not prove: that `k` states can be retained; that is `retainedPrefix_licensed`.
Relation: `LicensedOn S (augmentObserver (obs n) s) (cost n)`.
Closure: observer-fiber equality on the retained set `S ⊆ Prefix n`.
Strategy: leftmost-outermost cost through `cost_injective`.
Trust: kernel-only.
Scope: every `n k : Nat`, every `s : Prefix n → Fin k`, every retained `S`.
-/
theorem licensed_retained_card_le (n k : Nat) (s : Prefix n → Fin k) (S : Finset (Prefix n))
    (hS : LicensedOn (↑S : Set (Prefix n)) (augmentObserver (obs n) s) (cost n)) :
    S.card ≤ k := by
  have hinj : Set.InjOn s (↑S : Set (Prefix n)) := by
    intro x hx y hy hxy
    apply cost_injective n
    apply hS x hx y hy
    show (obs n x, s x) = (obs n y, s y)
    rw [obs_const n x, obs_const n y, hxy]
  have hcard : S.card ≤ (Finset.univ : Finset (Fin k)).card :=
    Finset.card_le_card_of_injOn s (fun x _ => Finset.mem_univ (s x)) hinj
  simpa using hcard

/--
Proves: under the uniform prior, every `k`-valued lift that licenses the prefix cost on a
retained set refuses mass at least `1 - k / (n + 1)`.
Does not prove: attainment; that is `refusedMass_retainedPrefix`.
Relation: `refusedMass (uniformPrior n) S` for `S` licensed by `augmentObserver (obs n) s`.
Closure: the retained set `S ⊆ Prefix n`.
Strategy: leftmost-outermost cost.
Trust: kernel-only.
Scope: every `n k : Nat`, every `s : Prefix n → Fin k`, every retained `S`.
-/
theorem refusedMass_ge_repair_curve (n k : Nat) (s : Prefix n → Fin k) (S : Finset (Prefix n))
    (hS : LicensedOn (↑S : Set (Prefix n)) (augmentObserver (obs n) s) (cost n)) :
    1 - (k : ℚ) / ((n : ℚ) + 1) ≤ refusedMass (uniformPrior n) S := by
  rw [refusedMass_uniform]
  have hcard : S.card ≤ k := licensed_retained_card_le n k s S hS
  have hle : S.card ≤ n + 1 := by
    rw [← prefix_card n]
    exact Finset.card_le_univ S
  have hpos : (0 : ℚ) < (n : ℚ) + 1 := by positivity
  have hcardQ : (S.card : ℚ) ≤ k := by exact_mod_cast hcard
  rw [Nat.cast_sub hle]
  push_cast
  rw [le_div_iff₀ hpos]
  have hsplit : (1 - (k : ℚ) / ((n : ℚ) + 1)) * ((n : ℚ) + 1) = (n : ℚ) + 1 - k := by
    field_simp
  rw [hsplit]
  linarith

/--
Proves: nothing by itself; the `m`-th Church application as a state of `Prefix n`, for `m < n + 1`.
Does not prove: a cost or typing fact.
Relation: membership in `churchPrefix n`.
Closure: finite image of `Finset.range (n + 1)`.
Strategy: not applicable.
Trust: kernel-only.
Scope: every `m < n + 1`.
-/
def prefixOf (n m : Nat) (hm : m < n + 1) : Prefix n :=
  ⟨churchApp m, by
    unfold churchPrefix
    exact Finset.mem_image.mpr ⟨m, Finset.mem_range.mpr hm, rfl⟩⟩

/--
Proves: nothing by itself; the first `k` Church applications as a retained subset of `Prefix n`.
Does not prove: its cardinality without `retainedPrefix_card`.
Relation: not applicable.
Closure: finite image of `Fin k`.
Strategy: not applicable.
Trust: kernel-only.
Scope: every `k ≤ n + 1`.
-/
def retainedPrefix (n k : Nat) (hk : k ≤ n + 1) : Finset (Prefix n) :=
  Finset.univ.image (fun m : Fin k => prefixOf n m.1 (lt_of_lt_of_le m.2 hk))

/--
Proves: the retained prefix of the first `k` Church applications has exactly `k` states.
Does not prove: a licensing fact.
Relation: equality of `Nat`.
Closure: finite image of `Fin k` under an injective map.
Strategy: not applicable.
Trust: kernel-only.
Scope: every `k ≤ n + 1`.
-/
theorem retainedPrefix_card (n k : Nat) (hk : k ≤ n + 1) :
    (retainedPrefix n k hk).card = k := by
  unfold retainedPrefix
  rw [Finset.card_image_of_injective, Finset.card_univ, Fintype.card_fin]
  intro a b hab
  have hval : churchApp a.1 = churchApp b.1 := congrArg Subtype.val hab
  exact Fin.ext (churchApp_injective hval)

/--
Proves: nothing by itself; the `k`-valued side channel that reads the Church index and clamps it
to `k - 1`, for `1 ≤ k`.
Does not prove: injectivity outside the first `k` Church applications.
Relation: syntactic observation through `indexChannel`.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: every `n`, every `k` with `1 ≤ k`.
-/
def clampIndex (n k : Nat) (hk1 : 1 ≤ k) : Prefix n → Fin k :=
  fun t => ⟨Nat.min (indexChannel t.1) (k - 1),
    Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (Nat.sub_lt hk1 Nat.one_pos)⟩

/--
Proves: the clamped index channel reads `m` on the `m`-th Church application when `m < k`.
Does not prove: the value on a Church application with index at least `k`.
Relation: equality in `Fin k`.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: every `m < k` with `m < n + 1`.
-/
theorem clampIndex_prefixOf (n k : Nat) (hk1 : 1 ≤ k) (m : Nat) (hm : m < n + 1)
    (hmk : m < k) :
    clampIndex n k hk1 (prefixOf n m hm) = ⟨m, hmk⟩ := by
  apply Fin.ext
  simp [clampIndex, prefixOf, indexChannel, isChurchApp?_churchApp]
  omega

/--
Proves: the type observer paired with the clamped index channel licenses the prefix cost on the
first `k` Church applications.
Does not prove: licensing outside that retained set.
Relation: `LicensedOn (retainedPrefix n k hk) (augmentObserver (obs n) (clampIndex n k hk1)) (cost n)`.
Closure: observer-fiber equality on the retained set.
Strategy: leftmost-outermost cost.
Trust: kernel-only.
Scope: every `1 ≤ k ≤ n + 1`.
-/
theorem retainedPrefix_licensed (n k : Nat) (hk1 : 1 ≤ k) (hk : k ≤ n + 1) :
    LicensedOn (↑(retainedPrefix n k hk) : Set (Prefix n))
      (augmentObserver (obs n) (clampIndex n k hk1)) (cost n) := by
  intro x hx y hy hxy
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
  obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hy)
  have hs := congrArg Prod.snd hxy
  simp only [augmentObserver] at hs
  rw [clampIndex_prefixOf n k hk1 a.1 _ a.2, clampIndex_prefixOf n k hk1 b.1 _ b.2] at hs
  have hab : a = b := Fin.ext (congrArg Fin.val hs)
  subst hab
  rfl

/--
Proves: under the uniform prior the retained prefix of the first `k` Church applications refuses
mass exactly `1 - k / (n + 1)`.
Does not prove: optimality by itself; that is `repair_curve`.
Relation: `refusedMass (uniformPrior n) (retainedPrefix n k hk)`.
Closure: the retained set.
Strategy: not applicable.
Trust: kernel-only.
Scope: every `k ≤ n + 1`.
-/
theorem refusedMass_retainedPrefix (n k : Nat) (hk : k ≤ n + 1) :
    refusedMass (uniformPrior n) (retainedPrefix n k hk) = 1 - (k : ℚ) / ((n : ℚ) + 1) := by
  rw [refusedMass_uniform, retainedPrefix_card, Nat.cast_sub hk]
  have h : ((n : ℚ) + 1) ≠ 0 := by positivity
  push_cast
  field_simp

/--
Proves: the repair curve. Under the uniform prior on `Prefix n`, for `1 ≤ k ≤ n + 1`, the least
refused mass over all `k`-valued side channels and all retained sets they license (jointly with
the type) is `1 - k / (n + 1)`.
Does not prove: the value of the observer framework's `repairFrontier`, whose statement needs a
finite target codomain that `Option Nat` is not; the curve is stated directly as a least refused
mass. Nothing at `k = 0`, where no channel into `Fin 0` exists on the nonempty carrier.
Relation: `LicensedOn S (augmentObserver (obs n) s) (cost n)` and `refusedMass (uniformPrior n) S`.
Closure: retained subsets of `Prefix n`.
Strategy: leftmost-outermost cost.
Trust: kernel-only.
Scope: every `n`, every `k` with `1 ≤ k ≤ n + 1`.
-/
theorem repair_curve (n k : Nat) (hk1 : 1 ≤ k) (hk : k ≤ n + 1) :
    IsLeast {r : ℚ | ∃ (s : Prefix n → Fin k) (S : Finset (Prefix n)),
        LicensedOn (↑S : Set (Prefix n)) (augmentObserver (obs n) s) (cost n) ∧
          refusedMass (uniformPrior n) S = r}
      (1 - (k : ℚ) / ((n : ℚ) + 1)) := by
  constructor
  · exact ⟨clampIndex n k hk1, retainedPrefix n k hk, retainedPrefix_licensed n k hk1 hk,
      refusedMass_retainedPrefix n k hk⟩
  · rintro r ⟨s, S, hS, rfl⟩
    exact refusedMass_ge_repair_curve n k s S hS

/--
Proves: at the capacity `k = n + 1` the least refused mass is zero: the lift of least cardinality
refuses nothing, which is the refusal-side statement of `church_least_lift`.
Does not prove: a value at any other `k`; that is `repair_curve`.
Relation: as in `repair_curve`.
Closure: retained subsets of `Prefix n`.
Strategy: leftmost-outermost cost.
Trust: kernel-only.
Scope: every `n : Nat`.
-/
theorem repair_curve_zero_at_capacity (n : Nat) :
    IsLeast {r : ℚ | ∃ (s : Prefix n → Fin (n + 1)) (S : Finset (Prefix n)),
        LicensedOn (↑S : Set (Prefix n)) (augmentObserver (obs n) s) (cost n) ∧
          refusedMass (uniformPrior n) S = r}
      0 := by
  have h := repair_curve n (n + 1) (by omega) le_rfl
  have hzero : (1 : ℚ) - ((n + 1 : Nat) : ℚ) / ((n : ℚ) + 1) = 0 := by
    have hne : ((n : ℚ) + 1) ≠ 0 := by positivity
    push_cast
    field_simp
  rwa [hzero] at h

/-! ## 3. Bayes risk of the type observer -/

/--
Proves: a decoder that reads the type alone is correct on at most one state of `Prefix n`.
Does not prove: which state; that depends on the decoder.
Relation: `correctFinset (obs n) (cost n) d`.
Closure: the subtype carrier `Prefix n`.
Strategy: leftmost-outermost cost through `cost_injective`.
Trust: kernel-only.
Scope: every `n`, every decoder `d : Option SysTTy → Option Nat`.
-/
theorem correctFinset_card_le_one (n : Nat) (d : Option SysTTy → Option Nat) :
    (correctFinset (obs n) (cost n) d).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro x hx y hy
  rw [correctFinset, Finset.mem_filter] at hx hy
  apply cost_injective n
  rw [hx.2, hy.2, obs_const, obs_const]

/--
Proves: under the uniform prior every type-only decoder refuses mass at least `n / (n + 1)`;
this is the Bayes risk floor of the type observer for the prefix cost.
Does not prove: attainment; that is `correctFinset_firstCostDecoder_card`.
Relation: `refusedMass (uniformPrior n) (correctFinset (obs n) (cost n) d)`.
Closure: the subtype carrier `Prefix n`.
Strategy: leftmost-outermost cost.
Trust: kernel-only.
Scope: every `n`, every decoder `d`.
-/
theorem type_decoder_refusedMass_ge (n : Nat) (d : Option SysTTy → Option Nat) :
    (n : ℚ) / ((n : ℚ) + 1) ≤ refusedMass (uniformPrior n) (correctFinset (obs n) (cost n) d) := by
  rw [refusedMass_uniform]
  have h1 := correctFinset_card_le_one n d
  have hle : (correctFinset (obs n) (cost n) d).card ≤ n + 1 := by
    rw [← prefix_card n]
    exact Finset.card_le_univ _
  have hpos : (0 : ℚ) < (n : ℚ) + 1 := by positivity
  have h1Q : ((correctFinset (obs n) (cost n) d).card : ℚ) ≤ 1 := by exact_mod_cast h1
  rw [Nat.cast_sub hle]
  push_cast
  rw [div_le_div_iff_of_pos_right hpos]
  linarith

/--
Proves: nothing by itself; the constant decoder answering the cost of `churchApp 0`, which is
`some 2` at every fuel of at least two.
Does not prove: correctness anywhere without `correctFinset_firstCostDecoder_card`.
Relation: not applicable.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: every observation.
-/
def firstCostDecoder : Option SysTTy → Option Nat := fun _ => some 2

/--
Proves: the constant decoder is correct on exactly one state of `Prefix n`, namely `churchApp 0`,
so the Bayes risk floor `n / (n + 1)` is attained.
Does not prove: a result for another decoder.
Relation: `correctFinset (obs n) (cost n) firstCostDecoder`.
Closure: the subtype carrier `Prefix n`.
Strategy: leftmost-outermost cost through `betaCost_churchApp`.
Trust: kernel-only.
Scope: every `n : Nat`.
-/
theorem correctFinset_firstCostDecoder_card (n : Nat) :
    (correctFinset (obs n) (cost n) firstCostDecoder).card = 1 := by
  apply le_antisymm (correctFinset_card_le_one n firstCostDecoder)
  apply Finset.card_pos.mpr
  refine ⟨prefixOf n 0 (Nat.zero_lt_succ n), ?_⟩
  rw [correctFinset, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  show betaCost (n + 2) (churchApp 0) = some 2
  have h := betaCost_churchApp 0 (n + 2) (by omega)
  simpa using h

/--
Proves: the Bayes risk of the type observer. Under the uniform prior on `Prefix n`, the least
refused mass over all type-only decoders is `n / (n + 1)`.
Does not prove: the observer framework's `bayesRisk` value, whose statement needs a finite
observation codomain that `Option SysTTy` is not; the risk is stated directly as a least refused
mass of a correctness set, which `LiftOrRefuse` identifies with the 0-1 risk when the codomains
are finite.
Relation: `refusedMass (uniformPrior n) (correctFinset (obs n) (cost n) d)`.
Closure: the subtype carrier `Prefix n`.
Strategy: leftmost-outermost cost.
Trust: kernel-only.
Scope: every `n : Nat`.
-/
theorem bayes_risk_of_type (n : Nat) :
    IsLeast {r : ℚ | ∃ d : Option SysTTy → Option Nat,
        refusedMass (uniformPrior n) (correctFinset (obs n) (cost n) d) = r}
      ((n : ℚ) / ((n : ℚ) + 1)) := by
  constructor
  · refine ⟨firstCostDecoder, ?_⟩
    rw [refusedMass_uniform, correctFinset_firstCostDecoder_card]
    have hne : ((n : ℚ) + 1) ≠ 0 := by positivity
    have hsub : n + 1 - 1 = n := by omega
    rw [hsub]
  · rintro r ⟨d, rfl⟩
    exact type_decoder_refusedMass_ge n d

/-! ## 4. Sufficiency and the Blackwell order on the Church family -/

/--
Proves: the type observer is a garbling of the indexed observer of L2: the indexed observer
refines it, since the type is its first component.
Does not prove: the converse, which `plain_observer_not_licensedOn_church` rules out through
licensing.
Relation: `ObserverRefines indexedObserver (infer [])`.
Closure: all System T terms.
Strategy: not applicable.
Trust: kernel-only.
Scope: every closed System T term.
-/
theorem type_is_garbling_of_indexed :
    ObserverRefines OperatorKO7.HigherOrderRewritingIndexedLicense.indexedObserver (infer []) := by
  intro x y hxy
  exact congrArg Prod.fst hxy

/--
Proves: the indexed observer refines the Church index alone.
Does not prove: that the index refines the indexed observer on all terms.
Relation: `ObserverRefines indexedObserver churchIndex`.
Closure: all System T terms.
Strategy: not applicable.
Trust: kernel-only.
Scope: every System T term.
-/
theorem indexed_refines_churchIndex :
    ObserverRefines OperatorKO7.HigherOrderRewritingIndexedLicense.indexedObserver
      OperatorKO7.HigherOrderRewritingIndexedLicense.churchIndex := by
  intro x y hxy
  exact congrArg Prod.snd hxy

/--
Proves: the Church index alone is a sufficient statistic for the cost on the Church family: it
licenses `betaCost f` there for every fuel.
Does not prove: sufficiency outside the Church family.
Relation: `LicensedOn ChurchFamily churchIndex (betaCost f)`.
Closure: observer-fiber equality on the Church family.
Strategy: leftmost-outermost cost.
Trust: kernel-only.
Scope: every fuel `f`.
-/
theorem churchIndex_licensedOn_church :
    ∀ f, LicensedOn OperatorKO7.HigherOrderRewritingIndexedLicense.ChurchFamily
      OperatorKO7.HigherOrderRewritingIndexedLicense.churchIndex (betaCost f) := by
  intro f x hx y hy hxy
  rcases hx with ⟨m, rfl⟩
  rcases hy with ⟨k, rfl⟩
  rw [OperatorKO7.HigherOrderRewritingIndexedLicense.churchIndex_churchApp,
    OperatorKO7.HigherOrderRewritingIndexedLicense.churchIndex_churchApp] at hxy
  subst hxy
  rfl

/--
Proves: the Blackwell triple on the Church family. The index refines nothing finer here, the
indexed observer refines both the index and the type, the index and the indexed observer license
the cost, and the type does not (at fuel three or more).
Does not prove: a statement about the stochastic Blackwell order; refinement here is the
deterministic garbling order of the observer framework.
Relation: `ObserverRefines` and `LicensedOn ChurchFamily _ (betaCost f)`.
Closure: the Church family.
Strategy: leftmost-outermost cost.
Trust: kernel-only.
Scope: every fuel `f` with `3 ≤ f`.
-/
theorem blackwell_triple_on_church (f : Nat) (hf : 3 ≤ f) :
    ObserverRefines OperatorKO7.HigherOrderRewritingIndexedLicense.indexedObserver (infer []) ∧
    ObserverRefines OperatorKO7.HigherOrderRewritingIndexedLicense.indexedObserver
      OperatorKO7.HigherOrderRewritingIndexedLicense.churchIndex ∧
    LicensedOn OperatorKO7.HigherOrderRewritingIndexedLicense.ChurchFamily
      OperatorKO7.HigherOrderRewritingIndexedLicense.indexedObserver (betaCost f) ∧
    LicensedOn OperatorKO7.HigherOrderRewritingIndexedLicense.ChurchFamily
      OperatorKO7.HigherOrderRewritingIndexedLicense.churchIndex (betaCost f) ∧
    ¬ LicensedOn OperatorKO7.HigherOrderRewritingIndexedLicense.ChurchFamily (infer [])
      (betaCost f) :=
  ⟨type_is_garbling_of_indexed, indexed_refines_churchIndex,
    OperatorKO7.HigherOrderRewritingIndexedLicense.indexed_observer_licensedOn_church f,
    churchIndex_licensedOn_church f,
    OperatorKO7.HigherOrderRewritingIndexedLicense.plain_observer_not_licensedOn_church f hf⟩

/-! ## Closed fixtures (Q49: every closed form evaluated at two instances) -/

example : fiberDeficit (obs 4) (cost 4) = 3 := by
  rw [church_fiberDeficit]
  have hb : (1 : Nat) < 2 := by norm_num
  apply le_antisymm
  · exact (Nat.le_pow_iff_clog_le hb).1 (by norm_num)
  · exact (Nat.pow_lt_iff_lt_clog hb).1 (by norm_num)

example : fiberDeficit (obs 7) (cost 7) = 3 := by
  rw [church_fiberDeficit]
  have hb : (1 : Nat) < 2 := by norm_num
  apply le_antisymm
  · exact (Nat.le_pow_iff_clog_le hb).1 (by norm_num)
  · exact (Nat.pow_lt_iff_lt_clog hb).1 (by norm_num)

example : fiberDeficit (obs 8) (cost 8) = 4 := by
  rw [church_fiberDeficit]
  have hb : (1 : Nat) < 2 := by norm_num
  apply le_antisymm
  · exact (Nat.le_pow_iff_clog_le hb).1 (by norm_num)
  · exact (Nat.pow_lt_iff_lt_clog hb).1 (by norm_num)

example : refusedMass (uniformPrior 4) (retainedPrefix 4 2 (by norm_num)) = 3 / 5 := by
  rw [refusedMass_retainedPrefix]
  norm_num

example : refusedMass (uniformPrior 1) (retainedPrefix 1 1 (by norm_num)) = 1 / 2 := by
  rw [refusedMass_retainedPrefix]
  norm_num

example : refusedMass (uniformPrior 4) (retainedPrefix 4 5 le_rfl) = 0 := by
  rw [refusedMass_retainedPrefix]
  norm_num

example : refusedMass (uniformPrior 4) (correctFinset (obs 4) (cost 4) firstCostDecoder) = 4 / 5 := by
  rw [refusedMass_uniform, correctFinset_firstCostDecoder_card]
  norm_num

example : refusedMass (uniformPrior 1) (correctFinset (obs 1) (cost 1) firstCostDecoder) = 1 / 2 := by
  rw [refusedMass_uniform, correctFinset_firstCostDecoder_card]
  norm_num

end OperatorKO7.HigherOrderRewritingQuantitativeFace
