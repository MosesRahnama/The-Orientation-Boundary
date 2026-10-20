import Mathlib.Tactic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import OperatorKO7.Meta.HigherOrderRewriting_SystemTSyntax
import OperatorKO7.Meta.HigherOrderRewriting_TypeCostBoundary
import OperatorKO7.Meta.OperationalInexpressibility.LiftOrRefuse

/-!
# L21 channel capacity for Church-cost licensing

Relation: the observer `infer []` paired with a side channel, against `betaCost (n + 2)`.
Closure: observer-fiber equality on the finite Church prefix `churchPrefix n`.
Strategy: leftmost-outermost cost through `betaCost`.
Trust: kernel-only; closed arithmetic and finite fixtures use `decide`.
Scope: the first `n + 1` Church applications and finite side-channel codomains.
-/

set_option autoImplicit false

namespace OperatorKO7.HigherOrderRewritingChannelCapacity

open OperatorKO7.HigherOrderRewritingSystemT
open OperatorKO7.HigherOrderRewritingTypeCostBoundary
open OperatorKO7.Meta.OperationalInexpressibility.LiftOrRefuse

/-! ## NameGate -/

#check @OperatorKO7.HigherOrderRewritingSystemT.SysTTerm
#check @OperatorKO7.HigherOrderRewritingTypeCostBoundary.infer_churchApp
#check @OperatorKO7.HigherOrderRewritingTypeCostBoundary.betaCost_churchApp
#check @OperatorKO7.HigherOrderRewritingTypeCostBoundary.church_fiber_unbounded
#check @OperatorKO7.Meta.OperationalInexpressibility.LiftOrRefuse.LicensedOn
#check @Fintype.card
#check @Finset.card_le_card_of_injOn
#check @Nat.log_mono_right
#check @Nat.pow_log_le_self

/--
Proves: `churchPrefix n` is the image of the first `n + 1` natural indices under `churchApp`.
Does not prove: that every System T term is a Church application.
Relation: equality of `SysTTerm`.
Closure: finite image.
Trust: kernel-only.
Scope: every `n : Nat`.
-/
def churchPrefix (n : Nat) : Finset SysTTerm :=
  Finset.image churchApp (Finset.range (n + 1))

private theorem churchBody_injective : Function.Injective churchBody := by
  intro m n h
  induction m generalizing n with
  | zero =>
      cases n with
      | zero => rfl
      | succ _ => cases h
  | succ m ih =>
      cases n with
      | zero => cases h
      | succ n =>
          injection h with _ hbody
          exact congrArg Nat.succ (ih hbody)

/--
Proves: distinct natural indices give distinct Church applications.
Does not prove: injectivity of any larger System T encoding.
Relation: equality of `SysTTerm`.
Closure: not applicable.
Trust: kernel-only.
Scope: `churchApp : Nat → SysTTerm`.
-/
theorem churchApp_injective : Function.Injective churchApp := by
  intro m n h
  injection h with happ _
  injection happ with hchurch _
  injection hchurch with _ hlam
  injection hlam with _ hbody
  exact churchBody_injective hbody

/--
Proves: the first `n + 1` Church applications form a finite set of cardinality `n + 1`.
Does not prove: a cardinality statement for any larger family of System T terms.
Relation: equality of `SysTTerm`.
Closure: finite image.
Trust: kernel-only.
Scope: every `n : Nat`.
-/
theorem churchPrefix_card (n : Nat) : (churchPrefix n).card = n + 1 := by
  unfold churchPrefix
  rw [Finset.card_image_of_injective _ churchApp_injective, Finset.card_range]

/--
Proves: every member of `churchPrefix n` has inferred type `nat` in the empty context.
Does not prove: completeness of `infer`, nor a cost fact.
Relation: `infer []`.
Closure: finite retained set.
Trust: kernel-only.
Scope: every member of `churchPrefix n`.
-/
theorem churchPrefix_typed (n : Nat) :
    ∀ t ∈ churchPrefix n, infer [] t = some .nat := by
  intro t ht
  unfold churchPrefix at ht
  obtain ⟨m, _, rfl⟩ := Finset.mem_image.mp ht
  exact infer_churchApp m

/--
Proves: the type observer paired with `s` licenses `betaCost (n + 2)` on `churchPrefix n`.
Does not prove: licensing outside the prefix, for another observer, or for another cost strategy.
Relation: `LicensedOn (churchPrefix n) (fun t => (infer [] t, s t)) (betaCost (n + 2))`.
Closure: observer-fiber equality on the finite prefix.
Trust: kernel-only.
Scope: the first `n + 1` Church applications.
-/
def ChannelLicenses (n : Nat) {C : Type} (s : SysTTerm → C) : Prop :=
  LicensedOn (churchPrefix n : Set SysTTerm) (fun t => (infer [] t, s t)) (betaCost (n + 2))

/--
Proves: any side channel licensing the Church-prefix cost is injective on that prefix.
Does not prove: injectivity outside the prefix, or a bound for observers other than `infer []`.
Relation: `ChannelLicenses n s` and `Set.InjOn s (churchPrefix n)`.
Closure: observer-fiber equality on the finite prefix.
Trust: kernel-only.
Scope: arbitrary channel codomain `C`, every `n`, every `s : SysTTerm → C`.
-/
theorem channel_licenses_injOn {n : Nat} {C : Type} {s : SysTTerm → C} :
    ChannelLicenses n s → Set.InjOn s (churchPrefix n : Set SysTTerm) := by
  intro hlicensed x hx y hy hside
  have hx' : x ∈ churchPrefix n := Finset.mem_coe.mp hx
  have hy' : y ∈ churchPrefix n := Finset.mem_coe.mp hy
  unfold churchPrefix at hx' hy'
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hx'
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hy'
  have hobs :
      (infer [] (churchApp m), s (churchApp m)) =
        (infer [] (churchApp k), s (churchApp k)) := by
    apply Prod.ext
    · exact (infer_churchApp m).trans (infer_churchApp k).symm
    · exact hside
  have hcost := hlicensed
    (churchApp m) (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨m, hm, rfl⟩))
    (churchApp k) (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨k, hk, rfl⟩))
    hobs
  have hmFuel : m + 2 ≤ n + 2 := by
    have hm' := Finset.mem_range.mp hm
    omega
  have hkFuel : k + 2 ≤ n + 2 := by
    have hk' := Finset.mem_range.mp hk
    omega
  rw [betaCost_churchApp m (n + 2) hmFuel, betaCost_churchApp k (n + 2) hkFuel] at hcost
  have hmk : m + 2 = k + 2 := Option.some_injective _ hcost
  have : m = k := Nat.add_right_cancel hmk
  subst k
  rfl

/--
Proves: a finite licensing channel has at least `n + 1` values.
Does not prove: a Shannon-entropy bound, nor a bound for another observer or target.
Relation: `ChannelLicenses n s`.
Closure: finite prefix and finite channel codomain.
Trust: kernel-only.
Scope: every finite channel type `C`.
-/
theorem capacity_lower_bound {n : Nat} {C : Type} [Fintype C] {s : SysTTerm → C} :
    ChannelLicenses n s → n + 1 ≤ Fintype.card C := by
  intro hlicensed
  have hinj := channel_licenses_injOn hlicensed
  have hcard : (churchPrefix n).card ≤ (Finset.univ : Finset C).card := by
    apply Finset.card_le_card_of_injOn s
    · intro t _
      exact Finset.mem_univ (s t)
    · intro x hx y hy hxy
      exact hinj (Finset.mem_coe.mpr hx) (Finset.mem_coe.mpr hy) hxy
  simpa [churchPrefix_card] using hcard

/--
Proves: if a finite channel has fewer than `n + 1` values, no channel function into it licenses the prefix cost.
Does not prove: failure at cardinality `n + 1`, nor failure of an infinite channel.
Relation: `ChannelLicenses n s`.
Closure: finite prefix and finite channel codomain.
Trust: kernel-only.
Scope: every finite `C` with `Fintype.card C < n + 1`.
-/
theorem no_channel_below_capacity {n : Nat} {C : Type} [Fintype C]
    (h : Fintype.card C < n + 1) :
    ∀ s : SysTTerm → C, ¬ ChannelLicenses n s := by
  intro s hlicensed
  have hlow := capacity_lower_bound (n := n) (C := C) (s := s) hlicensed
  omega

private def churchBodyIndex? : SysTTerm → Option Nat
  | .var 0 => some 0
  | .app (.var 1) b => (churchBodyIndex? b).map Nat.succ
  | _ => none

private theorem churchBodyIndex?_churchBody :
    ∀ n, churchBodyIndex? (churchBody n) = some n
  | 0 => rfl
  | n + 1 => by
      simp [churchBody, churchBodyIndex?, churchBodyIndex?_churchBody n]

/--
Proves: this syntactic recognizer returns an index for terms with the exact `churchApp` shape.
Does not prove: that every term returning an index is typed, normalizing, or extensionally a Church numeral.
Relation: syntactic equality of `SysTTerm`.
Closure: structural recursion on syntax.
Trust: kernel-only.
Scope: all System T terms.
-/
def isChurchApp? : SysTTerm → Option Nat
  | .app (.app (.lam (.arrow .nat .nat) (.lam .nat b)) sf) .zero =>
      if sf = succFn then churchBodyIndex? b else none
  | _ => none

/--
Proves: the recognizer returns `some n` on `churchApp n`.
Does not prove: a semantic characterization of all terms recognized by `isChurchApp?`.
Relation: syntactic equality.
Closure: structural computation.
Trust: kernel-only.
Scope: every Church index `n`.
-/
theorem isChurchApp?_churchApp : ∀ n, isChurchApp? (churchApp n) = some n := by
  intro n
  simp [isChurchApp?, churchApp, church, succFn, churchBodyIndex?_churchBody]

/--
Proves: `indexChannel` reads the recognized Church index and defaults to zero otherwise.
Does not prove: injectivity on arbitrary System T terms.
Relation: syntactic observation.
Closure: not applicable.
Trust: kernel-only.
Scope: all System T terms.
-/
def indexChannel : SysTTerm → Nat :=
  fun t => (isChurchApp? t).getD 0

/--
Proves: `finIndexChannel n` clamps the recognized index into `Fin (n + 1)`.
Does not prove: that the clamp preserves indices above `n`.
Relation: syntactic observation.
Closure: not applicable.
Trust: kernel-only.
Scope: all System T terms, with exact preservation used only on `churchPrefix n`.
-/
def finIndexChannel (n : Nat) : SysTTerm → Fin (n + 1) :=
  fun t => ⟨Nat.min (indexChannel t) n, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩

private theorem finIndexChannel_churchApp {n m : Nat} (hm : m < n + 1) :
    finIndexChannel n (churchApp m) = ⟨m, hm⟩ := by
  apply Fin.ext
  simp [finIndexChannel, indexChannel, isChurchApp?_churchApp]
  omega

/--
Proves: a channel with exactly `n + 1` values licenses the cost on `churchPrefix n`.
Does not prove: licensing outside the prefix, nor optimality by itself.
Relation: `ChannelLicenses n (finIndexChannel n)`.
Closure: observer-fiber equality on the finite prefix.
Trust: kernel-only.
Scope: every `n : Nat`.
-/
theorem capacity_attained : ∀ n, ChannelLicenses n (finIndexChannel n) := by
  intro n x hx y hy hobs
  have hx' : x ∈ churchPrefix n := Finset.mem_coe.mp hx
  have hy' : y ∈ churchPrefix n := Finset.mem_coe.mp hy
  unfold churchPrefix at hx' hy'
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hx'
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hy'
  have hside :
      finIndexChannel n (churchApp m) = finIndexChannel n (churchApp k) :=
    congrArg Prod.snd hobs
  have hm' : m < n + 1 := Finset.mem_range.mp hm
  have hk' : k < n + 1 := Finset.mem_range.mp hk
  rw [finIndexChannel_churchApp hm', finIndexChannel_churchApp hk'] at hside
  have hmk : m = k := by
    have hv := congrArg Fin.val hside
    exact hv
  subst k
  rfl

/--
Proves: `n + 1` is the least cardinality of a finite `Fin k` channel licensing the prefix cost.
Does not prove: a result about entropy or non-finite channel types.
Relation: `ChannelLicenses n s`.
Closure: finite prefix and finite channel codomain.
Trust: kernel-only.
Scope: every `n : Nat`.
-/
theorem least_channel_card (n : Nat) :
    IsLeast {k : Nat | ∃ (s : SysTTerm → Fin k), ChannelLicenses n s} (n + 1) := by
  constructor
  · exact ⟨finIndexChannel n, capacity_attained n⟩
  · intro k hk
    obtain ⟨s, hs⟩ := hk
    have hlow := capacity_lower_bound (n := n) (C := Fin k) (s := s) hs
    simpa using hlow

/- Q49 controls: evaluate the logarithm and its associated power at four prefix sizes. -/
example : Nat.log 2 (0 + 1) = 0 :=
  Nat.log_eq_of_pow_le_of_lt_pow (by decide) (by decide)
example : Nat.log 2 (1 + 1) = 1 :=
  Nat.log_eq_of_pow_le_of_lt_pow (by decide) (by decide)
example : Nat.log 2 (3 + 1) = 2 :=
  Nat.log_eq_of_pow_le_of_lt_pow (by decide) (by decide)
example : Nat.log 2 (7 + 1) = 3 :=
  Nat.log_eq_of_pow_le_of_lt_pow (by decide) (by decide)
example : 2 ^ Nat.log 2 (0 + 1) = 1 := by
  have h : Nat.log 2 1 = 0 :=
    Nat.log_eq_of_pow_le_of_lt_pow (by decide) (by decide)
  rw [h]
  decide
example : 2 ^ Nat.log 2 (1 + 1) = 2 := by
  have h : Nat.log 2 2 = 1 :=
    Nat.log_eq_of_pow_le_of_lt_pow (by decide) (by decide)
  rw [h]
  decide
example : 2 ^ Nat.log 2 (3 + 1) = 4 := by
  have h : Nat.log 2 4 = 2 :=
    Nat.log_eq_of_pow_le_of_lt_pow (by decide) (by decide)
  rw [h]
  decide
example : 2 ^ Nat.log 2 (7 + 1) = 8 := by
  have h : Nat.log 2 8 = 3 :=
    Nat.log_eq_of_pow_le_of_lt_pow (by decide) (by decide)
  rw [h]
  decide

/--
Proves: licensing implies monotonicity of the floor base-two logarithm from `n + 1` to the channel cardinality.
Does not prove: a Shannon-entropy bound, a ceiling-log encoding bound, or a bound for another observer.
Relation: `ChannelLicenses n s`.
Closure: finite prefix and finite channel codomain.
Trust: kernel-only; uses `Nat.log_mono_right`.
Scope: every finite channel type `C`.
-/
theorem capacity_bits_lower_bound {n : Nat} {C : Type} [Fintype C] {s : SysTTerm → C} :
    ChannelLicenses n s →
      Nat.log 2 (n + 1) ≤ Nat.log 2 (Fintype.card C) := by
  intro hlicensed
  exact Nat.log_mono_right (capacity_lower_bound (n := n) (C := C) (s := s) hlicensed)

/--
Proves: the largest power of two selected by `Nat.log 2 (n + 1)` is at most the channel cardinality.
Does not prove: Shannon entropy, nor that `Nat.log` is a ceiling logarithm.
Relation: `ChannelLicenses n s`.
Closure: finite prefix and finite channel codomain.
Trust: kernel-only; uses `Nat.pow_log_le_self`.
Scope: every finite channel type `C`.
-/
theorem two_pow_bits_le_card {n : Nat} {C : Type} [Fintype C] {s : SysTTerm → C} :
    ChannelLicenses n s →
      2 ^ (Nat.log 2 (n + 1)) ≤ Fintype.card C := by
  intro hlicensed
  have hpow : 2 ^ Nat.log 2 (n + 1) ≤ n + 1 :=
    Nat.pow_log_le_self 2 (by omega)
  exact hpow.trans (capacity_lower_bound (n := n) (C := C) (s := s) hlicensed)

/-! ## Closed fixtures -/

example :
    churchApp 0 ∈ churchPrefix 3 ∧
    churchApp 1 ∈ churchPrefix 3 ∧
    churchApp 2 ∈ churchPrefix 3 ∧
    churchApp 3 ∈ churchPrefix 3 ∧
    (churchPrefix 3).card = 4 ∧
    betaCost 5 (churchApp 0) = some 2 ∧
    betaCost 5 (churchApp 1) = some 3 ∧
    betaCost 5 (churchApp 2) = some 4 ∧
    betaCost 5 (churchApp 3) = some 5 := by
  decide

example : ∀ s : SysTTerm → Fin 3, ¬ ChannelLicenses 3 s :=
  no_channel_below_capacity (n := 3) (C := Fin 3) (by decide)

example : ChannelLicenses 3 (finIndexChannel 3) :=
  capacity_attained 3

end OperatorKO7.HigherOrderRewritingChannelCapacity
