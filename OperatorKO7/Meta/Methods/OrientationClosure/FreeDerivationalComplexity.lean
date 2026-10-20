import OperatorKO7.Meta.Methods.OrientationClosure.MethodRowsSubstrate
import OperatorKO7.Meta.Methods.OrientationClosure.ObserverSufficiency
import Mathlib.Tactic

/-!
# Derivational complexity of the free recursor

The free two-rule recursor has single-exponential derivational complexity under contextual
rewriting, with explicit constants on both sides, over every variable type. No rule inspects a
variable, so every statement below quantifies over `ν : Type u`; the natural-number statements are
its instances at `Nat`.

Upper bound. The polynomial weight `freeWeight`
(`freeWeight (recur b s n) = freeWeight b + (freeWeight s + 2) (freeWeight n + 1)`) drops on every
contextual step (`freeWeight_contextStep`), so a derivation from `t` has at most `freeWeight t`
steps (`relPow_le_freeWeight`), and `freeWeight t + 2 ≤ 3 ^ |t|` (`freeWeight_add_two_le_pow`).
Every derivation from `t` therefore has fewer than `3 ^ |t|` steps (`derivation_lt_pow_size`). At
natural-number variables `freeWeight` is the weight `qw` of `MethodRowsSubstrate`
(`freeWeight_eq_qw`), and `relPow_le_qw` and `qw_add_two_le_pow` are the instances.

Lower bound. The nested payload family `nestFamily k 0 = recur 0 0 0`,
`nestFamily k (d + 1) = recur 0 (nestFamily k d) (succ^k 0)` has size `4 + d (k + 3)`
(`termSize_nestFamily`), and it has a derivation of at least `k ^ d` steps
(`nestFamily_long_derivation`): the recursor emits `k` copies of the payload before any copy is
reduced, and every copy is then reduced in full. `nest` is the family at natural-number variables.

The dependency-pair escape counts calls: along any sequence of recursive calls the number of calls
equals the drop of the successor count of the counter (`callChain_length_eq`).
-/

set_option autoImplicit false

namespace OperatorKO7.Methods.OrientationClosure.FreeDerivationalComplexity

open OperatorKO7.Methods.OrientationClosure.SchemaCore
open OperatorKO7.Methods.OrientationClosure.ProcessorSemantics
open OperatorKO7.Methods.OrientationClosure.MethodRowsSubstrate
open OperatorKO7.Methods.OrientationClosure.SourceChainSoundness

universe u

variable {ν : Type u}

/-- Term size: the number of constructors and variables of a free term.

Proves: (definition) a variable and `zero` have size one; `succ`, `wrap` and `recur` add one to
the sizes of their arguments.
Does not prove: any bound on rewriting.
Relation: none.
Closure: none.
Strategy: not applicable.
Trust: kernel-only.
Scope: every variable type `ν`; the variable itself is never inspected. -/
def termSize : FreeTerm ν → Nat
  | .var _ => 1
  | .zero => 1
  | .succ t => termSize t + 1
  | .wrap s t => termSize s + termSize t + 1
  | .recur b s n => termSize b + termSize s + termSize n + 1

/-! ## Upper bound -/

/-- The polynomial weight of the free recursor: a variable weighs `0`, `zero` weighs `1`, `succ`
adds one, `wrap` adds one to the sum of its arguments, and `recur b s n` weighs
`b + (s + 2) (n + 1)`.

Proves: (definition) the five defining equations above.
Does not prove: a decrease along a step; `freeWeight_contextStep` states the decrease.
Relation: none.
Closure: none.
Strategy: not applicable.
Trust: kernel-only.
Scope: every variable type `ν`; at `Nat` it equals `qw` (`freeWeight_eq_qw`). -/
def freeWeight : FreeTerm ν → Nat
  | .var _ => 0
  | .zero => 1
  | .succ t => freeWeight t + 1
  | .wrap s t => freeWeight s + freeWeight t + 1
  | .recur b s n => freeWeight b + (freeWeight s + 2) * (freeWeight n + 1)

/-- At natural-number variables the weight is the weight `qw` of `MethodRowsSubstrate`.

Proves: `freeWeight t = qw t` for every `t : FreeTerm Nat`.
Does not prove: a statement at another variable type.
Relation: none.
Closure: none.
Strategy: not applicable.
Trust: kernel-only.
Scope: natural-number variables, every term. -/
theorem freeWeight_eq_qw (t : FreeTerm Nat) : freeWeight t = qw t := by
  induction t with
  | var x => rfl
  | zero => rfl
  | succ t ih => simp only [freeWeight, qw, ih]
  | wrap s t ihs iht => simp only [freeWeight, qw, ihs, iht]
  | recur b s n ihb ihs ihn => simp only [freeWeight, qw, ihb, ihs, ihn]

/-- Both root rules drop the weight.

Proves: `RootStep t u → freeWeight u < freeWeight t`.
Does not prove: a decrease under contexts; `freeWeight_contextStep` adds the contexts.
Relation: RootStep.
Closure: root.
Strategy: full.
Trust: kernel-only.
Scope: every variable type `ν`. -/
theorem freeWeight_rootStep {t u : FreeTerm ν} (h : RootStep t u) :
    freeWeight u < freeWeight t := by
  cases h with
  | recurZero b s =>
    simp only [freeWeight]
    nlinarith
  | recurSucc b s n =>
    simp only [freeWeight]
    nlinarith

/-- The weight is strictly monotone under every one-hole constructor context.

Proves: `freeWeight b < freeWeight a → freeWeight (C.plug b) < freeWeight (C.plug a)`.
Does not prove: monotonicity for multi-hole contexts.
Relation: none (a property of the weight).
Closure: one-hole constructor contexts.
Strategy: not applicable.
Trust: kernel-only.
Scope: every variable type `ν` and every context `C`. -/
theorem freeWeight_plug_lt (C : FreeContext ν) {a b : FreeTerm ν}
    (h : freeWeight b < freeWeight a) : freeWeight (C.plug b) < freeWeight (C.plug a) := by
  induction C with
  | hole => simpa using h
  | succ C ih =>
    simp only [FreeContext.plug, freeWeight]
    omega
  | wrapLeft C r ih =>
    simp only [FreeContext.plug, freeWeight]
    omega
  | wrapRight l C ih =>
    simp only [FreeContext.plug, freeWeight]
    omega
  | recurBase C s n ih =>
    simp only [FreeContext.plug, freeWeight]
    omega
  | recurStep x C n ih =>
    simp only [FreeContext.plug, freeWeight]
    have hpos : 0 < freeWeight n + 1 := Nat.succ_pos _
    nlinarith
  | recurCounter x s C ih =>
    simp only [FreeContext.plug, freeWeight]
    have hpos : 0 < freeWeight s + 2 := by omega
    nlinarith

/-- Every contextual step drops the weight.

Proves: `ContextStep t u → freeWeight u < freeWeight t`.
Does not prove: a decrease along steps of another relation.
Relation: ContextStep.
Closure: context.
Strategy: full.
Trust: kernel-only.
Scope: every variable type `ν`. -/
theorem freeWeight_contextStep {t u : FreeTerm ν} (h : ContextStep t u) :
    freeWeight u < freeWeight t := by
  cases h with
  | lift C hr => exact freeWeight_plug_lt C (freeWeight_rootStep hr)

/-- A derivation drops the weight by at least its length.

Proves: a contextual derivation of `m` steps from `t` to `u` gives
`m + freeWeight u ≤ freeWeight t`.
Does not prove: the size bound; `derivation_lt_pow_size` adds it.
Relation: ContextStep.
Closure: exactly `m` steps (`RelPow`).
Strategy: full.
Trust: kernel-only.
Scope: every variable type `ν`. -/
theorem relPow_le_freeWeight {m : Nat} {t u : FreeTerm ν} (h : RelPow ContextStep m t u) :
    m + freeWeight u ≤ freeWeight t := by
  induction h with
  | zero => simp
  | succ _ hst ih =>
    have := freeWeight_contextStep hst
    omega

/-- A derivation drops the weight `qw` by at least its length.

Proves: the instance of `relPow_le_freeWeight` at natural-number variables, stated with `qw`.
Does not prove: a statement at another variable type; `relPow_le_freeWeight` is the general form.
Relation: ContextStep.
Closure: exactly `m` steps (`RelPow`).
Strategy: full.
Trust: kernel-only.
Scope: natural-number variables. -/
theorem relPow_le_qw {m : Nat} {t u : FreeTerm Nat} (h : RelPow ContextStep m t u) :
    m + qw u ≤ qw t := by
  have h1 := relPow_le_freeWeight h
  rwa [freeWeight_eq_qw, freeWeight_eq_qw] at h1

/-- The weight plus two is at most three to the size.

Proves: `freeWeight t + 2 ≤ 3 ^ termSize t`.
Does not prove: a lower bound on the weight.
Relation: none.
Closure: none.
Strategy: not applicable.
Trust: kernel-only.
Scope: every variable type `ν` and every term. -/
theorem freeWeight_add_two_le_pow (t : FreeTerm ν) : freeWeight t + 2 ≤ 3 ^ termSize t := by
  induction t with
  | var x => simp [freeWeight, termSize]
  | zero => simp [freeWeight, termSize]
  | succ t ih =>
    obtain ⟨A, hA⟩ : ∃ A, A = 3 ^ termSize t := ⟨_, rfl⟩
    rw [show termSize (.succ t) = termSize t + 1 from rfl, pow_succ, ← hA]
    simp only [freeWeight]
    omega
  | wrap s t ihs iht =>
    obtain ⟨A, hA⟩ : ∃ A, A = 3 ^ termSize s := ⟨_, rfl⟩
    obtain ⟨B, hB⟩ : ∃ B, B = 3 ^ termSize t := ⟨_, rfl⟩
    rw [show termSize (.wrap s t) = termSize s + termSize t + 1 from rfl, pow_succ, pow_add,
      ← hA, ← hB]
    rw [← hA] at ihs
    rw [← hB] at iht
    simp only [freeWeight]
    nlinarith [Nat.mul_le_mul ihs iht]
  | recur b s n ihb ihs ihn =>
    obtain ⟨A, hA⟩ : ∃ A, A = 3 ^ termSize b := ⟨_, rfl⟩
    obtain ⟨B, hB⟩ : ∃ B, B = 3 ^ termSize s := ⟨_, rfl⟩
    obtain ⟨C, hC⟩ : ∃ C, C = 3 ^ termSize n := ⟨_, rfl⟩
    rw [show termSize (.recur b s n) = termSize b + termSize s + termSize n + 1 from rfl, pow_succ,
      pow_add, pow_add, ← hA, ← hB, ← hC]
    rw [← hA] at ihb
    rw [← hB] at ihs
    rw [← hC] at ihn
    simp only [freeWeight]
    have h1 : (freeWeight s + 2) * (freeWeight n + 1) ≤ B * C := Nat.mul_le_mul ihs (by omega)
    have h2 : 1 ≤ B * C := Nat.one_le_iff_ne_zero.2 (mul_ne_zero (by omega) (by omega))
    have h3 : 1 ≤ A := by omega
    have h4 : A * 1 ≤ A * (B * C) := Nat.mul_le_mul_left A h2
    have h5 : 1 * (B * C) ≤ A * (B * C) := Nat.mul_le_mul_right (B * C) h3
    nlinarith

/-- The weight `qw` plus two is at most three to the size.

Proves: the instance of `freeWeight_add_two_le_pow` at natural-number variables, stated with `qw`.
Does not prove: a statement at another variable type; `freeWeight_add_two_le_pow` is the general
form.
Relation: none.
Closure: none.
Strategy: not applicable.
Trust: kernel-only.
Scope: natural-number variables. -/
theorem qw_add_two_le_pow (t : FreeTerm Nat) : qw t + 2 ≤ 3 ^ termSize t := by
  rw [← freeWeight_eq_qw]
  exact freeWeight_add_two_le_pow t

/-- Every derivation from `t` has fewer than `3 ^ |t|` steps.

Proves: a contextual derivation of `m` steps from `t` gives `m + 2 ≤ 3 ^ termSize t`, that is, at
most `3 ^ |t| - 2` steps.
Does not prove: that the bound is attained; `nestFamily_long_derivation` gives the exponential
lower bound.
Relation: ContextStep.
Closure: exactly `m` steps (`RelPow`), every `m`.
Strategy: full.
Trust: kernel-only.
Scope: every variable type `ν`; at `Nat` it is the natural-number statement. -/
theorem derivation_lt_pow_size {m : Nat} {t u : FreeTerm ν} (h : RelPow ContextStep m t u) :
    m + 2 ≤ 3 ^ termSize t := by
  have h1 := relPow_le_freeWeight h
  have h2 := freeWeight_add_two_le_pow t
  omega

/-! ## Lower bound -/

/-- `j` successors on top of `n`.

Proves: (definition) `sucOn 0 n = n` and `sucOn (j + 1) n = succ (sucOn j n)`.
Does not prove: any rewriting fact.
Relation: none.
Closure: none.
Strategy: not applicable.
Trust: kernel-only.
Scope: every variable type `ν`. -/
def sucOn : Nat → FreeTerm ν → FreeTerm ν
  | 0, n => n
  | j + 1, n => .succ (sucOn j n)

/-- `j` wrappers with payload `s` around `y`.

Proves: (definition) `wrapPow s 0 y = y` and `wrapPow s (j + 1) y = wrap s (wrapPow s j y)`.
Does not prove: any rewriting fact.
Relation: none.
Closure: none.
Strategy: not applicable.
Trust: kernel-only.
Scope: every variable type `ν`. -/
def wrapPow (s : FreeTerm ν) : Nat → FreeTerm ν → FreeTerm ν
  | 0, y => y
  | j + 1, y => .wrap s (wrapPow s j y)

/-- A derivation lifts through a one-hole context with the same number of steps.

Proves: `RelPow ContextStep m x y → RelPow ContextStep m (C.plug x) (C.plug y)`.
Does not prove: a lift through a multi-hole context.
Relation: ContextStep.
Closure: exactly `m` steps under one context.
Strategy: full.
Trust: kernel-only.
Scope: every variable type `ν` and every context `C`. -/
theorem relPow_plug (C : FreeContext ν) {m : Nat} {x y : FreeTerm ν}
    (h : RelPow ContextStep m x y) : RelPow ContextStep m (C.plug x) (C.plug y) := by
  induction h with
  | zero => exact RelPow.zero _
  | succ _ hst ih => exact RelPow.succ ih (hst.outer C)

/-- Unfolding the recursor `j` times emits `j` copies of the payload.

Proves: `recur b s (succ^j n)` reaches `wrapPow s j (recur b s n)` in exactly `j` contextual
steps.
Does not prove: any statement about the copies after they are emitted.
Relation: ContextStep.
Closure: exactly `j` steps.
Strategy: full.
Trust: kernel-only.
Scope: every variable type `ν`, every `b`, `s`, `n` and `j`. -/
theorem unfold_steps (b s : FreeTerm ν) :
    ∀ (j : Nat) (n : FreeTerm ν),
      RelPow ContextStep j (.recur b s (sucOn j n)) (wrapPow s j (.recur b s n))
  | 0, n => RelPow.zero _
  | j + 1, n => by
    have h1 : RelPow ContextStep 1 (.recur b s (sucOn (j + 1) n))
        (.wrap s (.recur b s (sucOn j n))) :=
      RelPow.succ (RelPow.zero _) (rootStep_contextStep (.recurSucc b s (sucOn j n)))
    have h2 : RelPow ContextStep j (.wrap s (.recur b s (sucOn j n)))
        (.wrap s (wrapPow s j (.recur b s n))) :=
      relPow_plug (.wrapRight s .hole) (unfold_steps b s j n)
    have h3 := h1.append h2
    rw [show 1 + j = j + 1 from Nat.add_comm 1 j] at h3
    exact h3

/-- Reducing every payload copy costs the reduction of one copy times the number of copies.

Proves: an `m`-step derivation from `s` to `s'` gives a `j * m`-step derivation from
`wrapPow s j y` to `wrapPow s' j y`.
Does not prove: any statement about `y`.
Relation: ContextStep.
Closure: exactly `j * m` steps.
Strategy: full.
Trust: kernel-only.
Scope: every variable type `ν`. -/
theorem reduce_copies {m : Nat} {s s' : FreeTerm ν} (hs : RelPow ContextStep m s s')
    (y : FreeTerm ν) : ∀ j : Nat, RelPow ContextStep (j * m) (wrapPow s j y) (wrapPow s' j y)
  | 0 => by
    rw [Nat.zero_mul]
    exact RelPow.zero _
  | j + 1 => by
    have h1 : RelPow ContextStep m (.wrap s (wrapPow s j y)) (.wrap s' (wrapPow s j y)) :=
      relPow_plug (.wrapLeft .hole (wrapPow s j y)) hs
    have h2 : RelPow ContextStep (j * m) (.wrap s' (wrapPow s j y)) (.wrap s' (wrapPow s' j y)) :=
      relPow_plug (.wrapRight s' .hole) (reduce_copies hs y j)
    have h3 := h1.append h2
    rw [show m + j * m = (j + 1) * m by ring] at h3
    exact h3

/-- The nested payload family over any variable type: `nestFamily k 0 = recur 0 0 0` and
`nestFamily k (d + 1) = recur 0 (nestFamily k d) (succ^k 0)`.

Proves: (definition) the two equations above.
Does not prove: any size or length fact; `termSize_nestFamily` and `nestFamily_long_derivation`
state them.
Relation: none.
Closure: none.
Strategy: not applicable.
Trust: kernel-only.
Scope: every variable type `ν`; the terms are closed, so the family is the same at every `ν`. -/
def nestFamily (k : Nat) : Nat → FreeTerm ν
  | 0 => .recur .zero .zero .zero
  | d + 1 => .recur .zero (nestFamily k d) (sucOn k .zero)

/-- The nested payload family at natural-number variables.

Proves: (definition) `nest k = nestFamily (ν := Nat) k`.
Does not prove: any fact at another variable type.
Relation: none.
Closure: none.
Strategy: not applicable.
Trust: kernel-only.
Scope: natural-number variables. -/
abbrev nest (k : Nat) : Nat → FreeTerm Nat := nestFamily k

/-- Successors add their number to the size.

Proves: `termSize (sucOn k n) = termSize n + k`.
Does not prove: any rewriting fact.
Relation: none.
Closure: none.
Strategy: not applicable.
Trust: kernel-only.
Scope: every variable type `ν`. -/
theorem termSize_sucOn (n : FreeTerm ν) : ∀ k : Nat, termSize (sucOn k n) = termSize n + k
  | 0 => rfl
  | k + 1 => by
    simp only [sucOn, termSize, termSize_sucOn n k]
    omega

/-- The size of the nested family.

Proves: `termSize (nestFamily k d) = 4 + d * (k + 3)`.
Does not prove: any rewriting fact.
Relation: none.
Closure: none.
Strategy: not applicable.
Trust: kernel-only.
Scope: every variable type `ν`, every `k` and `d`. -/
theorem termSize_nestFamily (k : Nat) :
    ∀ d : Nat, termSize (nestFamily (ν := ν) k d) = 4 + d * (k + 3)
  | 0 => by simp [nestFamily, termSize]
  | d + 1 => by
    simp only [nestFamily, termSize, termSize_sucOn, termSize_nestFamily k d]
    ring

/-- The size of the nested family at natural-number variables.

Proves: the instance of `termSize_nestFamily` at `Nat`, stated with `nest`.
Does not prove: a statement at another variable type; `termSize_nestFamily` is the general form.
Relation: none.
Closure: none.
Strategy: not applicable.
Trust: kernel-only.
Scope: natural-number variables. -/
theorem termSize_nest (k : Nat) : ∀ d : Nat, termSize (nest k d) = 4 + d * (k + 3) :=
  termSize_nestFamily (ν := Nat) k

/-- The nested family has a derivation of at least `k ^ d` steps.

Proves: for every `d` some `m ≥ k ^ d` and some `u` carry an `m`-step contextual derivation from
`nestFamily k d` to `u`.
Does not prove: that every derivation from the family is that long.
Relation: ContextStep.
Closure: exactly `m` steps (`RelPow`).
Strategy: full.
Trust: kernel-only.
Scope: every variable type `ν`, every `k` and `d`. -/
theorem nestFamily_long_derivation (k : Nat) :
    ∀ d : Nat, ∃ m u, k ^ d ≤ m ∧ RelPow ContextStep m (nestFamily (ν := ν) k d) u
  | 0 => ⟨1, .zero, by simp,
      RelPow.succ (RelPow.zero _) (rootStep_contextStep (.recurZero _ _))⟩
  | d + 1 => by
    obtain ⟨m, u, hm, hd⟩ := nestFamily_long_derivation k d
    have h1 := unfold_steps .zero (nestFamily (ν := ν) k d) k .zero
    have h2 := reduce_copies hd (.recur .zero (nestFamily (ν := ν) k d) .zero) k
    refine ⟨k + k * m, _, ?_, h1.append h2⟩
    calc k ^ (d + 1) = k * k ^ d := by ring
      _ ≤ k * m := Nat.mul_le_mul_left k hm
      _ ≤ k + k * m := Nat.le_add_left _ _

/-- The nested family at natural-number variables has a derivation of at least `k ^ d` steps.

Proves: the instance of `nestFamily_long_derivation` at `Nat`, stated with `nest`.
Does not prove: a statement at another variable type; `nestFamily_long_derivation` is the general
form.
Relation: ContextStep.
Closure: exactly `m` steps (`RelPow`).
Strategy: full.
Trust: kernel-only.
Scope: natural-number variables. -/
theorem nest_long_derivation (k : Nat) :
    ∀ d : Nat, ∃ m u, k ^ d ≤ m ∧ RelPow ContextStep m (nest k d) u :=
  nestFamily_long_derivation (ν := Nat) k

/-- Single-exponential sandwich: every derivation from `t` has fewer than `3 ^ |t|` steps, and the
nested family at `k = 2` has a derivation of at least `2 ^ d` steps from a term of size `5 d + 4`.

Proves: the upper bound `m + 2 ≤ 3 ^ termSize t` for every contextual derivation, and for every
`d` the size `termSize (nestFamily 2 d) = 5 * d + 4` together with a derivation of at least `2 ^ d`
steps from that term.
Does not prove: a matching upper bound on the derivations of the family.
Relation: ContextStep.
Closure: exactly `m` steps (`RelPow`), every `m`.
Strategy: full.
Trust: kernel-only.
Scope: every variable type `ν`; at `Nat` the family is `nest 2`. -/
theorem exponential_sandwich :
    (∀ {m : Nat} {t u : FreeTerm ν}, RelPow ContextStep m t u → m + 2 ≤ 3 ^ termSize t) ∧
      ∀ d : Nat, termSize (nestFamily (ν := ν) 2 d) = 5 * d + 4 ∧
        ∃ m u, 2 ^ d ≤ m ∧ RelPow ContextStep m (nestFamily (ν := ν) 2 d) u := by
  refine ⟨fun h => derivation_lt_pow_size h, fun d => ⟨?_, nestFamily_long_derivation 2 d⟩⟩
  rw [termSize_nestFamily]
  ring

/-! ## The dependency-pair escape -/

/-- Along a sequence of recursive calls the number of calls equals the drop of the call counter.

Proves: an `m`-step chain of `FreeRecursiveCallPair` from `a` to `c` gives
`m + recursiveCallRank c = recursiveCallRank a`.
Does not prove: any statement about contextual rewriting.
Relation: FreeRecursiveCallPair.
Closure: exactly `m` calls (`RelPow`).
Strategy: not applicable (a dependency-pair chain).
Trust: kernel-only.
Scope: every variable type `ν`. -/
theorem callChain_length_eq {m : Nat} {a c : FreeTerm ν}
    (h : RelPow FreeRecursiveCallPair m a c) : m + recursiveCallRank c = recursiveCallRank a := by
  induction h with
  | zero => simp
  | succ _ hst ih =>
    have := ObserverSufficiency.recursiveCallRank_call hst
    omega

end OperatorKO7.Methods.OrientationClosure.FreeDerivationalComplexity
