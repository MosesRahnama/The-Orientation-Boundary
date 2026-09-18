import OperatorKO7.Meta.Methods.OrientationClosure.MethodRowsSubstrate
import OperatorKO7.Meta.Methods.OrientationClosure.ObserverSufficiency
import Mathlib.Tactic

/-!
# Derivational complexity of the free recursor

The free two-rule recursor has single-exponential derivational complexity under contextual
rewriting, with explicit constants on both sides.

Upper bound. The polynomial weight `qw` (`qw (recur b s n) = qw b + (qw s + 2) (qw n + 1)`) drops on
every contextual step, so a derivation from `t` has at most `qw t` steps (`relPow_le_qw`), and
`qw t + 2 ≤ 3 ^ |t|` (`qw_add_two_le_pow`). Every derivation from `t` therefore has fewer than
`3 ^ |t|` steps (`derivation_lt_pow_size`).

Lower bound. The nested payload family `nest k 0 = recur 0 0 0`,
`nest k (d + 1) = recur 0 (nest k d) (succ^k 0)` has size `4 + d (k + 3)` (`termSize_nest`), and it
has a derivation of at least `k ^ d` steps (`nest_long_derivation`): the recursor emits `k` copies of
the payload before any copy is reduced, and every copy is then reduced in full.

The dependency-pair escape counts calls: along any sequence of recursive calls the number of calls
equals the drop of the successor count of the counter (`callChain_length_eq`).
-/

set_option autoImplicit false

namespace OperatorKO7.Methods.OrientationClosure.FreeDerivationalComplexity

open OperatorKO7.Methods.OrientationClosure.SchemaCore
open OperatorKO7.Methods.OrientationClosure.ProcessorSemantics
open OperatorKO7.Methods.OrientationClosure.MethodRowsSubstrate
open OperatorKO7.Methods.OrientationClosure.SourceChainSoundness

/-- Term size. -/
def termSize : FreeTerm Nat → Nat
  | .var _ => 1
  | .zero => 1
  | .succ t => termSize t + 1
  | .wrap s t => termSize s + termSize t + 1
  | .recur b s n => termSize b + termSize s + termSize n + 1

/-! ## Upper bound -/

/-- A derivation drops the weight by at least its length. -/
theorem relPow_le_qw {m : Nat} {t u : FreeTerm Nat} (h : RelPow ContextStep m t u) :
    m + qw u ≤ qw t := by
  induction h with
  | zero => simp
  | succ _ hst ih =>
    have := qw_contextStep hst
    omega

theorem qw_add_two_le_pow (t : FreeTerm Nat) : qw t + 2 ≤ 3 ^ termSize t := by
  induction t with
  | var x => simp [qw, termSize]
  | zero => simp [qw, termSize]
  | succ t ih =>
    obtain ⟨A, hA⟩ : ∃ A, A = 3 ^ termSize t := ⟨_, rfl⟩
    rw [show termSize (.succ t) = termSize t + 1 from rfl, pow_succ, ← hA]
    simp only [qw]
    omega
  | wrap s t ihs iht =>
    obtain ⟨A, hA⟩ : ∃ A, A = 3 ^ termSize s := ⟨_, rfl⟩
    obtain ⟨B, hB⟩ : ∃ B, B = 3 ^ termSize t := ⟨_, rfl⟩
    rw [show termSize (.wrap s t) = termSize s + termSize t + 1 from rfl, pow_succ, pow_add,
      ← hA, ← hB]
    rw [← hA] at ihs
    rw [← hB] at iht
    simp only [qw]
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
    simp only [qw]
    have h1 : (qw s + 2) * (qw n + 1) ≤ B * C := Nat.mul_le_mul ihs (by omega)
    have h2 : 1 ≤ B * C := Nat.one_le_iff_ne_zero.2 (mul_ne_zero (by omega) (by omega))
    have h3 : 1 ≤ A := by omega
    have h4 : A * 1 ≤ A * (B * C) := Nat.mul_le_mul_left A h2
    have h5 : 1 * (B * C) ≤ A * (B * C) := Nat.mul_le_mul_right (B * C) h3
    nlinarith

/-- Every derivation from `t` has fewer than `3 ^ |t|` steps. -/
theorem derivation_lt_pow_size {m : Nat} {t u : FreeTerm Nat} (h : RelPow ContextStep m t u) :
    m + 2 ≤ 3 ^ termSize t := by
  have h1 := relPow_le_qw h
  have h2 := qw_add_two_le_pow t
  omega

/-! ## Lower bound -/

/-- `j` successors on top of `n`. -/
def sucOn : Nat → FreeTerm Nat → FreeTerm Nat
  | 0, n => n
  | j + 1, n => .succ (sucOn j n)

/-- `j` wrappers with payload `s` around `y`. -/
def wrapPow (s : FreeTerm Nat) : Nat → FreeTerm Nat → FreeTerm Nat
  | 0, y => y
  | j + 1, y => .wrap s (wrapPow s j y)

theorem relPow_plug (C : FreeContext Nat) {m : Nat} {x y : FreeTerm Nat}
    (h : RelPow ContextStep m x y) : RelPow ContextStep m (C.plug x) (C.plug y) := by
  induction h with
  | zero => exact RelPow.zero _
  | succ _ hst ih => exact RelPow.succ ih (hst.outer C)

/-- Unfolding the recursor `j` times emits `j` copies of the payload. -/
theorem unfold_steps (b s : FreeTerm Nat) :
    ∀ (j : Nat) (n : FreeTerm Nat),
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

/-- Reducing every payload copy costs the reduction of one copy times the number of copies. -/
theorem reduce_copies {m : Nat} {s s' : FreeTerm Nat} (hs : RelPow ContextStep m s s')
    (y : FreeTerm Nat) : ∀ j : Nat, RelPow ContextStep (j * m) (wrapPow s j y) (wrapPow s' j y)
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

/-- The nested payload family. -/
def nest (k : Nat) : Nat → FreeTerm Nat
  | 0 => .recur .zero .zero .zero
  | d + 1 => .recur .zero (nest k d) (sucOn k .zero)

theorem termSize_sucOn (n : FreeTerm Nat) : ∀ k : Nat, termSize (sucOn k n) = termSize n + k
  | 0 => rfl
  | k + 1 => by
    simp only [sucOn, termSize, termSize_sucOn n k]
    omega

theorem termSize_nest (k : Nat) : ∀ d : Nat, termSize (nest k d) = 4 + d * (k + 3)
  | 0 => by simp [nest, termSize]
  | d + 1 => by
    simp only [nest, termSize, termSize_sucOn, termSize_nest k d]
    ring

/-- The nested family has a derivation of at least `k ^ d` steps. -/
theorem nest_long_derivation (k : Nat) :
    ∀ d : Nat, ∃ m u, k ^ d ≤ m ∧ RelPow ContextStep m (nest k d) u
  | 0 => ⟨1, .zero, by simp,
      RelPow.succ (RelPow.zero _) (rootStep_contextStep (.recurZero _ _))⟩
  | d + 1 => by
    obtain ⟨m, u, hm, hd⟩ := nest_long_derivation k d
    have h1 := unfold_steps .zero (nest k d) k .zero
    have h2 := reduce_copies hd (.recur .zero (nest k d) .zero) k
    refine ⟨k + k * m, _, ?_, h1.append h2⟩
    calc k ^ (d + 1) = k * k ^ d := by ring
      _ ≤ k * m := Nat.mul_le_mul_left k hm
      _ ≤ k + k * m := Nat.le_add_left _ _

/-- Single-exponential sandwich: every derivation from `t` has fewer than `3 ^ |t|` steps, and the
nested family at `k = 2` has a derivation of at least `2 ^ d` steps from a term of size `5 d + 4`. -/
theorem exponential_sandwich :
    (∀ {m : Nat} {t u : FreeTerm Nat}, RelPow ContextStep m t u → m + 2 ≤ 3 ^ termSize t) ∧
      ∀ d : Nat, termSize (nest 2 d) = 5 * d + 4 ∧
        ∃ m u, 2 ^ d ≤ m ∧ RelPow ContextStep m (nest 2 d) u := by
  refine ⟨fun h => derivation_lt_pow_size h, fun d => ⟨?_, nest_long_derivation 2 d⟩⟩
  rw [termSize_nest]
  ring

/-! ## The dependency-pair escape -/

/-- Along a sequence of recursive calls the number of calls equals the drop of the call counter. -/
theorem callChain_length_eq {m : Nat} {a c : FreeTerm Nat}
    (h : RelPow FreeRecursiveCallPair m a c) : m + recursiveCallRank c = recursiveCallRank a := by
  induction h with
  | zero => simp
  | succ _ hst ih =>
    have := ObserverSufficiency.recursiveCallRank_call hst
    omega

end OperatorKO7.Methods.OrientationClosure.FreeDerivationalComplexity
