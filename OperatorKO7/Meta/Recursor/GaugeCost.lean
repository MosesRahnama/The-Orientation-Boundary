import OperatorKO7.Meta.Recursor.TraceAction

/-!
# Arithmetic cost identities and canonical-record decoding

The arithmetic section proves identities and bounds for the displayed cost functions. The decoding
section defines a partial decoder and proves correctness and injectivity only for canonical
`orbitState` records at positive depth. It does not prove total decoding for every terminal term.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.Recursor.GaugeCost

open SchemaTraceKernel
open TraceAction

def cumCell (j w : Nat) : Nat := tri j * w

def bitCost (m w : Nat) : Nat :=
  cumCell (2 ^ m - 1) w - cumCell (2 ^ (m - 1) - 1) w

/-- Sufficient fixed-width bit count for representing a counter below `2^bits`.

This is not claimed to be the exact minimum for all edge cases; its proved role is
`k < 2 ^ projBits k`. -/
def projBits (k : Nat) : Nat := Nat.log 2 k + 1

/-- Clarified alias for `projBits`, emphasizing sufficiency rather than global minimality. -/
def sufficientProjectionBits (k : Nat) : Nat := projBits k

/-- The sufficient-width alias is definitionally the legacy projection-bit count. -/
theorem sufficientProjectionBits_eq_projBits (k : Nat) :
    sufficientProjectionBits k = projBits k := rfl

def projectionBitCost : Nat := 1

theorem tri_mono {a b : Nat} (h : a <= b) : tri a <= tri b := by
  induction h with
  | refl => exact le_rfl
  | @step b h ih =>
      exact ih.trans (by simp [tri])

theorem cumCell_mono {a b w : Nat} (h : a <= b) :
    cumCell a w <= cumCell b w := by
  unfold cumCell
  exact Nat.mul_le_mul_right w (tri_mono h)

theorem two_mul_cumCell (j w : Nat) :
    2 * cumCell j w = w * j * (j + 1) := by
  unfold cumCell
  rw [← Nat.mul_assoc, two_mul_tri]
  ring

theorem four_pow_eq_two_pow_sq (n : Nat) :
    4 ^ n = 2 ^ n * 2 ^ n := by
  rw [show (4 : Nat) = 2 * 2 by norm_num, mul_pow]

theorem two_tri_gap (q : Nat) (hq : 1 <= q) :
    2 * (tri (2 * q - 1) - tri (q - 1)) + q = 3 * q * q := by
  have hidx : q - 1 <= 2 * q - 1 := by omega
  have htri : tri (q - 1) <= tri (2 * q - 1) := tri_mono hidx
  rw [Nat.mul_sub_left_distrib, two_mul_tri, two_mul_tri]
  have hq1 : q - 1 + 1 = q := Nat.sub_add_cancel hq
  have h2q : 2 * q - 1 + 1 = 2 * q := Nat.sub_add_cancel (by omega)
  rw [hq1, h2q]
  have hprod : (q - 1) * q <= (2 * q - 1) * (2 * q) := by
    apply Nat.mul_le_mul
    · omega
    · omega
  have hpoly :
      (2 * q - 1) * (2 * q) + q =
        3 * q * q + (q - 1) * q := by
    nlinarith [hq1]
  omega

theorem bitCost_as_tri_gap (m w : Nat) (hm : 1 <= m) :
    bitCost m w =
      (tri (2 * (2 ^ (m - 1)) - 1) - tri (2 ^ (m - 1) - 1)) * w := by
  have hpow : 2 ^ m = 2 * (2 ^ (m - 1)) := by
    have hmEq : m = (m - 1) + 1 := by omega
    calc
      2 ^ m = 2 ^ ((m - 1) + 1) := congrArg (fun q : Nat => 2 ^ q) hmEq
      _ = 2 * (2 ^ (m - 1)) := by rw [pow_succ]; ring
  unfold bitCost cumCell
  rw [hpow, Nat.sub_mul]

/-- Law 8 exact subtraction-free marginal-bit identity. -/
theorem L8_bitcost_exact (m w : Nat) (hm : 1 <= m) :
    2 * bitCost m w + w * 2 ^ (m - 1) =
      3 * w * 4 ^ (m - 1) := by
  rw [bitCost_as_tri_gap m w hm, four_pow_eq_two_pow_sq]
  have hq : 1 <= 2 ^ (m - 1) := Nat.one_le_pow _ _ (by decide)
  have hgap := two_tri_gap (2 ^ (m - 1)) hq
  nlinarith

/-- Law 8 lower bound: each new bit costs at least a geometric carrier block. -/
theorem L8_bitcost_lower (m w : Nat) (hm : 1 <= m) :
    w * 4 ^ (m - 1) <= bitCost m w := by
  have hexact := L8_bitcost_exact m w hm
  rw [four_pow_eq_two_pow_sq] at hexact ⊢
  have hq : 1 <= 2 ^ (m - 1) := Nat.one_le_pow _ _ (by decide)
  nlinarith

/-- Law 8 projection comparison: the binary counter fits and each register bit costs one bit. -/
theorem L8_projection_comparison (k : Nat) :
    k < 2 ^ projBits k ∧ projectionBitCost = 1 := by
  constructor
  · exact Nat.lt_pow_succ_log_self (by decide : 1 < 2) k
  · rfl

/-- Law 8, clarified alias: the sufficient projection width fits the counter. -/
theorem L8_sufficientProjection_comparison (k : Nat) :
    k < 2 ^ sufficientProjectionBits k ∧ projectionBitCost = 1 := by
  simpa [sufficientProjectionBits] using L8_projection_comparison k

def decodeWith (ib depth : Nat) : SchemaTerm -> Option (Nat × Nat × Nat)
  | .base ia => some (ia, ib, depth)
  | .G (.pay ib') t =>
      if ib' = ib then decodeWith ib (depth + 1) t else none
  | _ => none

def decodeRecord : SchemaTerm -> Option (Nat × Nat × Nat)
  | .G (.pay ib) t => decodeWith ib 1 t
  | _ => none

theorem decodeWith_gPow (ia ib depth k : Nat) :
    decodeWith ib depth (gPow (.pay ib) k (.base ia)) =
      some (ia, ib, depth + k) := by
  induction k generalizing depth with
  | zero => rfl
  | succ k ih =>
      simp only [gPow, decodeWith]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (depth + 1)

/-- A positive-depth canonical `orbitState` record decodes to its input tuple. -/
theorem L9_decode_correct (ia ib k : Nat) (hk : 1 <= k) :
    decodeRecord (orbitState (.base ia) (.pay ib) k (k + 1)) =
      some (ia, ib, k) := by
  cases k with
  | zero => omega
  | succ k =>
      rw [orbitState, if_neg (by omega)]
      simp only [gPow, decodeRecord]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        decodeWith_gPow ia ib 1 k

/-- Equality of two positive-depth canonical `orbitState` records implies equality of their base,
payload, and depth parameters. -/
theorem L9_terminal_injective
    (ia ib k ia' ib' k' : Nat) (hk : 1 <= k) (hk' : 1 <= k')
    (hEq : orbitState (.base ia) (.pay ib) k (k + 1) =
      orbitState (.base ia') (.pay ib') k' (k' + 1)) :
    ia = ia' ∧ ib = ib' ∧ k = k' := by
  have hdecode := congrArg decodeRecord hEq
  rw [L9_decode_correct ia ib k hk, L9_decode_correct ia' ib' k' hk'] at hdecode
  simpa using hdecode

/-- Law 9 boundary case: at depth zero the unused payload is absent from the record. -/
theorem L9_zero_depth_payload_absent (ia ib : Nat) :
    decodeRecord (orbitState (.base ia) (.pay ib) 0 1) = none := by
  rfl

/-- Law 9 capstone, legacy name: exact terminal decoding coexists with quadratic confessed mass.

Despite the historical name, this is not a claim of zero information cost. It states that the terminal
record decodes exactly while the confessed payload mass satisfies the quadratic lower bound. -/
theorem L9_zero_bit_confession (ia ib k beta : Nat) (hk : 1 <= k) :
    decodeRecord (orbitState (.base ia) (.pay ib) k (k + 1)) =
        some (ia, ib, k) ∧
      k * k * beta <= 2 * conMassPayManuscript k beta :=
  ⟨L9_decode_correct ia ib k hk, (L4_dominance_ratio k beta).1⟩

/-- Clarified Law 9 name: terminal decoding plus the confessed-mass lower bound. -/
theorem L9_terminal_decode_with_confession_mass (ia ib k beta : Nat) (hk : 1 <= k) :
    decodeRecord (orbitState (.base ia) (.pay ib) k (k + 1)) =
        some (ia, ib, k) ∧
      k * k * beta <= 2 * conMassPayManuscript k beta :=
  L9_zero_bit_confession ia ib k beta hk

theorem sample_bitCost_one : bitCost 1 3 = 3 := by decide

theorem sample_bitCost_two : bitCost 2 3 = 15 := by decide

theorem sample_decode :
    decodeRecord (orbitState (.base 2) (.pay 7) 3 4) = some (2, 7, 3) := by decide

/-- Concrete negative witness: inconsistent frame payloads are rejected. -/
theorem inconsistent_payload_record_rejected :
    decodeRecord (.G (.pay 1) (.G (.pay 2) (.base 0))) = none := by decide

end OperatorKO7.Meta.Recursor.GaugeCost
