import OperatorKO7.Meta.DistinctionBoundary.Quantitative.Core

/-!
# Refusal-certificate coding floor

The theorem is purely finite: distinguishable refused alternatives encoded by
fixed-length binary words require at least the ceiling base-two logarithm of the
number of alternatives. No KO7 term or rewrite relation appears.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.DistinctionBoundary.Quantitative

/-- A fixed-length binary certificate. -/
abbrev BitWord (L : Nat) := Fin L -> Bool

theorem bitWord_card (L : Nat) : Fintype.card (BitWord L) = 2 ^ L := by
  simp [BitWord]

/-- An injective fixed-length certificate map can distinguish at most `2^L`
alternatives. -/
theorem injective_certificate_card_bound {E : Type} [Fintype E]
    (L : Nat) (encode : E -> BitWord L) (hencode : Function.Injective encode) :
    Fintype.card E <= 2 ^ L := by
  rw [← bitWord_card L]
  exact Fintype.card_le_of_injective encode hencode

/-- Exact fixed-length bit floor, expressed with Mathlib's upper natural
logarithm. -/
theorem injective_certificate_clog_floor {E : Type} [Fintype E]
    (L : Nat) (encode : E -> BitWord L) (hencode : Function.Injective encode) :
    Nat.clog 2 (Fintype.card E) <= L := by
  rw [← Nat.le_pow_iff_clog_le (by norm_num : 1 < (2 : Nat))]
  exact injective_certificate_card_bound L encode hencode

/-- If the available word space is smaller than the alternative set, no
injective certificate exists. -/
theorem no_injective_certificate_of_pow_lt {E : Type} [Fintype E]
    (L : Nat) (hsmall : 2 ^ L < Fintype.card E) :
    Not (exists encode : E -> BitWord L, Function.Injective encode) := by
  rintro ⟨encode, hencode⟩
  exact (not_le_of_gt hsmall) (injective_certificate_card_bound L encode hencode)

/-- For an `m`-way fork licensed to one branch, the `m-1` refused alternatives
require at least `clog 2 (m-1)` fixed-length bits whenever they are encoded
injectively. -/
theorem refused_branch_certificate_floor (m L : Nat)
    (encode : Fin (m - 1) -> BitWord L) (hencode : Function.Injective encode) :
    Nat.clog 2 (m - 1) <= L := by
  simpa using injective_certificate_clog_floor L encode hencode

/-! ## Computing positive witness and concrete negative -/

/-- The two-bit binary representation of a number in `Fin 4`. -/
def codeFin4 (i : Fin 4) (j : Fin 2) : Bool :=
  if j.val = 0 then decide (i.val % 2 = 1) else decide (2 <= i.val)

theorem codeFin4_injective : Function.Injective codeFin4 := by
  intro a b h
  fin_cases a <;> fin_cases b
  all_goals try rfl
  all_goals
    exfalso
    have h0 := congrFun h (0 : Fin 2)
    have h1 := congrFun h (1 : Fin 2)
    norm_num [codeFin4] at h0 h1

theorem four_alternatives_fit_two_bits :
    exists encode : Fin 4 -> BitWord 2, Function.Injective encode :=
  ⟨codeFin4, codeFin4_injective⟩

theorem four_alternatives_do_not_fit_one_bit :
    Not (exists encode : Fin 4 -> BitWord 1, Function.Injective encode) := by
  apply no_injective_certificate_of_pow_lt (E := Fin 4) 1
  norm_num

theorem four_alternative_floor_is_two : Nat.clog 2 4 = 2 := by
  norm_num [Nat.clog]

#print axioms injective_certificate_card_bound
#print axioms injective_certificate_clog_floor
#print axioms no_injective_certificate_of_pow_lt
#print axioms refused_branch_certificate_floor
#print axioms codeFin4_injective
#print axioms four_alternatives_do_not_fit_one_bit

end OperatorKO7.Meta.DistinctionBoundary.Quantitative
