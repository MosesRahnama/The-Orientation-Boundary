import OperatorKO7.Meta.StepDuplicatingSchema
import Mathlib.SetTheory.Ordinal.NaturalOps
import Mathlib.SetTheory.Ordinal.Arithmetic

set_option autoImplicit false

/-!
# Schema barriers over ordered carriers

Tier 1: partially ordered commutative monoid, `eval x + eval y ≤ eval (wrap x y)`.
If some term meets `w_succ`, the duplicating step cannot strictly decrease eval.
The premise is automatic when the base weight is nonnegative and is necessary
over arbitrary ordered groups, as witnessed by the strictly negative integers.

Tier 2: arbitrary preorder, wrap-subterm `eval y < eval (wrap x y)`, successor
transparent at base. The Nat proof is replayed with no arithmetic.

Both instantiate at `NatOrdinal` (ordinals with Hessenberg addition `♯`, a
well-order). Without transparency, the affine reading `[recur](b,s,n) = ω·n ⊕ s ⊕ b`
orients at finite payloads and fails once the payload is `ω`.

Trust: kernel-only. No `sorry`/`admit`/`axiom`/`native_decide`.
-/

open Ordinal
open OperatorKO7.StepDuplicating

namespace OperatorKO7.StepDuplicating.StepDuplicatingSchema

variable {S : StepDuplicatingSchema} {α : Type*}

structure OrderedAdditiveMeasure (S : StepDuplicatingSchema) (α : Type*)
    [AddCommMonoid α] [PartialOrder α] [IsOrderedAddMonoid α] where
  eval : S.T → α
  w_base : α
  w_succ : α
  w_recur : α
  eval_base : eval S.base = w_base
  eval_succ : ∀ t, eval (S.succ t) = eval t + w_succ
  eval_wrap_ge : ∀ x y, eval x + eval y ≤ eval (S.wrap x y)
  eval_recur : ∀ b s n, eval (S.recur b s n) = w_recur + eval b + eval s + eval n

theorem no_ordered_additive_orients_dup_step
    [AddCommMonoid α] [PartialOrder α] [IsOrderedAddMonoid α]
    (M : OrderedAdditiveMeasure S α)
    (hatt : ∃ t : S.T, M.w_succ ≤ M.eval t) :
    ¬ (∀ (b s n : S.T),
      M.eval (S.wrap s (S.recur b s n)) < M.eval (S.recur b s (S.succ n))) := by
  intro h
  rcases hatt with ⟨s, hs⟩
  have hspec := h S.base s S.base
  have hge := M.eval_wrap_ge s (S.recur S.base s S.base)
  have inner :
      M.eval (S.recur S.base s S.base) = M.w_recur + M.w_base + M.eval s + M.w_base := by
    simp [M.eval_recur, M.eval_base]
  have source :
      M.eval (S.recur S.base s (S.succ S.base)) =
        M.w_recur + M.w_base + M.eval s + (M.w_base + M.w_succ) := by
    simp [M.eval_recur, M.eval_base, M.eval_succ]
  have hsum : M.eval s + (M.w_recur + M.w_base + M.eval s + M.w_base) ≤
      M.eval (S.wrap s (S.recur S.base s S.base)) := by
    simpa [inner] using hge
  have hchain :
      M.w_recur + M.w_base + M.eval s + M.w_base + M.w_succ ≤
        M.eval s + (M.w_recur + M.w_base + M.eval s + M.w_base) := by
    have hs' : M.eval s + M.w_succ ≤ M.eval s + M.eval s := add_le_add_left hs (M.eval s)
    calc
      M.w_recur + M.w_base + M.eval s + M.w_base + M.w_succ
          = M.w_recur + M.w_base + M.w_base + (M.eval s + M.w_succ) := by
            simp [add_assoc, add_left_comm, add_comm]
      _ ≤ M.w_recur + M.w_base + M.w_base + (M.eval s + M.eval s) :=
        add_le_add_left hs' _
      _ = M.eval s + (M.w_recur + M.w_base + M.eval s + M.w_base) := by
            simp [add_assoc, add_left_comm, add_comm]
  have hge' : M.eval (S.recur S.base s (S.succ S.base)) ≤
      M.eval (S.wrap s (S.recur S.base s S.base)) := by
    have hsrc :
        M.eval (S.recur S.base s (S.succ S.base)) =
          M.w_recur + M.w_base + M.eval s + M.w_base + M.w_succ := by
      simpa [add_assoc] using source
    exact le_trans (le_of_eq hsrc) (le_trans hchain hsum)
  exact not_lt_of_ge hge' hspec

/-- A nonnegative base makes the successor weight attainable at `succ base`. -/
theorem ordered_additive_succ_attained_of_base_nonneg
    [AddCommMonoid α] [PartialOrder α] [IsOrderedAddMonoid α]
    (M : OrderedAdditiveMeasure S α) (hbase : 0 ≤ M.w_base) :
    ∃ t : S.T, M.w_succ ≤ M.eval t := by
  refine ⟨S.succ S.base, ?_⟩
  rw [M.eval_succ, M.eval_base]
  simpa [zero_add] using add_le_add_right hbase M.w_succ

/-- Unconditional additive barrier whenever the base weight is nonnegative. -/
theorem no_ordered_additive_orients_dup_step_of_base_nonneg
    [AddCommMonoid α] [PartialOrder α] [IsOrderedAddMonoid α]
    (M : OrderedAdditiveMeasure S α) (hbase : 0 ≤ M.w_base) :
    ¬ (∀ (b s n : S.T),
      M.eval (S.wrap s (S.recur b s n)) < M.eval (S.recur b s (S.succ n))) :=
  no_ordered_additive_orients_dup_step M
    (ordered_additive_succ_attained_of_base_nonneg M hbase)

structure OrderedCompositionalMeasure (S : StepDuplicatingSchema) (α : Type*)
    [Preorder α] where
  eval : S.T → α
  c_base : α
  c_succ : α → α
  c_wrap : α → α → α
  c_recur : α → α → α → α
  eval_base : eval S.base = c_base
  eval_succ : ∀ t, eval (S.succ t) = c_succ (eval t)
  eval_wrap : ∀ x y, eval (S.wrap x y) = c_wrap (eval x) (eval y)
  eval_recur : ∀ b s n, eval (S.recur b s n) = c_recur (eval b) (eval s) (eval n)
  wrap_subterm2 : ∀ x y, eval y < eval (S.wrap x y)

theorem no_ordered_compositional_orients_dup_step_transparent
    [Preorder α] (CM : OrderedCompositionalMeasure S α)
    (h_transparent : CM.c_succ CM.c_base = CM.c_base) :
    ¬ (∀ (b s n : S.T),
      CM.eval (S.wrap s (S.recur b s n)) < CM.eval (S.recur b s (S.succ n))) := by
  intro h
  have hspec := h S.base S.base S.base
  have hright :
      CM.eval (S.recur S.base S.base (S.succ S.base)) =
        CM.eval (S.recur S.base S.base S.base) := by
    simp [CM.eval_recur, CM.eval_succ, CM.eval_base, h_transparent]
  have hsub := CM.wrap_subterm2 S.base (S.recur S.base S.base S.base)
  have : CM.eval (S.wrap S.base (S.recur S.base S.base S.base)) <
      CM.eval (S.recur S.base S.base S.base) := by
    simpa [hright] using hspec
  exact lt_asymm hsub this

/-! ## Necessity of the additive attainment premise -/

/-- The term carrier of strictly negative integers. -/
abbrev StrictlyNegativeInt := {z : Int // z < 0}

/-- A duplicating schema closed inside the strictly negative integers. -/
def negativeIntSchema : StepDuplicatingSchema where
  T := StrictlyNegativeInt
  base := ⟨-1, by omega⟩
  succ := id
  wrap := fun x y => ⟨x.1 + y.1, by omega⟩
  recur := fun b s n => ⟨b.1 + s.1 + n.1, by omega⟩

/-- The identity-valued additive measure on the negative carrier. -/
def negativeIntOrderedAdditiveMeasure :
    OrderedAdditiveMeasure negativeIntSchema Int where
  eval := fun t => t.1
  w_base := -1
  w_succ := 0
  w_recur := 0
  eval_base := rfl
  eval_succ := fun _ => by simp [negativeIntSchema]
  eval_wrap_ge := fun _ _ => by simp [negativeIntSchema]
  eval_recur := fun _ _ _ => by simp [negativeIntSchema]

/-- Every instance of the duplicating step strictly decreases in the negative
integer model. -/
theorem negativeInt_additive_orients_dup_step :
    ∀ b s n : negativeIntSchema.T,
      negativeIntOrderedAdditiveMeasure.eval
          (negativeIntSchema.wrap s (negativeIntSchema.recur b s n)) <
        negativeIntOrderedAdditiveMeasure.eval
          (negativeIntSchema.recur b s (negativeIntSchema.succ n)) := by
  intro b s n
  change s.1 + (b.1 + s.1 + n.1) < b.1 + s.1 + n.1
  have hs := s.2
  omega

/-- No negative carrier term attains the zero successor weight. -/
theorem negativeInt_succ_weight_not_attained :
    ¬ ∃ t : negativeIntSchema.T,
      negativeIntOrderedAdditiveMeasure.w_succ ≤ negativeIntOrderedAdditiveMeasure.eval t := by
  rintro ⟨t, ht⟩
  exact (not_le_of_gt t.2) ht

/-- The attainment hypothesis in the arbitrary ordered-group theorem is
logically necessary: without it, a live additive model orients every instance. -/
theorem ordered_additive_attainment_hypothesis_necessary :
    (∀ b s n : negativeIntSchema.T,
      negativeIntOrderedAdditiveMeasure.eval
          (negativeIntSchema.wrap s (negativeIntSchema.recur b s n)) <
        negativeIntOrderedAdditiveMeasure.eval
          (negativeIntSchema.recur b s (negativeIntSchema.succ n))) ∧
    ¬ ∃ t : negativeIntSchema.T,
      negativeIntOrderedAdditiveMeasure.w_succ ≤ negativeIntOrderedAdditiveMeasure.eval t :=
  ⟨negativeInt_additive_orients_dup_step, negativeInt_succ_weight_not_attained⟩

/-! ## Ordinal-valued instances

`StepDuplicatingSchema.T` is universe 0, so the schema layer uses `Nat`.
Eval lands in `NatOrdinal` (Hessenberg `♯`, `WellFoundedLT`). The affine
non-example is stated directly on `NatOrdinal`.
-/

open NaturalOps

noncomputable def natCastNatOrdinal (n : Nat) : NatOrdinal := n

def natAddSchema : StepDuplicatingSchema where
  T := Nat
  base := 0
  succ := Nat.succ
  wrap := Nat.add
  recur := fun b s n => b + s + n

noncomputable def natOrdinalAdditiveMeasure :
    OrderedAdditiveMeasure natAddSchema NatOrdinal where
  eval := fun n => natCastNatOrdinal n
  w_base := 0
  w_succ := 1
  w_recur := 0
  eval_base := rfl
  eval_succ := fun (t : Nat) => Nat.cast_succ t
  eval_wrap_ge := fun (x y : Nat) => le_of_eq (Nat.cast_add x y).symm
  eval_recur := fun (b s n : Nat) => by
    simp [natAddSchema, natCastNatOrdinal, Nat.cast_add]

theorem natOrdinal_w_succ_attained :
    ∃ t : natAddSchema.T, natOrdinalAdditiveMeasure.w_succ ≤
      natOrdinalAdditiveMeasure.eval t :=
  ⟨(1 : Nat), by simp [natOrdinalAdditiveMeasure, natCastNatOrdinal]⟩

theorem no_natOrdinal_additive_orients_dup_step :
    ¬ (∀ (b s n : natAddSchema.T),
      natOrdinalAdditiveMeasure.eval
          (natAddSchema.wrap s (natAddSchema.recur b s n)) <
        natOrdinalAdditiveMeasure.eval
          (natAddSchema.recur b s (natAddSchema.succ n))) :=
  no_ordered_additive_orients_dup_step natOrdinalAdditiveMeasure
    natOrdinal_w_succ_attained

def natTransparentSchema : StepDuplicatingSchema where
  T := Nat
  base := 0
  succ := fun t => t
  wrap := fun _x y => y + 1
  recur := fun b s n => b + s + n

noncomputable def natOrdinalTransparentMeasure :
    OrderedCompositionalMeasure natTransparentSchema NatOrdinal where
  eval := fun n => natCastNatOrdinal n
  c_base := 0
  c_succ := id
  c_wrap := fun _x y => y + 1
  c_recur := fun b s n => b + s + n
  eval_base := rfl
  eval_succ := fun (_ : Nat) => rfl
  eval_wrap := fun (_ y : Nat) => Nat.cast_succ y
  eval_recur := fun (b s n : Nat) => by
    simp [natTransparentSchema, natCastNatOrdinal, Nat.cast_add]
  wrap_subterm2 := fun (_x y : Nat) => by
    simp [natTransparentSchema, natCastNatOrdinal, Nat.cast_succ]

theorem no_natOrdinal_compositional_orients_dup_step_transparent :
    ¬ (∀ (b s n : natTransparentSchema.T),
      natOrdinalTransparentMeasure.eval
          (natTransparentSchema.wrap s (natTransparentSchema.recur b s n)) <
        natOrdinalTransparentMeasure.eval
          (natTransparentSchema.recur b s (natTransparentSchema.succ n))) :=
  no_ordered_compositional_orients_dup_step_transparent
    natOrdinalTransparentMeasure rfl

/-! Affine ordinal reading without transparency: `[recur](b,s,n) = ω·n ⊕ s ⊕ b`. -/

noncomputable def omegaNadd (n : NatOrdinal) : NatOrdinal :=
  Ordinal.toNatOrdinal (ω * n.toOrdinal)

theorem omegaNadd_nat (m : ℕ) :
    omegaNadd (m : NatOrdinal) = Ordinal.toNatOrdinal (ω * (m : Ordinal)) := by
  simp [omegaNadd, NatOrdinal.toOrdinal_natCast]

theorem omegaNadd_zero : omegaNadd 0 = 0 := by
  simp [omegaNadd]

theorem omegaNadd_one : omegaNadd 1 = Ordinal.toNatOrdinal ω := by
  simp [omegaNadd, NatOrdinal.toOrdinal_one]

theorem ordinal_affine_orients_finite_payload (k m : ℕ) :
    ((k : NatOrdinal) + (omegaNadd (m : NatOrdinal) + (k : NatOrdinal))) <
      omegaNadd ((m : NatOrdinal) + 1) + (k : NatOrdinal) := by
  refine (NatOrdinal.toOrdinal.lt_iff_lt).mp ?_
  have hsucc : ((m : NatOrdinal) + 1).toOrdinal = (m + 1 : Ordinal) := by
    rw [← Nat.cast_succ m, NatOrdinal.toOrdinal_natCast, Nat.cast_succ]
  have hL :
      ((k : NatOrdinal) + (omegaNadd (m : NatOrdinal) + (k : NatOrdinal))).toOrdinal =
        (ω * (m : Ordinal)) + (2 * k : ℕ) := by
    have hk2 : ((k : NatOrdinal) + (k : NatOrdinal)).toOrdinal = ((2 * k : ℕ) : Ordinal) := by
      calc
        ((k : NatOrdinal) + (k : NatOrdinal)).toOrdinal
            = (k : NatOrdinal).toOrdinal ♯ (k : NatOrdinal).toOrdinal := rfl
        _ = (k : Ordinal) ♯ (k : Ordinal) := by simp [NatOrdinal.toOrdinal_natCast]
        _ = (k : Ordinal) + (k : Ordinal) := nadd_nat (k : Ordinal) k
        _ = ((2 * k : ℕ) : Ordinal) := by simp [two_mul, Nat.cast_add]
    have hωm : (omegaNadd (m : NatOrdinal)).toOrdinal = ω * (m : Ordinal) := by
      simp [omegaNadd, NatOrdinal.toOrdinal_natCast]
    have hcomm :
        ((k : NatOrdinal) + (omegaNadd (m : NatOrdinal) + (k : NatOrdinal))) =
          omegaNadd (m : NatOrdinal) + ((k : NatOrdinal) + (k : NatOrdinal)) := by
      rw [add_comm (k : NatOrdinal), add_assoc]
    rw [hcomm]
    have hnadd :
        (omegaNadd (m : NatOrdinal) + ((k : NatOrdinal) + (k : NatOrdinal))).toOrdinal =
          (omegaNadd (m : NatOrdinal)).toOrdinal ♯
            ((k : NatOrdinal) + (k : NatOrdinal)).toOrdinal :=
      rfl
    rw [hnadd, hωm, hk2, nadd_nat]
  have hR :
      (omegaNadd ((m : NatOrdinal) + 1) + (k : NatOrdinal)).toOrdinal =
        ω * (m + 1 : Ordinal) + (k : Ordinal) := by
    have hω : (omegaNadd ((m : NatOrdinal) + 1)).toOrdinal = ω * (m + 1 : Ordinal) := by
      unfold omegaNadd
      rw [Ordinal.toNatOrdinal_toOrdinal, hsucc]
    have hnadd :
        (omegaNadd ((m : NatOrdinal) + 1) + (k : NatOrdinal)).toOrdinal =
          (omegaNadd ((m : NatOrdinal) + 1)).toOrdinal ♯ (k : NatOrdinal).toOrdinal :=
      rfl
    rw [hnadd, hω, NatOrdinal.toOrdinal_natCast, nadd_nat]
  rw [hL, hR, mul_add, mul_one]
  have hfin : ((2 * k : ℕ) : Ordinal) < ω := nat_lt_omega0 (2 * k)
  have hleft : ω * (m : Ordinal) + (2 * k : ℕ) < ω * (m : Ordinal) + ω :=
    add_lt_add_left hfin _
  have hright : ω * (m : Ordinal) + ω ≤ ω * (m : Ordinal) + ω + (k : Ordinal) :=
    le_self_add
  exact lt_of_lt_of_le hleft hright

theorem ordinal_affine_fails_at_omega_payload :
    ¬ (Ordinal.toNatOrdinal ω + (omegaNadd 0 + Ordinal.toNatOrdinal ω) <
        omegaNadd (0 + 1) + Ordinal.toNatOrdinal ω) := by
  intro h
  have h0 : omegaNadd 0 = 0 := omegaNadd_zero
  have h1 : omegaNadd (0 + 1) = Ordinal.toNatOrdinal ω := by
    simp [omegaNadd_one]
  rw [h0, zero_add, h1] at h
  exact lt_irrefl _ h

def ordinal_affine_transparency_essential :
    (∀ k m : ℕ,
      ((k : NatOrdinal) + (omegaNadd (m : NatOrdinal) + (k : NatOrdinal))) <
        omegaNadd ((m : NatOrdinal) + 1) + (k : NatOrdinal)) ∧
    ¬ (Ordinal.toNatOrdinal ω + (omegaNadd 0 + Ordinal.toNatOrdinal ω) <
        omegaNadd (0 + 1) + Ordinal.toNatOrdinal ω) :=
  ⟨fun k m => ordinal_affine_orients_finite_payload k m, ordinal_affine_fails_at_omega_payload⟩

end OperatorKO7.StepDuplicating.StepDuplicatingSchema
