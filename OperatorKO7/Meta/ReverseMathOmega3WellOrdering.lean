import OperatorKO7.Meta.ReverseMathSupport
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.Ordinal.Exponential

/-!
# Ambient `ω^3` order and descent facts

This module defines the ordinal `ω^3`, its canonical carrier, and proofs in
Lean's ambient logic that the carrier is well founded and has order type `ω^3`.
It also transports decreasing ranks into well-foundedness and proves that every
ordinal below `ω^3` occurs as a canonical rank.

The formal surface contains neither a deductive presentation of `RCA₀` nor an
Arts-Giesl or size-change-termination adapter. Reverse-mathematical strength
calibration therefore requires additional syntax, provability, and transport
theorems. The results below are ambient ordinal facts used as inputs to such a
future bridge.
-/

namespace OperatorKO7.ReverseMathOmega3

open Ordinal
open OperatorKO7.ReverseMathSupport

/-- The calibration ordinal `ω^3`, reusing the existing paper-facing constant. -/
noncomputable def omega3 : Ordinal.{0} := omegaPowThree

@[simp] theorem omega3_def : omega3 = (ω : Ordinal) ^ (3 : Ordinal) := rfl

/-- `ω^3` is strictly positive. -/
theorem omega3_pos : 0 < omega3 := by
  dsimp [omega3, omegaPowThree]
  exact Ordinal.opow_pos (3 : Ordinal) Ordinal.omega0_pos

/-- `ω^3` sits strictly below `ε₀` (reuse of the mechanized support fact). -/
theorem omega3_lt_epsilon0 : omega3 < ε₀ :=
  omegaPowThree_lt_epsilon0

/-! ## Canonical `ω^3` well order -/

/-- Carrier obtained from `ω^3` by `Ordinal.toType`. -/
abbrev Omega3Carrier : Type := omega3.toType

/-- The strict order on the canonical carrier of `ω^3` is well founded in
Lean's ambient logic. -/
theorem wo_omega3 :
    WellFounded ((· < ·) : Omega3Carrier → Omega3Carrier → Prop) :=
  (inferInstanceAs (IsWellOrder Omega3Carrier (· < ·))).wf

/-- The canonical carrier's order type equals `ω^3`. -/
theorem omega3_orderType :
    Ordinal.type ((· < ·) : Omega3Carrier → Omega3Carrier → Prop) = omega3 :=
  Ordinal.type_toType omega3

/-! ## Descent soundness -/

/-- **Descent soundness.** If a reduction relation `R` on `α` admits a measure
`μ : α → Ordinal` that strictly decreases along each step (`R a b → μ b < μ a`),
then `R` terminates: the reversed relation `fun a b => R b a` is well-founded
(the repo's strong-normalization convention, matching `WellFounded (fun a b => Step b a)`).

This theorem is an ambient ordinal descent principle. Method-specific
termination requires an adapter supplying the relation and rank. -/
theorem descent_sound {α : Type _} (μ : α → Ordinal)
    {R : α → α → Prop} (hdesc : ∀ a b, R a b → μ b < μ a) :
    WellFounded (fun a b => R b a) := by
  have hsub : Subrelation (fun a b => R b a) (InvImage (· < ·) μ) := by
    intro a b hab
    exact hdesc b a hab
  exact Subrelation.wf hsub (InvImage.wf μ wellFounded_lt)

/-- A rank into the canonical `Omega3Carrier` structurally lies below `ω^3`.
Strict decrease along `R` makes the reverse relation well founded. -/
theorem descent_into_omega3_sound {α : Type _} (μ : α → Omega3Carrier)
    {R : α → α → Prop} (hdesc : ∀ a b, R a b → μ b < μ a) :
    WellFounded (fun a b => R b a) := by
  have hsub : Subrelation (fun a b => R b a) (InvImage (· < ·) μ) := by
    intro a b hab
    exact hdesc b a hab
  exact Subrelation.wf hsub (InvImage.wf μ wo_omega3)

/-- Every natural number lies strictly below `ω^3` (since `n < ω = ω^1 ≤ ω^3`).
The base case for the recursor's linear (`ω`) base order living inside `WO(ω^3)`. -/
theorem nat_lt_omega3 (n : Nat) : (n : Ordinal) < omega3 := by
  have h1 : (n : Ordinal) < (ω : Ordinal) := Ordinal.nat_lt_omega0 n
  have h2 : (ω : Ordinal) ≤ omega3 := by
    dsimp [omega3, omegaPowThree]
    calc (ω : Ordinal) = (ω : Ordinal) ^ (1 : Ordinal) := (Ordinal.opow_one _).symm
      _ ≤ (ω : Ordinal) ^ (3 : Ordinal) :=
          Ordinal.opow_le_opow_right Ordinal.omega0_pos (by exact_mod_cast (by norm_num : (1 : Nat) ≤ 3))
  exact lt_of_lt_of_le h1 h2

/-- Embed a natural number as the canonical element with the corresponding
ordinal rank inside `Omega3Carrier`. -/
noncomputable def natRankOmega3 (n : Nat) : Omega3Carrier :=
  Ordinal.enum ((· < ·) : Omega3Carrier → Omega3Carrier → Prop)
    ⟨(n : Ordinal), by
      rw [omega3_orderType]
      exact nat_lt_omega3 n⟩

/-- The canonical natural-number embedding preserves strict order. -/
theorem natRankOmega3_strictMono : StrictMono natRankOmega3 := by
  intro a b hab
  rw [← Ordinal.typein_lt_typein
    ((· < ·) : Omega3Carrier → Omega3Carrier → Prop)]
  simp only [natRankOmega3, Ordinal.typein_enum]
  exact_mod_cast hab

/-- **Natural-rank termination inside the canonical `ω^3` carrier.**
Any relation `R` carrying a `Nat`-valued measure that strictly decreases along it
is well founded after embedding the measure into `Omega3Carrier`. This theorem
contains no recursor or dependency-pair relation; those require an adapter. -/
theorem nat_measure_terminates_within_omega3 {α : Type _} (μ : α → Nat)
    {R : α → α → Prop} (hdesc : ∀ a b, R a b → μ b < μ a) :
    WellFounded (fun a b => R b a) := by
  refine descent_into_omega3_sound (fun a => natRankOmega3 (μ a)) ?_
  intro a b hab
  exact natRankOmega3_strictMono (hdesc a b hab)

/-! ## Rank surjectivity below `ω^3` -/

/-- Every ordinal strictly below `ω^3` is the rank of an element of the
canonical carrier. The conclusion is surjectivity onto the initial segment
`[0, ω^3)`. -/
theorem omega3_sharp :
    ∀ β : Ordinal, β < omega3 →
      ∃ x : Omega3Carrier, Ordinal.typein ((· < ·) : Omega3Carrier → _ → Prop) x = β := by
  intro β hβ
  have hβ' : β < Ordinal.type ((· < ·) : Omega3Carrier → Omega3Carrier → Prop) := by
    rw [omega3_orderType]; exact hβ
  exact ⟨Ordinal.enum ((· < ·) : Omega3Carrier → _ → Prop) ⟨β, hβ'⟩,
    by simp⟩

/-! ## Theorem-backed `ω^3` calibration witness -/

/-- An order-type-`ω^3` witness: a carrier, its strict order, a proof of
well-foundedness, and an order-type equality. -/
structure OrderTypeOmega3Witness where
  /-- Underlying carrier. -/
  carrier : Type
  /-- Strict order on the carrier. -/
  rel : carrier → carrier → Prop
  /-- The order is well-founded (`WO`). -/
  wf : WellFounded rel
  /-- It is a well-order (linearity + well-foundedness), so `type` is defined. -/
  isWellOrder : IsWellOrder carrier rel
  /-- Its order type equals `ω^3`. -/
  orderType : @Ordinal.type carrier rel isWellOrder = omega3

/-- Canonical witness built from `Omega3Carrier` and its ambient ordinal
theorems. -/
noncomputable def canonicalOmega3Witness : OrderTypeOmega3Witness where
  carrier := Omega3Carrier
  rel := (· < ·)
  wf := wo_omega3
  isWellOrder := inferInstanceAs (IsWellOrder Omega3Carrier (· < ·))
  orderType := omega3_orderType

/-- Project well-foundedness and the order-type equality from a witness. -/
theorem OrderTypeOmega3Witness.supported (W : OrderTypeOmega3Witness) :
    WellFounded W.rel ∧ @Ordinal.type W.carrier W.rel W.isWellOrder = omega3 :=
  ⟨W.wf, W.orderType⟩

/-- Packaged `WO(ω^3)` backing as a single proposition: well-foundedness of the
order type of `ω^3` together with the order-type identity. -/
def WOOmega3Backing : Prop :=
  WellFounded ((· < ·) : Omega3Carrier → Omega3Carrier → Prop)
    ∧ Ordinal.type ((· < ·) : Omega3Carrier → Omega3Carrier → Prop) = omega3

/-- The `WO(ω^3)` backing holds, proven from `wo_omega3` and `omega3_orderType`. -/
theorem wo_omega3_backing : WOOmega3Backing :=
  ⟨wo_omega3, omega3_orderType⟩

end OperatorKO7.ReverseMathOmega3
