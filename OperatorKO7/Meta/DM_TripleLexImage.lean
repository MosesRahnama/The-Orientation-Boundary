import OperatorKO7.Meta.DM_OrderType_LowerBound

namespace OperatorKO7.MetaDM

open Ordinal
open OperatorKO7.MetaCM

/-- The calibrated binary-phase carrier behind the explicit triple-lex image. -/
structure FullTripleLexCarrier where
  phase : Nat
  dmComponent : Multiset Nat
  tauComponent : Nat
  phase_le_one : phase ≤ 1

namespace FullTripleLexCarrier

/-- Forget the binary-phase carrier into the ambient `Lex3c` tuple. -/
@[simp] def toLex3cTuple (x : FullTripleLexCarrier) : Nat × (Multiset Nat × Nat) :=
  (x.phase, (x.dmComponent, x.tauComponent))

end FullTripleLexCarrier

/-- The explicit ordinal image of the calibrated binary-phase triple-lex carrier. -/
def FullTripleLexImage (α : Ordinal.{0}) : Prop :=
  ∃ x : FullTripleLexCarrier, lex3cToOrd x.toLex3cTuple = α

/-- Every calibrated binary-phase triple lies below `ω^ω * 2`. -/
theorem full_triple_lex_image_upper_bound (x : FullTripleLexCarrier) :
    lex3cToOrd x.toLex3cTuple < ((ω : Ordinal) ^ (ω : Ordinal)) * (2 : Nat) :=
  lex3cToOrd_lt_opow_omega_mul_two x.phase_le_one

/-- The phase-`0` slice is exactly the inner `lexDMToOrd` block. -/
theorem full_triple_lex_dm_component_embeds (κ : Multiset Nat) (τ : Nat) :
    lex3cToOrd
        (FullTripleLexCarrier.toLex3cTuple
          { phase := 0, dmComponent := κ, tauComponent := τ, phase_le_one := by decide }) =
      lexDMToOrd (κ, τ) := by
  simp [FullTripleLexCarrier.toLex3cTuple, lex3cToOrd]

/-- The inner `lexDMToOrd` block is surjective on ordinals below `ω^ω`. -/
theorem lexDMToOrd_surjective_lt_opow_omega
    {α : Ordinal.{0}} (hα : α < (ω : Ordinal) ^ (ω : Ordinal)) :
    ∃ p : Multiset Nat × Nat, lexDMToOrd p = α := by
  let β : Ordinal := α / (ω : Ordinal)
  let nOrd : Ordinal := α % (ω : Ordinal)
  have hnOrd : nOrd < (ω : Ordinal) := by
    exact Ordinal.mod_lt α Ordinal.omega0_pos.ne'
  obtain ⟨n, hn⟩ := Ordinal.lt_omega0.1 hnOrd
  have hβleMul : β ≤ (ω : Ordinal) * β := by
    simpa [β] using (Ordinal.le_mul_right (a := β) (b := (ω : Ordinal)) Ordinal.omega0_pos)
  have hMulLeα : (ω : Ordinal) * β ≤ α := by
    simpa [β] using (Ordinal.mul_div_le α (ω : Ordinal))
  have hβ : β < (ω : Ordinal) ^ (ω : Ordinal) :=
    lt_of_le_of_lt (hβleMul.trans hMulLeα) hα
  rcases CNFωω.dmOrdEmbed_surjective_lt_opow_omega β hβ with ⟨m, hm⟩
  refine ⟨(m, n), ?_⟩
  calc
    lexDMToOrd (m, n) = (ω : Ordinal) * dmOrdEmbed m + (n : Ordinal) := by
      rfl
    _ = (ω : Ordinal) * β + nOrd := by rw [hm, hn]
    _ = α := by
      simpa [β, nOrd] using (Ordinal.div_add_mod α (ω : Ordinal))

/-- Every ordinal below `ω^ω` appears in the phase-`0` slice. -/
theorem full_triple_lex_phase_zero_family
    {α : Ordinal.{0}} (hα : α < (ω : Ordinal) ^ (ω : Ordinal)) :
    ∃ x : FullTripleLexCarrier, x.phase = 0 ∧ lex3cToOrd x.toLex3cTuple = α := by
  rcases lexDMToOrd_surjective_lt_opow_omega hα with ⟨⟨κ, τ⟩, hOrd⟩
  refine ⟨{ phase := 0, dmComponent := κ, tauComponent := τ, phase_le_one := by decide }, rfl, ?_⟩
  simpa [FullTripleLexCarrier.toLex3cTuple, lex3cToOrd] using hOrd

/-- Every ordinal in the second `ω^ω` block appears in the phase-`1` slice. -/
theorem full_triple_lex_phase_one_family
    {α : Ordinal.{0}} (hα : α < (ω : Ordinal) ^ (ω : Ordinal)) :
    ∃ x : FullTripleLexCarrier,
      x.phase = 1 ∧ lex3cToOrd x.toLex3cTuple = ((ω : Ordinal) ^ (ω : Ordinal)) + α := by
  rcases lexDMToOrd_surjective_lt_opow_omega hα with ⟨⟨κ, τ⟩, hOrd⟩
  refine ⟨{ phase := 1, dmComponent := κ, tauComponent := τ, phase_le_one := by decide }, rfl, ?_⟩
  simpa [FullTripleLexCarrier.toLex3cTuple, lex3cToOrd] using hOrd

/-- The phase-`0` family lies in the explicit triple-lex image. -/
theorem full_triple_lex_phase_zero_in_image
    {α : Ordinal.{0}} (hα : α < (ω : Ordinal) ^ (ω : Ordinal)) :
    FullTripleLexImage α := by
  rcases full_triple_lex_phase_zero_family hα with ⟨x, _, hx⟩
  exact ⟨x, hx⟩

/-- The phase-`1` family lies in the explicit triple-lex image. -/
theorem full_triple_lex_phase_one_in_image
    {α : Ordinal.{0}} (hα : α < (ω : Ordinal) ^ (ω : Ordinal)) :
    FullTripleLexImage (((ω : Ordinal) ^ (ω : Ordinal)) + α) := by
  rcases full_triple_lex_phase_one_family hα with ⟨x, _, hx⟩
  exact ⟨x, hx⟩

end OperatorKO7.MetaDM
