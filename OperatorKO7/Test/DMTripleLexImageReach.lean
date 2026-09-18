import OperatorKO7.Meta.DM_TripleLexImage

namespace DMTripleLexImageReach

open Ordinal
open OperatorKO7.MetaDM

#check FullTripleLexCarrier
#check FullTripleLexCarrier.toLex3cTuple
#check FullTripleLexImage
#check full_triple_lex_image_upper_bound
#check full_triple_lex_dm_component_embeds
#check lexDMToOrd_surjective_lt_opow_omega
#check full_triple_lex_phase_zero_family
#check full_triple_lex_phase_one_family
#check full_triple_lex_phase_zero_in_image
#check full_triple_lex_phase_one_in_image

example (κ : Multiset Nat) (τ : Nat) :
    lex3cToOrd
        (FullTripleLexCarrier.toLex3cTuple
          { phase := 0, dmComponent := κ, tauComponent := τ, phase_le_one := by decide }) =
      lexDMToOrd (κ, τ) := by
  simpa using full_triple_lex_dm_component_embeds κ τ

example :
    ∃ x : FullTripleLexCarrier, x.phase = 0 ∧ lex3cToOrd x.toLex3cTuple = 0 := by
  have h0 : (0 : Ordinal) < (ω : Ordinal) ^ (ω : Ordinal) := by
    exact Ordinal.opow_pos (a := (ω : Ordinal)) (b := (ω : Ordinal)) Ordinal.omega0_pos
  simpa using full_triple_lex_phase_zero_family h0

example :
    ∃ x : FullTripleLexCarrier,
      x.phase = 1 ∧ lex3cToOrd x.toLex3cTuple = (ω : Ordinal) ^ (ω : Ordinal) := by
  have h0 : (0 : Ordinal) < (ω : Ordinal) ^ (ω : Ordinal) := by
    exact Ordinal.opow_pos (a := (ω : Ordinal)) (b := (ω : Ordinal)) Ordinal.omega0_pos
  simpa using full_triple_lex_phase_one_family h0

example : FullTripleLexImage 0 := by
  have h0 : (0 : Ordinal) < (ω : Ordinal) ^ (ω : Ordinal) := by
    exact Ordinal.opow_pos (a := (ω : Ordinal)) (b := (ω : Ordinal)) Ordinal.omega0_pos
  exact full_triple_lex_phase_zero_in_image h0

end DMTripleLexImageReach
