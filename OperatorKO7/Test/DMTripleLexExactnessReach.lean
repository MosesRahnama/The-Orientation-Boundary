import OperatorKO7.Meta.DM_TripleLexExactness

namespace DMTripleLexExactnessReach

open Ordinal
open OperatorKO7.MetaCM
open OperatorKO7.MetaDM

#check full_triple_lex_image_surjective_lt_opow_omega_mul_two
#check DmOrdEmbedInjective
#check FullTripleLexOrderReflects
#check dmOrdEmbedInjective
#check lexDMToOrd_reflects_of_dmOrdEmbedInjective
#check lexDMToOrd_order_iff_of_dmOrdEmbedInjective
#check lexDMToOrd_reflects
#check lexDMToOrd_order_iff
#check lexDMToOrd_injective
#check lexDMToOrd_eq_iff
#check full_triple_lex_phase_eq_of_code_eq
#check full_triple_lex_inner_eq_of_code_eq
#check lex3cToOrd_injective_on_fullCarrier
#check lex3cToOrd_eq_iff_on_fullCarrier
#check full_triple_lex_order_reflects_of_lexDMToOrd_reflects
#check full_triple_lex_order_reflects_of_dmOrdEmbedInjective
#check full_triple_lex_order_reflects
#check full_triple_lex_image_surjective_package
#check full_triple_lex_exactness_residual_boundary
#check full_triple_lex_exact_order_type_of_dmOrdEmbedInjective
#check full_triple_lex_exact_order_type

example :
    ∃ x : FullTripleLexCarrier, lex3cToOrd x.toLex3cTuple = 0 := by
  have hωωpos : (0 : Ordinal) < (ω : Ordinal) ^ (ω : Ordinal) := by
    exact Ordinal.opow_pos (a := (ω : Ordinal)) (b := (ω : Ordinal)) Ordinal.omega0_pos
  have h0 : (0 : Ordinal) < ((ω : Ordinal) ^ (ω : Ordinal)) * (2 : Nat) := by
    exact Ordinal.mul_pos hωωpos (by exact_mod_cast (show 0 < 2 by decide))
  exact full_triple_lex_image_surjective_lt_opow_omega_mul_two h0

example :
    ∃ x : FullTripleLexCarrier,
      lex3cToOrd x.toLex3cTuple = (ω : Ordinal) ^ (ω : Ordinal) := by
  refine ⟨{ phase := 1, dmComponent := 0, tauComponent := 0, phase_le_one := by decide }, ?_⟩
  simp [FullTripleLexCarrier.toLex3cTuple, lex3cToOrd, lexDMToOrd]

example :
    (∀ x : FullTripleLexCarrier,
      lex3cToOrd x.toLex3cTuple < ((ω : Ordinal) ^ (ω : Ordinal)) * (2 : Nat)) :=
  full_triple_lex_image_surjective_package.2.1

example :
    ∀ α < ((ω : Ordinal) ^ (ω : Ordinal)) * (2 : Nat),
      ∃ x : FullTripleLexCarrier, lex3cToOrd x.toLex3cTuple = α :=
  full_triple_lex_image_surjective_package.2.2

example (hReflect : FullTripleLexOrderReflects) :
    ∀ x y : FullTripleLexCarrier,
      Lex3c x.toLex3cTuple y.toLex3cTuple ↔
        lex3cToOrd x.toLex3cTuple < lex3cToOrd y.toLex3cTuple :=
  (full_triple_lex_exactness_residual_boundary hReflect).1

example (hInj : DmOrdEmbedInjective) :
    ∀ p q : Multiset Nat × Nat,
      LexDM_c p q ↔ lexDMToOrd p < lexDMToOrd q :=
  lexDMToOrd_order_iff_of_dmOrdEmbedInjective hInj

example (hInj : DmOrdEmbedInjective) :
    ∀ x y : FullTripleLexCarrier,
      Lex3c x.toLex3cTuple y.toLex3cTuple ↔
        lex3cToOrd x.toLex3cTuple < lex3cToOrd y.toLex3cTuple :=
  (full_triple_lex_exact_order_type_of_dmOrdEmbedInjective hInj).1

example :
    ∀ p q : Multiset Nat × Nat,
      LexDM_c p q ↔ lexDMToOrd p < lexDMToOrd q :=
  lexDMToOrd_order_iff

example {p q : Multiset Nat × Nat} (h : lexDMToOrd p = lexDMToOrd q) : p = q :=
  lexDMToOrd_injective h

example {p q : Multiset Nat × Nat} : lexDMToOrd p = lexDMToOrd q ↔ p = q :=
  lexDMToOrd_eq_iff

example {x y : FullTripleLexCarrier}
    (h : lex3cToOrd x.toLex3cTuple = lex3cToOrd y.toLex3cTuple) :
    x.phase = y.phase :=
  full_triple_lex_phase_eq_of_code_eq h

example {x y : FullTripleLexCarrier}
    (h : lex3cToOrd x.toLex3cTuple = lex3cToOrd y.toLex3cTuple) :
    (x.dmComponent, x.tauComponent) = (y.dmComponent, y.tauComponent) :=
  full_triple_lex_inner_eq_of_code_eq h

example {x y : FullTripleLexCarrier}
    (h : lex3cToOrd x.toLex3cTuple = lex3cToOrd y.toLex3cTuple) : x = y :=
  lex3cToOrd_injective_on_fullCarrier h

example {x y : FullTripleLexCarrier} :
    lex3cToOrd x.toLex3cTuple = lex3cToOrd y.toLex3cTuple ↔ x = y :=
  lex3cToOrd_eq_iff_on_fullCarrier

example :
    ∀ x y : FullTripleLexCarrier,
      Lex3c x.toLex3cTuple y.toLex3cTuple ↔
        lex3cToOrd x.toLex3cTuple < lex3cToOrd y.toLex3cTuple :=
  full_triple_lex_exact_order_type.1

end DMTripleLexExactnessReach
