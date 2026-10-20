import OperatorKO7.Meta.DM_TripleLexExactness

/-!
# Final M3 Triple-Lex Exactness Catalog

This file packages the final theorem-backed M3 surface after the DM-code
injectivity bridge is closed. No new assumptions are introduced here.
-/

namespace OperatorKO7.DMTripleLexExactnessFinalCatalog

open Ordinal
open OperatorKO7.MetaCM
open OperatorKO7.MetaDM

/-- Final paper-facing M3 catalog for the calibrated binary-phase triple-lex
exactness surface. -/
structure TripleLexExactnessFinalCatalog : Prop where
  dmCodeInjective : DmOrdEmbedInjective
  innerReflects :
    ∀ {p q : Multiset Nat × Nat},
      lexDMToOrd p < lexDMToOrd q → LexDM_c p q
  innerOrderIff :
    ∀ p q : Multiset Nat × Nat,
      LexDM_c p q ↔ lexDMToOrd p < lexDMToOrd q
  innerInjective : Function.Injective lexDMToOrd
  innerEqIff :
    ∀ {p q : Multiset Nat × Nat},
      lexDMToOrd p = lexDMToOrd q ↔ p = q
  carrierPhaseEq :
    ∀ {x y : FullTripleLexCarrier},
      lex3cToOrd x.toLex3cTuple = lex3cToOrd y.toLex3cTuple → x.phase = y.phase
  carrierInnerEq :
    ∀ {x y : FullTripleLexCarrier},
      lex3cToOrd x.toLex3cTuple = lex3cToOrd y.toLex3cTuple →
        (x.dmComponent, x.tauComponent) = (y.dmComponent, y.tauComponent)
  carrierInjective :
    Function.Injective (fun x : FullTripleLexCarrier => lex3cToOrd x.toLex3cTuple)
  carrierEqIff :
    ∀ {x y : FullTripleLexCarrier},
      lex3cToOrd x.toLex3cTuple = lex3cToOrd y.toLex3cTuple ↔ x = y
  tripleReflects : FullTripleLexOrderReflects
  exactOrderType :
    (∀ x y : FullTripleLexCarrier,
      Lex3c x.toLex3cTuple y.toLex3cTuple ↔
        lex3cToOrd x.toLex3cTuple < lex3cToOrd y.toLex3cTuple) ∧
    (∀ x : FullTripleLexCarrier,
      lex3cToOrd x.toLex3cTuple < ((ω : Ordinal) ^ (ω : Ordinal)) * (2 : Nat)) ∧
    (∀ α < ((ω : Ordinal) ^ (ω : Ordinal)) * (2 : Nat),
      ∃ x : FullTripleLexCarrier, lex3cToOrd x.toLex3cTuple = α)

/-- Final M3 catalog theorem: the DM-code injectivity bridge closes the full
unconditional exactness surface. -/
theorem triple_lex_exactness_final_catalog : TripleLexExactnessFinalCatalog := by
  refine ⟨dmOrdEmbedInjective, ?_, lexDMToOrd_order_iff, lexDMToOrd_injective, ?_,
    full_triple_lex_phase_eq_of_code_eq, full_triple_lex_inner_eq_of_code_eq,
    lex3cToOrd_injective_on_fullCarrier, ?_, full_triple_lex_order_reflects,
    full_triple_lex_exact_order_type⟩
  · intro p q hlt
    exact lexDMToOrd_reflects hlt
  · intro p q
    exact lexDMToOrd_eq_iff
  · intro x y
    exact lex3cToOrd_eq_iff_on_fullCarrier

/-- The final M3 catalog projects the DM-code injectivity bridge. -/
theorem final_catalog_projects_dm_code_injective :
    DmOrdEmbedInjective :=
  triple_lex_exactness_final_catalog.dmCodeInjective

/-- The final M3 catalog projects the inner equality criterion. -/
theorem final_catalog_projects_inner_eq_iff
    {p q : Multiset Nat × Nat} :
    lexDMToOrd p = lexDMToOrd q ↔ p = q :=
  triple_lex_exactness_final_catalog.innerEqIff

/-- The final M3 catalog projects phase recovery on the calibrated carrier. -/
theorem final_catalog_projects_carrier_phase_eq
    {x y : FullTripleLexCarrier}
    (h : lex3cToOrd x.toLex3cTuple = lex3cToOrd y.toLex3cTuple) :
    x.phase = y.phase :=
  triple_lex_exactness_final_catalog.carrierPhaseEq h

/-- The final M3 catalog projects inner-pair recovery on the calibrated carrier. -/
theorem final_catalog_projects_carrier_inner_eq
    {x y : FullTripleLexCarrier}
    (h : lex3cToOrd x.toLex3cTuple = lex3cToOrd y.toLex3cTuple) :
    (x.dmComponent, x.tauComponent) = (y.dmComponent, y.tauComponent) :=
  triple_lex_exactness_final_catalog.carrierInnerEq h

/-- The final M3 catalog projects carrier injectivity for the calibrated code. -/
theorem final_catalog_projects_carrier_injective :
    Function.Injective (fun x : FullTripleLexCarrier => lex3cToOrd x.toLex3cTuple) :=
  triple_lex_exactness_final_catalog.carrierInjective

/-- The final M3 catalog projects the carrier equality criterion for the calibrated code. -/
theorem final_catalog_projects_carrier_eq_iff
    {x y : FullTripleLexCarrier} :
    lex3cToOrd x.toLex3cTuple = lex3cToOrd y.toLex3cTuple ↔ x = y :=
  triple_lex_exactness_final_catalog.carrierEqIff

/-- The final M3 catalog projects the unconditional exact-order-type package. -/
theorem final_catalog_projects_exact_order_type :
    (∀ x y : FullTripleLexCarrier,
      Lex3c x.toLex3cTuple y.toLex3cTuple ↔
        lex3cToOrd x.toLex3cTuple < lex3cToOrd y.toLex3cTuple) ∧
    (∀ x : FullTripleLexCarrier,
      lex3cToOrd x.toLex3cTuple < ((ω : Ordinal) ^ (ω : Ordinal)) * (2 : Nat)) ∧
    (∀ α < ((ω : Ordinal) ^ (ω : Ordinal)) * (2 : Nat),
      ∃ x : FullTripleLexCarrier, lex3cToOrd x.toLex3cTuple = α) :=
  triple_lex_exactness_final_catalog.exactOrderType

end OperatorKO7.DMTripleLexExactnessFinalCatalog
