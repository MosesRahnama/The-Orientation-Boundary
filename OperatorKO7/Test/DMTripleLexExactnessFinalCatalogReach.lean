import OperatorKO7.Meta.DM_TripleLexExactness_FinalCatalog

namespace DMTripleLexExactnessFinalCatalogReach

open Ordinal
open OperatorKO7.MetaCM
open OperatorKO7.MetaDM
open OperatorKO7.DMTripleLexExactnessFinalCatalog

#check TripleLexExactnessFinalCatalog
#check triple_lex_exactness_final_catalog
#check final_catalog_projects_dm_code_injective
#check final_catalog_projects_inner_eq_iff
#check final_catalog_projects_carrier_phase_eq
#check final_catalog_projects_carrier_inner_eq
#check final_catalog_projects_carrier_injective
#check final_catalog_projects_carrier_eq_iff
#check final_catalog_projects_exact_order_type

example {p q : Multiset Nat × Nat} (h : lexDMToOrd p = lexDMToOrd q) : p = q :=
  (triple_lex_exactness_final_catalog.innerInjective h)

example {x y : FullTripleLexCarrier}
    (h : lex3cToOrd x.toLex3cTuple = lex3cToOrd y.toLex3cTuple) :
    x.phase = y.phase :=
  final_catalog_projects_carrier_phase_eq h

example {x y : FullTripleLexCarrier}
    (h : lex3cToOrd x.toLex3cTuple = lex3cToOrd y.toLex3cTuple) :
    (x.dmComponent, x.tauComponent) = (y.dmComponent, y.tauComponent) :=
  final_catalog_projects_carrier_inner_eq h

example {x y : FullTripleLexCarrier}
    (h : lex3cToOrd x.toLex3cTuple = lex3cToOrd y.toLex3cTuple) : x = y :=
  final_catalog_projects_carrier_injective h

example {x y : FullTripleLexCarrier} :
    lex3cToOrd x.toLex3cTuple = lex3cToOrd y.toLex3cTuple ↔ x = y :=
  final_catalog_projects_carrier_eq_iff

example :
    ∀ x y : FullTripleLexCarrier,
      Lex3c x.toLex3cTuple y.toLex3cTuple ↔
        lex3cToOrd x.toLex3cTuple < lex3cToOrd y.toLex3cTuple :=
  final_catalog_projects_exact_order_type.1

end DMTripleLexExactnessFinalCatalogReach
