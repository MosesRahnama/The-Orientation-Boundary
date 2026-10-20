import OperatorKO7.Meta.RDRSSemanticProjectionTransaction

/-!
# The semantic projection escape as four pieces

The semantic form of `prop:s4-projection-transaction` in the Orientation Boundary paper describes a
semantic projection escape by four pieces: a projection commuting with the source and target of the
step, a well-founded strict relation on the projected type with an orienting measure, a collapse map
through which the projection factors, and the projected orientation. `SemanticProjectionTransactionEscape`
carries the first, second and fourth pieces as fields. This file adds the record with all four
pieces as fields, its transport theorem, and the maps between the two records: the four-piece
record is inhabited exactly when the escape is, the identity collapse supplying the third piece.
-/

set_option autoImplicit false

namespace OperatorKO7.RDRSSemanticProjectionFourPiece

open OperatorKO7.RDRSDescentLens
open OperatorKO7.RDRSSeedCollapse
open OperatorKO7.RDRSSemanticProjectionTransaction

/-- A semantic projection escape given by its four pieces: the commuting projection with its
well-founded projected measure (`transaction`), a collapse map through which the projection
factors, and the projected orientation. -/
structure SemanticProjectionEscapeFourPiece {B S N T : Type} (R : RDRSStep B S N T) : Type 1 where
  transaction : SemanticProjectionTransaction R
  PayloadCarrier : Type
  seedCollapse : SeedCollapse PayloadCarrier T
  factorization : FactorsThroughSeedCollapse seedCollapse transaction.pi
  projected_orientation :
    Orients transaction.Rproj transaction.semanticMeasure.μ transaction.semanticMeasure.ltA

namespace SemanticProjectionEscapeFourPiece

variable {B S N T : Type} {R : RDRSStep B S N T}

/-- Forgetting the collapse gives a semantic projection escape. -/
def toEscape (E : SemanticProjectionEscapeFourPiece R) : SemanticProjectionTransactionEscape R :=
  { transaction := E.transaction
    projected_orientation := E.projected_orientation }

/-- The four pieces transport orientation back to the source step through `μ' ∘ π`. -/
theorem lifted_orients (E : SemanticProjectionEscapeFourPiece R) :
    Orients R (fun t => E.transaction.semanticMeasure.μ (E.transaction.pi t))
      E.transaction.semanticMeasure.ltA :=
  E.toEscape.lifted_orients

/-- The projected strict relation of the four pieces is well founded. -/
theorem projected_wellFounded (E : SemanticProjectionEscapeFourPiece R) :
    WellFounded E.transaction.semanticMeasure.ltA :=
  E.transaction.semanticMeasure.wf_ltA

/-- The projection agrees with its factor on the collapsed term. -/
theorem pi_eq_factor_collapse (E : SemanticProjectionEscapeFourPiece R) (t : T) :
    E.transaction.pi t = E.factorization.factor (E.seedCollapse.collapse t) :=
  E.factorization.obs_eq t

end SemanticProjectionEscapeFourPiece

/-- Every semantic projection escape has the four pieces, the identity collapse supplying the
third. -/
def ofEscape {B S N T : Type} {R : RDRSStep B S N T} (E : SemanticProjectionTransactionEscape R) :
    SemanticProjectionEscapeFourPiece R :=
  { transaction := E.transaction
    PayloadCarrier := T
    seedCollapse := SeedCollapse.id T
    factorization := FactorsThroughSeedCollapse.of_factor (SeedCollapse.id T) E.transaction.pi
      E.transaction.pi (fun _ => rfl)
    projected_orientation := E.projected_orientation }

/-- A step has a four-piece semantic projection escape if and only if it has a semantic projection
escape. -/
theorem fourPiece_nonempty_iff {B S N T : Type} (R : RDRSStep B S N T) :
    Nonempty (SemanticProjectionEscapeFourPiece R) ↔ Nonempty (SemanticProjectionTransactionEscape R) :=
  ⟨fun ⟨E⟩ => ⟨E.toEscape⟩, fun ⟨E⟩ => ⟨ofEscape E⟩⟩

end OperatorKO7.RDRSSemanticProjectionFourPiece
