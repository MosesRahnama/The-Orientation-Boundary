import OperatorKO7.Meta.RDRSDescentLens

/-!
This module defines a commuting syntactic projection and a record carrying a projected
orientation proof. The lifted-orientation theorem uses the two commuting equations and that
stored proof. Payload-erasure semantics require an additional property of the projection.










































-/

set_option autoImplicit false

namespace OperatorKO7.RDRSProjectionSyntax

open OperatorKO7.RDRSDescentLens

/-- Data record whose requirements are the fields displayed below.









-/
structure PayloadForgetErasure
    {B S N T : Type} (R : RDRSStep B S N T) (T' : Type) where
  /-- Field requirements are given by the displayed type. -/
  erase : T → T'
  /-- Field requirements are given by the displayed type. -/
  Rproj : RDRSStep B S N T'
  /-- Field requirements are given by the displayed type. -/
  erase_commutes_lhs :
    ∀ b s n, erase (R.lhs b s n) = Rproj.lhs b s n
  /-- Field requirements are given by the displayed type. -/
  erase_commutes_rhs :
    ∀ b s n, erase (R.rhs b s n) = Rproj.rhs b s n

/-- Data record whose requirements are the fields displayed below.


















-/
structure ProjectionEscape
    {B S N T : Type} (R : RDRSStep B S N T) where
  /-- Field requirements are given by the displayed type. -/
  T' : Type
  /-- Field requirements are given by the displayed type. -/
  A' : Type
  /-- Field requirements are given by the displayed type. -/
  E : PayloadForgetErasure R T'
  /-- Field requirements are given by the displayed type. -/
  mu' : T' → A'
  /-- Field requirements are given by the displayed type. -/
  ltA' : A' → A' → Prop
  /-- Field requirements are given by the displayed type.

-/
  projected_orientation :
    Orients E.Rproj mu' ltA'

namespace ProjectionEscape

variable {B S N T : Type} {R : RDRSStep B S N T} (P : ProjectionEscape R)

/-- Definition with formal content given by the displayed type and body.











-/
def liftedMeasure : T → P.A' := fun t => P.mu' (P.E.erase t)

/-- The displayed proposition follows from the stated hypotheses.














-/
theorem lifted_orients :
    Orients R P.liftedMeasure P.ltA' := by
  intro b s n
  show P.ltA' (P.mu' (P.E.erase (R.rhs b s n)))
              (P.mu' (P.E.erase (R.lhs b s n)))
  rw [P.E.erase_commutes_lhs, P.E.erase_commutes_rhs]
  exact P.projected_orientation b s n

/-- The displayed proposition follows from the stated hypotheses.














-/
theorem requires_positive_evidence (P : ProjectionEscape R) :
    ∃ (T' A' : Type) (E : PayloadForgetErasure R T')
      (mu' : T' → A') (ltA' : A' → A' → Prop),
      Orients E.Rproj mu' ltA' :=
  ⟨P.T', P.A', P.E, P.mu', P.ltA', P.projected_orientation⟩

end ProjectionEscape

/-- Definition with formal content given by the displayed type and body.










-/
def rdrs_projection_escape_positive_evidence_anchor : String :=
  "OperatorKO7.RDRSProjectionSyntax.ProjectionEscape.requires_positive_evidence"

/-- Definition with formal content given by the displayed type and body.














-/
def rdrs_projection_syntax_superseded_marker : String :=
  "OperatorKO7.RDRSProjectionSyntax: lower-level; final classifier surface in OperatorKO7.RDRSProjectionTransaction"

end OperatorKO7.RDRSProjectionSyntax
