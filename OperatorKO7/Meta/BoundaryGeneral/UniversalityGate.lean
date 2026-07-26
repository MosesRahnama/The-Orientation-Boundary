/-!
This module defines a finite registry gate over a caller-supplied complete proposition. The
equivalence and failure lemmas manipulate that field; they establish registry coverage rather
than semantic completeness of licenses, proof pointers, or reachability.










-/

set_option autoImplicit false

namespace OperatorKO7.Meta.BoundaryGeneral.UniversalityGate

/-- Data record whose requirements are the fields displayed below.

-/
structure CalculusRow where
  statement : Type
  proof : Type
  license : Type
  reach : Type
  scope : Type
  complete : Prop

/-- Definition with formal content given by the displayed type and body.
-/
def UGate {ClaimId : Type} (Claims : ClaimId → Prop) (row : ClaimId → CalculusRow) : Prop :=
  ∀ c, Claims c → (row c).complete

/-- The displayed proposition follows from the stated hypotheses.
-/
theorem ugate_iff_all_complete {ClaimId : Type} (Claims : ClaimId → Prop)
    (row : ClaimId → CalculusRow) :
    UGate Claims row ↔ ∀ c, Claims c → (row c).complete := Iff.rfl

/-- The displayed proposition follows from the stated hypotheses.
-/
theorem missing_row_failure {ClaimId : Type} (Claims : ClaimId → Prop)
    (row : ClaimId → CalculusRow) (c : ClaimId) (hc : Claims c)
    (hincomplete : ¬ (row c).complete) : ¬ UGate Claims row :=
  fun hg => hincomplete (hg c hc)

/-! Declarations for the section below. -/

/-- Definition with formal content given by the displayed type and body. -/
def completeRow : CalculusRow where
  statement := Unit
  proof := Unit
  license := Unit
  reach := Unit
  scope := Unit
  complete := True

/-- Definition with formal content given by the displayed type and body. -/
def incompleteRow : CalculusRow where
  statement := Unit
  proof := Unit
  license := Unit
  reach := Unit
  scope := Unit
  complete := False

/-- The displayed proposition follows from the stated hypotheses. -/
theorem ugate_holds_example : UGate (fun _ : Unit => True) (fun _ => completeRow) :=
  fun _ _ => trivial

/-- The displayed proposition follows from the stated hypotheses. -/
theorem ugate_fails_example : ¬ UGate (fun _ : Unit => True) (fun _ => incompleteRow) :=
  missing_row_failure (fun _ : Unit => True) (fun _ => incompleteRow) () trivial (fun h => h)

#print axioms missing_row_failure
#print axioms ugate_fails_example

end OperatorKO7.Meta.BoundaryGeneral.UniversalityGate
