import OperatorKO7.Meta.ClassicalAscentProfile

/-!
# Six-stage profile equivalence

`IncompletenessViaConfession` is an alias for `CompatibleWithDp` on an `AscentProfile`. The imported
Godel-labelled and dependency-pair profiles satisfy that predicate. The two theorems below compose
their stored pointwise equivalences between six proposition-valued stage fields.

The formal vocabulary here is limited to `AscentProfile`, `CompatibleWithDp`, and
`StagewiseEquivalent`. Accordingly, the declarations establish profile-shape equivalence. The
declaration names containing `transfer` do not supply transport of Godel's incompleteness proof.
-/

namespace OperatorKO7.Meta.BoundaryOperator.UniversalGoedelTransfer

open OperatorKO7.ClassicalAscentProfile
open OperatorKO7.ReflectionSchema

/-- Name for compatibility of an ascent profile with the designated dependency-pair
six-stage shape. -/
def IncompletenessViaConfession (C : AscentProfile) : Prop := CompatibleWithDp C

/-- The imported Godel-labelled metadata profile satisfies `CompatibleWithDp`. -/
theorem godel_is_incompleteness_via_confession :
    IncompletenessViaConfession godel1931PaperAscentProfile :=
  godel1931PaperAscentProfile_compatible

/-- The imported dependency-pair metadata profile satisfies `CompatibleWithDp`. -/
theorem dp_is_incompleteness_via_confession :
    IncompletenessViaConfession dpAsClassicalAscentProfile :=
  dpAsClassicalAscentProfile_compatible

/-- Pointwise logical equivalence between the six stage fields of the two imported profiles. -/
theorem goedel_transfers_to_dp_confession :
    StagewiseEquivalent godel1931PaperAscentProfile.shape
      dpAsClassicalAscentProfile.shape :=
  godel_is_incompleteness_via_confession.1

/-- Compose two compatibility witnesses through the designated dependency-pair profile to obtain
stagewise equivalence of the supplied profiles. -/
theorem incompleteness_instances_transfer
    (C₁ C₂ : AscentProfile)
    (h₁ : IncompletenessViaConfession C₁)
    (h₂ : IncompletenessViaConfession C₂) :
    StagewiseEquivalent C₁.shape C₂.shape := by
  intro s
  exact (h₁.1 s).trans (h₂.1 s).symm

/-- String containing the declaration name of `incompleteness_instances_transfer`. -/
def universal_goedel_transfer_anchor : String :=
  "OperatorKO7.Meta.BoundaryOperator.UniversalGoedelTransfer.incompleteness_instances_transfer"

end OperatorKO7.Meta.BoundaryOperator.UniversalGoedelTransfer
