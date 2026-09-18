import OperatorKO7.Meta.DistinctionBoundary.SharedRoot
import OperatorKO7.Meta.SafeStep.SyntacticNonDerivability
import OperatorKO7.Meta.SafeStep.FalseFormalLegitimacy

set_option autoImplicit false

namespace OperatorKO7.Meta.DistinctionBoundary.DualExternalLicenseBoundary

open OperatorKO7 Trace

/-- A formal interface at a boundary event carries the four observable ways a
sound boundary process can discharge the missing internal license. The fields are
not conclusions; they are the interface's declared discharge evidence. The theorem
below classifies which discharge a given interface exposes. -/
structure SoundBoundaryInterface where
  importsProjection : Prop
  importsDisequality : Prop
  emitsTypedRefusal : Prop
  overclaims : Prop
  exhaustive :
    importsProjection ∨ importsDisequality ∨ emitsTypedRefusal ∨ overclaims

inductive BoundaryInterfaceDischarge (I : SoundBoundaryInterface) : Prop
  | importsProjection (h : I.importsProjection)
  | importsDisequality (h : I.importsDisequality)
  | emitsTypedRefusal (h : I.emitsTypedRefusal)
  | overclaims (h : I.overclaims)

theorem sound_boundary_interface_four_way
    (I : SoundBoundaryInterface) :
    Nonempty (BoundaryInterfaceDischarge I) := by
  rcases I.exhaustive with h | h | h | h
  · exact ⟨BoundaryInterfaceDischarge.importsProjection h⟩
  · exact ⟨BoundaryInterfaceDischarge.importsDisequality h⟩
  · exact ⟨BoundaryInterfaceDischarge.emitsTypedRefusal h⟩
  · exact ⟨BoundaryInterfaceDischarge.overclaims h⟩

/-- The projection arm is live, using the orientation obstruction from the shared
root package as concrete evidence that an external projection can separate a pair
collapsed by the internal fold. -/
def projectionInterface : SoundBoundaryInterface where
  importsProjection :=
    SharedRoot.orientationObstruction.license SharedRoot.orientationObstruction.a
      ≠ SharedRoot.orientationObstruction.license SharedRoot.orientationObstruction.b
  importsDisequality := False
  emitsTypedRefusal := False
  overclaims := False
  exhaustive := Or.inl SharedRoot.orientationObstruction.license_separates

def disequalityInterface : SoundBoundaryInterface where
  importsProjection := False
  importsDisequality := void ≠ delta void
  emitsTypedRefusal := False
  overclaims := False
  exhaustive := Or.inr (Or.inl (by intro h; cases h))

def typedRefusalInterface : SoundBoundaryInterface where
  importsProjection := False
  importsDisequality := False
  emitsTypedRefusal := True
  overclaims := False
  exhaustive := Or.inr (Or.inr (Or.inl trivial))

def overclaimInterface : SoundBoundaryInterface where
  importsProjection := False
  importsDisequality := False
  emitsTypedRefusal := False
  overclaims :=
    OperatorKO7.Meta.SafeStep.FalseFormalLegitimacy.FalseFormalLegitimacyToken
      void void (integrate (merge void void))
  exhaustive :=
    Or.inr (Or.inr (Or.inr
      (OperatorKO7.Meta.SafeStep.FalseFormalLegitimacy.raw_diagonal_emits_false_formal_legitimacy
        void).2))

theorem all_four_discharge_arms_live :
    Nonempty (BoundaryInterfaceDischarge projectionInterface)
      ∧ Nonempty (BoundaryInterfaceDischarge disequalityInterface)
      ∧ Nonempty (BoundaryInterfaceDischarge typedRefusalInterface)
      ∧ Nonempty (BoundaryInterfaceDischarge overclaimInterface) :=
  ⟨sound_boundary_interface_four_way projectionInterface,
    sound_boundary_interface_four_way disequalityInterface,
    sound_boundary_interface_four_way typedRefusalInterface,
    sound_boundary_interface_four_way overclaimInterface⟩

#print axioms sound_boundary_interface_four_way
#print axioms all_four_discharge_arms_live

end OperatorKO7.Meta.DistinctionBoundary.DualExternalLicenseBoundary
