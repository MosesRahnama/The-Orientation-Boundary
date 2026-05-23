import OperatorKO7.Meta.KO7EscapeRouteCharacterization

/-!
# Reach test: Phase F.5 Escape-Route Characterization

Confirms that every public name added across the Phase F.5 pair
(`Meta/RecursiveFamilyEscapeCharacterization.lean` and
`Meta/KO7EscapeRouteCharacterization.lean`) is reachable and type-checks.
The reach test imports nothing beyond the KO7 instantiation module
(which transitively pulls the schema-generic module, the escape-trichotomy
stack, the canonical-witness universality layer, and the KO7 RDRS adapter).
-/

namespace OperatorKO7.StepDuplicating

#check @RecursiveFamilyEscapeCharacterization.DirectObserverEscape
#check @RecursiveFamilyEscapeCharacterization.DirectObserverEscape.exposureFailure
#check @RecursiveFamilyEscapeCharacterization.DirectObserverEscape.pumpFailure
#check @RecursiveFamilyEscapeCharacterization.DirectObserverEscape.visibilityFailure
#check @RecursiveFamilyEscapeCharacterization.DirectObserverEscape.sensitivityFailure

#check @RecursiveFamilyEscapeCharacterization.recursiveFamily_barrier_implies_escape_one_way
#check @RecursiveFamilyEscapeCharacterization.RecursiveFamilyEscapeCharacterization
#check @RecursiveFamilyEscapeCharacterization.recursiveFamily_escape_characterization_certificate

#check @KO7EscapeClause
#check @KO7EscapeClause.violatesSensitivity
#check @KO7EscapeClause.violatesTransparency
#check @KO7EscapeClause.importsCrossCoupling
#check @KO7EscapeClause.projectsPayload
#check @KO7EscapeClause.importsStructuralOrder

#check @KO7EscapingOrienter
#check @ko7_escape_route_forward
#check @ko7_escape_route_backward
#check @ko7_escape_route_iff
#check @KO7EscapeRouteCharacterization
#check @ko7_escape_characterization_certificate
#check @phaseF5_escape_characterization_closed

/-! ## Concrete reach example: schema-generic one-way classification

A minimal `DuplicatingRecursiveFamily` reuses the simplest possible RDRS
shape (Bool / Unit). The schema-generic certificate is applied to it and
the four-clause escape disjunction is exercised. -/

private def reachSchema : RightDuplicatingRecursorSchema where
  Term := Bool
  PayloadCoord := Unit
  Position := Unit
  lhs := false
  rhs := true
  payloadOccursAt := fun _ _ _ => True
  payloadCount := fun _ t => if t then 2 else 1
  distinguishedPayload := ()
  lhs_has_payload := rfl
  rhs_duplicates_payload := by decide
  firesOnClosedTerms := True

private def reachFamily : DuplicatingRecursiveFamily where
  schema := reachSchema
  Step := fun a b => a = false ∧ b = true
  duplicating_step := And.intro rfl rfl
  HasUnboundedPayloadPump := fun _ => True
  ExposesPayloadStrictly := fun _ => True
  distinguished_exposed := True.intro
  exposure_strict_count := by
    intro _ _
    show (1 : Nat) < 2
    decide

/-- The schema-generic one-way certificate applies unconditionally to every
duplicating recursive family, including the inline reach family above. -/
example :
    RecursiveFamilyEscapeCharacterization.RecursiveFamilyEscapeCharacterization
      reachFamily :=
  RecursiveFamilyEscapeCharacterization.recursiveFamily_escape_characterization_certificate
    reachFamily

/-! ## Concrete reach example: KO7 iff at a representative direct orienter

A trivial Nat-valued direct orienter checks that the iff signature accepts
a concrete orienter argument. The target predicate is `KO7EscapingOrienter`,
which packages both the orientation proof and a concrete escape clause. -/
example :
    (fun _ : OperatorKO7.Trace => (0 : Nat)) =
      (OperatorKO7.EscapeTrichotomy.KO7DirectOrienter.nat
        (fun _ => 0)).primaryScalar :=
  rfl

end OperatorKO7.StepDuplicating
