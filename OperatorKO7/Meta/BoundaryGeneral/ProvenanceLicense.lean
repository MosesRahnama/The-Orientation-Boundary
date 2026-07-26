/-!
# Provenance and license fields

`Response` stores provenance, support, license, and admissibility as four
independent propositions. `AdmissibilityNeedsLicense` is the implication from
admissibility to license. `provenance_not_license` is modus tollens for that
implication and does not use the provenance or support fields.

`unlicensedResponse` is a concrete record whose provenance and support fields
are true while its license and admissibility fields are false. The example
theorem establishes the declared false admissibility field; it does not derive
inadmissibility from provenance alone.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.BoundaryGeneral.ProvenanceLicense

/-- A response with a retrieved source span, local support, an external license, and an
admissibility verdict, each carried as a proposition. The license is a distinct field from the span:
having the span (provenance) is not the same as having the license. -/
structure Response where
  spanRetrieved : Prop      -- the source span was returned (provenance capture)
  spanSupports : Prop       -- the span locally supports the answer
  licensed : Prop           -- the verdict's external dependency is licensed
  admissible : Prop         -- the answer is admissible for its verdict class

/-- Admissibility depends on a license: an admissible answer must be licensed. -/
def AdmissibilityNeedsLicense (R : Response) : Prop :=
  R.admissible → R.licensed

/-- If admissibility implies license and the response is unlicensed, then it is inadmissible. -/
theorem provenance_not_license (R : Response) (hneed : AdmissibilityNeedsLicense R)
    (hunlicensed : ¬ R.licensed) : ¬ R.admissible :=
  fun hadm => hunlicensed (hneed hadm)

/-! ### Concrete record -/

/-- A response with provenance capture (span retrieved and supporting) but no license, where
admissibility needs a license. -/
def unlicensedResponse : Response where
  spanRetrieved := True
  spanSupports := True
  licensed := False
  admissible := False

theorem unlicensedResponse_has_provenance :
    unlicensedResponse.spanRetrieved ∧ unlicensedResponse.spanSupports :=
  ⟨trivial, trivial⟩

/-- The concrete record's `admissible` field is false. -/
theorem unlicensed_example : ¬ unlicensedResponse.admissible :=
  provenance_not_license unlicensedResponse (fun h => h) (fun h => h)

#print axioms provenance_not_license
#print axioms unlicensed_example

end OperatorKO7.Meta.BoundaryGeneral.ProvenanceLicense
