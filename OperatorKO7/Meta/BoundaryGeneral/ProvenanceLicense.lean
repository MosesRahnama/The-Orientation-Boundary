/-!
# Theory II: Provenance-boundary loop (provenance is not license)

Boundary-general cross-paper packet, Theory II. Returning the correct source span (provenance
capture) proves the span is present and locally supports the answer; it does not prove the span is
controlling, current, non-excepted, or licensed for the verdict class. License is a distinct object
from the source span. Hence when admissibility depends on a license, provenance capture alone does
not discharge the confession burden: the answer carries the payload carrier but has not licensed the
verdict.

`provenance_not_license` is the load-bearing theorem; `unlicensed_example` witnesses an inadmissible
response that nonetheless has provenance capture, so the statement is non-vacuous.

No `sorry`, `axiom`, or `native_decide`.
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

/-- **Provenance is not license (Theorem 2.5).** If admissibility needs a license, then provenance
capture (span retrieved and supporting) without the license does not make the answer admissible: the
confession burden is undischarged. -/
theorem provenance_not_license (R : Response) (hneed : AdmissibilityNeedsLicense R)
    (hunlicensed : ¬ R.licensed) : ¬ R.admissible :=
  fun hadm => hunlicensed (hneed hadm)

/-! ### Non-vacuity -/

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

/-- **Non-vacuity.** The provenance-captured-but-unlicensed response is inadmissible. -/
theorem unlicensed_example : ¬ unlicensedResponse.admissible :=
  provenance_not_license unlicensedResponse (fun h => h) (fun h => h)

#print axioms provenance_not_license
#print axioms unlicensed_example

end OperatorKO7.Meta.BoundaryGeneral.ProvenanceLicense
