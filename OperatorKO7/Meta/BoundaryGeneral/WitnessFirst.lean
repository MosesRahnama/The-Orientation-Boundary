/-!
# Conjunctive certificate-policy interface

`Certificate` stores six proposition-valued obligations, and `Accepts` requires all six. Theorems project individual fields and show that a missing license or cost rejects a record. Example certificates set all fields to `True` or set the license field to `False`. The propositions define an abstract policy record; executable span, cost, license, and replay checks require adapters.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.BoundaryGeneral.WitnessFirst

/-- A transformation certificate's acceptance-relevant obligations, each carried as a proposition. -/
structure Certificate where
  witnessPresent : Prop
  citationsGrounded : Prop
  projectionsCosted : Prop
  externalsLicensed : Prop
  replayRecorded : Prop
  verdictSupported : Prop

/-- Conjunction of the six proposition-valued certificate fields. -/
def Accepts (T : Certificate) : Prop :=
  T.witnessPresent ∧ T.citationsGrounded ∧ T.projectionsCosted ∧
    T.externalsLicensed ∧ T.replayRecorded ∧ T.verdictSupported

/-- Project `verdictSupported` from an `Accepts` witness. -/
theorem accepts_verdict_supported {T : Certificate} (h : Accepts T) : T.verdictSupported :=
  h.2.2.2.2.2

/-- An accepted certificate also carries its witness. -/
theorem accepts_witness_present {T : Certificate} (h : Accepts T) : T.witnessPresent :=
  h.1

/-- Failure of `externalsLicensed` contradicts `Accepts`. -/
theorem provenance_without_license_rejected {T : Certificate} (h : ¬ T.externalsLicensed) :
    ¬ Accepts T :=
  fun ha => h ha.2.2.2.1

/-- Failure of `projectionsCosted` contradicts `Accepts`. -/
theorem carrier_blind_projection_rejected {T : Certificate} (h : ¬ T.projectionsCosted) :
    ¬ Accepts T :=
  fun ha => h ha.2.2.1

/-! ### Example certificates -/

/-- An example certificate with every field true. -/
def goodCertificate : Certificate where
  witnessPresent := True
  citationsGrounded := True
  projectionsCosted := True
  externalsLicensed := True
  replayRecorded := True
  verdictSupported := True

theorem accepts_example : Accepts goodCertificate :=
  ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩

/-- An example certificate with the license field false and the other fields true. -/
def licenseMissingCertificate : Certificate where
  witnessPresent := True
  citationsGrounded := True
  projectionsCosted := True
  externalsLicensed := False
  replayRecorded := True
  verdictSupported := True

theorem license_missing_rejected_example : ¬ Accepts licenseMissingCertificate :=
  provenance_without_license_rejected (fun h => h)

#print axioms provenance_without_license_rejected
#print axioms accepts_example

end OperatorKO7.Meta.BoundaryGeneral.WitnessFirst
