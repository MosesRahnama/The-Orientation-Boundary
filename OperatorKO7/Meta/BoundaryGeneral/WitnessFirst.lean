/-!
# Theory VIII: Witness-first provenance-bearing transform gate

Boundary-general cross-paper packet, Theory VIII. The supervisory engine's acceptance gate: a
transformation certificate is accepted only if it is witness-first, every cited source span is
grounded, every projected dimension is costed in the carrier ledger, every external verdict
dependency is licensed, the replay inputs are recorded, and the verdict is witness-backed rather than
free-text. The three rejection theorems are the engineering translation of the orientation-boundary
and operational-inexpressibility results: no free-text verdict without a witness, provenance without
license is rejected, and carrier-blind projection is rejected.

`accepts_verdict_supported`, `provenance_without_license_rejected`, and
`carrier_blind_projection_rejected` are the load-bearing theorems; `accepts_example` /
`license_missing_rejected_example` witness both outcomes.

No `sorry`, `axiom`, or `native_decide`.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.BoundaryGeneral.WitnessFirst

/-- A transformation certificate's acceptance-relevant obligations, each carried as a proposition. -/
structure Certificate where
  witnessPresent : Prop
  citationsGrounded : Prop
  projectionsCosted : Prop      -- carrier ledger records every projected (burden-changing) dimension
  externalsLicensed : Prop      -- a license for every verdict dependency not internal to the spans
  replayRecorded : Prop         -- deterministic compiler version + replay inputs recorded
  verdictSupported : Prop        -- the verdict is witness-backed, not unsupported free text

/-- The gate accepts a certificate exactly when all six obligations hold (Definition 8.3). -/
def Accepts (T : Certificate) : Prop :=
  T.witnessPresent ∧ T.citationsGrounded ∧ T.projectionsCosted ∧
    T.externalsLicensed ∧ T.replayRecorded ∧ T.verdictSupported

/-- **No free-text verdict without a witness (Theorem 8.4).** An accepted certificate has a
witness-backed verdict. -/
theorem accepts_verdict_supported {T : Certificate} (h : Accepts T) : T.verdictSupported :=
  h.2.2.2.2.2

/-- An accepted certificate also carries its witness. -/
theorem accepts_witness_present {T : Certificate} (h : Accepts T) : T.witnessPresent :=
  h.1

/-- **Provenance without license is rejected (Theorem 8.5).** A certificate whose verdict has an
unlicensed external dependency cannot pass the gate. -/
theorem provenance_without_license_rejected {T : Certificate} (h : ¬ T.externalsLicensed) :
    ¬ Accepts T :=
  fun ha => h ha.2.2.2.1

/-- **Carrier-blind projection is rejected (Theorem 8.6).** A certificate that projects away a
burden-changing dimension without a carrier-ledger entry cannot pass the gate. -/
theorem carrier_blind_projection_rejected {T : Certificate} (h : ¬ T.projectionsCosted) :
    ¬ Accepts T :=
  fun ha => h ha.2.2.1

/-! ### Non-vacuity: both outcomes are realized -/

/-- A fully discharged certificate (all obligations `True`). -/
def goodCertificate : Certificate where
  witnessPresent := True
  citationsGrounded := True
  projectionsCosted := True
  externalsLicensed := True
  replayRecorded := True
  verdictSupported := True

theorem accepts_example : Accepts goodCertificate :=
  ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩

/-- A certificate missing the external license (all else discharged). -/
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
