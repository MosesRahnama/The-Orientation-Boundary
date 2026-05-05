import OperatorKO7.Meta.LCELP4CCanonicalInstances

/-!
# LCEL P4C Universal Certification

This file closes the first open P4C constructor obligation.

For arbitrary `L : FormalLCELInstance`, the current typed LCEL carrier already
supplies enough theorem-backed semantic content to build a certified overlay:
schema realization, base support, license support, reimport support, and
boundary-factorization support. The earlier boundary equivalences remain as
auditable projections of that now-universal constructor.
-/

namespace OperatorKO7.LCELP4CUniversalCertification

open OperatorKO7.LCELSchema
open OperatorKO7.LCELReversibility
open OperatorKO7.LCELDpInstance
open OperatorKO7.LCELAdmissibility
open OperatorKO7.LCELP4CResidualObligation
open OperatorKO7.LCELP4CCanonicalInstances

/-- Exact theorem-visible per-instance boundary for P4C universal
certification. Bare `FormalLCELInstance` data does not automatically produce
these five fields. -/
structure LCELP4CUniversalCertificationBoundaryData
    (L : FormalLCELInstance) : Type 1 where
  realizes : RealizesLCELSchema L.toSlotProfile
  baseSupport : BaseReversibilitySupport L
  licenseSupport : LicenseIrreversibilitySupport L
  reimportSupport : ReimportReversibilitySupport L
  boundarySupport : BoundaryFactorizationSupport L

namespace LCELP4CUniversalCertificationBoundaryData

/-- Repackage certification-boundary data as the existing admissibility-data
package. -/
def toAdmissibilityData
    {L : FormalLCELInstance}
    (B : LCELP4CUniversalCertificationBoundaryData L) :
    LCELAdmissibilityData L where
  realizes := B.realizes
  baseSupport := B.baseSupport
  licenseSupport := B.licenseSupport
  reimportSupport := B.reimportSupport
  boundarySupport := B.boundarySupport

/-- Repackage the existing admissibility-data package as certification-boundary
data. -/
def ofAdmissibilityData
    {L : FormalLCELInstance}
    (A : LCELAdmissibilityData L) :
    LCELP4CUniversalCertificationBoundaryData L where
  realizes := A.realizes
  baseSupport := A.baseSupport
  licenseSupport := A.licenseSupport
  reimportSupport := A.reimportSupport
  boundarySupport := A.boundarySupport

@[simp] theorem ofAdmissibilityData_toAdmissibilityData
    {L : FormalLCELInstance}
    (A : LCELAdmissibilityData L) :
    (ofAdmissibilityData A).toAdmissibilityData = A :=
  rfl

@[simp] theorem toAdmissibilityData_ofAdmissibilityData
    {L : FormalLCELInstance}
    (B : LCELP4CUniversalCertificationBoundaryData L) :
    ofAdmissibilityData B.toAdmissibilityData = B := by
  cases B
  rfl

/-- Turn certification-boundary data into the certified overlay used by the
residual-obligation file. -/
def toCertifiedFormalLCELInstance
    {L : FormalLCELInstance}
    (B : LCELP4CUniversalCertificationBoundaryData L) :
    CertifiedFormalLCELInstance :=
  CertifiedFormalLCELInstance.ofAdmissibilityData L B.toAdmissibilityData

@[simp] theorem toCertifiedFormalLCELInstance_instance_
    {L : FormalLCELInstance}
    (B : LCELP4CUniversalCertificationBoundaryData L) :
    B.toCertifiedFormalLCELInstance.instance_ = L :=
  rfl

end LCELP4CUniversalCertificationBoundaryData

/-- Universal per-instance boundary corresponding exactly to universal
certification. -/
abbrev UniversalCertificationBoundary : Prop :=
  ∀ L : FormalLCELInstance,
    Nonempty (LCELP4CUniversalCertificationBoundaryData L)

namespace CertifiedFormalLCELInstance

/-- Generic certified overlay built directly from the theorem-backed semantic
content already carried by an arbitrary formal LCEL instance. -/
def certificationOfFormalLCELInstance
    (L : FormalLCELInstance) : CertifiedFormalLCELInstance := by
  let hSupported := L.comparison.supported
  let hSemantic := L.comparison.semanticSupported
  let hTransfer := L.comparison.semanticTransferSupported
  let baseSupport :=
    baseReversibilitySupport_of_semanticBase (L := L) hSemantic.1
  let licenseSupport :=
    licenseIrreversibilitySupport_of_semanticTransfer (L := L) hTransfer.1
  let reimportSupport :=
    reimportReversibilitySupport_of_semanticTransfer (L := L) hTransfer.2
  exact
    { instance_ := L
      realizes := L.realizesLCELSchema_of_supported hSupported
      baseSupport := baseSupport
      licenseSupport := licenseSupport
      reimportSupport := reimportSupport
      boundarySupport :=
        boundaryFactorizationSupport_of_supports (L := L)
          reimportSupport licenseSupport }

@[simp] theorem certificationOfFormalLCELInstance_instance_
    (L : FormalLCELInstance) :
    (certificationOfFormalLCELInstance L).instance_ = L :=
  rfl

/-- Every formal LCEL instance now has a certified overlay. -/
theorem hasCertification_universal
    (L : FormalLCELInstance) :
    OperatorKO7.LCELP4CResidualObligation.CertifiedFormalLCELInstance.HasCertification L := by
  exact ⟨⟨certificationOfFormalLCELInstance L, rfl⟩⟩

/-- Universal certification now closes unconditionally on the current typed
LCEL carrier. -/
theorem universalCertification_closed :
    OperatorKO7.LCELP4CResidualObligation.CertifiedFormalLCELInstance.UniversalCertification := by
  intro L
  exact hasCertification_universal L

end CertifiedFormalLCELInstance

/-- Per-instance certification is equivalent to existence of the exact boundary
data package. -/
theorem hasCertification_iff_nonempty_boundaryData
    (L : FormalLCELInstance) :
    CertifiedFormalLCELInstance.HasCertification L ↔
      Nonempty (LCELP4CUniversalCertificationBoundaryData L) := by
  constructor
  · intro h
    rcases h with ⟨⟨C, hC⟩⟩
    cases hC
    exact ⟨LCELP4CUniversalCertificationBoundaryData.ofAdmissibilityData
      C.toAdmissibilityData⟩
  · intro h
    rcases h with ⟨B⟩
    exact ⟨⟨B.toCertifiedFormalLCELInstance, rfl⟩⟩

/-- Per-instance certification is equivalent to existence of admissibility data.
This is the exact obstruction boundary for the first open P4C constructor
obligation. -/
theorem hasCertification_iff_nonempty_admissibilityData
    (L : FormalLCELInstance) :
    CertifiedFormalLCELInstance.HasCertification L ↔
      Nonempty (LCELAdmissibilityData L) := by
  constructor
  · intro h
    rcases (hasCertification_iff_nonempty_boundaryData L).1 h with ⟨B⟩
    exact ⟨B.toAdmissibilityData⟩
  · intro h
    rcases h with ⟨A⟩
    exact (hasCertification_iff_nonempty_boundaryData L).2
      ⟨LCELP4CUniversalCertificationBoundaryData.ofAdmissibilityData A⟩

/-- Universal certification is equivalent to universal existence of the exact
per-instance boundary data package. -/
theorem universalCertification_iff_universalBoundary :
    CertifiedFormalLCELInstance.UniversalCertification ↔
      UniversalCertificationBoundary := by
  constructor
  · intro h L
    exact (hasCertification_iff_nonempty_boundaryData L).1 (h L)
  · intro h L
    exact (hasCertification_iff_nonempty_boundaryData L).2 (h L)

/-- Universal certification is equivalent to universal existence of
`LCELAdmissibilityData`. -/
theorem universalCertification_iff_universalAdmissibilityData :
    CertifiedFormalLCELInstance.UniversalCertification ↔
      ∀ L : FormalLCELInstance, Nonempty (LCELAdmissibilityData L) := by
  constructor
  · intro h L
    exact (hasCertification_iff_nonempty_admissibilityData L).1 (h L)
  · intro h L
    exact (hasCertification_iff_nonempty_admissibilityData L).2 (h L)

/-- Auditable projection: certification of `L` yields schema realization. -/
theorem hasCertification_projects_realizes
    {L : FormalLCELInstance}
    (h : CertifiedFormalLCELInstance.HasCertification L) :
    Nonempty (RealizesLCELSchema L.toSlotProfile) := by
  rcases (hasCertification_iff_nonempty_boundaryData L).1 h with ⟨B⟩
  exact ⟨B.realizes⟩

/-- Auditable projection: certification of `L` yields base-layer support. -/
theorem hasCertification_projects_baseSupport
    {L : FormalLCELInstance}
    (h : CertifiedFormalLCELInstance.HasCertification L) :
    Nonempty (BaseReversibilitySupport L) := by
  rcases (hasCertification_iff_nonempty_boundaryData L).1 h with ⟨B⟩
  exact ⟨B.baseSupport⟩

/-- Auditable projection: certification of `L` yields license-side support. -/
theorem hasCertification_projects_licenseSupport
    {L : FormalLCELInstance}
    (h : CertifiedFormalLCELInstance.HasCertification L) :
    Nonempty (LicenseIrreversibilitySupport L) := by
  rcases (hasCertification_iff_nonempty_boundaryData L).1 h with ⟨B⟩
  exact ⟨B.licenseSupport⟩

/-- Auditable projection: certification of `L` yields reimport-side support. -/
theorem hasCertification_projects_reimportSupport
    {L : FormalLCELInstance}
    (h : CertifiedFormalLCELInstance.HasCertification L) :
    Nonempty (ReimportReversibilitySupport L) := by
  rcases (hasCertification_iff_nonempty_boundaryData L).1 h with ⟨B⟩
  exact ⟨B.reimportSupport⟩

/-- Auditable projection: certification of `L` yields boundary-factorization
support. -/
theorem hasCertification_projects_boundarySupport
    {L : FormalLCELInstance}
    (h : CertifiedFormalLCELInstance.HasCertification L) :
    Nonempty (BoundaryFactorizationSupport L) := by
  rcases (hasCertification_iff_nonempty_boundaryData L).1 h with ⟨B⟩
  exact ⟨B.boundarySupport⟩

/-- Canonical certification-boundary data on the Gödel 1931 instance. -/
def godel1931UniversalCertificationBoundaryData :
    LCELP4CUniversalCertificationBoundaryData godel1931LCELInstance :=
  LCELP4CUniversalCertificationBoundaryData.ofAdmissibilityData
    godel1931LCELAdmissibilityData

/-- Canonical certification-boundary data on the benchmark-transport instance. -/
def benchmarkTransportUniversalCertificationBoundaryData :
    LCELP4CUniversalCertificationBoundaryData benchmarkTransportLCELInstance :=
  LCELP4CUniversalCertificationBoundaryData.ofAdmissibilityData
    benchmarkTransportLCELAdmissibilityData

/-- Canonical certification-boundary data on the DP / emitter instance. -/
def dpEmitterUniversalCertificationBoundaryData :
    LCELP4CUniversalCertificationBoundaryData dpEmitterLCELInstance :=
  LCELP4CUniversalCertificationBoundaryData.ofAdmissibilityData
    dpEmitterLCELAdmissibilityData

@[simp] theorem godel1931UniversalCertificationBoundaryData_toAdmissibilityData :
    godel1931UniversalCertificationBoundaryData.toAdmissibilityData
      = godel1931LCELAdmissibilityData :=
  rfl

@[simp] theorem benchmarkTransportUniversalCertificationBoundaryData_toAdmissibilityData :
    benchmarkTransportUniversalCertificationBoundaryData.toAdmissibilityData
      = benchmarkTransportLCELAdmissibilityData :=
  rfl

@[simp] theorem dpEmitterUniversalCertificationBoundaryData_toAdmissibilityData :
    dpEmitterUniversalCertificationBoundaryData.toAdmissibilityData
      = dpEmitterLCELAdmissibilityData :=
  rfl

/-- The canonical certification-boundary data agrees with the existing Gödel
certified wrapper. -/
theorem godel1931UniversalCertificationBoundaryData_toCertifiedFormalLCELInstance :
    godel1931UniversalCertificationBoundaryData.toCertifiedFormalLCELInstance
      = godel1931CertifiedFormalLCELInstance :=
  rfl

/-- The canonical certification-boundary data agrees with the existing
benchmark certified wrapper. -/
theorem benchmarkTransportUniversalCertificationBoundaryData_toCertifiedFormalLCELInstance :
    benchmarkTransportUniversalCertificationBoundaryData.toCertifiedFormalLCELInstance
      = benchmarkTransportCertifiedFormalLCELInstance :=
  rfl

/-- The canonical certification-boundary data agrees with the existing DP
certified wrapper. -/
theorem dpEmitterUniversalCertificationBoundaryData_toCertifiedFormalLCELInstance :
    dpEmitterUniversalCertificationBoundaryData.toCertifiedFormalLCELInstance
      = dpEmitterCertifiedFormalLCELInstance :=
  rfl

/-- Canonical Gödel certification witness. -/
theorem godel1931_hasCertification :
    CertifiedFormalLCELInstance.HasCertification godel1931LCELInstance :=
  (hasCertification_iff_nonempty_boundaryData godel1931LCELInstance).2
    ⟨godel1931UniversalCertificationBoundaryData⟩

/-- Canonical benchmark certification witness. -/
theorem benchmarkTransport_hasCertification :
    CertifiedFormalLCELInstance.HasCertification benchmarkTransportLCELInstance :=
  (hasCertification_iff_nonempty_boundaryData benchmarkTransportLCELInstance).2
    ⟨benchmarkTransportUniversalCertificationBoundaryData⟩

/-- Canonical DP certification witness. -/
theorem dpEmitter_hasCertification :
    CertifiedFormalLCELInstance.HasCertification dpEmitterLCELInstance :=
  (hasCertification_iff_nonempty_boundaryData dpEmitterLCELInstance).2
    ⟨dpEmitterUniversalCertificationBoundaryData⟩

end OperatorKO7.LCELP4CUniversalCertification
