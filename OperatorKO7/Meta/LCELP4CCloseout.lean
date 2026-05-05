import OperatorKO7.Meta.LCELP4CCanonicalInstances
import OperatorKO7.Meta.LCELP4CUniversalCertification
import OperatorKO7.Meta.LCELP4CUniversalBlueprint

/-!
# LCEL P4C Closeout

This file states the exact formal closeout boundary for L3 / Phase P4C.

Raw unconditional P4C is not claimed on bare `FormalLCELInstance`. The
strongest current theorem boundary is the certified one already isolated in the
residual-obligation file: universal raw-instance certification together with
universal certified pair-blueprints.

This module packages that boundary under explicit theorem names and routes the
three canonical paper-facing pairs through the same closeout surface.
-/

namespace OperatorKO7.LCELP4CCloseout

open OperatorKO7.LCELSchema
open OperatorKO7.LCELUniversalTheorem
open OperatorKO7.LCELUnrestrictedExistence
open OperatorKO7.LCELP4CResidualObligation
open OperatorKO7.LCELP4CCanonicalInstances

/-- Exact theorem boundary for the current P4C closeout: the raw theorem is
available only once every raw instance is certified and every certified pair
carries a certified route-lift blueprint. -/
abbrev LCELP4CExactCertifiedBoundary : Prop :=
  CertifiedFormalLCELInstance.UniversalCertification
    ∧ CertifiedFormalLCELInstance.UniversalCertifiedRouteLiftBlueprint

/-- The exact certified boundary is now inhabited unconditionally because both
universal constructor obligations are closed on the current typed carrier. -/
theorem lcel_p4c_exactCertifiedBoundary_closed :
    LCELP4CExactCertifiedBoundary :=
  ⟨OperatorKO7.LCELP4CUniversalCertification.CertifiedFormalLCELInstance.universalCertification_closed,
    OperatorKO7.LCELP4CUniversalBlueprint.CertifiedFormalLCELInstance.universalCertifiedRouteLiftBlueprint_closed⟩

namespace LCELP4CExactCertifiedBoundary

/-- Namespace alias for the unconditional exact certified boundary theorem. -/
theorem unconditional :
    OperatorKO7.LCELP4CCloseout.LCELP4CExactCertifiedBoundary :=
  lcel_p4c_exactCertifiedBoundary_closed

end LCELP4CExactCertifiedBoundary

/-- Repackage the exact closeout boundary as the named residual-data catalog. -/
def lcel_p4c_residualDataCatalog_of_exactCertifiedBoundary
    (h : LCELP4CExactCertifiedBoundary) :
    LCELP4CResidualDataCatalog where
  universalCertification := h.1
  universalCertifiedRouteLiftBlueprint := h.2

/-- Repackage the exact closeout boundary as the paper-facing certified-boundary
catalog. -/
def lcel_p4c_certifiedBoundaryCatalog_of_exactCertifiedBoundary
    (h : LCELP4CExactCertifiedBoundary) :
    LCELP4CCertifiedBoundaryCatalog :=
  lcel_p4c_certified_boundary_catalog h.1 h.2

/-- The residual-data catalog is exactly the conjunction of the two open
universal constructor obligations. -/
theorem lcel_p4c_residualDataCatalog_iff_exactCertifiedBoundary :
    LCELP4CResidualDataCatalog ↔ LCELP4CExactCertifiedBoundary := by
  constructor
  · intro h
    exact ⟨h.universalCertification, h.universalCertifiedRouteLiftBlueprint⟩
  · intro h
    exact lcel_p4c_residualDataCatalog_of_exactCertifiedBoundary h

/-- The paper-facing certified-boundary catalog is equivalent to the exact open
constructor boundary. This makes the closeout theorem boundary impossible to
misstate. -/
theorem lcel_p4c_certifiedBoundaryCatalog_iff_exactCertifiedBoundary :
    LCELP4CCertifiedBoundaryCatalog ↔ LCELP4CExactCertifiedBoundary := by
  constructor
  · intro h
    exact certified_boundary_catalog_requires_open_universal_data h
  · intro h
    exact lcel_p4c_certifiedBoundaryCatalog_of_exactCertifiedBoundary h

/-- Strongest current universal theorem at the exact certified closeout
boundary. -/
theorem universal_lcel_witness_free_structural_identity_of_exactCertifiedBoundary
    (h : LCELP4CExactCertifiedBoundary) :
    LCELP4CRawTarget :=
  certified_boundary_catalog_projects_rawTarget
    (lcel_p4c_certifiedBoundaryCatalog_of_exactCertifiedBoundary h)

/-- The exact certified closeout boundary also projects the named universal
residual-package layer. -/
theorem universal_residualPackage_of_exactCertifiedBoundary
    (h : LCELP4CExactCertifiedBoundary) :
    UniversalLCELRouteLiftResidualPackage :=
  certified_boundary_catalog_projects_universalResidualPackage
    (lcel_p4c_certifiedBoundaryCatalog_of_exactCertifiedBoundary h)

/-- The named universal residual-package layer is now available without extra
hypotheses. -/
theorem lcel_p4c_unconditional_residualPackage :
    UniversalLCELRouteLiftResidualPackage :=
  universal_residualPackage_of_exactCertifiedBoundary
    lcel_p4c_exactCertifiedBoundary_closed

namespace LCELP4CRawTarget

/-- Namespace alias for the now-unconditional raw bare P4C theorem. -/
theorem unconditional :
    OperatorKO7.LCELP4CResidualObligation.LCELP4CRawTarget :=
  universal_lcel_witness_free_structural_identity_of_exactCertifiedBoundary
    lcel_p4c_exactCertifiedBoundary_closed

end LCELP4CRawTarget

/-- Public unconditional raw bare P4C theorem. -/
theorem lcel_p4c_unconditional_rawTarget :
    LCELP4CRawTarget :=
  LCELP4CRawTarget.unconditional

/-- Canonical benchmark ↔ DP closeout theorem routed through the finite
certified boundary catalog. -/
theorem benchmark_dp_witnessFreeStructuralIdentity_viaCloseoutBoundary :
    ∃ A₁ A₂ : AdmissibleLCELInstance,
      A₁.instance_ = benchmarkTransportLCELInstance
        ∧ A₂.instance_ = OperatorKO7.LCELDpInstance.dpEmitterLCELInstance
        ∧ Nonempty (LCELUniversalQuasiFunctor A₁ A₂) :=
  lcel_witness_free_structural_identity_of_hasResidualPackage
    benchmark_dp_hasRouteLiftResidualPackage

/-- Canonical Gödel ↔ DP closeout theorem routed through the finite certified
boundary catalog. -/
theorem godel_dp_witnessFreeStructuralIdentity_viaCloseoutBoundary :
    ∃ A₁ A₂ : AdmissibleLCELInstance,
      A₁.instance_ = godel1931LCELInstance
        ∧ A₂.instance_ = OperatorKO7.LCELDpInstance.dpEmitterLCELInstance
        ∧ Nonempty (LCELUniversalQuasiFunctor A₁ A₂) :=
  lcel_witness_free_structural_identity_of_hasResidualPackage
    godel_dp_hasRouteLiftResidualPackage

/-- Canonical Gödel ↔ benchmark closeout theorem routed through the finite
certified boundary catalog. -/
theorem godel_benchmark_witnessFreeStructuralIdentity_viaCloseoutBoundary :
    ∃ A₁ A₂ : AdmissibleLCELInstance,
      A₁.instance_ = godel1931LCELInstance
        ∧ A₂.instance_ = benchmarkTransportLCELInstance
        ∧ Nonempty (LCELUniversalQuasiFunctor A₁ A₂) :=
  lcel_witness_free_structural_identity_of_hasResidualPackage
    godel_benchmark_hasRouteLiftResidualPackage

end OperatorKO7.LCELP4CCloseout
