import OperatorKO7.Meta.LCELSchema
import OperatorKO7.Meta.LCELReversibility
import OperatorKO7.Meta.LCELDpInstance
import OperatorKO7.Meta.LCELStructuralIdentity
import OperatorKO7.Meta.LCELUniversalTheorem

/-!
# LCEL admissibility data

This file packages the schema realization and four support records associated
with one `FormalLCELInstance`. `toAdmissibleInstance` projects the package into
the corresponding `AdmissibleLCELInstance` record.

The carrier `LCELAdmissibilityData L` packages:

- a schema-realization witness `realizes : RealizesLCELSchema L.toSlotProfile`;
- the four proof-carrying substrate support records
  (`baseSupport`, `licenseSupport`, `reimportSupport`, `boundarySupport`)
  on the instance `L`.

Admissibility-data packages are supplied for the three declared LCEL instances.

The named equalities at the end show that these projections reduce
definitionally to the separately declared admissible instances.
-/

namespace OperatorKO7.LCELAdmissibility

open OperatorKO7.LCELSchema
open OperatorKO7.LCELReversibility
open OperatorKO7.LCELStructuralIdentity
open OperatorKO7.LCELDpInstance
open OperatorKO7.LCELUniversalTheorem

/-- Admissibility data attached to a single raw `FormalLCELInstance`:
schema realization plus the four proof-carrying substrate support
records. -/
structure LCELAdmissibilityData (L : FormalLCELInstance) : Type 1 where
  /-- Schema realization for `L`. -/
  realizes : RealizesLCELSchema L.toSlotProfile
  /-- Base-layer reversibility support. -/
  baseSupport : BaseReversibilitySupport L
  /-- License-side irreversibility support. -/
  licenseSupport : LicenseIrreversibilitySupport L
  /-- Reimport-side reversibility support. -/
  reimportSupport : ReimportReversibilitySupport L
  /-- Boundary-factorization support. -/
  boundarySupport : BoundaryFactorizationSupport L

namespace LCELAdmissibilityData

/-- Lift admissibility data into an `AdmissibleLCELInstance`. -/
def toAdmissibleInstance
    {L : FormalLCELInstance}
    (D : LCELAdmissibilityData L) :
    AdmissibleLCELInstance where
  instance_ := L
  realizes := D.realizes
  baseSupport := D.baseSupport
  licenseSupport := D.licenseSupport
  reimportSupport := D.reimportSupport
  boundarySupport := D.boundarySupport

/-- The lifted admissible instance's underlying LCEL carrier is `L`. -/
theorem toAdmissibleInstance_instance_
    {L : FormalLCELInstance}
    (D : LCELAdmissibilityData L) :
    D.toAdmissibleInstance.instance_ = L := rfl

end LCELAdmissibilityData

/-! ## Canonical admissibility-data packages

Each package uses the same support records and realization theorem as the
corresponding admissible instance in `Meta/LCELUniversalTheorem.lean`. -/

/-- Gödel 1931-side canonical admissibility data. -/
def godel1931LCELAdmissibilityData :
    LCELAdmissibilityData godel1931LCELInstance where
  realizes := godel1931LCELInstance_realizesSchema
  baseSupport := godel1931BaseReversibilitySupport
  licenseSupport := godel1931LicenseIrreversibilitySupport
  reimportSupport := godel1931ReimportReversibilitySupport
  boundarySupport := godel1931BoundaryFactorizationSupport

/-- Benchmark-transport-side canonical admissibility data. -/
def benchmarkTransportLCELAdmissibilityData :
    LCELAdmissibilityData benchmarkTransportLCELInstance where
  realizes := benchmarkTransportLCELInstance_realizesSchema
  baseSupport := benchmarkTransportBaseReversibilitySupport
  licenseSupport := benchmarkTransportLicenseIrreversibilitySupport
  reimportSupport := benchmarkTransportReimportReversibilitySupport
  boundarySupport := benchmarkTransportBoundaryFactorizationSupport

/-- Native DP / emitter-side canonical admissibility data. -/
def dpEmitterLCELAdmissibilityData :
    LCELAdmissibilityData dpEmitterLCELInstance where
  realizes := dpEmitterLCELInstance_realizesSchema
  baseSupport := dpEmitterBaseReversibilitySupport
  licenseSupport := dpEmitterLicenseIrreversibilitySupport
  reimportSupport := dpEmitterReimportReversibilitySupport
  boundarySupport := dpEmitterBoundaryFactorizationSupport

/-! ## Coincidence with canonical admissible instances

Each lifted admissible instance is definitionally equal to its separately
declared counterpart. -/

/-- Gödel 1931 canonical admissibility data lifts to
`godel1931AdmissibleLCELInstance`. -/
theorem godel1931LCELAdmissibilityData_toAdmissibleInstance_eq :
    godel1931LCELAdmissibilityData.toAdmissibleInstance
      = godel1931AdmissibleLCELInstance :=
  rfl

/-- Benchmark-transport canonical admissibility data lifts to
`benchmarkTransportAdmissibleLCELInstance`. -/
theorem benchmarkTransportLCELAdmissibilityData_toAdmissibleInstance_eq :
    benchmarkTransportLCELAdmissibilityData.toAdmissibleInstance
      = benchmarkTransportAdmissibleLCELInstance :=
  rfl

/-- Native DP / emitter canonical admissibility data lifts to
`dpEmitterAdmissibleLCELInstance`. -/
theorem dpEmitterLCELAdmissibilityData_toAdmissibleInstance_eq :
    dpEmitterLCELAdmissibilityData.toAdmissibleInstance
      = dpEmitterAdmissibleLCELInstance :=
  rfl

end OperatorKO7.LCELAdmissibility
