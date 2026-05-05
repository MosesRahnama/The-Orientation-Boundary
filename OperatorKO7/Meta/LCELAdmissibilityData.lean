import OperatorKO7.Meta.LCELSchema
import OperatorKO7.Meta.LCELReversibility
import OperatorKO7.Meta.LCELDpInstance
import OperatorKO7.Meta.LCELStructuralIdentity
import OperatorKO7.Meta.LCELUniversalTheorem

/-!
# LCEL Admissibility Data (post-closure Phase P2)

This file factors the data currently inlined into `AdmissibleLCELInstance`
into a standalone record tied to a single `FormalLCELInstance`. The goal
is to eliminate hand-written wrapper fragility in the post-closure
program: once a raw `FormalLCELInstance` has an
`LCELAdmissibilityData` package, lifting it into an
`AdmissibleLCELInstance` and bundling a pair into an
`LCELUnrestrictedMathematicalWitness` is a cheap and uniform operation.

The carrier `LCELAdmissibilityData L` packages:

- a schema-realization witness `realizes : RealizesLCELSchema L.toSlotProfile`;
- the four proof-carrying substrate support records
  (`baseSupport`, `licenseSupport`, `reimportSupport`, `boundarySupport`)
  on the instance `L`.

Canonical admissibility-data packages are supplied for the three
paper-facing canonical LCEL instances.

The coercion `LCELAdmissibilityData.toAdmissibleInstance` lifts an
admissibility-data package into an `AdmissibleLCELInstance`, and it is
definitionally equal to the existing hand-written canonical admissible
instances.
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

One package per paper-facing canonical LCEL instance, each built from the
same support records and realization theorem as the corresponding
canonical admissible instance in `Meta/LCELUniversalTheorem.lean`. The
resulting admissibility packages coincide definitionally with the
existing canonical admissible instances — see the named equalities
below. -/

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

The lifted admissible instance from canonical admissibility data equals
the existing canonical admissible instance, definitionally. -/

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
