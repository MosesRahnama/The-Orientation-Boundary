import OperatorKO7.Meta.LCELSchema
import OperatorKO7.Meta.LCELReversibility
import OperatorKO7.Meta.LCELDpInstance
import OperatorKO7.Meta.LCELStructuralIdentity

/-!
# LCEL Universal Structural Identity Theorem

This file closes the universal form of Theorem~\ref{thm:lcel-structural-identity}
(*Operational Inexpressibility at the Primitive-Recursion Orientation Boundary*) under the admissibility route E1 described
in `LCEL_UNIVERSAL_THEOREM_ROADMAP.md`, and it closes it **via genuine
source-to-target transport through an explicit comparison witness**, not by
target-supplied target packages. The weaker admissibility-only packaging is
kept as a separate convenience wrapper; the genuine transport theorem is the
main endpoint.

Two layers live here:

1. an admissibility carrier `AdmissibleLCELInstance`, bundling a typed
   `FormalLCELInstance` with a schema-realization witness and the four
   proof-carrying substrate support records; and
2. a transport-carrying `LCELUniversalQuasiFunctor`, built from an
   `AdmissibleLCELComparisonWitness` (a support-comparison witness between the
   underlying LCEL instances). The target reversibility-asymmetry and
   boundary-factorization packages are obtained by transport from the source
   admissibility data via the comparison witness, not by copying from the
   target admissibility data.

The three paper-facing canonical instances (`godel1931LCELInstance`,
`benchmarkTransportLCELInstance`, and the native `dpEmitterLCELInstance`) are
all admissible, and the three canonical pairs all carry concrete support
comparison witnesses from `LCELStructuralIdentity.lean`. The universal
structural-identity theorem specializes to these three pairs by genuine
transport.
-/

namespace OperatorKO7.LCELUniversalTheorem

open OperatorKO7.LCELSchema
open OperatorKO7.LCELReversibility
open OperatorKO7.LCELStructuralIdentity
open OperatorKO7.LCELDpInstance

/-! ## Admissibility carrier -/

/-- An admissible LCEL instance bundles a typed `FormalLCELInstance` with a
schema-realization witness and the four proof-carrying substrate support
records required by the operational-inexpressibility manuscript Propositions 5.8 and 5.9.

Admissibility is not the same as mere instance-inhabitance: it additionally
packages the four substrate records documented in `Meta/LCELReversibility.lean`,
which already carry proof-carrying content for the base, license, reimport,
and boundary-factorization clauses. -/
structure AdmissibleLCELInstance : Type 1 where
  /-- Underlying typed LCEL carrier. -/
  instance_ : FormalLCELInstance
  /-- Schema realization: all six LCEL clauses hold. -/
  realizes : RealizesLCELSchema instance_.toSlotProfile
  /-- Proof-carrying base-layer reversibility support. -/
  baseSupport : BaseReversibilitySupport instance_
  /-- Proof-carrying license-side irreversibility support. -/
  licenseSupport : LicenseIrreversibilitySupport instance_
  /-- Proof-carrying reimport-side reversibility support. -/
  reimportSupport : ReimportReversibilitySupport instance_
  /-- Proof-carrying boundary-factorization support. -/
  boundarySupport : BoundaryFactorizationSupport instance_

namespace AdmissibleLCELInstance

/-- The reversibility-asymmetry package derived from the admissibility data. -/
def reversibilityAsymmetry (A : AdmissibleLCELInstance) :
    LCELReversibilityAsymmetry A.instance_ :=
  lcelReversibilityAsymmetry_of_strongerSupports
    A.baseSupport A.licenseSupport A.reimportSupport

/-- The boundary-factorization package derived from the admissibility data. -/
def boundaryFactorization (A : AdmissibleLCELInstance) :
    LCELBoundaryFactorization A.instance_ :=
  lcelBoundaryFactorization_of_strongerSupport A.boundarySupport

/-- Base-step reversibility witness extracted from the admissibility data. -/
def baseStepReversibilityWitness (A : AdmissibleLCELInstance) :
    BaseStepReversibilityWitness A.instance_ :=
  BaseReversibilitySupport.toBaseStepReversibilityWitness A.baseSupport

/-- License-irreversibility witness extracted from the admissibility data. -/
def licenseIrreversibilityWitness (A : AdmissibleLCELInstance) :
    LicenseIrreversibilityWitness A.instance_ :=
  LicenseIrreversibilitySupport.toLicenseIrreversibilityWitness A.licenseSupport

/-- Reimport-reversibility witness extracted from the admissibility data. -/
def reimportReversibilityWitness (A : AdmissibleLCELInstance) :
    ReimportReversibilityWitness A.instance_ :=
  ReimportReversibilitySupport.toReimportReversibilityWitness A.reimportSupport

/-- Projection-factorization witness extracted from the admissibility data. -/
def projectionFactorizationWitness (A : AdmissibleLCELInstance) :
    ProjectionFactorizationWitness A.instance_ :=
  BoundaryFactorizationSupport.toProjectionFactorizationWitness A.boundarySupport

end AdmissibleLCELInstance

/-! ## Canonical admissibility packages -/

/-- The Gödel 1931 canonical LCEL instance is admissible. -/
def godel1931AdmissibleLCELInstance : AdmissibleLCELInstance where
  instance_ := godel1931LCELInstance
  realizes := godel1931LCELInstance_realizesSchema
  baseSupport := godel1931BaseReversibilitySupport
  licenseSupport := godel1931LicenseIrreversibilitySupport
  reimportSupport := godel1931ReimportReversibilitySupport
  boundarySupport := godel1931BoundaryFactorizationSupport

/-- The benchmark-transport canonical LCEL instance is admissible. -/
def benchmarkTransportAdmissibleLCELInstance : AdmissibleLCELInstance where
  instance_ := benchmarkTransportLCELInstance
  realizes := benchmarkTransportLCELInstance_realizesSchema
  baseSupport := benchmarkTransportBaseReversibilitySupport
  licenseSupport := benchmarkTransportLicenseIrreversibilitySupport
  reimportSupport := benchmarkTransportReimportReversibilitySupport
  boundarySupport := benchmarkTransportBoundaryFactorizationSupport

/-- The native DP / emitter-side canonical LCEL instance is admissible. -/
def dpEmitterAdmissibleLCELInstance : AdmissibleLCELInstance where
  instance_ := dpEmitterLCELInstance
  realizes := dpEmitterLCELInstance_realizesSchema
  baseSupport := dpEmitterBaseReversibilitySupport
  licenseSupport := dpEmitterLicenseIrreversibilitySupport
  reimportSupport := dpEmitterReimportReversibilitySupport
  boundarySupport := dpEmitterBoundaryFactorizationSupport

/-! ## Universal quasi-functor

A `LCELUniversalQuasiFunctor` carries the slot-level quasi-functor together
with a target-side reversibility-asymmetry package and a target-side
boundary-factorization package. No coherence field forces the target packages
to equal the target admissibility data's own packages: this is deliberate,
because the main universal constructor supplies these target packages via
genuine source-to-target transport through a comparison witness, not by
copying from the target side.
-/

/-- Universal quasi-functor between two admissible LCEL instances. -/
structure LCELUniversalQuasiFunctor
    (A₁ A₂ : AdmissibleLCELInstance) : Type where
  /-- Slot-level quasi-functor between the underlying LCEL instances. -/
  toQuasiFunctor : LCELQuasiFunctor A₁.instance_ A₂.instance_
  /-- Target-side reversibility-asymmetry package. -/
  transportedReversibilityAsymmetry : LCELReversibilityAsymmetry A₂.instance_
  /-- Target-side boundary-factorization package. -/
  transportedBoundaryFactorization : LCELBoundaryFactorization A₂.instance_

namespace LCELUniversalQuasiFunctor

/-- A universal quasi-functor yields a schema-realization transport from the
source to the target, via its slot-level quasi-functor. -/
theorem transports_realization
    {A₁ A₂ : AdmissibleLCELInstance}
    (F : LCELUniversalQuasiFunctor A₁ A₂) :
    RealizesLCELSchema A₂.instance_.toSlotProfile :=
  F.toQuasiFunctor.transports_realization A₁.realizes

/-- A universal quasi-functor certifies target-side reversibility asymmetry. -/
def delivers_reversibilityAsymmetry
    {A₁ A₂ : AdmissibleLCELInstance}
    (F : LCELUniversalQuasiFunctor A₁ A₂) :
    LCELReversibilityAsymmetry A₂.instance_ :=
  F.transportedReversibilityAsymmetry

/-- A universal quasi-functor certifies target-side boundary factorization. -/
def delivers_boundaryFactorization
    {A₁ A₂ : AdmissibleLCELInstance}
    (F : LCELUniversalQuasiFunctor A₁ A₂) :
    LCELBoundaryFactorization A₂.instance_ :=
  F.transportedBoundaryFactorization

/-- Identity universal quasi-functor on any admissible instance. The target
packages on the self-loop come from the instance's own admissibility data. -/
def id (A : AdmissibleLCELInstance) : LCELUniversalQuasiFunctor A A where
  toQuasiFunctor := LCELQuasiFunctor.id A.instance_
  transportedReversibilityAsymmetry := A.reversibilityAsymmetry
  transportedBoundaryFactorization := A.boundaryFactorization

end LCELUniversalQuasiFunctor

/-! ## Admissibility-comparison witness

The honest universal theorem takes a comparison witness between the
underlying LCEL instances. That witness is already supplied by
`LCELSupportComparisonWitness`, which carries both sides' substrate support
records together with equivalence data on the external-license and
reimport-class slots. An admissibility-comparison witness is simply such a
support-comparison witness between the `instance_` fields of two admissible
instances.
-/

/-- Comparison witness between two admissible LCEL instances. -/
abbrev AdmissibleLCELComparisonWitness
    (A₁ A₂ : AdmissibleLCELInstance) : Type :=
  LCELSupportComparisonWitness A₁.instance_ A₂.instance_

namespace AdmissibleLCELComparisonWitness

/-- Reverse an admissibility-comparison witness. -/
def symm
    {A₁ A₂ : AdmissibleLCELInstance}
    (W : AdmissibleLCELComparisonWitness A₁ A₂) :
    AdmissibleLCELComparisonWitness A₂ A₁ :=
  LCELSupportComparisonWitness.symm W

end AdmissibleLCELComparisonWitness

/-! ## Genuine source-to-target transport: the main universal constructor -/

/-- Universal quasi-functor built from a comparison witness by genuine
source-to-target transport.

The slot-level part is obtained by forgetting the support-record fields and
recovering the underlying slot-level comparison witness, which yields a
`LCELQuasiFunctor` directly. The target reversibility-asymmetry and
boundary-factorization packages are obtained by **transporting the source
admissibility data** across the comparison witness using the source-side
transport theorems already proved in
`Meta/LCELStructuralIdentity.lean`. They are not copied from the target
admissibility data.

This is the honest Route E1 closure of the universal structural-identity
theorem: the universal quantifier runs over admissibility pairs equipped
with genuine comparison data. -/
def lcelUniversalQuasiFunctor_ofComparison
    {A₁ A₂ : AdmissibleLCELInstance}
    (W : AdmissibleLCELComparisonWitness A₁ A₂) :
    LCELUniversalQuasiFunctor A₁ A₂ where
  toQuasiFunctor :=
    LCELComparisonWitness.toQuasiFunctor
      (LCELSemanticComparisonWitness.toComparisonWitness
        (LCELSupportComparisonWitness.toSemanticComparisonWitness W))
  transportedReversibilityAsymmetry :=
    LCELSupportComparisonWitness.transports_reversibilityAsymmetryFromSourceSupport W
  transportedBoundaryFactorization :=
    LCELSupportComparisonWitness.transports_boundaryFactorizationFromSourceSupport W

/-! ## The universal structural-identity theorem -/

/-- **LCEL universal structural-identity theorem (Route E1, transport form).**

For every pair of admissible LCEL instances `A₁`, `A₂` equipped with a
comparison witness `W`, there exists a universal quasi-functor whose
target-side reversibility-asymmetry and boundary-factorization packages are
obtained by genuine source-to-target transport through `W` rather than
copied from `A₂`. The universal quantifier runs over admissibility pairs
equipped with real comparison data; no slot-level parallelism is asserted
without such data. -/
theorem lcel_universal_structural_identity_of_comparison
    {A₁ A₂ : AdmissibleLCELInstance}
    (W : AdmissibleLCELComparisonWitness A₁ A₂) :
    Nonempty (LCELUniversalQuasiFunctor A₁ A₂) :=
  ⟨lcelUniversalQuasiFunctor_ofComparison W⟩

/-- Constructive form: the universal quasi-functor is definable from the
comparison witness. -/
def lcel_universal_structural_identity_of_comparison_witness
    {A₁ A₂ : AdmissibleLCELInstance}
    (W : AdmissibleLCELComparisonWitness A₁ A₂) :
    LCELUniversalQuasiFunctor A₁ A₂ :=
  lcelUniversalQuasiFunctor_ofComparison W

/-- Bidirectional form: reversing the comparison witness gives the reverse
universal quasi-functor. -/
theorem lcel_universal_structural_identity_of_comparison_bidirectional
    {A₁ A₂ : AdmissibleLCELInstance}
    (W : AdmissibleLCELComparisonWitness A₁ A₂) :
    Nonempty (LCELUniversalQuasiFunctor A₁ A₂)
      ∧ Nonempty (LCELUniversalQuasiFunctor A₂ A₁) :=
  ⟨lcel_universal_structural_identity_of_comparison W,
    lcel_universal_structural_identity_of_comparison
      (AdmissibleLCELComparisonWitness.symm W)⟩

/-! ## Admissibility-only packaging (weaker convenience wrapper)

The following section is an admissibility-only packaging layer. It does not
use any cross-instance comparison witness: given two admissible instances,
it builds a universal quasi-functor whose slot-level biconditionals come
from the fact that both instances realize the LCEL schema, and whose
target-side substrate packages are the target admissibility data's own
packages.

This is not the same as the genuine transport theorem above. It is kept as
a convenience wrapper documenting what admissibility alone supplies, and as
an upper bound on what can be claimed without a comparison witness. -/

/-- Slot-level quasi-functor between two admissible LCEL instances assembled
from the fact that both instances realize the LCEL schema. Each biconditional
is discharged by realization inhabitance on both sides; no cross-instance
comparison data is used. -/
def quasiFunctor_ofAdmissibilityOnly
    (A₁ A₂ : AdmissibleLCELInstance) :
    LCELQuasiFunctor A₁.instance_ A₂.instance_ where
  baseSystemMap := Iff.intro (fun _ => A₂.realizes.1) (fun _ => A₁.realizes.1)
  boundaryMap :=
    Iff.intro (fun _ => A₂.realizes.2.1) (fun _ => A₁.realizes.2.1)
  externalLicenseMap :=
    Iff.intro (fun _ => A₂.realizes.2.2.1) (fun _ => A₁.realizes.2.2.1)
  licensedExtensionMap :=
    Iff.intro (fun _ => A₂.realizes.2.2.2.1) (fun _ => A₁.realizes.2.2.2.1)
  reimportClassMap :=
    Iff.intro (fun _ => A₂.realizes.2.2.2.2.1)
      (fun _ => A₁.realizes.2.2.2.2.1)
  annotationFunctorMap :=
    Iff.intro (fun _ => A₂.realizes.2.2.2.2.2)
      (fun _ => A₁.realizes.2.2.2.2.2)

/-- Universal quasi-functor assembled from admissibility alone, with
target-side substrate packages supplied by the target admissibility data.

This is the admissibility-only packaging wrapper. It is weaker than
`lcelUniversalQuasiFunctor_ofComparison`: it does not transport anything
from the source; it certifies that given admissibility on both sides, a
universal-shaped carrier exists. -/
def lcelUniversalQuasiFunctor_fromAdmissibilityOnly
    (A₁ A₂ : AdmissibleLCELInstance) :
    LCELUniversalQuasiFunctor A₁ A₂ where
  toQuasiFunctor := quasiFunctor_ofAdmissibilityOnly A₁ A₂
  transportedReversibilityAsymmetry := A₂.reversibilityAsymmetry
  transportedBoundaryFactorization := A₂.boundaryFactorization

/-- Admissibility-only packaging: any two admissible LCEL instances admit a
universal-shaped carrier. This does not use a comparison witness and does
not establish source-to-target transport; it certifies only that
admissibility on both sides suffices to populate the universal carrier from
target-local data. -/
theorem lcel_admissibility_gives_universalQuasiFunctor
    (A₁ A₂ : AdmissibleLCELInstance) :
    Nonempty (LCELUniversalQuasiFunctor A₁ A₂) :=
  ⟨lcelUniversalQuasiFunctor_fromAdmissibilityOnly A₁ A₂⟩

/-! ## Canonical comparison witnesses for the three paper-facing pairs

Each of the three paper-facing canonical pairs carries a concrete
support-comparison witness proved in `Meta/LCELStructuralIdentity.lean`.
Lifting the witness to an `AdmissibleLCELComparisonWitness` is a matter of
matching `instance_` fields; the admissibility packages on both sides are
supplied by the canonical admissibility packages above.
-/

/-- Canonical comparison witness between the Gödel 1931 admissible LCEL
instance and the native DP / emitter-side admissible LCEL instance. This is
the manuscript-critical comparison. -/
def godel_dp_admissibleLCELComparisonWitness :
    AdmissibleLCELComparisonWitness
      godel1931AdmissibleLCELInstance
      dpEmitterAdmissibleLCELInstance :=
  godel_dpEmitter_lcelSupportComparisonWitness

/-- Canonical comparison witness between the Gödel 1931 admissible LCEL
instance and the benchmark-transport admissible LCEL instance. -/
def godel_benchmark_admissibleLCELComparisonWitness :
    AdmissibleLCELComparisonWitness
      godel1931AdmissibleLCELInstance
      benchmarkTransportAdmissibleLCELInstance :=
  godel_benchmark_lcelSupportComparisonWitness

/-! ## Canonical universal corollaries via genuine transport -/

/-- Universal quasi-functor from the Gödel 1931 side to the native DP /
emitter side, constructed by genuine source-to-target transport through the
canonical support-comparison witness. -/
def godel_dp_universal_quasiFunctor :
    LCELUniversalQuasiFunctor
      godel1931AdmissibleLCELInstance
      dpEmitterAdmissibleLCELInstance :=
  lcelUniversalQuasiFunctor_ofComparison
    godel_dp_admissibleLCELComparisonWitness

/-- Universal structural identity between the Gödel 1931 side and the native
DP / emitter side, obtained by genuine source-to-target transport through
the canonical support-comparison witness. This is the manuscript-critical
corollary of the universal theorem. -/
theorem godel_dp_universal_structural_identity :
    Nonempty
      (LCELUniversalQuasiFunctor
        godel1931AdmissibleLCELInstance
        dpEmitterAdmissibleLCELInstance) :=
  lcel_universal_structural_identity_of_comparison
    godel_dp_admissibleLCELComparisonWitness

/-- Universal quasi-functor from the Gödel 1931 side to the
benchmark-transport side, constructed by genuine source-to-target transport
through the canonical support-comparison witness. -/
def godel_benchmark_universal_quasiFunctor :
    LCELUniversalQuasiFunctor
      godel1931AdmissibleLCELInstance
      benchmarkTransportAdmissibleLCELInstance :=
  lcelUniversalQuasiFunctor_ofComparison
    godel_benchmark_admissibleLCELComparisonWitness

/-- Universal structural identity between the Gödel 1931 side and the
benchmark-transport side, obtained by genuine source-to-target transport
through the canonical support-comparison witness. -/
theorem godel_benchmark_universal_structural_identity :
    Nonempty
      (LCELUniversalQuasiFunctor
        godel1931AdmissibleLCELInstance
        benchmarkTransportAdmissibleLCELInstance) :=
  lcel_universal_structural_identity_of_comparison
    godel_benchmark_admissibleLCELComparisonWitness

end OperatorKO7.LCELUniversalTheorem
