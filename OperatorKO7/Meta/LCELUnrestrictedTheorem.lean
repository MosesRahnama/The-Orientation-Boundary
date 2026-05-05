import OperatorKO7.Meta.LCELSchema
import OperatorKO7.Meta.LCELReversibility
import OperatorKO7.Meta.LCELDpInstance
import OperatorKO7.Meta.LCELStructuralIdentity
import OperatorKO7.Meta.LCELUniversalTheorem
import OperatorKO7.Meta.LCELSemanticCorrespondence
import OperatorKO7.Meta.LCELSubstrateMathematics
import OperatorKO7.Meta.LCELBenchmarkDpComparison
import OperatorKO7.Meta.LCELMathematicalSupportWitness
import OperatorKO7.Meta.LCELMathematicalStructuralIdentity
import OperatorKO7.Meta.LCELAdmissibilityData

/-!
# LCEL Unrestricted Structural-Identity Theorem (Workstream E)

This file closes Workstream E of the LCEL universal-theorem roadmap: the
universal structural-identity theorem stated over raw `FormalLCELInstance`
pairs rather than over prepackaged `AdmissibleLCELInstance`s at the
theorem boundary.

The route is the one fixed in `LCEL_UNIVERSAL_THEOREM_ROADMAP.md`:
package the realization / support / comparison data into a single
unrestricted mathematical witness over raw instance pairs, build
admissibility **internally** from that witness, and lift the already-closed
Track G theorem (`lcel_structural_identity_of_mathematicalComparison`)
through the new carrier. No transport mathematics is reimplemented here;
the new module is a packaging-and-lift sprint sitting on top of the closed
`LCELMathematicalStructuralIdentity.lean` / `LCELUniversalTheorem.lean`
stack.

## Scope (honest residual boundary)

This file proves the universal structural-identity theorem **via an
unrestricted mathematical witness**. It does **not** prove the stronger
witness-free theorem `∀ L₁ L₂ : FormalLCELInstance, ∃ F, ...` over
arbitrary raw `FormalLCELInstance` pairs without any witness: producing
the witness for an arbitrary pair still requires mathematical content
that lives outside the LCEL schema itself (schema realization, four
proof-carrying substrate support records on each side, and a
cross-instance mathematical support witness including a strong slot
correspondence). The bare-quantifier form is explicitly not the target of
this sprint and is not claimed anywhere in this file.
-/

namespace OperatorKO7.LCELUnrestrictedTheorem

open OperatorKO7.LCELSchema
open OperatorKO7.LCELReversibility
open OperatorKO7.LCELStructuralIdentity
open OperatorKO7.LCELDpInstance
open OperatorKO7.LCELUniversalTheorem
open OperatorKO7.LCELSemanticCorrespondence
open OperatorKO7.LCELSubstrateMathematics
open OperatorKO7.LCELBenchmarkDpComparison
open OperatorKO7.LCELMathematical
open OperatorKO7.LCELMathematicalStructuralIdentity
open OperatorKO7.LCELAdmissibility

/-! ## The unrestricted mathematical witness carrier -/

/-- Unrestricted mathematical witness between two raw LCEL instances.

This carrier keeps the universal quantifier on **raw `FormalLCELInstance`
pairs** while packaging the realization, support, and comparison data
that the closed admissible-instance theorem stack actually needs:

- `sourceRealizes` / `targetRealizes` supply schema realization on both
  sides, without which no admissibility package can be built;
- `comparison` supplies the full `LCELMathematicalSupportWitness L₁ L₂`,
  which in turn carries the four proof-carrying substrate support
  records on each side, the strong slot correspondence
  (`LCELStrongSemanticSlotCorrespondence`), the theorem-strength
  substrate objects on each side, and the four cross-instance
  theorem-object transport functions with their coherence equations.

The unrestricted carrier is deliberately lightweight: every non-trivial
piece of mathematics it depends on already lives in
`Meta/LCELMathematicalSupportWitness.lean`. -/
structure LCELUnrestrictedMathematicalWitness
    (L₁ L₂ : FormalLCELInstance) : Type 1 where
  /-- Source-side schema realization. -/
  sourceRealizes : RealizesLCELSchema L₁.toSlotProfile
  /-- Target-side schema realization. -/
  targetRealizes : RealizesLCELSchema L₂.toSlotProfile
  /-- The full mathematical support witness between the two raw LCEL
  instances. -/
  comparison : LCELMathematicalSupportWitness L₁ L₂

namespace LCELUnrestrictedMathematicalWitness

/-- Build the source-side admissible instance from the unrestricted
witness. The underlying LCEL instance is `L₁`, the schema-realization
witness is `sourceRealizes`, and the four proof-carrying substrate
support records are read off from the `comparison` witness's source-side
fields. -/
def sourceAdmissibleInstance
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELUnrestrictedMathematicalWitness L₁ L₂) :
    AdmissibleLCELInstance where
  instance_ := L₁
  realizes := W.sourceRealizes
  baseSupport := W.comparison.sourceBaseSupport
  licenseSupport := W.comparison.sourceLicenseSupport
  reimportSupport := W.comparison.sourceReimportSupport
  boundarySupport := W.comparison.sourceBoundarySupport

/-- Build the target-side admissible instance from the unrestricted
witness. -/
def targetAdmissibleInstance
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELUnrestrictedMathematicalWitness L₁ L₂) :
    AdmissibleLCELInstance where
  instance_ := L₂
  realizes := W.targetRealizes
  baseSupport := W.comparison.targetBaseSupport
  licenseSupport := W.comparison.targetLicenseSupport
  reimportSupport := W.comparison.targetReimportSupport
  boundarySupport := W.comparison.targetBoundarySupport

/-- The source admissible instance's underlying LCEL carrier is literally
`L₁`. This is `rfl` by construction; named for documentation. -/
theorem sourceAdmissibleInstance_instance_
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELUnrestrictedMathematicalWitness L₁ L₂) :
    W.sourceAdmissibleInstance.instance_ = L₁ := rfl

/-- The target admissible instance's underlying LCEL carrier is literally
`L₂`. -/
theorem targetAdmissibleInstance_instance_
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELUnrestrictedMathematicalWitness L₁ L₂) :
    W.targetAdmissibleInstance.instance_ = L₂ := rfl

end LCELUnrestrictedMathematicalWitness

/-! ## Phase P2: unrestricted-witness construction automation

The builder `LCELUnrestrictedMathematicalWitness.ofAdmissibilityData`
takes two admissibility-data packages (one per side) and a cross-instance
mathematical support witness, and produces the unrestricted carrier
without any field-by-field repetition. Canonical unrestricted witnesses
below are refactored to use this builder. -/

/-- Build an unrestricted mathematical witness from two admissibility-data
packages plus a cross-instance mathematical support witness. The
support records stored in `W` are the authoritative ones used by the
unrestricted layer's internal admissibility builders; the `A₁` / `A₂`
arguments contribute the schema-realization witnesses. -/
def LCELUnrestrictedMathematicalWitness.ofAdmissibilityData
    {L₁ L₂ : FormalLCELInstance}
    (A₁ : LCELAdmissibilityData L₁)
    (A₂ : LCELAdmissibilityData L₂)
    (W : LCELMathematicalSupportWitness L₁ L₂) :
    LCELUnrestrictedMathematicalWitness L₁ L₂ where
  sourceRealizes := A₁.realizes
  targetRealizes := A₂.realizes
  comparison := W

/-! ## The unrestricted universal theorem

The theorem is a direct lift of the closed Track G theorem
`lcel_structural_identity_of_mathematicalComparison` through the new
carrier: the admissible instances are constructed internally from `W`
rather than being demanded at the theorem boundary. -/

/-- **LCEL unrestricted universal structural-identity theorem
(Workstream E, unrestricted-mathematical-witness form).**

For every pair of raw `FormalLCELInstance`s `L₁`, `L₂` equipped with an
`LCELUnrestrictedMathematicalWitness`, there exists a universal
quasi-functor between the admissible instances internally built from the
witness, with the target-side reversibility-asymmetry and
boundary-factorization packages obtained by genuine source-to-target
transport through the mathematical witness's theorem-object transport
functions (the Track G pipeline).

The universal quantifier runs over **raw `FormalLCELInstance` pairs** at
the theorem boundary; admissibility is constructed internally by the
witness rather than required of the caller. This is the sense in which
this theorem is unrestricted: it no longer demands prepackaged
`AdmissibleLCELInstance`s. -/
theorem lcel_unrestricted_structural_identity_of_mathematicalWitness
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELUnrestrictedMathematicalWitness L₁ L₂) :
    Nonempty
      (LCELUniversalQuasiFunctor
        W.sourceAdmissibleInstance
        W.targetAdmissibleInstance) :=
  lcel_structural_identity_of_mathematicalComparison
    (A₁ := W.sourceAdmissibleInstance)
    (A₂ := W.targetAdmissibleInstance)
    W.comparison

/-- Constructive form of the unrestricted universal theorem: the
universal quasi-functor is definable from the unrestricted mathematical
witness, with its target packages obtained by Track G transport. -/
def lcel_unrestricted_structural_identity_of_mathematicalWitness_witness
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELUnrestrictedMathematicalWitness L₁ L₂) :
    LCELUniversalQuasiFunctor
      W.sourceAdmissibleInstance
      W.targetAdmissibleInstance :=
  lcelUniversalQuasiFunctor_ofMathematicalComparison
    (A₁ := W.sourceAdmissibleInstance)
    (A₂ := W.targetAdmissibleInstance)
    W.comparison

/-- Bidirectional form: an unrestricted mathematical witness also yields
the reverse universal quasi-functor, via the support-comparison witness
obtained by downgrading `W.comparison` and reversing through
`LCELSupportComparisonWitness.symm`, then lifting through the closed
Route E1 theorem `lcel_universal_structural_identity_of_comparison`. -/
theorem lcel_unrestricted_structural_identity_of_mathematicalWitness_bidirectional
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELUnrestrictedMathematicalWitness L₁ L₂) :
    Nonempty
        (LCELUniversalQuasiFunctor
          W.sourceAdmissibleInstance
          W.targetAdmissibleInstance)
      ∧ Nonempty
        (LCELUniversalQuasiFunctor
          W.targetAdmissibleInstance
          W.sourceAdmissibleInstance) :=
  ⟨lcel_unrestricted_structural_identity_of_mathematicalWitness W,
    lcel_universal_structural_identity_of_comparison
      (A₁ := W.targetAdmissibleInstance)
      (A₂ := W.sourceAdmissibleInstance)
      (LCELSupportComparisonWitness.symm
        W.comparison.toLCELSupportComparisonWitness)⟩

/-! ## Canonical unrestricted witnesses and corollaries

Two canonical unrestricted mathematical witnesses, one per paper-facing
canonical pair, both thin wrappers around the canonical
`LCELMathematicalSupportWitness`es already defined in
`Meta/LCELMathematicalSupportWitness.lean`. -/

/-- Canonical Gödel 1931 ↔ native DP / emitter unrestricted mathematical
witness. The manuscript-critical endpoint for Workstream E.

Built via the Phase P2 `ofAdmissibilityData` builder from the canonical
admissibility-data packages plus the canonical mathematical support
witness. -/
def godel_dp_unrestrictedMathematicalWitness :
    LCELUnrestrictedMathematicalWitness
      godel1931LCELInstance
      dpEmitterLCELInstance :=
  LCELUnrestrictedMathematicalWitness.ofAdmissibilityData
    godel1931LCELAdmissibilityData
    dpEmitterLCELAdmissibilityData
    godel_dp_lcelMathematicalSupportWitness

/-- Canonical Gödel 1931 ↔ benchmark-transport unrestricted mathematical
witness, built via the Phase P2 `ofAdmissibilityData` builder. -/
def godel_benchmark_unrestrictedMathematicalWitness :
    LCELUnrestrictedMathematicalWitness
      godel1931LCELInstance
      benchmarkTransportLCELInstance :=
  LCELUnrestrictedMathematicalWitness.ofAdmissibilityData
    godel1931LCELAdmissibilityData
    benchmarkTransportLCELAdmissibilityData
    godel_benchmark_lcelMathematicalSupportWitness

/-- Universal structural identity between the Gödel 1931 side and the
native DP / emitter side, obtained over raw `FormalLCELInstance` pairs
via the unrestricted mathematical witness. Manuscript-critical corollary. -/
theorem godel_dp_unrestricted_structural_identity :
    Nonempty
      (LCELUniversalQuasiFunctor
        godel_dp_unrestrictedMathematicalWitness.sourceAdmissibleInstance
        godel_dp_unrestrictedMathematicalWitness.targetAdmissibleInstance) :=
  lcel_unrestricted_structural_identity_of_mathematicalWitness
    godel_dp_unrestrictedMathematicalWitness

/-- Universal structural identity between the Gödel 1931 side and the
benchmark-transport side, obtained over raw `FormalLCELInstance` pairs
via the unrestricted mathematical witness. -/
theorem godel_benchmark_unrestricted_structural_identity :
    Nonempty
      (LCELUniversalQuasiFunctor
        godel_benchmark_unrestrictedMathematicalWitness.sourceAdmissibleInstance
        godel_benchmark_unrestrictedMathematicalWitness.targetAdmissibleInstance) :=
  lcel_unrestricted_structural_identity_of_mathematicalWitness
    godel_benchmark_unrestrictedMathematicalWitness

/-- Bidirectional unrestricted structural identity on the Gödel ↔ DP
pair. -/
theorem godel_dp_unrestricted_structural_identity_bidirectional :
    Nonempty
        (LCELUniversalQuasiFunctor
          godel_dp_unrestrictedMathematicalWitness.sourceAdmissibleInstance
          godel_dp_unrestrictedMathematicalWitness.targetAdmissibleInstance)
      ∧ Nonempty
        (LCELUniversalQuasiFunctor
          godel_dp_unrestrictedMathematicalWitness.targetAdmissibleInstance
          godel_dp_unrestrictedMathematicalWitness.sourceAdmissibleInstance) :=
  lcel_unrestricted_structural_identity_of_mathematicalWitness_bidirectional
    godel_dp_unrestrictedMathematicalWitness

/-- Bidirectional unrestricted structural identity on the Gödel ↔
benchmark pair. -/
theorem godel_benchmark_unrestricted_structural_identity_bidirectional :
    Nonempty
        (LCELUniversalQuasiFunctor
          godel_benchmark_unrestrictedMathematicalWitness.sourceAdmissibleInstance
          godel_benchmark_unrestrictedMathematicalWitness.targetAdmissibleInstance)
      ∧ Nonempty
        (LCELUniversalQuasiFunctor
          godel_benchmark_unrestrictedMathematicalWitness.targetAdmissibleInstance
          godel_benchmark_unrestrictedMathematicalWitness.sourceAdmissibleInstance) :=
  lcel_unrestricted_structural_identity_of_mathematicalWitness_bidirectional
    godel_benchmark_unrestrictedMathematicalWitness

/-! ## Post-closure Phase P1: named hardening lemmas

These four named lemmas expose, as theorem-level statements, the
relationship between the unrestricted layer, the Track G transport
theorem, and the Route E1 comparison theorem. Each lemma is `rfl` by
design of the unrestricted layer; the point is that a future refactor
that accidentally forked the unrestricted layer off from Track G / Route
E1 would break these named theorems rather than silently pass. -/

/-- The source admissibility package's reversibility-asymmetry is built
from the comparison witness's source-side support records via
`lcelReversibilityAsymmetry_of_strongerSupports`, not from any
second code path. -/
theorem sourceAdmissibleInstance_reversibilityAsymmetry_eq
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELUnrestrictedMathematicalWitness L₁ L₂) :
    W.sourceAdmissibleInstance.reversibilityAsymmetry
      = lcelReversibilityAsymmetry_of_strongerSupports
          W.comparison.sourceBaseSupport
          W.comparison.sourceLicenseSupport
          W.comparison.sourceReimportSupport :=
  rfl

/-- The target admissibility package's boundary-factorization is built
from the comparison witness's target-side boundary support via
`lcelBoundaryFactorization_of_strongerSupport`, not from any second code
path. -/
theorem targetAdmissibleInstance_boundaryFactorization_eq
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELUnrestrictedMathematicalWitness L₁ L₂) :
    W.targetAdmissibleInstance.boundaryFactorization
      = lcelBoundaryFactorization_of_strongerSupport
          W.comparison.targetBoundarySupport :=
  rfl

/-- The unrestricted structural-identity constructive form is exactly
the Track G constructor
`lcelUniversalQuasiFunctor_ofMathematicalComparison` applied to the
unrestricted witness's comparison data on the internally built
admissible instances. This is the key "no fork" regression at the
theorem level: breaking the Track G lift would break this lemma. -/
theorem lcel_unrestricted_witness_eq_trackG
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELUnrestrictedMathematicalWitness L₁ L₂) :
    lcel_unrestricted_structural_identity_of_mathematicalWitness_witness W
      = lcelUniversalQuasiFunctor_ofMathematicalComparison
          (A₁ := W.sourceAdmissibleInstance)
          (A₂ := W.targetAdmissibleInstance)
          W.comparison :=
  rfl

/-- The reverse direction of the unrestricted bidirectional theorem is
exactly the Route E1 comparison theorem
`lcel_universal_structural_identity_of_comparison` applied to the
symm'd support-comparison downgrade of the unrestricted witness's
comparison data. -/
theorem lcel_unrestricted_bidirectional_reverse_eq_routeE1
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELUnrestrictedMathematicalWitness L₁ L₂) :
    (lcel_unrestricted_structural_identity_of_mathematicalWitness_bidirectional W).2
      = lcel_universal_structural_identity_of_comparison
          (A₁ := W.targetAdmissibleInstance)
          (A₂ := W.sourceAdmissibleInstance)
          (LCELSupportComparisonWitness.symm
            W.comparison.toLCELSupportComparisonWitness) :=
  rfl

end OperatorKO7.LCELUnrestrictedTheorem
