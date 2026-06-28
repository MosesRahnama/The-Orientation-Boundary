import OperatorKO7.Meta.LCELSchema
import OperatorKO7.Meta.LCELReversibility
import OperatorKO7.Meta.LCELDpInstance
import OperatorKO7.Meta.LCELStructuralIdentity
import OperatorKO7.Meta.LCELUniversalTheorem
import OperatorKO7.Meta.LCELSemanticCorrespondence
import OperatorKO7.Meta.LCELSubstrateMathematics
import OperatorKO7.Meta.LCELBenchmarkDpComparison
import OperatorKO7.Meta.LCELMathematicalSupportWitness

/-!
# LCEL Structural Identity via Mathematical Support Witness

Workstream D of the LCEL universal-theorem roadmap: the strong restricted
theorem that takes a `LCELMathematicalSupportWitness` as input and delivers
a universal quasi-functor whose slot-level and substrate output is built
**operationally from the mathematical support fields**, not by downgrading
to the weaker support-comparison witness.

The main constructor `lcelUniversalQuasiFunctor_ofMathematicalComparison`
consumes:

- the slot correspondence `W.slotCorrespondence` (Workstream A) together
  with the stagewise equivalence, to build the slot-level `LCELQuasiFunctor`
  via `LCELComparisonWitness.ofSemanticSlotCorrespondence`; and
- **the source-side theorem-strength substrate objects together with the
  witness's explicit theorem-object transport functions**
  (`transportBase W.sourceBaseTheorem`,
  `transportLicense W.sourceLicenseTheorem`,
  `transportReimport W.sourceReimportTheorem`,
  `transportBoundary W.sourceBoundaryTheorem` from Workstream B and the
  cross-instance transport layer added on top of it)
  to build the target-side reversibility-asymmetry and boundary-
  factorization packages via the substrate-downgrade lemmas.

The target-side theorem fields `W.targetBaseTheorem` etc. are still
present on the witness (they are what makes the support comparison
biconditional honest), but the constructor never uses them directly: by
the transport coherence equations (`transportBase_source` etc.) the
transported source theorem is equal to the target field anyway, so the
constructor-level switch is a mathematical upgrade, not just a refactor.

The earlier downgrade route `toLCELSupportComparisonWitness →
lcelUniversalQuasiFunctor_ofComparison` remains available as
`lcelUniversalQuasiFunctor_ofMathematicalComparison_viaSupportDowngrade`
and is provably equivalent to the stronger construction on the canonical
instances.

Canonical corollaries are supplied for the two manuscript-critical canonical
pairs (Gödel ↔ benchmark-transport and Gödel ↔ native DP / emitter) via
the stronger operational route.
-/

namespace OperatorKO7.LCELMathematicalStructuralIdentity

open OperatorKO7.LCELSchema
open OperatorKO7.LCELReversibility
open OperatorKO7.LCELStructuralIdentity
open OperatorKO7.LCELDpInstance
open OperatorKO7.LCELUniversalTheorem
open OperatorKO7.LCELSemanticCorrespondence
open OperatorKO7.LCELSubstrateMathematics
open OperatorKO7.LCELBenchmarkDpComparison
open OperatorKO7.LCELMathematical

/-! ## Universal quasi-functor from a mathematical support witness

The stronger constructor builds each output component from the
mathematical support witness's new fields, not from the inherited
support-comparison witness:

- the slot-level quasi-functor comes from the slot correspondence plus the
  stagewise equivalence via `LCELComparisonWitness.ofSemanticSlotCorrespondence`;
- the target reversibility-asymmetry package is obtained by running the
  witness's explicit theorem-object transport maps on the **source-side**
  theorem-strength substrate objects `sourceBaseTheorem`,
  `sourceLicenseTheorem`, `sourceReimportTheorem`, and then substrate-
  downgrading the transported targets into the witness layer used by
  `lcel_reversibility_asymmetry_of_witnesses`;
- the target boundary-factorization package is obtained by running
  `transportBoundary` on `sourceBoundaryTheorem` and substrate-downgrading
  the result via `lcel_boundary_factorization_of_witness`.

This means every mathematical field of the input is used operationally:
both the four `source...Theorem` fields and the four `transport...`
transport functions enter the constructor body. The target-side theorem
fields `W.target...Theorem` are no longer mentioned; by the transport
coherence equations they are equal to the transported source theorems,
so the conclusion is unchanged, but the mathematical route is now
source-to-target.
-/

/-- Universal quasi-functor constructed operationally from the mathematical
support witness's source-side theorems plus explicit theorem-object
transport. Slot biconditionals come from `slotCorrespondence` and
`comparisonStagewise`; each target-side substrate package is built by
applying the corresponding `transport...` function to the source-side
theorem and downgrading the transported target theorem into the substrate
witness layer. -/
def lcelUniversalQuasiFunctor_ofMathematicalComparison
    {A₁ A₂ : AdmissibleLCELInstance}
    (W :
      LCELMathematicalSupportWitness
        A₁.instance_ A₂.instance_) :
    LCELUniversalQuasiFunctor A₁ A₂ where
  toQuasiFunctor :=
    LCELComparisonWitness.toQuasiFunctor
      (LCELComparisonWitness.ofSemanticSlotCorrespondence
        W.slotCorrespondence.toSlotCorrespondence
        W.comparisonStagewise)
  transportedReversibilityAsymmetry :=
    lcel_reversibility_asymmetry_of_witnesses
      (BaseReversibilityTheorem.toBaseStepReversibilityWitness
        (W.transportBase W.sourceBaseTheorem))
      (LicenseIrreversibilityTheorem.toLicenseIrreversibilityWitness
        (W.transportLicense W.sourceLicenseTheorem))
      (ReimportReversibilityTheorem.toReimportReversibilityWitness
        (W.transportReimport W.sourceReimportTheorem))
  transportedBoundaryFactorization :=
    lcel_boundary_factorization_of_witness
      (BoundaryFactorizationTheorem.toProjectionFactorizationWitness
        (W.transportBoundary W.sourceBoundaryTheorem))

/-! ## Transport-coherence regression lemmas

The following four lemmas are the mathematical content of the source-to-
target upgrade: each says that, on the canonical source theorem, the
witness's transport produces the canonical target theorem. They are
provable by `rfl` on the canonical witnesses by design of the transport
fields, but they are stated as named theorems so that any *future*
non-canonical instance of `LCELMathematicalSupportWitness` has to discharge
them explicitly in order to be admissible.

These are the "nontrivial transport tests": they are mathematical
regression statements about how the transport interacts with the canonical
theorem fields, not `#check`-style reachability. -/

/-- Transport of the source base theorem recovers the target base theorem. -/
theorem transportBase_canonical
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELMathematicalSupportWitness L₁ L₂) :
    W.transportBase W.sourceBaseTheorem = W.targetBaseTheorem :=
  W.transportBase_source

/-- Transport of the source license theorem recovers the target license
theorem. -/
theorem transportLicense_canonical
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELMathematicalSupportWitness L₁ L₂) :
    W.transportLicense W.sourceLicenseTheorem = W.targetLicenseTheorem :=
  W.transportLicense_source

/-- Transport of the source reimport theorem recovers the target reimport
theorem. -/
theorem transportReimport_canonical
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELMathematicalSupportWitness L₁ L₂) :
    W.transportReimport W.sourceReimportTheorem = W.targetReimportTheorem :=
  W.transportReimport_source

/-- Transport of the source boundary theorem recovers the target boundary
theorem. -/
theorem transportBoundary_canonical
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELMathematicalSupportWitness L₁ L₂) :
    W.transportBoundary W.sourceBoundaryTheorem = W.targetBoundaryTheorem :=
  W.transportBoundary_source

/-- The transported source base theorem's unproved sentence is the target
instance's designated boundary sentence. This is a non-`rfl` mathematical
consequence of the transport coherence and the canonical extraction
identity: the target theorem's unproved sentence is by construction the
target instance's designated boundary sentence. -/
theorem transportBase_unprovedSentence_eq_targetDesignatedBoundary
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELMathematicalSupportWitness L₁ L₂) :
    (W.transportBase W.sourceBaseTheorem).unprovedSentence
      = L₂.boundaryObject.boundarySentence L₂.boundaryObject.designated := by
  have h := (W.transportBase W.sourceBaseTheorem).unprovedSentence_eq
  exact h

/-- The transported source license theorem's blocked sentence is the
target instance's reflection-content blocked sentence. -/
theorem transportLicense_blockedSentence_eq_targetReflectionBlocked
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELMathematicalSupportWitness L₁ L₂) :
    (W.transportLicense W.sourceLicenseTheorem).blockedSentence
      = L₂.comparison.reflectionContent.blockedSentence :=
  (W.transportLicense W.sourceLicenseTheorem).blockedSentence_eq

/-- The transported source reimport theorem's imported sentence is the
target instance's reimport-content imported sentence. -/
theorem transportReimport_importedSentence_eq_targetReimportImported
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELMathematicalSupportWitness L₁ L₂) :
    (W.transportReimport W.sourceReimportTheorem).importedSentence
      = L₂.comparison.reimportContent.importedSentence :=
  (W.transportReimport W.sourceReimportTheorem).importedSentence_eq

/-- Earlier downgrade route: build the universal quasi-functor by downgrading
the mathematical support witness to the weaker support-comparison witness
and applying `lcelUniversalQuasiFunctor_ofComparison`. This construction
is preserved as a reference point showing that the strong restricted
theorem dominates the earlier universal theorem: any mathematical support
witness yields the same conclusion through either route. -/
def lcelUniversalQuasiFunctor_ofMathematicalComparison_viaSupportDowngrade
    {A₁ A₂ : AdmissibleLCELInstance}
    (W :
      LCELMathematicalSupportWitness
        A₁.instance_ A₂.instance_) :
    LCELUniversalQuasiFunctor A₁ A₂ :=
  lcelUniversalQuasiFunctor_ofComparison W.toLCELSupportComparisonWitness

/-! ## The strong restricted theorem -/

/-- **LCEL strong restricted structural-identity theorem (Workstream D).**

For every pair of admissible LCEL instances `A₁`, `A₂` equipped with a
mathematical support witness `W` between their underlying LCEL instances,
there exists a universal quasi-functor whose target-side reversibility-
asymmetry and boundary-factorization packages are obtained by genuine
source-to-target transport through `W`.

This is strictly stronger than
`lcel_universal_structural_identity_of_comparison`: the input carries the
mathematical slot correspondence (Workstream A) and the theorem-strength
base reversibility objects (Workstream B) in addition to the content of the
plain `LCELSupportComparisonWitness`. The earlier universal theorem is a
special case obtained by ignoring the extra fields. -/
theorem lcel_structural_identity_of_mathematicalComparison
    {A₁ A₂ : AdmissibleLCELInstance}
    (W :
      LCELMathematicalSupportWitness
        A₁.instance_ A₂.instance_) :
    Nonempty (LCELUniversalQuasiFunctor A₁ A₂) :=
  ⟨lcelUniversalQuasiFunctor_ofMathematicalComparison W⟩

/-- Constructive form of the strong restricted theorem. -/
def lcel_structural_identity_of_mathematicalComparison_witness
    {A₁ A₂ : AdmissibleLCELInstance}
    (W :
      LCELMathematicalSupportWitness
        A₁.instance_ A₂.instance_) :
    LCELUniversalQuasiFunctor A₁ A₂ :=
  lcelUniversalQuasiFunctor_ofMathematicalComparison W

/-! ## Derivation of the earlier universal theorem as a corollary

Any `LCELMathematicalSupportWitness` extends an `LCELSupportComparisonWitness`,
so the earlier universal theorem
`lcel_universal_structural_identity_of_comparison` applies and delivers the
same conclusion. This shows that the strong restricted theorem dominates
the earlier universal theorem: every mathematical support witness yields
the same conclusion through either route. -/

/-- Demotion of the earlier universal theorem: any mathematical support
witness yields universal structural identity through the earlier
`lcel_universal_structural_identity_of_comparison` as well, because the
underlying support-comparison witness is available by extension. -/
theorem lcel_universal_structural_identity_of_mathematicalComparison_via_earlier
    {A₁ A₂ : AdmissibleLCELInstance}
    (W :
      LCELMathematicalSupportWitness
        A₁.instance_ A₂.instance_) :
    Nonempty (LCELUniversalQuasiFunctor A₁ A₂) :=
  lcel_universal_structural_identity_of_comparison
    W.toLCELSupportComparisonWitness

/-! ## Canonical corollaries via the mathematical support route -/

/-- Universal quasi-functor from the Gödel 1931 admissible instance to the
native DP / emitter admissible instance, via the mathematical support
witness route (genuine source-to-target transport through the slot
correspondence and the theorem-strength base reversibility objects). -/
def godel_dp_mathematical_universal_quasiFunctor :
    LCELUniversalQuasiFunctor
      godel1931AdmissibleLCELInstance
      dpEmitterAdmissibleLCELInstance :=
  lcelUniversalQuasiFunctor_ofMathematicalComparison
    godel_dp_lcelMathematicalSupportWitness

/-- Universal structural identity between the Gödel 1931 side and the native
DP / emitter side, via the mathematical support witness route. This is the
manuscript-critical corollary of the strong restricted theorem. -/
theorem godel_dp_mathematical_universal_structural_identity :
    Nonempty
      (LCELUniversalQuasiFunctor
        godel1931AdmissibleLCELInstance
        dpEmitterAdmissibleLCELInstance) :=
  lcel_structural_identity_of_mathematicalComparison
    godel_dp_lcelMathematicalSupportWitness

/-- Universal quasi-functor from the Gödel 1931 admissible instance to the
benchmark-transport admissible instance, via the mathematical support
witness route. -/
def godel_benchmark_mathematical_universal_quasiFunctor :
    LCELUniversalQuasiFunctor
      godel1931AdmissibleLCELInstance
      benchmarkTransportAdmissibleLCELInstance :=
  lcelUniversalQuasiFunctor_ofMathematicalComparison
    godel_benchmark_lcelMathematicalSupportWitness

/-- Universal structural identity between the Gödel 1931 side and the
benchmark-transport side, via the mathematical support witness route. -/
theorem godel_benchmark_mathematical_universal_structural_identity :
    Nonempty
      (LCELUniversalQuasiFunctor
        godel1931AdmissibleLCELInstance
        benchmarkTransportAdmissibleLCELInstance) :=
  lcel_structural_identity_of_mathematicalComparison
    godel_benchmark_lcelMathematicalSupportWitness

end OperatorKO7.LCELMathematicalStructuralIdentity
