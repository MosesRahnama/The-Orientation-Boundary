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

## Formal Scope

The main constructor projects transport and coherence fields supplied by its input witness. The theorem with the stronger premise is a specialization, not a logically stronger conclusion.
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
so the conclusion is unchanged, but the mathematical route is here
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

/-- Alternative construction obtained by forgetting the additional fields of
the mathematical support witness and applying
`lcelUniversalQuasiFunctor_ofComparison`. -/
def lcelUniversalQuasiFunctor_ofMathematicalComparison_viaSupportDowngrade
    {A₁ A₂ : AdmissibleLCELInstance}
    (W :
      LCELMathematicalSupportWitness
        A₁.instance_ A₂.instance_) :
    LCELUniversalQuasiFunctor A₁ A₂ :=
  lcelUniversalQuasiFunctor_ofComparison W.toLCELSupportComparisonWitness

/-! ## Construction from Mathematical Support -/

/-- A mathematical support witness supplies the fields used to construct an
`LCELUniversalQuasiFunctor`. The premise contains more data than the plain
support-comparison premise, while the conclusion has the same type. -/
theorem lcel_structural_identity_of_mathematicalComparison
    {A₁ A₂ : AdmissibleLCELInstance}
    (W :
      LCELMathematicalSupportWitness
        A₁.instance_ A₂.instance_) :
    Nonempty (LCELUniversalQuasiFunctor A₁ A₂) :=
  ⟨lcelUniversalQuasiFunctor_ofMathematicalComparison W⟩

/-- Constructor-valued form of the preceding theorem. -/
def lcel_structural_identity_of_mathematicalComparison_witness
    {A₁ A₂ : AdmissibleLCELInstance}
    (W :
      LCELMathematicalSupportWitness
        A₁.instance_ A₂.instance_) :
    LCELUniversalQuasiFunctor A₁ A₂ :=
  lcelUniversalQuasiFunctor_ofMathematicalComparison W

/-! ## Construction through the Support-Comparison Projection -/

/-- The support-comparison projection of a mathematical witness supplies the
premise of `lcel_universal_structural_identity_of_comparison`. -/
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
paper-critical corollary of the strong restricted theorem. -/
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
