import OperatorKO7.Meta.LCELUnrestrictedTheorem

namespace LCELUnrestrictedTheoremReach

open OperatorKO7
open OperatorKO7.LCELUnrestrictedTheorem

/-! Reachability smoke tests for the Workstream E unrestricted universal
theorem layer. Each example below elaborates an identifier introduced in
`Meta/LCELUnrestrictedTheorem.lean`, so if any of these identifiers were
renamed, removed, or had their type signature changed, this file would
fail to elaborate. -/

/-! ### Carrier and admissibility builders -/

example : True := by
  have := godel_dp_unrestrictedMathematicalWitness
  trivial

example : True := by
  have := godel_benchmark_unrestrictedMathematicalWitness
  trivial

example : True := by
  have :=
    LCELUnrestrictedMathematicalWitness.sourceAdmissibleInstance
      godel_dp_unrestrictedMathematicalWitness
  trivial

example : True := by
  have :=
    LCELUnrestrictedMathematicalWitness.targetAdmissibleInstance
      godel_dp_unrestrictedMathematicalWitness
  trivial

example : True := by
  have :=
    LCELUnrestrictedMathematicalWitness.sourceAdmissibleInstance
      godel_benchmark_unrestrictedMathematicalWitness
  trivial

example : True := by
  have :=
    LCELUnrestrictedMathematicalWitness.targetAdmissibleInstance
      godel_benchmark_unrestrictedMathematicalWitness
  trivial

/-! ### Admissibility builders preserve the underlying LCEL instance -/

example :
    godel_dp_unrestrictedMathematicalWitness.sourceAdmissibleInstance.instance_
      = OperatorKO7.LCELSchema.godel1931LCELInstance :=
  LCELUnrestrictedMathematicalWitness.sourceAdmissibleInstance_instance_
    godel_dp_unrestrictedMathematicalWitness

example :
    godel_dp_unrestrictedMathematicalWitness.targetAdmissibleInstance.instance_
      = OperatorKO7.LCELDpInstance.dpEmitterLCELInstance :=
  LCELUnrestrictedMathematicalWitness.targetAdmissibleInstance_instance_
    godel_dp_unrestrictedMathematicalWitness

example :
    godel_benchmark_unrestrictedMathematicalWitness.sourceAdmissibleInstance.instance_
      = OperatorKO7.LCELSchema.godel1931LCELInstance :=
  LCELUnrestrictedMathematicalWitness.sourceAdmissibleInstance_instance_
    godel_benchmark_unrestrictedMathematicalWitness

example :
    godel_benchmark_unrestrictedMathematicalWitness.targetAdmissibleInstance.instance_
      = OperatorKO7.LCELSchema.benchmarkTransportLCELInstance :=
  LCELUnrestrictedMathematicalWitness.targetAdmissibleInstance_instance_
    godel_benchmark_unrestrictedMathematicalWitness

/-! ### Main unrestricted theorem and its forms -/

example : True := by
  have :=
    lcel_unrestricted_structural_identity_of_mathematicalWitness
      godel_dp_unrestrictedMathematicalWitness
  trivial

example : True := by
  have :=
    lcel_unrestricted_structural_identity_of_mathematicalWitness_witness
      godel_dp_unrestrictedMathematicalWitness
  trivial

example : True := by
  have :=
    lcel_unrestricted_structural_identity_of_mathematicalWitness_bidirectional
      godel_dp_unrestrictedMathematicalWitness
  trivial

example : True := by
  have :=
    lcel_unrestricted_structural_identity_of_mathematicalWitness
      godel_benchmark_unrestrictedMathematicalWitness
  trivial

example : True := by
  have :=
    lcel_unrestricted_structural_identity_of_mathematicalWitness_witness
      godel_benchmark_unrestrictedMathematicalWitness
  trivial

example : True := by
  have :=
    lcel_unrestricted_structural_identity_of_mathematicalWitness_bidirectional
      godel_benchmark_unrestrictedMathematicalWitness
  trivial

/-! ### Canonical unrestricted corollaries -/

example : True := by
  have := godel_dp_unrestricted_structural_identity
  trivial

example : True := by
  have := godel_benchmark_unrestricted_structural_identity
  trivial

example : True := by
  have := godel_dp_unrestricted_structural_identity_bidirectional
  trivial

example : True := by
  have := godel_benchmark_unrestricted_structural_identity_bidirectional
  trivial

/-! ### Track G reduction regression

These tests assert that the unrestricted theorem is a genuine lift of
the Track G theorem on the canonical witness, not a parallel
construction. Concretely: the universal quasi-functor produced by the
unrestricted theorem's constructive form is **definitionally equal** to
the universal quasi-functor produced by the Track G constructor
`lcelUniversalQuasiFunctor_ofMathematicalComparison` applied to the same
comparison data. If a future refactor accidentally forked the
unrestricted layer off from the Track G transport stack, these `rfl`
checks would fail. -/

example :
    lcel_unrestricted_structural_identity_of_mathematicalWitness_witness
        godel_dp_unrestrictedMathematicalWitness
      = OperatorKO7.LCELMathematicalStructuralIdentity.lcelUniversalQuasiFunctor_ofMathematicalComparison
          (A₁ := godel_dp_unrestrictedMathematicalWitness.sourceAdmissibleInstance)
          (A₂ := godel_dp_unrestrictedMathematicalWitness.targetAdmissibleInstance)
          godel_dp_unrestrictedMathematicalWitness.comparison :=
  rfl

example :
    lcel_unrestricted_structural_identity_of_mathematicalWitness_witness
        godel_benchmark_unrestrictedMathematicalWitness
      = OperatorKO7.LCELMathematicalStructuralIdentity.lcelUniversalQuasiFunctor_ofMathematicalComparison
          (A₁ := godel_benchmark_unrestrictedMathematicalWitness.sourceAdmissibleInstance)
          (A₂ := godel_benchmark_unrestrictedMathematicalWitness.targetAdmissibleInstance)
          godel_benchmark_unrestrictedMathematicalWitness.comparison :=
  rfl

/-! The internal admissibility builders pull **exactly** the comparison
witness's source / target support records, not copies from somewhere
else. These `rfl` regressions fail if a future refactor introduced a
second code path that rebuilt admissibility from different data. -/

example :
    godel_dp_unrestrictedMathematicalWitness.sourceAdmissibleInstance.baseSupport
      = godel_dp_unrestrictedMathematicalWitness.comparison.sourceBaseSupport :=
  rfl

example :
    godel_dp_unrestrictedMathematicalWitness.sourceAdmissibleInstance.licenseSupport
      = godel_dp_unrestrictedMathematicalWitness.comparison.sourceLicenseSupport :=
  rfl

example :
    godel_dp_unrestrictedMathematicalWitness.sourceAdmissibleInstance.reimportSupport
      = godel_dp_unrestrictedMathematicalWitness.comparison.sourceReimportSupport :=
  rfl

example :
    godel_dp_unrestrictedMathematicalWitness.sourceAdmissibleInstance.boundarySupport
      = godel_dp_unrestrictedMathematicalWitness.comparison.sourceBoundarySupport :=
  rfl

example :
    godel_dp_unrestrictedMathematicalWitness.targetAdmissibleInstance.baseSupport
      = godel_dp_unrestrictedMathematicalWitness.comparison.targetBaseSupport :=
  rfl

example :
    godel_dp_unrestrictedMathematicalWitness.targetAdmissibleInstance.licenseSupport
      = godel_dp_unrestrictedMathematicalWitness.comparison.targetLicenseSupport :=
  rfl

example :
    godel_dp_unrestrictedMathematicalWitness.targetAdmissibleInstance.reimportSupport
      = godel_dp_unrestrictedMathematicalWitness.comparison.targetReimportSupport :=
  rfl

example :
    godel_dp_unrestrictedMathematicalWitness.targetAdmissibleInstance.boundarySupport
      = godel_dp_unrestrictedMathematicalWitness.comparison.targetBoundarySupport :=
  rfl

/-! The admissibility builders also carry the witness-supplied
realization, not the canonical realization fetched from somewhere
else. -/

example :
    godel_dp_unrestrictedMathematicalWitness.sourceAdmissibleInstance.realizes
      = godel_dp_unrestrictedMathematicalWitness.sourceRealizes :=
  rfl

example :
    godel_dp_unrestrictedMathematicalWitness.targetAdmissibleInstance.realizes
      = godel_dp_unrestrictedMathematicalWitness.targetRealizes :=
  rfl

/-! ### Phase P1 named-hardening-lemma regressions

Each of the four named hardening lemmas from
`Meta/LCELUnrestrictedTheorem.lean` is exercised on both canonical
pairs, so the regression surface covers the full unrestricted-layer
connective tissue between Track G and Route E1. -/

example : True := by
  have :=
    sourceAdmissibleInstance_reversibilityAsymmetry_eq
      godel_dp_unrestrictedMathematicalWitness
  trivial

example : True := by
  have :=
    sourceAdmissibleInstance_reversibilityAsymmetry_eq
      godel_benchmark_unrestrictedMathematicalWitness
  trivial

example : True := by
  have :=
    targetAdmissibleInstance_boundaryFactorization_eq
      godel_dp_unrestrictedMathematicalWitness
  trivial

example : True := by
  have :=
    targetAdmissibleInstance_boundaryFactorization_eq
      godel_benchmark_unrestrictedMathematicalWitness
  trivial

example : True := by
  have :=
    lcel_unrestricted_witness_eq_trackG
      godel_dp_unrestrictedMathematicalWitness
  trivial

example : True := by
  have :=
    lcel_unrestricted_witness_eq_trackG
      godel_benchmark_unrestrictedMathematicalWitness
  trivial

example : True := by
  have :=
    lcel_unrestricted_bidirectional_reverse_eq_routeE1
      godel_dp_unrestrictedMathematicalWitness
  trivial

example : True := by
  have :=
    lcel_unrestricted_bidirectional_reverse_eq_routeE1
      godel_benchmark_unrestrictedMathematicalWitness
  trivial

/-! ### Phase P2 builder regressions

The canonical unrestricted witnesses are now built via the
`ofAdmissibilityData` builder. The following `rfl` assertions check
that the builder-based witnesses coincide definitionally with what the
earlier hand-written structure literals produced. -/

example :
    godel_dp_unrestrictedMathematicalWitness
      = LCELUnrestrictedMathematicalWitness.ofAdmissibilityData
          OperatorKO7.LCELAdmissibility.godel1931LCELAdmissibilityData
          OperatorKO7.LCELAdmissibility.dpEmitterLCELAdmissibilityData
          OperatorKO7.LCELMathematical.godel_dp_lcelMathematicalSupportWitness :=
  rfl

example :
    godel_benchmark_unrestrictedMathematicalWitness
      = LCELUnrestrictedMathematicalWitness.ofAdmissibilityData
          OperatorKO7.LCELAdmissibility.godel1931LCELAdmissibilityData
          OperatorKO7.LCELAdmissibility.benchmarkTransportLCELAdmissibilityData
          OperatorKO7.LCELMathematical.godel_benchmark_lcelMathematicalSupportWitness :=
  rfl

end LCELUnrestrictedTheoremReach
