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
import OperatorKO7.Meta.LCELUnrestrictedTheorem

/-!
# LCEL Unrestricted Witness-Existence and Classification Layer
(post-closure Phase P3)

This file factors the closed unrestricted theorem
`lcel_unrestricted_structural_identity_of_mathematicalWitness` through a
clean witness-existence predicate, separating two questions:

1. the already-closed theorem "a witness implies structural identity", and
2. the still-open question "which raw `FormalLCELInstance` pairs admit
   such a witness?"

The second question is the exact bridge needed before any bare /
witness-free raw-pair theorem can be attempted (Phase P4). This file
does **not** attempt that bridge; it only isolates it.
-/

namespace OperatorKO7.LCELUnrestrictedExistence

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
open OperatorKO7.LCELUnrestrictedTheorem

/-- A raw pair of `FormalLCELInstance`s admits an unrestricted
mathematical witness iff one exists in Prop.

This predicate is the propositional content of Workstream E's carrier:
it hides the choice of witness but not its existence. -/
abbrev AdmitsLCELUnrestrictedWitness
    (L₁ L₂ : FormalLCELInstance) : Prop :=
  Nonempty (LCELUnrestrictedMathematicalWitness L₁ L₂)

/-! ## The witness-existence universal theorem

This is the existence-form of the unrestricted structural-identity
theorem: given only the propositional fact that a witness exists, the
theorem still produces an admissibility pair whose underlying LCEL
carriers are the original raw instances and between which a universal
quasi-functor exists. -/

/-- **LCEL unrestricted structural-identity theorem (Phase P3,
existence form).**

For every pair of raw `FormalLCELInstance`s that propositionally admit
an unrestricted mathematical witness, there exists a pair of
`AdmissibleLCELInstance`s whose underlying LCEL carriers are exactly the
given raw instances and between which a universal quasi-functor exists.

This is a direct consequence of
`lcel_unrestricted_structural_identity_of_mathematicalWitness` applied
to any witness recovered from the `Nonempty` hypothesis. -/
theorem lcel_unrestricted_structural_identity_of_existsWitness
    {L₁ L₂ : FormalLCELInstance}
    (h : AdmitsLCELUnrestrictedWitness L₁ L₂) :
    ∃ A₁ A₂ : AdmissibleLCELInstance,
      A₁.instance_ = L₁
        ∧ A₂.instance_ = L₂
        ∧ Nonempty (LCELUniversalQuasiFunctor A₁ A₂) := by
  obtain ⟨W⟩ := h
  refine ⟨W.sourceAdmissibleInstance, W.targetAdmissibleInstance, ?_, ?_, ?_⟩
  · exact LCELUnrestrictedMathematicalWitness.sourceAdmissibleInstance_instance_ W
  · exact LCELUnrestrictedMathematicalWitness.targetAdmissibleInstance_instance_ W
  · exact lcel_unrestricted_structural_identity_of_mathematicalWitness W

/-! ## Canonical existence lemmas

Witness-existence is witnessed on the two paper-facing canonical pairs
by the canonical unrestricted mathematical witnesses of
`Meta/LCELUnrestrictedTheorem.lean`. -/

/-- The Gödel ↔ native DP raw pair admits an unrestricted mathematical
witness. -/
theorem godel_dp_admitsUnrestrictedWitness :
    AdmitsLCELUnrestrictedWitness
      godel1931LCELInstance
      dpEmitterLCELInstance :=
  ⟨godel_dp_unrestrictedMathematicalWitness⟩

/-- The Gödel ↔ benchmark-transport raw pair admits an unrestricted
mathematical witness. -/
theorem godel_benchmark_admitsUnrestrictedWitness :
    AdmitsLCELUnrestrictedWitness
      godel1931LCELInstance
      benchmarkTransportLCELInstance :=
  ⟨godel_benchmark_unrestrictedMathematicalWitness⟩

/-- On the Gödel ↔ native DP pair, the existence-form of the unrestricted
structural-identity theorem is discharged by the canonical witness. -/
theorem godel_dp_existsStructuralIdentityFromExistsWitness :
    ∃ A₁ A₂ : AdmissibleLCELInstance,
      A₁.instance_ = godel1931LCELInstance
        ∧ A₂.instance_ = dpEmitterLCELInstance
        ∧ Nonempty (LCELUniversalQuasiFunctor A₁ A₂) :=
  lcel_unrestricted_structural_identity_of_existsWitness
    godel_dp_admitsUnrestrictedWitness

/-- On the Gödel ↔ benchmark-transport pair, the existence-form of the
unrestricted structural-identity theorem is discharged by the canonical
witness. -/
theorem godel_benchmark_existsStructuralIdentityFromExistsWitness :
    ∃ A₁ A₂ : AdmissibleLCELInstance,
      A₁.instance_ = godel1931LCELInstance
        ∧ A₂.instance_ = benchmarkTransportLCELInstance
        ∧ Nonempty (LCELUniversalQuasiFunctor A₁ A₂) :=
  lcel_unrestricted_structural_identity_of_existsWitness
    godel_benchmark_admitsUnrestrictedWitness

end OperatorKO7.LCELUnrestrictedExistence
