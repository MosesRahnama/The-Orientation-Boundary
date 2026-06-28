import OperatorKO7.Meta.SchemaConfessionDominance
import OperatorKO7.Meta.DependencyPairs_HeadView
import Mathlib.Tactic

/-!
# Arts--Giesl Derivational Complexity

Finite-TRS-parametric cost layer for the paper-facing Arts--Giesl license story.

This module deliberately separates four levels:

- a fixed-finite-TRS audit surface (`FixedFiniteTRS`);
- a generic finite first-order TRS extraction-side pair-count bound;
- a theorem-backed three-stage bound for one AG soundness application;
- a metadata-only fallback theorem using an explicit pair-count witness.

The resulting surface strengthens the old recursor-only theorem in two ways:

- it gives a generic fixed-finite-TRS cost layer;
- it now also derives the dependency-pair-count bound from the artifact's own
  finite first-order extraction procedure, for finite symbol carriers.
-/

namespace OperatorKO7.ArtsGieslDerivationalComplexity

open OperatorKO7.StepDuplicating.StepDuplicatingSchema.BaseDuplicatingSystem
open OperatorKO7.DependencyPairsFragment

/-- Fixed finite-TRS metadata used by the paper's Arts--Giesl derivational-cost
proposition. -/
structure FixedFiniteTRS where
  ruleCount : Nat
  signatureSize : Nat
  dependencyPairCount : Nat

namespace FixedFiniteTRS

/-- Graph-construction contribution in the paper's cost audit. -/
def graphConstructionBound (R : FixedFiniteTRS) (constructionConstant : Nat) : Nat :=
  constructionConstant * R.ruleCount ^ 2 * R.signatureSize

/-- One-application AG proof-length envelope on a fixed finite TRS. -/
def singleApplicationBound (R : FixedFiniteTRS)
    (constructionConstant : Nat)
    (baseOrderProofLength : Nat → Nat)
    (soundnessConstant : Nat) : Nat :=
  R.graphConstructionBound constructionConstant
    + baseOrderProofLength R.dependencyPairCount
    + soundnessConstant

/-- Total certificate envelope after appending transformed-problem residual
proof work. -/
def totalCertificateBound (R : FixedFiniteTRS)
    (constructionConstant : Nat)
    (baseOrderProofLength : Nat → Nat)
    (soundnessConstant : Nat)
    (residualCost : Nat) : Nat :=
  R.singleApplicationBound constructionConstant baseOrderProofLength soundnessConstant
    + residualCost

end FixedFiniteTRS

private theorem list_sum_le_length_mul {α : Type}
    (l : List α) (f : α → Nat) (c : Nat)
    (h : ∀ a, f a ≤ c) :
    (l.map f).sum ≤ l.length * c := by
  induction l with
  | nil => simp
  | cons a t ih =>
      calc
        (List.map f (a :: t)).sum = f a + (List.map f t).sum := by simp
        _ ≤ c + t.length * c := by
          exact Nat.add_le_add (h a) ih
        _ = 1 * c + t.length * c := by simp
        _ = (1 + t.length) * c := by rw [← Nat.add_mul]
        _ = (t.length + 1) * c := by rw [Nat.add_comm]
        _ = (a :: t).length * c := by simp

/-- Affine upper-bound witness for a base-order proof-length function. This is
strong enough for the paper's "linear base order implies polynomial overhead"
corollary, while remaining honest about the dependency-pair count parameter. -/
structure AffineBaseOrderBound (L : Nat → Nat) where
  coefficient : Nat
  constant : Nat
  bound : ∀ n, L n ≤ coefficient * n + constant

/-- Optional dependency-pair-count witness. This packages the exact extra input
needed to collapse the AG bound from the explicit pair-count parameter down to a
pure rule/signature polynomial. -/
structure DependencyPairCountBound (R : FixedFiniteTRS) where
  bound : Nat
  cert : R.dependencyPairCount ≤ bound

/-- Three-stage audit for one Arts--Giesl soundness application on a fixed
finite TRS. The theorem below uses only these stage bounds and their additive
assembly; no hidden extraction theorem is assumed. -/
structure ArtsGieslSingleApplicationAudit (R : FixedFiniteTRS) where
  constructionConstant : Nat
  baseOrderProofLength : Nat → Nat
  soundnessConstant : Nat
  graphConstructionCost : Nat
  baseOrderCheckCost : Nat
  soundnessInvocationCost : Nat
  totalProofLength : Nat
  graphConstruction_le :
    graphConstructionCost ≤ R.graphConstructionBound constructionConstant
  baseOrderCheck_le :
    baseOrderCheckCost ≤ baseOrderProofLength R.dependencyPairCount
  soundnessInvocation_le : soundnessInvocationCost ≤ soundnessConstant
  total_eq :
    totalProofLength =
      graphConstructionCost + baseOrderCheckCost + soundnessInvocationCost

namespace FixedFiniteTRS

/-- Canonical three-stage audit saturating the fixed-finite-TRS cost envelope. -/
def canonicalAudit (R : FixedFiniteTRS)
    (constructionConstant : Nat)
    (baseOrderProofLength : Nat → Nat)
    (soundnessConstant : Nat) :
    ArtsGieslSingleApplicationAudit R where
  constructionConstant := constructionConstant
  baseOrderProofLength := baseOrderProofLength
  soundnessConstant := soundnessConstant
  graphConstructionCost := R.graphConstructionBound constructionConstant
  baseOrderCheckCost := baseOrderProofLength R.dependencyPairCount
  soundnessInvocationCost := soundnessConstant
  totalProofLength :=
    R.graphConstructionBound constructionConstant
      + baseOrderProofLength R.dependencyPairCount
      + soundnessConstant
  graphConstruction_le := le_rfl
  baseOrderCheck_le := le_rfl
  soundnessInvocation_le := le_rfl
  total_eq := by
    simp [graphConstructionBound]

end FixedFiniteTRS

/-- Finite-TRS-parametric AG bound for one soundness application. This is the
strongest theorem-backed generic surface currently available in the repository:
construction-stage bound + base-order proof-length on the extracted pair count
+ constant soundness-invocation overhead. -/
theorem ag_proof_length_on_fixedFiniteTRS
    {R : FixedFiniteTRS}
    (A : ArtsGieslSingleApplicationAudit R) :
    A.totalProofLength ≤
      R.singleApplicationBound
        A.constructionConstant
        A.baseOrderProofLength
        A.soundnessConstant := by
  rw [A.total_eq, FixedFiniteTRS.singleApplicationBound]
  exact Nat.add_le_add
    (Nat.add_le_add A.graphConstruction_le A.baseOrderCheck_le)
    A.soundnessInvocation_le

/-- Total certificate bound after adjoining residual transformed-problem proof
work. -/
theorem ag_total_certificate_length_on_fixedFiniteTRS
    {R : FixedFiniteTRS}
    (A : ArtsGieslSingleApplicationAudit R)
    (residualCost : Nat) :
    A.totalProofLength + residualCost ≤
      R.totalCertificateBound
        A.constructionConstant
        A.baseOrderProofLength
        A.soundnessConstant
        residualCost := by
  exact Nat.add_le_add_right (ag_proof_length_on_fixedFiniteTRS A) residualCost

/-- If the chosen base order has affine proof-length, the AG overhead is
polynomial in the explicit finite-TRS parameters `(ruleCount, signatureSize,
dependencyPairCount)`. -/
theorem arts_giesl_derivational_overhead_polynomial
    {R : FixedFiniteTRS}
    (A : ArtsGieslSingleApplicationAudit R)
    (hBase : AffineBaseOrderBound A.baseOrderProofLength) :
    A.totalProofLength ≤
      R.graphConstructionBound A.constructionConstant
        + (hBase.coefficient * R.dependencyPairCount + hBase.constant)
        + A.soundnessConstant := by
  calc
    A.totalProofLength ≤
        R.singleApplicationBound
          A.constructionConstant
          A.baseOrderProofLength
          A.soundnessConstant :=
      ag_proof_length_on_fixedFiniteTRS A
    _ ≤
        R.graphConstructionBound A.constructionConstant
          + (hBase.coefficient * R.dependencyPairCount + hBase.constant)
          + A.soundnessConstant := by
      simpa [FixedFiniteTRS.singleApplicationBound, Nat.add_assoc] using
        Nat.add_le_add_left
          (Nat.add_le_add_right
            (hBase.bound R.dependencyPairCount)
            A.soundnessConstant)
          (R.graphConstructionBound A.constructionConstant)

/-- Metadata-only fallback: if an external theorem bounds the number of
extracted dependency pairs, the AG overhead collapses to a pure
rule/signature-side polynomial. -/
theorem arts_giesl_derivational_overhead_polynomial_of_pairCountBound
    {R : FixedFiniteTRS}
    (A : ArtsGieslSingleApplicationAudit R)
    (hBase : AffineBaseOrderBound A.baseOrderProofLength)
    (hPairs : DependencyPairCountBound R) :
    A.totalProofLength ≤
      R.graphConstructionBound A.constructionConstant
        + (hBase.coefficient * hPairs.bound + hBase.constant)
        + A.soundnessConstant := by
  calc
    A.totalProofLength ≤
        R.graphConstructionBound A.constructionConstant
          + (hBase.coefficient * R.dependencyPairCount + hBase.constant)
          + A.soundnessConstant :=
      arts_giesl_derivational_overhead_polynomial A hBase
    _ ≤
        R.graphConstructionBound A.constructionConstant
          + (hBase.coefficient * hPairs.bound + hBase.constant)
          + A.soundnessConstant := by
      simpa [Nat.add_assoc] using
        Nat.add_le_add_left
          (Nat.add_le_add_right
            (Nat.add_le_add_right
              (Nat.mul_le_mul_left hBase.coefficient hPairs.cert)
              hBase.constant)
            A.soundnessConstant)
          (R.graphConstructionBound A.constructionConstant)

/-! ## Finite first-order TRS closure -/

/-- Per-rule contribution to the extracted dependency-pair count in a finite
head-view TRS presentation. -/
noncomputable def finiteHeadRuleProcedureRuleContribution
    {σ : Type} [DecidableEq σ]
    (E : DependencyPairsFragment.FiniteHeadRuleProcedure σ)
    (r : E.Rule) : Nat :=
  let _ : HasCallHeadView E.Term σ := E.termView
  if HasCallHeadView.rootHead? (τ := E.Term) (σ := σ) (E.lhs r) = none then
    0
  else
    ((HasCallHeadView.callHeads (τ := E.Term) (σ := σ) (E.rhs r)).filter
      (· ∈ E.definedHeads)).card

/-- Extracted dependency-pair count induced by a finite head-view TRS
presentation. This counts the filtered defined-head call obligations contributed
by all rules in the presentation. -/
noncomputable def finiteHeadRuleProcedureExtractedPairCount
    {σ : Type} [DecidableEq σ]
    (E : DependencyPairsFragment.FiniteHeadRuleProcedure σ) : Nat :=
  (E.rules.toList.map (finiteHeadRuleProcedureRuleContribution E)).sum

/-- Finite-signature bound on the extracted dependency-pair count of a finite
head-view TRS presentation. Each rule contributes at most one filtered call-head
set of size bounded by the signature carrier. -/
theorem finiteHeadRuleProcedureExtractedPairCount_le_ruleCount_mul_signatureSize
    {σ : Type} [DecidableEq σ] [Fintype σ]
    (E : DependencyPairsFragment.FiniteHeadRuleProcedure σ) :
    finiteHeadRuleProcedureExtractedPairCount E ≤ E.rules.size * Fintype.card σ := by
  let contribution : E.Rule → Nat := finiteHeadRuleProcedureRuleContribution E
  have hcontribution : ∀ r, contribution r ≤ Fintype.card σ := by
    intro r
    let _ : HasCallHeadView E.Term σ := E.termView
    by_cases hroot : HasCallHeadView.rootHead? (τ := E.Term) (σ := σ) (E.lhs r) = none
    · simp [contribution, finiteHeadRuleProcedureRuleContribution, hroot]
    · have hcard :
          ((HasCallHeadView.callHeads (τ := E.Term) (σ := σ) (E.rhs r)).filter
            (· ∈ E.definedHeads)).card ≤ Fintype.card σ := by
        simpa using
          (Finset.card_le_univ
            ((HasCallHeadView.callHeads (τ := E.Term) (σ := σ) (E.rhs r)).filter
              (· ∈ E.definedHeads)))
      simpa [contribution, finiteHeadRuleProcedureRuleContribution, hroot] using hcard
  simpa [finiteHeadRuleProcedureExtractedPairCount, contribution] using
    list_sum_le_length_mul E.rules.toList contribution (Fintype.card σ) hcontribution

/-- Fixed-finite-TRS metadata induced by a finite head-view TRS presentation. -/
noncomputable def FixedFiniteTRS.ofFiniteHeadRuleProcedure
    {σ : Type} [DecidableEq σ] [Fintype σ]
    (E : DependencyPairsFragment.FiniteHeadRuleProcedure σ) : FixedFiniteTRS where
  ruleCount := E.rules.size
  signatureSize := Fintype.card σ
  dependencyPairCount := finiteHeadRuleProcedureExtractedPairCount E

/-- The extracted dependency-pair count bound carried by a finite head-view TRS
presentation. -/
abbrev dependencyPairCountBound_of_finiteHeadRuleProcedure
    {σ : Type} [DecidableEq σ] [Fintype σ]
    (E : DependencyPairsFragment.FiniteHeadRuleProcedure σ) :
    DependencyPairCountBound (FixedFiniteTRS.ofFiniteHeadRuleProcedure E) where
  bound := E.rules.size * Fintype.card σ
  cert := finiteHeadRuleProcedureExtractedPairCount_le_ruleCount_mul_signatureSize E

/-- One-application AG proof-length theorem for an artifact-internal finite
head-view TRS presentation. This is the direct mechanized counterpart of the
paper's `C * |R|^2 * |Σ| + L_base(n)` form, with `n` computed by the artifact's
own extraction layer. -/
theorem ag_proof_length_on_finiteHeadRuleTRS
    {σ : Type} [DecidableEq σ] [Fintype σ]
    (E : DependencyPairsFragment.FiniteHeadRuleProcedure σ)
    (A : ArtsGieslSingleApplicationAudit (FixedFiniteTRS.ofFiniteHeadRuleProcedure E)) :
    A.totalProofLength ≤
      A.constructionConstant * E.rules.size ^ 2 * Fintype.card σ
        + A.baseOrderProofLength (finiteHeadRuleProcedureExtractedPairCount E)
        + A.soundnessConstant := by
  simpa [FixedFiniteTRS.ofFiniteHeadRuleProcedure,
      FixedFiniteTRS.singleApplicationBound,
      FixedFiniteTRS.graphConstructionBound,
      finiteHeadRuleProcedureExtractedPairCount] using
    ag_proof_length_on_fixedFiniteTRS A

/-- Total certificate bound for an artifact-internal finite head-view TRS
presentation. -/
theorem ag_total_certificate_length_on_finiteHeadRuleTRS
    {σ : Type} [DecidableEq σ] [Fintype σ]
    (E : DependencyPairsFragment.FiniteHeadRuleProcedure σ)
    (A : ArtsGieslSingleApplicationAudit (FixedFiniteTRS.ofFiniteHeadRuleProcedure E))
    (residualCost : Nat) :
    A.totalProofLength + residualCost ≤
      A.constructionConstant * E.rules.size ^ 2 * Fintype.card σ
        + A.baseOrderProofLength (finiteHeadRuleProcedureExtractedPairCount E)
        + A.soundnessConstant
        + residualCost := by
  simpa [FixedFiniteTRS.ofFiniteHeadRuleProcedure,
      FixedFiniteTRS.totalCertificateBound,
      FixedFiniteTRS.singleApplicationBound,
      FixedFiniteTRS.graphConstructionBound,
      finiteHeadRuleProcedureExtractedPairCount,
      Nat.add_assoc] using
    ag_total_certificate_length_on_fixedFiniteTRS A residualCost

/-- Polynomial-overhead corollary for artifact-internal finite head-view TRS
presentations with affine base-order proof length. -/
theorem arts_giesl_derivational_overhead_polynomial_of_finiteHeadRuleTRS
    {σ : Type} [DecidableEq σ] [Fintype σ]
    (E : DependencyPairsFragment.FiniteHeadRuleProcedure σ)
    (A : ArtsGieslSingleApplicationAudit (FixedFiniteTRS.ofFiniteHeadRuleProcedure E))
    (hBase : AffineBaseOrderBound A.baseOrderProofLength) :
    A.totalProofLength ≤
      A.constructionConstant * E.rules.size ^ 2 * Fintype.card σ
        + (hBase.coefficient * (E.rules.size * Fintype.card σ) + hBase.constant)
        + A.soundnessConstant := by
  simpa [FixedFiniteTRS.ofFiniteHeadRuleProcedure,
      FixedFiniteTRS.graphConstructionBound,
      dependencyPairCountBound_of_finiteHeadRuleProcedure] using
    arts_giesl_derivational_overhead_polynomial_of_pairCountBound
      A hBase (dependencyPairCountBound_of_finiteHeadRuleProcedure E)

/-- Extracted dependency-pair count induced by a finite first-order TRS
presentation. -/
noncomputable def finiteFirstOrderProcedureExtractedPairCount
    {σ ν : Type} [DecidableEq σ] [Fintype σ]
    (E : DependencyPairsFragment.FiniteFirstOrderProcedure σ ν) : Nat :=
  finiteHeadRuleProcedureExtractedPairCount
    (DependencyPairsFragment.FiniteHeadRuleProcedure.ofFiniteFirstOrderProcedure E)

/-- Finite-signature bound on the extracted dependency-pair count of a finite
first-order TRS presentation. -/
theorem finiteFirstOrderProcedureExtractedPairCount_le_ruleCount_mul_signatureSize
    {σ ν : Type} [DecidableEq σ] [Fintype σ]
    (E : DependencyPairsFragment.FiniteFirstOrderProcedure σ ν) :
    finiteFirstOrderProcedureExtractedPairCount E ≤ E.rules.size * Fintype.card σ :=
  finiteHeadRuleProcedureExtractedPairCount_le_ruleCount_mul_signatureSize
    (DependencyPairsFragment.FiniteHeadRuleProcedure.ofFiniteFirstOrderProcedure E)

/-- Fixed-finite-TRS metadata induced by a finite first-order TRS presentation. -/
noncomputable def FixedFiniteTRS.ofFiniteFirstOrderProcedure
    {σ ν : Type} [DecidableEq σ] [Fintype σ]
    (E : DependencyPairsFragment.FiniteFirstOrderProcedure σ ν) : FixedFiniteTRS where
  ruleCount := E.rules.size
  signatureSize := Fintype.card σ
  dependencyPairCount := finiteFirstOrderProcedureExtractedPairCount E

/-- The extracted dependency-pair count bound carried by a finite first-order
TRS presentation. -/
abbrev dependencyPairCountBound_of_finiteFirstOrderProcedure
    {σ ν : Type} [DecidableEq σ] [Fintype σ]
    (E : DependencyPairsFragment.FiniteFirstOrderProcedure σ ν) :
    DependencyPairCountBound (FixedFiniteTRS.ofFiniteFirstOrderProcedure E) where
  bound := E.rules.size * Fintype.card σ
  cert := finiteFirstOrderProcedureExtractedPairCount_le_ruleCount_mul_signatureSize E

/-- One-application AG proof-length theorem for a finite first-order TRS
presentation. This is the artifact's strongest honest theorem-level analogue of
the paper's `L_AG(R) ≤ C * |R|^2 * |Σ| + L_base(n)`. -/
theorem ag_proof_length_on_finiteFirstOrderTRS
    {σ ν : Type} [DecidableEq σ] [Fintype σ]
    (E : DependencyPairsFragment.FiniteFirstOrderProcedure σ ν)
    (A : ArtsGieslSingleApplicationAudit (FixedFiniteTRS.ofFiniteFirstOrderProcedure E)) :
    A.totalProofLength ≤
      A.constructionConstant * E.rules.size ^ 2 * Fintype.card σ
        + A.baseOrderProofLength (finiteFirstOrderProcedureExtractedPairCount E)
        + A.soundnessConstant := by
  simpa [FixedFiniteTRS.ofFiniteFirstOrderProcedure,
      finiteFirstOrderProcedureExtractedPairCount,
      FixedFiniteTRS.singleApplicationBound,
      FixedFiniteTRS.graphConstructionBound] using
    ag_proof_length_on_fixedFiniteTRS A

/-- Total certificate bound for a finite first-order TRS presentation. -/
theorem ag_total_certificate_length_on_finiteFirstOrderTRS
    {σ ν : Type} [DecidableEq σ] [Fintype σ]
    (E : DependencyPairsFragment.FiniteFirstOrderProcedure σ ν)
    (A : ArtsGieslSingleApplicationAudit (FixedFiniteTRS.ofFiniteFirstOrderProcedure E))
    (residualCost : Nat) :
    A.totalProofLength + residualCost ≤
      A.constructionConstant * E.rules.size ^ 2 * Fintype.card σ
        + A.baseOrderProofLength (finiteFirstOrderProcedureExtractedPairCount E)
        + A.soundnessConstant
        + residualCost := by
  simpa [FixedFiniteTRS.ofFiniteFirstOrderProcedure,
      finiteFirstOrderProcedureExtractedPairCount,
      FixedFiniteTRS.totalCertificateBound,
      FixedFiniteTRS.singleApplicationBound,
      FixedFiniteTRS.graphConstructionBound,
      Nat.add_assoc] using
    ag_total_certificate_length_on_fixedFiniteTRS A residualCost

/-- Polynomial-overhead corollary for finite first-order TRS presentations with
affine base-order proof length. This discharges the remaining pair-count side of
`prop:ag-derivational` directly from the artifact's extraction layer. -/
theorem arts_giesl_derivational_overhead_polynomial_of_finiteFirstOrderTRS
    {σ ν : Type} [DecidableEq σ] [Fintype σ]
    (E : DependencyPairsFragment.FiniteFirstOrderProcedure σ ν)
    (A : ArtsGieslSingleApplicationAudit (FixedFiniteTRS.ofFiniteFirstOrderProcedure E))
    (hBase : AffineBaseOrderBound A.baseOrderProofLength) :
    A.totalProofLength ≤
      A.constructionConstant * E.rules.size ^ 2 * Fintype.card σ
        + (hBase.coefficient * (E.rules.size * Fintype.card σ) + hBase.constant)
        + A.soundnessConstant := by
  simpa [FixedFiniteTRS.ofFiniteFirstOrderProcedure,
      FixedFiniteTRS.graphConstructionBound,
      dependencyPairCountBound_of_finiteFirstOrderProcedure] using
    arts_giesl_derivational_overhead_polynomial_of_pairCountBound
      A hBase (dependencyPairCountBound_of_finiteFirstOrderProcedure E)

/-! ## Recursor-side specialization -/

/-- Fixed finite-TRS metadata for the primitive step-duplicating recursor. -/
def stepDuplicatingRecursorTRS : FixedFiniteTRS where
  ruleCount := 2
  signatureSize := 4
  dependencyPairCount := 1

/-- Rule count of the primitive duplicator. -/
def recursorRuleCount : Nat := stepDuplicatingRecursorTRS.ruleCount

/-- Signature size used by the paper's recursor-side bound. -/
def recursorSignatureSize : Nat := stepDuplicatingRecursorTRS.signatureSize

/-- Extracted dependency-pair count for the primitive duplicator. -/
def recursorDependencyPairCount : Nat := stepDuplicatingRecursorTRS.dependencyPairCount

/-- Paper-facing construction cost envelope for the recursor's DP graph. -/
def agGraphConstructionCost : Nat :=
  stepDuplicatingRecursorTRS.graphConstructionBound 1

/-- Paper-facing base-order check cost on the single extracted pair. -/
def agBaseOrderCost : Nat :=
  recursorDependencyPairCount

/-- Constant schematic overhead of one Arts--Giesl soundness invocation in the
recursor-side cost model. -/
def agSchematicInvocationCost : Nat := 1

/-- Total constant license overhead on the primitive duplicator. -/
def agLicenseOverhead : Nat :=
  agGraphConstructionCost + agBaseOrderCost + agSchematicInvocationCost

@[simp] theorem ag_license_overhead_eq : agLicenseOverhead = 18 := by
  decide

/-- The recursor-side base-order proof-length function is linear on the single
extracted dependency pair. -/
def stepDuplicatingRecursorBaseOrderProofLength : Nat → Nat := fun n => n

/-- Affine base-order witness for the recursor specialization. -/
def stepDuplicatingRecursorAffineBaseOrderBound :
    AffineBaseOrderBound stepDuplicatingRecursorBaseOrderProofLength where
  coefficient := 1
  constant := 0
  bound := by
    intro n
    simp [stepDuplicatingRecursorBaseOrderProofLength]

/-- Exact singleton dependency-pair-count witness for the recursor. -/
def stepDuplicatingRecursorPairCountBound :
    DependencyPairCountBound stepDuplicatingRecursorTRS where
  bound := 1
  cert := by
    simp [stepDuplicatingRecursorTRS]

/-- Concrete three-stage AG audit on the primitive recursor. -/
def stepDuplicatingRecursorAudit :
    ArtsGieslSingleApplicationAudit stepDuplicatingRecursorTRS where
  constructionConstant := 1
  baseOrderProofLength := stepDuplicatingRecursorBaseOrderProofLength
  soundnessConstant := agSchematicInvocationCost
  graphConstructionCost := agGraphConstructionCost
  baseOrderCheckCost := agBaseOrderCost
  soundnessInvocationCost := agSchematicInvocationCost
  totalProofLength := agLicenseOverhead
  graphConstruction_le := by
    simp [agGraphConstructionCost, stepDuplicatingRecursorTRS,
      FixedFiniteTRS.graphConstructionBound]
  baseOrderCheck_le := by
    simp [agBaseOrderCost, recursorDependencyPairCount, stepDuplicatingRecursorTRS,
      stepDuplicatingRecursorBaseOrderProofLength]
  soundnessInvocation_le := by
    simp [agSchematicInvocationCost]
  total_eq := by
    simp [agLicenseOverhead]

@[simp] theorem stepDuplicatingRecursorAudit_totalProofLength :
    stepDuplicatingRecursorAudit.totalProofLength = agLicenseOverhead := rfl

/-- Original recursor-side exact identity, preserved in the stronger module. -/
theorem ag_proof_length_on_step_duplicating_recursor (K : Nat) :
    residualProofWork K + agLicenseOverhead = K + agLicenseOverhead := by
  simp [residualProofWork, agLicenseOverhead]

/-- Clean specialization bridge from the generic fixed-finite-TRS layer to the
step-duplicating recursor. This is a bound theorem, not the exact residual
identity above. -/
theorem ag_total_certificate_length_on_step_duplicating_recursor_via_fixedFiniteTRS
    (K : Nat) :
    stepDuplicatingRecursorAudit.totalProofLength + residualProofWork K ≤
      K + agLicenseOverhead := by
  refine
    (ag_total_certificate_length_on_fixedFiniteTRS
      stepDuplicatingRecursorAudit
      (residualProofWork K)).trans ?_
  simp [FixedFiniteTRS.totalCertificateBound,
      FixedFiniteTRS.singleApplicationBound,
      FixedFiniteTRS.graphConstructionBound,
      stepDuplicatingRecursorAudit,
      stepDuplicatingRecursorTRS,
      stepDuplicatingRecursorBaseOrderProofLength,
      residualProofWork,
      agLicenseOverhead,
      agGraphConstructionCost,
      agBaseOrderCost,
      agSchematicInvocationCost,
      recursorDependencyPairCount,
      Nat.add_comm]

end OperatorKO7.ArtsGieslDerivationalComplexity
