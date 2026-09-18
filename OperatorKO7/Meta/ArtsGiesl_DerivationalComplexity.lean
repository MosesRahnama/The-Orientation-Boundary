import OperatorKO7.Meta.SchemaConfessionDominance
import OperatorKO7.Meta.DependencyPairs_HeadView
import Mathlib.Tactic

/-!
# Arts-Giesl Derivational-Cost Accounting

Finite-TRS-parametric accounting records for a modeled dependency-pair soundness
application.

This module deliberately separates four levels:

- a fixed-finite-TRS metadata surface (`FixedFiniteTRS`);
- a generic finite first-order TRS head-abstracted call-obligation count bound;
- an additive three-stage bound conditional on supplied stage costs;
- a metadata-only fallback theorem using an explicit pair-count witness.

The generic layer exposes two forms of arithmetic bookkeeping:

- it gives a generic fixed-finite-TRS cost layer;
- it bounds the head-abstracted call obligations produced by the artifact's
  finite first-order extraction engine when the symbol carrier is finite.

The extraction count below records distinct defined call heads per rule and
collapses repeated occurrences with the same head. External Arts-Giesl
processor costs enter through supplied budget fields.
-/

namespace OperatorKO7.ArtsGieslDerivationalComplexity

open OperatorKO7.StepDuplicating.StepDuplicatingSchema.BaseDuplicatingSystem
open OperatorKO7.DependencyPairsFragment

/-- Abstract finite-TRS metadata used by the additive cost model. -/
structure FixedFiniteTRS where
  ruleCount : Nat
  signatureSize : Nat
  dependencyPairCount : Nat

namespace FixedFiniteTRS

/-- Polynomial graph-construction budget stipulated by the cost model. -/
def graphConstructionBound (R : FixedFiniteTRS) (constructionConstant : Nat) : Nat :=
  constructionConstant * R.ruleCount ^ 2 * R.signatureSize

/-- Sum of the graph, base-order, and soundness budget terms. -/
def singleApplicationBound (R : FixedFiniteTRS)
    (constructionConstant : Nat)
    (baseOrderProofLength : Nat → Nat)
    (soundnessConstant : Nat) : Nat :=
  R.graphConstructionBound constructionConstant
    + baseOrderProofLength R.dependencyPairCount
    + soundnessConstant

/-- Cost-model envelope after adding a supplied residual-proof budget. -/
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

/-- Affine upper bound for a supplied base-order proof-length function. -/
structure AffineBaseOrderBound (L : Nat → Nat) where
  coefficient : Nat
  constant : Nat
  bound : ∀ n, L n ≤ coefficient * n + constant

/-- Upper-bound witness for the count stored in `FixedFiniteTRS`. -/
structure DependencyPairCountBound (R : FixedFiniteTRS) where
  bound : Nat
  cert : R.dependencyPairCount ≤ bound

/-- Supplied stage costs and upper bounds for one modeled soundness application.
The structure stores external processor costs as caller-provided metadata. -/
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

/-- Three-stage record obtained by setting every modeled stage cost to its budget. -/
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

/-- Additive envelope obtained from the three supplied stage inequalities. -/
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

/-- Additive envelope after adjoining a supplied residual-proof budget. -/
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

/-- An affine base-order budget yields the displayed polynomial expression in
the three metadata fields. -/
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

/-- Replacing the stored call-obligation count by an upper bound yields the
displayed metadata-side polynomial. -/
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

/-- Number of distinct defined call heads on one rule's right-hand side, with
zero assigned to a headless left-hand side. This head abstraction collapses
repeated call occurrences. -/
noncomputable def finiteHeadRuleEngineRuleContribution
    {σ : Type} [DecidableEq σ]
    (E : DependencyPairsFragment.FiniteHeadRuleEngine σ)
    (r : E.Rule) : Nat :=
  let _ : HasCallHeadView E.Term σ := E.termView
  if HasCallHeadView.rootHead? (τ := E.Term) (σ := σ) (E.lhs r) = none then
    0
  else
    ((HasCallHeadView.callHeads (τ := E.Term) (σ := σ) (E.rhs r)).filter
      (· ∈ E.definedHeads)).card

/-- Sum of the distinct defined call-head obligations contributed by all rules. -/
noncomputable def finiteHeadRuleEngineExtractedPairCount
    {σ : Type} [DecidableEq σ]
    (E : DependencyPairsFragment.FiniteHeadRuleEngine σ) : Nat :=
  (E.rules.toList.map (finiteHeadRuleEngineRuleContribution E)).sum

/-- The head-abstracted call-obligation count is at most the number of rules
times the number of symbols. -/
theorem finiteHeadRuleEngineExtractedPairCount_le_ruleCount_mul_signatureSize
    {σ : Type} [DecidableEq σ] [Fintype σ]
    (E : DependencyPairsFragment.FiniteHeadRuleEngine σ) :
    finiteHeadRuleEngineExtractedPairCount E ≤ E.rules.size * Fintype.card σ := by
  let contribution : E.Rule → Nat := finiteHeadRuleEngineRuleContribution E
  have hcontribution : ∀ r, contribution r ≤ Fintype.card σ := by
    intro r
    let _ : HasCallHeadView E.Term σ := E.termView
    by_cases hroot : HasCallHeadView.rootHead? (τ := E.Term) (σ := σ) (E.lhs r) = none
    · simp [contribution, finiteHeadRuleEngineRuleContribution, hroot]
    · have hcard :
          ((HasCallHeadView.callHeads (τ := E.Term) (σ := σ) (E.rhs r)).filter
            (· ∈ E.definedHeads)).card ≤ Fintype.card σ := by
        simpa using
          (Finset.card_le_univ
            ((HasCallHeadView.callHeads (τ := E.Term) (σ := σ) (E.rhs r)).filter
              (· ∈ E.definedHeads)))
      simpa [contribution, finiteHeadRuleEngineRuleContribution, hroot] using hcard
  simpa [finiteHeadRuleEngineExtractedPairCount, contribution] using
    list_sum_le_length_mul E.rules.toList contribution (Fintype.card σ) hcontribution

/-- Cost-model metadata induced by a finite head-view presentation. Its
`dependencyPairCount` field stores the head-abstracted call-obligation count. -/
noncomputable def FixedFiniteTRS.ofFiniteHeadRuleEngine
    {σ : Type} [DecidableEq σ] [Fintype σ]
    (E : DependencyPairsFragment.FiniteHeadRuleEngine σ) : FixedFiniteTRS where
  ruleCount := E.rules.size
  signatureSize := Fintype.card σ
  dependencyPairCount := finiteHeadRuleEngineExtractedPairCount E

/-- Rule-count times signature-size bound for the head-abstracted count. -/
abbrev dependencyPairCountBound_of_finiteHeadRuleEngine
    {σ : Type} [DecidableEq σ] [Fintype σ]
    (E : DependencyPairsFragment.FiniteHeadRuleEngine σ) :
    DependencyPairCountBound (FixedFiniteTRS.ofFiniteHeadRuleEngine E) where
  bound := E.rules.size * Fintype.card σ
  cert := finiteHeadRuleEngineExtractedPairCount_le_ruleCount_mul_signatureSize E

/-- Instantiation of the additive cost envelope for a finite head-view
presentation, with `n` equal to the head-abstracted call-obligation count. -/
theorem ag_proof_length_on_finiteHeadRuleTRS
    {σ : Type} [DecidableEq σ] [Fintype σ]
    (E : DependencyPairsFragment.FiniteHeadRuleEngine σ)
    (A : ArtsGieslSingleApplicationAudit (FixedFiniteTRS.ofFiniteHeadRuleEngine E)) :
    A.totalProofLength ≤
      A.constructionConstant * E.rules.size ^ 2 * Fintype.card σ
        + A.baseOrderProofLength (finiteHeadRuleEngineExtractedPairCount E)
        + A.soundnessConstant := by
  simpa [FixedFiniteTRS.ofFiniteHeadRuleEngine,
      FixedFiniteTRS.singleApplicationBound,
      FixedFiniteTRS.graphConstructionBound,
      finiteHeadRuleEngineExtractedPairCount] using
    ag_proof_length_on_fixedFiniteTRS A

/-- Head-view cost envelope after adding a supplied residual budget. -/
theorem ag_total_certificate_length_on_finiteHeadRuleTRS
    {σ : Type} [DecidableEq σ] [Fintype σ]
    (E : DependencyPairsFragment.FiniteHeadRuleEngine σ)
    (A : ArtsGieslSingleApplicationAudit (FixedFiniteTRS.ofFiniteHeadRuleEngine E))
    (residualCost : Nat) :
    A.totalProofLength + residualCost ≤
      A.constructionConstant * E.rules.size ^ 2 * Fintype.card σ
        + A.baseOrderProofLength (finiteHeadRuleEngineExtractedPairCount E)
        + A.soundnessConstant
        + residualCost := by
  simpa [FixedFiniteTRS.ofFiniteHeadRuleEngine,
      FixedFiniteTRS.totalCertificateBound,
      FixedFiniteTRS.singleApplicationBound,
      FixedFiniteTRS.graphConstructionBound,
      finiteHeadRuleEngineExtractedPairCount,
      Nat.add_assoc] using
    ag_total_certificate_length_on_fixedFiniteTRS A residualCost

/-- Metadata-side polynomial bound for a head-view presentation with an affine
base-order budget. -/
theorem arts_giesl_derivational_overhead_polynomial_of_finiteHeadRuleTRS
    {σ : Type} [DecidableEq σ] [Fintype σ]
    (E : DependencyPairsFragment.FiniteHeadRuleEngine σ)
    (A : ArtsGieslSingleApplicationAudit (FixedFiniteTRS.ofFiniteHeadRuleEngine E))
    (hBase : AffineBaseOrderBound A.baseOrderProofLength) :
    A.totalProofLength ≤
      A.constructionConstant * E.rules.size ^ 2 * Fintype.card σ
        + (hBase.coefficient * (E.rules.size * Fintype.card σ) + hBase.constant)
        + A.soundnessConstant := by
  simpa [FixedFiniteTRS.ofFiniteHeadRuleEngine,
      FixedFiniteTRS.graphConstructionBound,
      dependencyPairCountBound_of_finiteHeadRuleEngine] using
    arts_giesl_derivational_overhead_polynomial_of_pairCountBound
      A hBase (dependencyPairCountBound_of_finiteHeadRuleEngine E)

/-- Head-abstracted call-obligation count induced by a finite first-order
presentation. Repeated calls with the same head in one rule are collapsed. -/
noncomputable def finiteFirstOrderEngineExtractedPairCount
    {σ ν : Type} [DecidableEq σ] [Fintype σ]
    (E : DependencyPairsFragment.FiniteFirstOrderEngine σ ν) : Nat :=
  finiteHeadRuleEngineExtractedPairCount
    (DependencyPairsFragment.FiniteHeadRuleEngine.ofFiniteFirstOrderEngine E)

/-- Rule-count times signature-size bound for the first-order head abstraction. -/
theorem finiteFirstOrderEngineExtractedPairCount_le_ruleCount_mul_signatureSize
    {σ ν : Type} [DecidableEq σ] [Fintype σ]
    (E : DependencyPairsFragment.FiniteFirstOrderEngine σ ν) :
    finiteFirstOrderEngineExtractedPairCount E ≤ E.rules.size * Fintype.card σ :=
  finiteHeadRuleEngineExtractedPairCount_le_ruleCount_mul_signatureSize
    (DependencyPairsFragment.FiniteHeadRuleEngine.ofFiniteFirstOrderEngine E)

/-- Cost-model metadata induced by a finite first-order presentation. -/
noncomputable def FixedFiniteTRS.ofFiniteFirstOrderEngine
    {σ ν : Type} [DecidableEq σ] [Fintype σ]
    (E : DependencyPairsFragment.FiniteFirstOrderEngine σ ν) : FixedFiniteTRS where
  ruleCount := E.rules.size
  signatureSize := Fintype.card σ
  dependencyPairCount := finiteFirstOrderEngineExtractedPairCount E

/-- Rule-count times signature-size witness for the first-order head abstraction. -/
abbrev dependencyPairCountBound_of_finiteFirstOrderEngine
    {σ ν : Type} [DecidableEq σ] [Fintype σ]
    (E : DependencyPairsFragment.FiniteFirstOrderEngine σ ν) :
    DependencyPairCountBound (FixedFiniteTRS.ofFiniteFirstOrderEngine E) where
  bound := E.rules.size * Fintype.card σ
  cert := finiteFirstOrderEngineExtractedPairCount_le_ruleCount_mul_signatureSize E

/-- Instantiation of the additive cost envelope for a finite first-order
presentation, using its head-abstracted call-obligation count. -/
theorem ag_proof_length_on_finiteFirstOrderTRS
    {σ ν : Type} [DecidableEq σ] [Fintype σ]
    (E : DependencyPairsFragment.FiniteFirstOrderEngine σ ν)
    (A : ArtsGieslSingleApplicationAudit (FixedFiniteTRS.ofFiniteFirstOrderEngine E)) :
    A.totalProofLength ≤
      A.constructionConstant * E.rules.size ^ 2 * Fintype.card σ
        + A.baseOrderProofLength (finiteFirstOrderEngineExtractedPairCount E)
        + A.soundnessConstant := by
  simpa [FixedFiniteTRS.ofFiniteFirstOrderEngine,
      finiteFirstOrderEngineExtractedPairCount,
      FixedFiniteTRS.singleApplicationBound,
      FixedFiniteTRS.graphConstructionBound] using
    ag_proof_length_on_fixedFiniteTRS A

/-- First-order cost envelope after adding a supplied residual budget. -/
theorem ag_total_certificate_length_on_finiteFirstOrderTRS
    {σ ν : Type} [DecidableEq σ] [Fintype σ]
    (E : DependencyPairsFragment.FiniteFirstOrderEngine σ ν)
    (A : ArtsGieslSingleApplicationAudit (FixedFiniteTRS.ofFiniteFirstOrderEngine E))
    (residualCost : Nat) :
    A.totalProofLength + residualCost ≤
      A.constructionConstant * E.rules.size ^ 2 * Fintype.card σ
        + A.baseOrderProofLength (finiteFirstOrderEngineExtractedPairCount E)
        + A.soundnessConstant
        + residualCost := by
  simpa [FixedFiniteTRS.ofFiniteFirstOrderEngine,
      finiteFirstOrderEngineExtractedPairCount,
      FixedFiniteTRS.totalCertificateBound,
      FixedFiniteTRS.singleApplicationBound,
      FixedFiniteTRS.graphConstructionBound,
      Nat.add_assoc] using
    ag_total_certificate_length_on_fixedFiniteTRS A residualCost

/-- Metadata-side polynomial bound for a finite first-order presentation with
an affine base-order budget. -/
theorem arts_giesl_derivational_overhead_polynomial_of_finiteFirstOrderTRS
    {σ ν : Type} [DecidableEq σ] [Fintype σ]
    (E : DependencyPairsFragment.FiniteFirstOrderEngine σ ν)
    (A : ArtsGieslSingleApplicationAudit (FixedFiniteTRS.ofFiniteFirstOrderEngine E))
    (hBase : AffineBaseOrderBound A.baseOrderProofLength) :
    A.totalProofLength ≤
      A.constructionConstant * E.rules.size ^ 2 * Fintype.card σ
        + (hBase.coefficient * (E.rules.size * Fintype.card σ) + hBase.constant)
        + A.soundnessConstant := by
  simpa [FixedFiniteTRS.ofFiniteFirstOrderEngine,
      FixedFiniteTRS.graphConstructionBound,
      dependencyPairCountBound_of_finiteFirstOrderEngine] using
    arts_giesl_derivational_overhead_polynomial_of_pairCountBound
      A hBase (dependencyPairCountBound_of_finiteFirstOrderEngine E)

/-! ## Recursor-side specialization -/

/-- Stipulated metadata for the primitive step-duplicating recursor cost model. -/
def stepDuplicatingRecursorTRS : FixedFiniteTRS where
  ruleCount := 2
  signatureSize := 4
  dependencyPairCount := 1

/-- Stored rule count for the recursor model. -/
def recursorRuleCount : Nat := stepDuplicatingRecursorTRS.ruleCount

/-- Stored signature size for the recursor model. -/
def recursorSignatureSize : Nat := stepDuplicatingRecursorTRS.signatureSize

/-- Stored call-obligation count for the recursor model. -/
def recursorDependencyPairCount : Nat := stepDuplicatingRecursorTRS.dependencyPairCount

/-- Graph-construction budget assigned by the recursor cost model. -/
def agGraphConstructionCost : Nat :=
  stepDuplicatingRecursorTRS.graphConstructionBound 1

/-- Base-order budget assigned to the recursor's one stored call obligation. -/
def agBaseOrderCost : Nat :=
  recursorDependencyPairCount

/-- Soundness-invocation budget assigned by the recursor cost model. -/
def agSchematicInvocationCost : Nat := 1

/-- Sum of the three stipulated recursor budget terms. -/
def agLicenseOverhead : Nat :=
  agGraphConstructionCost + agBaseOrderCost + agSchematicInvocationCost

@[simp] theorem ag_license_overhead_eq : agLicenseOverhead = 18 := by
  decide

/-- Identity base-order budget function used in the recursor specialization. -/
def stepDuplicatingRecursorBaseOrderProofLength : Nat → Nat := fun n => n

/-- Affine upper-bound witness for the identity base-order budget. -/
def stepDuplicatingRecursorAffineBaseOrderBound :
    AffineBaseOrderBound stepDuplicatingRecursorBaseOrderProofLength where
  coefficient := 1
  constant := 0
  bound := by
    intro n
    simp [stepDuplicatingRecursorBaseOrderProofLength]

/-- Upper-bound witness for the recursor's stored count of one. -/
def stepDuplicatingRecursorPairCountBound :
    DependencyPairCountBound stepDuplicatingRecursorTRS where
  bound := 1
  cert := by
    simp [stepDuplicatingRecursorTRS]

/-- Three-stage record saturating the stipulated recursor budgets. -/
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

/-- Definitional accounting identity because `residualProofWork K = K`. -/
theorem ag_proof_length_on_step_duplicating_recursor (K : Nat) :
    residualProofWork K + agLicenseOverhead = K + agLicenseOverhead := by
  simp [residualProofWork, agLicenseOverhead]

/-- Recursor specialization of the generic additive envelope. -/
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
