import OperatorKO7.Meta.ProofTheoreticRegister
import OperatorKO7.Meta.DependencyPairs_KernelFirstOrder
import Mathlib.Tactic

namespace ArtsGieslDerivationalReach

open OperatorKO7

instance : Fintype OperatorKO7.DependencyPairsFragment.KernelFirstOrder.Symbol where
  elems :=
    { OperatorKO7.DependencyPairsFragment.KernelFirstOrder.Symbol.void,
      OperatorKO7.DependencyPairsFragment.KernelFirstOrder.Symbol.delta,
      OperatorKO7.DependencyPairsFragment.KernelFirstOrder.Symbol.integrate,
      OperatorKO7.DependencyPairsFragment.KernelFirstOrder.Symbol.merge,
      OperatorKO7.DependencyPairsFragment.KernelFirstOrder.Symbol.app,
      OperatorKO7.DependencyPairsFragment.KernelFirstOrder.Symbol.recD,
      OperatorKO7.DependencyPairsFragment.KernelFirstOrder.Symbol.eqW }
  complete := by
    intro s
    cases s <;> simp

example : True := by
  have := @OperatorKO7.ArtsGieslDerivationalComplexity.FixedFiniteTRS.mk
  trivial

#check OperatorKO7.ArtsGieslDerivationalComplexity.FixedFiniteTRS.graphConstructionBound
#check OperatorKO7.ArtsGieslDerivationalComplexity.FixedFiniteTRS.singleApplicationBound
#check OperatorKO7.ArtsGieslDerivationalComplexity.FixedFiniteTRS.totalCertificateBound
#check OperatorKO7.ArtsGieslDerivationalComplexity.AffineBaseOrderBound
#check OperatorKO7.ArtsGieslDerivationalComplexity.DependencyPairCountBound
#check OperatorKO7.ArtsGieslDerivationalComplexity.ArtsGieslSingleApplicationAudit
#check OperatorKO7.ArtsGieslDerivationalComplexity.ag_proof_length_on_fixedFiniteTRS
#check OperatorKO7.ArtsGieslDerivationalComplexity.ag_total_certificate_length_on_fixedFiniteTRS
#check OperatorKO7.ArtsGieslDerivationalComplexity.arts_giesl_derivational_overhead_polynomial
#check OperatorKO7.ArtsGieslDerivationalComplexity.arts_giesl_derivational_overhead_polynomial_of_pairCountBound
#check OperatorKO7.ArtsGieslDerivationalComplexity.FixedFiniteTRS.canonicalAudit
#check OperatorKO7.ArtsGieslDerivationalComplexity.finiteHeadRuleEngineExtractedPairCount
#check OperatorKO7.ArtsGieslDerivationalComplexity.finiteHeadRuleEngineExtractedPairCount_le_ruleCount_mul_signatureSize
#check OperatorKO7.ArtsGieslDerivationalComplexity.FixedFiniteTRS.ofFiniteHeadRuleEngine
#check OperatorKO7.ArtsGieslDerivationalComplexity.dependencyPairCountBound_of_finiteHeadRuleEngine
#check OperatorKO7.ArtsGieslDerivationalComplexity.ag_proof_length_on_finiteHeadRuleTRS
#check OperatorKO7.ArtsGieslDerivationalComplexity.ag_total_certificate_length_on_finiteHeadRuleTRS
#check OperatorKO7.ArtsGieslDerivationalComplexity.arts_giesl_derivational_overhead_polynomial_of_finiteHeadRuleTRS
#check OperatorKO7.ArtsGieslDerivationalComplexity.finiteFirstOrderEngineExtractedPairCount
#check OperatorKO7.ArtsGieslDerivationalComplexity.finiteFirstOrderEngineExtractedPairCount_le_ruleCount_mul_signatureSize
#check OperatorKO7.ArtsGieslDerivationalComplexity.FixedFiniteTRS.ofFiniteFirstOrderEngine
#check OperatorKO7.ArtsGieslDerivationalComplexity.dependencyPairCountBound_of_finiteFirstOrderEngine
#check OperatorKO7.ArtsGieslDerivationalComplexity.ag_proof_length_on_finiteFirstOrderTRS
#check OperatorKO7.ArtsGieslDerivationalComplexity.ag_total_certificate_length_on_finiteFirstOrderTRS
#check OperatorKO7.ArtsGieslDerivationalComplexity.arts_giesl_derivational_overhead_polynomial_of_finiteFirstOrderTRS
#check OperatorKO7.ArtsGieslDerivationalComplexity.stepDuplicatingRecursorTRS
#check OperatorKO7.ArtsGieslDerivationalComplexity.stepDuplicatingRecursorAudit
#check OperatorKO7.ArtsGieslDerivationalComplexity.ag_total_certificate_length_on_step_duplicating_recursor_via_fixedFiniteTRS

def idAffineBaseOrderBound :
    OperatorKO7.ArtsGieslDerivationalComplexity.AffineBaseOrderBound (fun n => n) where
  coefficient := 1
  constant := 0
  bound := by
    intro n
    omega

noncomputable def ko7Audit :
    OperatorKO7.ArtsGieslDerivationalComplexity.ArtsGieslSingleApplicationAudit
      (OperatorKO7.ArtsGieslDerivationalComplexity.FixedFiniteTRS.ofFiniteFirstOrderEngine
        OperatorKO7.DependencyPairsFragment.KernelFirstOrder.ko7Engine) :=
  OperatorKO7.ArtsGieslDerivationalComplexity.FixedFiniteTRS.canonicalAudit
    (OperatorKO7.ArtsGieslDerivationalComplexity.FixedFiniteTRS.ofFiniteFirstOrderEngine
      OperatorKO7.DependencyPairsFragment.KernelFirstOrder.ko7Engine)
    1
    (fun n => n)
    1

noncomputable def ko7HeadAudit :
    OperatorKO7.ArtsGieslDerivationalComplexity.ArtsGieslSingleApplicationAudit
      (OperatorKO7.ArtsGieslDerivationalComplexity.FixedFiniteTRS.ofFiniteHeadRuleEngine
        OperatorKO7.DependencyPairsFragment.KernelFirstOrder.ko7HeadEngine) :=
  OperatorKO7.ArtsGieslDerivationalComplexity.FixedFiniteTRS.canonicalAudit
    (OperatorKO7.ArtsGieslDerivationalComplexity.FixedFiniteTRS.ofFiniteHeadRuleEngine
      OperatorKO7.DependencyPairsFragment.KernelFirstOrder.ko7HeadEngine)
    1
    (fun n => n)
    1

example :
    OperatorKO7.ArtsGieslDerivationalComplexity.agLicenseOverhead = 18 :=
  OperatorKO7.ArtsGieslDerivationalComplexity.ag_license_overhead_eq

example :
    OperatorKO7.ProofTheoreticRegister.agLicenseOverhead = 18 :=
  OperatorKO7.ProofTheoreticRegister.ag_license_overhead_eq

example (K : Nat) :
    OperatorKO7.StepDuplicating.StepDuplicatingSchema.BaseDuplicatingSystem.residualProofWork K
      + OperatorKO7.ProofTheoreticRegister.agLicenseOverhead =
        K + OperatorKO7.ProofTheoreticRegister.agLicenseOverhead :=
  OperatorKO7.ProofTheoreticRegister.ag_proof_length_on_step_duplicating_recursor K

example :
    OperatorKO7.ArtsGieslDerivationalComplexity.stepDuplicatingRecursorAudit.totalProofLength ≤
      OperatorKO7.ArtsGieslDerivationalComplexity.stepDuplicatingRecursorTRS.singleApplicationBound
        OperatorKO7.ArtsGieslDerivationalComplexity.stepDuplicatingRecursorAudit.constructionConstant
        OperatorKO7.ArtsGieslDerivationalComplexity.stepDuplicatingRecursorAudit.baseOrderProofLength
        OperatorKO7.ArtsGieslDerivationalComplexity.stepDuplicatingRecursorAudit.soundnessConstant :=
  OperatorKO7.ArtsGieslDerivationalComplexity.ag_proof_length_on_fixedFiniteTRS
    OperatorKO7.ArtsGieslDerivationalComplexity.stepDuplicatingRecursorAudit

example :
    OperatorKO7.ArtsGieslDerivationalComplexity.stepDuplicatingRecursorAudit.totalProofLength ≤
      OperatorKO7.ArtsGieslDerivationalComplexity.stepDuplicatingRecursorTRS.graphConstructionBound
        OperatorKO7.ArtsGieslDerivationalComplexity.stepDuplicatingRecursorAudit.constructionConstant
        +
          (OperatorKO7.ArtsGieslDerivationalComplexity.stepDuplicatingRecursorAffineBaseOrderBound.coefficient
            * OperatorKO7.ArtsGieslDerivationalComplexity.stepDuplicatingRecursorTRS.dependencyPairCount
            +
              OperatorKO7.ArtsGieslDerivationalComplexity.stepDuplicatingRecursorAffineBaseOrderBound.constant)
        + OperatorKO7.ArtsGieslDerivationalComplexity.stepDuplicatingRecursorAudit.soundnessConstant :=
  OperatorKO7.ArtsGieslDerivationalComplexity.arts_giesl_derivational_overhead_polynomial
    OperatorKO7.ArtsGieslDerivationalComplexity.stepDuplicatingRecursorAudit
    OperatorKO7.ArtsGieslDerivationalComplexity.stepDuplicatingRecursorAffineBaseOrderBound

example :
    OperatorKO7.ArtsGieslDerivationalComplexity.stepDuplicatingRecursorAudit.totalProofLength ≤
      OperatorKO7.ArtsGieslDerivationalComplexity.stepDuplicatingRecursorTRS.graphConstructionBound
        OperatorKO7.ArtsGieslDerivationalComplexity.stepDuplicatingRecursorAudit.constructionConstant
        +
          (OperatorKO7.ArtsGieslDerivationalComplexity.stepDuplicatingRecursorAffineBaseOrderBound.coefficient
            * OperatorKO7.ArtsGieslDerivationalComplexity.stepDuplicatingRecursorPairCountBound.bound
            +
              OperatorKO7.ArtsGieslDerivationalComplexity.stepDuplicatingRecursorAffineBaseOrderBound.constant)
        + OperatorKO7.ArtsGieslDerivationalComplexity.stepDuplicatingRecursorAudit.soundnessConstant :=
  OperatorKO7.ArtsGieslDerivationalComplexity.arts_giesl_derivational_overhead_polynomial_of_pairCountBound
    OperatorKO7.ArtsGieslDerivationalComplexity.stepDuplicatingRecursorAudit
    OperatorKO7.ArtsGieslDerivationalComplexity.stepDuplicatingRecursorAffineBaseOrderBound
    OperatorKO7.ArtsGieslDerivationalComplexity.stepDuplicatingRecursorPairCountBound

example (K : Nat) :
    OperatorKO7.ArtsGieslDerivationalComplexity.stepDuplicatingRecursorAudit.totalProofLength
      + OperatorKO7.StepDuplicating.StepDuplicatingSchema.BaseDuplicatingSystem.residualProofWork K ≤
        K + OperatorKO7.ArtsGieslDerivationalComplexity.agLicenseOverhead :=
  OperatorKO7.ArtsGieslDerivationalComplexity.ag_total_certificate_length_on_step_duplicating_recursor_via_fixedFiniteTRS K

example :
    OperatorKO7.ArtsGieslDerivationalComplexity.finiteFirstOrderEngineExtractedPairCount
      OperatorKO7.DependencyPairsFragment.KernelFirstOrder.ko7Engine ≤
        OperatorKO7.DependencyPairsFragment.KernelFirstOrder.ko7Engine.rules.size
          * Fintype.card OperatorKO7.DependencyPairsFragment.KernelFirstOrder.Symbol :=
  OperatorKO7.ArtsGieslDerivationalComplexity.finiteFirstOrderEngineExtractedPairCount_le_ruleCount_mul_signatureSize
    OperatorKO7.DependencyPairsFragment.KernelFirstOrder.ko7Engine

example :
    (OperatorKO7.ArtsGieslDerivationalComplexity.dependencyPairCountBound_of_finiteHeadRuleEngine
      OperatorKO7.DependencyPairsFragment.KernelFirstOrder.ko7HeadEngine).bound =
        OperatorKO7.DependencyPairsFragment.KernelFirstOrder.ko7HeadEngine.rules.size
          * Fintype.card OperatorKO7.DependencyPairsFragment.KernelFirstOrder.Symbol :=
  rfl

example :
    (OperatorKO7.ArtsGieslDerivationalComplexity.dependencyPairCountBound_of_finiteFirstOrderEngine
      OperatorKO7.DependencyPairsFragment.KernelFirstOrder.ko7Engine).bound =
        OperatorKO7.DependencyPairsFragment.KernelFirstOrder.ko7Engine.rules.size
          * Fintype.card OperatorKO7.DependencyPairsFragment.KernelFirstOrder.Symbol :=
  rfl

example :
    OperatorKO7.ArtsGieslDerivationalComplexity.finiteHeadRuleEngineExtractedPairCount
      OperatorKO7.DependencyPairsFragment.KernelFirstOrder.ko7HeadEngine ≤
        OperatorKO7.DependencyPairsFragment.KernelFirstOrder.ko7HeadEngine.rules.size
          * Fintype.card OperatorKO7.DependencyPairsFragment.KernelFirstOrder.Symbol :=
  OperatorKO7.ArtsGieslDerivationalComplexity.finiteHeadRuleEngineExtractedPairCount_le_ruleCount_mul_signatureSize
    OperatorKO7.DependencyPairsFragment.KernelFirstOrder.ko7HeadEngine

example :
    ko7HeadAudit.totalProofLength ≤
      ko7HeadAudit.constructionConstant
        * OperatorKO7.DependencyPairsFragment.KernelFirstOrder.ko7HeadEngine.rules.size ^ 2
        * Fintype.card OperatorKO7.DependencyPairsFragment.KernelFirstOrder.Symbol
      + ko7HeadAudit.baseOrderProofLength
          (OperatorKO7.ArtsGieslDerivationalComplexity.finiteHeadRuleEngineExtractedPairCount
            OperatorKO7.DependencyPairsFragment.KernelFirstOrder.ko7HeadEngine)
      + ko7HeadAudit.soundnessConstant :=
  OperatorKO7.ArtsGieslDerivationalComplexity.ag_proof_length_on_finiteHeadRuleTRS
    OperatorKO7.DependencyPairsFragment.KernelFirstOrder.ko7HeadEngine
    ko7HeadAudit

example (residualCost : Nat) :
    ko7HeadAudit.totalProofLength + residualCost ≤
      ko7HeadAudit.constructionConstant
        * OperatorKO7.DependencyPairsFragment.KernelFirstOrder.ko7HeadEngine.rules.size ^ 2
        * Fintype.card OperatorKO7.DependencyPairsFragment.KernelFirstOrder.Symbol
      + ko7HeadAudit.baseOrderProofLength
          (OperatorKO7.ArtsGieslDerivationalComplexity.finiteHeadRuleEngineExtractedPairCount
            OperatorKO7.DependencyPairsFragment.KernelFirstOrder.ko7HeadEngine)
      + ko7HeadAudit.soundnessConstant
      + residualCost :=
  OperatorKO7.ArtsGieslDerivationalComplexity.ag_total_certificate_length_on_finiteHeadRuleTRS
    OperatorKO7.DependencyPairsFragment.KernelFirstOrder.ko7HeadEngine
    ko7HeadAudit
    residualCost

example :
    ko7HeadAudit.totalProofLength ≤
      ko7HeadAudit.constructionConstant
        * OperatorKO7.DependencyPairsFragment.KernelFirstOrder.ko7HeadEngine.rules.size ^ 2
        * Fintype.card OperatorKO7.DependencyPairsFragment.KernelFirstOrder.Symbol
      + (idAffineBaseOrderBound.coefficient
          * (OperatorKO7.DependencyPairsFragment.KernelFirstOrder.ko7HeadEngine.rules.size
              * Fintype.card OperatorKO7.DependencyPairsFragment.KernelFirstOrder.Symbol)
          + idAffineBaseOrderBound.constant)
      + ko7HeadAudit.soundnessConstant :=
  OperatorKO7.ArtsGieslDerivationalComplexity.arts_giesl_derivational_overhead_polynomial_of_finiteHeadRuleTRS
    OperatorKO7.DependencyPairsFragment.KernelFirstOrder.ko7HeadEngine
    ko7HeadAudit
    idAffineBaseOrderBound

example :
    ko7Audit.totalProofLength ≤
      ko7Audit.constructionConstant
        * OperatorKO7.DependencyPairsFragment.KernelFirstOrder.ko7Engine.rules.size ^ 2
        * Fintype.card OperatorKO7.DependencyPairsFragment.KernelFirstOrder.Symbol
      + ko7Audit.baseOrderProofLength
          (OperatorKO7.ArtsGieslDerivationalComplexity.finiteFirstOrderEngineExtractedPairCount
            OperatorKO7.DependencyPairsFragment.KernelFirstOrder.ko7Engine)
      + ko7Audit.soundnessConstant :=
  OperatorKO7.ArtsGieslDerivationalComplexity.ag_proof_length_on_finiteFirstOrderTRS
    OperatorKO7.DependencyPairsFragment.KernelFirstOrder.ko7Engine
    ko7Audit

example (residualCost : Nat) :
    ko7Audit.totalProofLength + residualCost ≤
      ko7Audit.constructionConstant
        * OperatorKO7.DependencyPairsFragment.KernelFirstOrder.ko7Engine.rules.size ^ 2
        * Fintype.card OperatorKO7.DependencyPairsFragment.KernelFirstOrder.Symbol
      + ko7Audit.baseOrderProofLength
          (OperatorKO7.ArtsGieslDerivationalComplexity.finiteFirstOrderEngineExtractedPairCount
            OperatorKO7.DependencyPairsFragment.KernelFirstOrder.ko7Engine)
      + ko7Audit.soundnessConstant
      + residualCost :=
  OperatorKO7.ArtsGieslDerivationalComplexity.ag_total_certificate_length_on_finiteFirstOrderTRS
    OperatorKO7.DependencyPairsFragment.KernelFirstOrder.ko7Engine
    ko7Audit
    residualCost

example :
    ko7Audit.totalProofLength ≤
      ko7Audit.constructionConstant
        * OperatorKO7.DependencyPairsFragment.KernelFirstOrder.ko7Engine.rules.size ^ 2
        * Fintype.card OperatorKO7.DependencyPairsFragment.KernelFirstOrder.Symbol
      + (idAffineBaseOrderBound.coefficient
          * (OperatorKO7.DependencyPairsFragment.KernelFirstOrder.ko7Engine.rules.size
              * Fintype.card OperatorKO7.DependencyPairsFragment.KernelFirstOrder.Symbol)
          + idAffineBaseOrderBound.constant)
      + ko7Audit.soundnessConstant :=
  OperatorKO7.ArtsGieslDerivationalComplexity.arts_giesl_derivational_overhead_polynomial_of_finiteFirstOrderTRS
    OperatorKO7.DependencyPairsFragment.KernelFirstOrder.ko7Engine
    ko7Audit
    idAffineBaseOrderBound

end ArtsGieslDerivationalReach
