import OperatorKO7.Meta.LicensedBoundaryCalculus.Quantitative.GuardedRates
import OperatorKO7.Meta.DistinctionBoundary.Quantitative.RepairCover
import OperatorKO7.Meta.DistinctionBoundary.Quantitative.WitnessRank
import OperatorKO7.Meta.DistinctionBoundary.Quantitative.CertificateLowerBound
import OperatorKO7.Meta.DistinctionBoundary.Quantitative.KraftPrefixCertificate

/-!
# Scoped quantitative profiles

The profile builder combines quantities computed from a typed relation scope,
a finite defect set, repair coverage, and graded witness data with numeric
inputs supplied by the caller. In particular, callers provide action costs and
the two alternative counts used by the certificate coordinates.

## Audit slots

Relation: the relation and source stored in `SemanticScope`.
Closure: the scope's explicit audit coordinate determines the reported scope.
Trust: kernel-only, with classical minimization over finite repair families.
Scope: finite local semantic profiles and coding floors.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.LicensedBoundaryCalculus

open OperatorKO7.Meta.DistinctionBoundary.Quantitative

universe u v w

/-- Construction data from which each profile coordinate is computed. The
`actionCost`, `fixedLengthAlternatives`, and `prefixCodeAlternatives` fields are
caller-supplied quantitative inputs. -/
structure SemanticConstructionData (A : ARS.{u}) [Fintype A.Carrier]
    (Defect : Type v) (Action : Type w)
    [DecidableEq Defect] [Fintype Action] [DecidableEq Action] where
  scope : SemanticScope A
  defects : Finset Defect
  closes : Action -> Finset Defect
  coverable : IsRepairCover defects closes Finset.univ
  actionCost : Action -> Nat
  witnessAdequacy : GradedAdequacy
  fixedLengthAlternatives : Nat
  prefixCodeAlternatives : Nat

/-- Quantitative profile produced from `SemanticConstructionData`. Optional
Hartley support represents the empty-support case with `none`. -/
structure SemanticProfile where
  terminalMultiplicity : Nat
  terminalHartley : Option Real
  criticalPairDefect : Nat
  minimumRepairCover : Nat
  minimumRepairCost : Nat
  witnessRank : Nat
  fixedLengthCertificateFloor : Nat
  prefixCodeCertificateFloor : Nat

@[ext] theorem SemanticProfile.ext {P Q : SemanticProfile}
    (terminalMultiplicity : P.terminalMultiplicity = Q.terminalMultiplicity)
    (terminalHartley : P.terminalHartley = Q.terminalHartley)
    (criticalPairDefect : P.criticalPairDefect = Q.criticalPairDefect)
    (minimumRepairCover : P.minimumRepairCover = Q.minimumRepairCover)
    (minimumRepairCost : P.minimumRepairCost = Q.minimumRepairCost)
    (witnessRank : P.witnessRank = Q.witnessRank)
    (fixedLengthCertificateFloor :
      P.fixedLengthCertificateFloor = Q.fixedLengthCertificateFloor)
    (prefixCodeCertificateFloor :
      P.prefixCodeCertificateFloor = Q.prefixCodeCertificateFloor) : P = Q := by
  cases P
  cases Q
  simp_all

noncomputable section

/-- Compute the profile from semantic construction data. -/
def semanticProfile {A : ARS.{u}} [Fintype A.Carrier]
    {Defect : Type v} {Action : Type w}
    [DecidableEq Defect] [Fintype Action] [DecidableEq Action]
    (D : SemanticConstructionData A Defect Action) : SemanticProfile where
  terminalMultiplicity := SemanticScope.terminalMultiplicity D.scope
  terminalHartley := SemanticScope.terminalHartley? D.scope
  criticalPairDefect := D.defects.card
  minimumRepairCover := repairCoverNumber D.defects D.closes D.coverable
  minimumRepairCost :=
    minimumRepairCoverCost D.defects D.closes D.actionCost D.coverable
  witnessRank :=
    OperatorKO7.Meta.DistinctionBoundary.Quantitative.witnessRank
      D.witnessAdequacy
  fixedLengthCertificateFloor := Nat.clog 2 D.fixedLengthAlternatives
  prefixCodeCertificateFloor := Nat.clog 2 D.prefixCodeAlternatives

/-- Unfolding the builder recovers all eight coordinate expressions
definitionally, including the expressions that use caller-supplied inputs. -/
theorem semanticProfile_eq_computed
    {A : ARS.{u}} [Fintype A.Carrier]
    {Defect : Type v} {Action : Type w}
    [DecidableEq Defect] [Fintype Action] [DecidableEq Action]
    (D : SemanticConstructionData A Defect Action) :
    semanticProfile D =
      { terminalMultiplicity := SemanticScope.terminalMultiplicity D.scope
        terminalHartley := SemanticScope.terminalHartley? D.scope
        criticalPairDefect := D.defects.card
        minimumRepairCover := repairCoverNumber D.defects D.closes D.coverable
        minimumRepairCost :=
          minimumRepairCoverCost D.defects D.closes D.actionCost D.coverable
        witnessRank :=
          OperatorKO7.Meta.DistinctionBoundary.Quantitative.witnessRank
            D.witnessAdequacy
        fixedLengthCertificateFloor := Nat.clog 2 D.fixedLengthAlternatives
        prefixCodeCertificateFloor := Nat.clog 2 D.prefixCodeAlternatives } :=
  rfl

/-- The fixed-length coordinate is a lower bound for every injective binary
encoding of a finite type whose cardinality equals the supplied alternative
count. -/
theorem fixedLengthCertificateFloor_le
    {A : ARS.{u}} [Fintype A.Carrier]
    {Defect : Type v} {Action : Type w}
    [DecidableEq Defect] [Fintype Action] [DecidableEq Action]
    (D : SemanticConstructionData A Defect Action)
    {E : Type} [Fintype E]
    (hcard : Fintype.card E = D.fixedLengthAlternatives)
    (L : Nat) (encode : E -> BitWord L) (hencode : Function.Injective encode) :
    (semanticProfile D).fixedLengthCertificateFloor <= L := by
  rw [semanticProfile, <- hcard]
  exact injective_certificate_clog_floor L encode hencode

/-- Normalization at the stored source makes the terminal Hartley field
defined for that source. -/
theorem semanticProfile_terminalHartley_defined
    {A : ARS.{u}} [Fintype A.Carrier]
    {Defect : Type v} {Action : Type w}
    [DecidableEq Defect] [Fintype Action] [DecidableEq Action]
    (D : SemanticConstructionData A Defect Action)
    (hnorm : NormalizingAt D.scope.relation D.scope.source) :
    exists h : Real, (semanticProfile D).terminalHartley = some h := by
  refine
    ⟨OperatorKO7.Meta.DistinctionBoundary.Quantitative.terminalHartleyEntropy
        D.scope.relation D.scope.source, ?_⟩
  exact SemanticScope.terminalHartley?_eq_some_of_normalizingAt D.scope hnorm

/-- An empty defect family has zero minimum repair cardinality. -/
theorem repairCoverNumber_empty_eq_zero
    {Defect : Type v} {Action : Type w}
    [DecidableEq Defect] [Fintype Action] [DecidableEq Action]
    (closes : Action -> Finset Defect)
    (hcoverable : IsRepairCover (∅ : Finset Defect) closes Finset.univ) :
    repairCoverNumber ∅ closes hcoverable = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply repairCoverNumber_le_card hcoverable (chosen := ∅)
  intro b hb
  simp at hb

/-- An empty defect family also has zero minimum weighted repair cost. -/
theorem minimumRepairCoverCost_empty_eq_zero
    {Defect : Type v} {Action : Type w}
    [DecidableEq Defect] [Fintype Action] [DecidableEq Action]
    (closes : Action -> Finset Defect) (cost : Action -> Nat)
    (hcoverable : IsRepairCover (∅ : Finset Defect) closes Finset.univ) :
    minimumRepairCoverCost ∅ closes cost hcoverable = 0 := by
  apply Nat.eq_zero_of_le_zero
  have hchosen : IsRepairCover (∅ : Finset Defect) closes ∅ := by
    intro b hb
    simp at hb
  simpa [repairCoverCost] using
    (minimumRepairCoverCost_le hcoverable hchosen)

#check @semanticProfile
#check @SemanticProfile.ext
#check @semanticProfile_eq_computed
#check @fixedLengthCertificateFloor_le
#check @semanticProfile_terminalHartley_defined
#check @repairCoverNumber_empty_eq_zero
#check @minimumRepairCoverCost_empty_eq_zero
#print axioms semanticProfile_eq_computed
#print axioms SemanticProfile.ext
#print axioms fixedLengthCertificateFloor_le
#print axioms semanticProfile_terminalHartley_defined
#print axioms repairCoverNumber_empty_eq_zero
#print axioms minimumRepairCoverCost_empty_eq_zero

end
end OperatorKO7.Meta.LicensedBoundaryCalculus
