import OperatorKO7.Meta.LicensedBoundaryCalculus.Quantitative.DistinctionAdapters

/-!
This module computes semantic profiles for a fixed three-node fixture. Equalities and drop
calculations apply to that finite instance.










-/

set_option autoImplicit false

namespace OperatorKO7.Meta.LicensedBoundaryCalculus
namespace KO7DistinctionAdapter

open OperatorKO7.Meta.DistinctionBoundary.Quantitative
open OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7LocalCone

namespace KRepair

open OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7RepairCover

/-- The displayed proposition follows from the stated hypotheses. -/
theorem raw_minimumRepairCoverCost_eq_one :
    minimumRepairCoverCost bad closes actionCost coverable = 1 := by
  have hguard : IsRepairCover bad closes ({.guardDiff} : Finset RepairAction) := by
    intro b hb
    simp [closes]
  apply le_antisymm
  · have hupper := minimumRepairCoverCost_le
      (cost := actionCost) coverable hguard
    simpa [repairCoverCost, actionCost] using hupper
  · calc
      1 = repairCoverNumber bad closes coverable :=
        canonical_breaker_repairCoverNumber_eq_one.symm
      _ ≤ minimumRepairCoverCost bad closes actionCost coverable :=
        repairCoverNumber_le_minimumRepairCoverCost coverable
          (fun a => by cases a <;> decide)

#print axioms raw_minimumRepairCoverCost_eq_one

end KRepair

/-- Expected raw profile, stated only after every coordinate has an intrinsic
definition. -/
def rawExactProfile : SemanticProfile where
  terminalMultiplicity := 2
  terminalHartley := some 1
  criticalPairDefect := 1
  minimumRepairCover := 1
  minimumRepairCost := 1
  witnessRank := 1
  fixedLengthCertificateFloor := 1
  prefixCodeCertificateFloor := 1

/-- Expected licensed profile. -/
def licensedExactProfile : SemanticProfile where
  terminalMultiplicity := 1
  terminalHartley := some 0
  criticalPairDefect := 0
  minimumRepairCover := 0
  minimumRepairCost := 0
  witnessRank := 0
  fixedLengthCertificateFloor := 0
  prefixCodeCertificateFloor := 0

theorem raw_terminalMultiplicity_exact :
    (semanticProfile rawData).terminalMultiplicity = 2 := by
  change terminalMultiplicity LocalRaw .source = 2
  exact
    OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7TerminalMultiplicity.raw_terminalMultiplicity_eq_two

theorem licensed_terminalMultiplicity_exact :
    (semanticProfile licensedData).terminalMultiplicity = 1 := by
  change terminalMultiplicity LocalLicensed .source = 1
  exact
    OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7TerminalMultiplicity.licensed_terminalMultiplicity_eq_one

theorem raw_terminalHartley_exact :
    (semanticProfile rawData).terminalHartley = some 1 := by
  change SemanticScope.terminalHartley? rawScope = some 1
  rw [SemanticScope.terminalHartley?_eq_some_of_normalizingAt
    rawScope rawScope_normalizing]
  congr 1
  exact
    OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7TerminalMultiplicity.raw_terminalHartleyEntropy_eq_one

theorem licensed_terminalHartley_exact :
    (semanticProfile licensedData).terminalHartley = some 0 := by
  change SemanticScope.terminalHartley? licensedScope = some 0
  rw [SemanticScope.terminalHartley?_eq_some_of_normalizingAt
    licensedScope licensedScope_normalizing]
  congr 1
  exact
    OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7TerminalMultiplicity.licensed_terminalHartleyEntropy_eq_zero

theorem raw_criticalPairDefect_exact :
    (semanticProfile rawData).criticalPairDefect = 1 := by
  change
    OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7RepairCover.bad.card = 1
  decide

theorem licensed_criticalPairDefect_exact :
    (semanticProfile licensedData).criticalPairDefect = 0 := by
  rfl

theorem raw_minimumRepairCover_exact :
    (semanticProfile rawData).minimumRepairCover = 1 := by
  change repairCoverNumber
    OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7RepairCover.bad
    OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7RepairCover.closes
    OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7RepairCover.coverable = 1
  exact
    OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7RepairCover.canonical_breaker_repairCoverNumber_eq_one

theorem licensed_minimumRepairCover_exact :
    (semanticProfile licensedData).minimumRepairCover = 0 := by
  change repairCoverNumber ∅ licensedCloses licensedCoverable = 0
  exact repairCoverNumber_empty_eq_zero licensedCloses licensedCoverable

theorem raw_minimumRepairCost_exact :
    (semanticProfile rawData).minimumRepairCost = 1 := by
  change minimumRepairCoverCost
    OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7RepairCover.bad
    OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7RepairCover.closes
    OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7RepairCover.actionCost
    OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7RepairCover.coverable = 1
  exact KRepair.raw_minimumRepairCoverCost_eq_one

theorem licensed_minimumRepairCost_exact :
    (semanticProfile licensedData).minimumRepairCost = 0 := by
  change minimumRepairCoverCost ∅ licensedCloses
    OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7RepairCover.actionCost
    licensedCoverable = 0
  exact minimumRepairCoverCost_empty_eq_zero licensedCloses _ licensedCoverable

theorem raw_witnessRank_exact :
    (semanticProfile rawData).witnessRank = 1 := by
  change witnessRank
    OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7WitnessRank.ko7Adequacy = 1
  exact
    OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7WitnessRank.ko7_distinction_witnessRank_eq_one

theorem licensed_witnessRank_exact :
    (semanticProfile licensedData).witnessRank = 0 := by
  change witnessRank baseAdequacy = 0
  exact baseAdequacy_rank_zero

theorem raw_fixedLengthFloor_exact :
    (semanticProfile rawData).fixedLengthCertificateFloor = 1 := by
  norm_num [semanticProfile, rawData, Nat.clog]

theorem licensed_fixedLengthFloor_exact :
    (semanticProfile licensedData).fixedLengthCertificateFloor = 0 := by
  norm_num [semanticProfile, licensedData, Nat.clog]

theorem raw_prefixCodeFloor_exact :
    (semanticProfile rawData).prefixCodeCertificateFloor = 1 := by
  norm_num [semanticProfile, rawData, Nat.clog]

theorem licensed_prefixCodeFloor_exact :
    (semanticProfile licensedData).prefixCodeCertificateFloor = 0 := by
  norm_num [semanticProfile, licensedData, Nat.clog]

/-- The displayed proposition follows from the stated hypotheses.
-/
theorem raw_semanticProfile_exact :
    semanticProfile rawData = rawExactProfile := by
  apply SemanticProfile.ext
  · exact raw_terminalMultiplicity_exact
  · exact raw_terminalHartley_exact
  · exact raw_criticalPairDefect_exact
  · exact raw_minimumRepairCover_exact
  · exact raw_minimumRepairCost_exact
  · exact raw_witnessRank_exact
  · exact raw_fixedLengthFloor_exact
  · exact raw_prefixCodeFloor_exact

/-- The displayed proposition follows from the stated hypotheses. -/
theorem licensed_semanticProfile_exact :
    semanticProfile licensedData = licensedExactProfile := by
  apply SemanticProfile.ext
  · exact licensed_terminalMultiplicity_exact
  · exact licensed_terminalHartley_exact
  · exact licensed_criticalPairDefect_exact
  · exact licensed_minimumRepairCover_exact
  · exact licensed_minimumRepairCost_exact
  · exact licensed_witnessRank_exact
  · exact licensed_fixedLengthFloor_exact
  · exact licensed_prefixCodeFloor_exact

/-- The displayed proposition follows from the stated hypotheses.
-/
theorem ko7_profile_drop_exact :
    (semanticProfile rawData).terminalMultiplicity =
        (semanticProfile licensedData).terminalMultiplicity + 1 ∧
      (semanticProfile rawData).criticalPairDefect =
        (semanticProfile licensedData).criticalPairDefect + 1 ∧
      (semanticProfile rawData).minimumRepairCover =
        (semanticProfile licensedData).minimumRepairCover + 1 ∧
      (semanticProfile rawData).witnessRank =
        (semanticProfile licensedData).witnessRank + 1 := by
  rw [raw_semanticProfile_exact, licensed_semanticProfile_exact]
  decide

#check raw_semanticProfile_exact
#check licensed_semanticProfile_exact
#check ko7_profile_drop_exact
#print axioms raw_semanticProfile_exact
#print axioms licensed_semanticProfile_exact
#print axioms ko7_profile_drop_exact

end KO7DistinctionAdapter
end OperatorKO7.Meta.LicensedBoundaryCalculus
