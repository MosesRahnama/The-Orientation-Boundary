import OperatorKO7.Meta.DistinctionBoundary.MinimalFork.InformationCollapse
import OperatorKO7.Meta.DistinctionBoundary.Quantitative.RepairCover
import OperatorKO7.Meta.DistinctionBoundary.Quantitative.WitnessRank
import OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7RepairCover
import OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7WitnessRank

/-!
# Minimal-fork defect, repair-cover, and witness-rank profile

The three coordinates below retain different meanings:
* terminal defect = extra terminal alternatives above uniqueness;
* repair-cover number = minimum number of declared interventions covering the
  single canonical defect;
* witness rank = least comparison grade in the declared adequacy profile.
They are numerically small here but are not identified definitionally.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.DistinctionBoundary.MinimalFork

open OperatorKO7.Meta.DistinctionBoundary.Quantitative

/-- Excess terminal support above deterministic multiplicity one. -/
noncomputable def terminalDefect (R : Fork3 → Fork3 → Prop) (src : Fork3) : Nat :=
  terminalMultiplicity R src - 1

/-- Raw fork has exactly one excess terminal alternative. -/
theorem minimalFork_raw_terminalDefect_eq_one :
    terminalDefect Fork3Step .source = 1 := by
  rw [terminalDefect, fork3_raw_terminalMultiplicity_eq_two]

/-- Licensed fork has zero excess terminal alternatives. -/
theorem minimalFork_licensed_terminalDefect_eq_zero :
    terminalDefect Fork3LicensedStep .source = 0 := by
  rw [terminalDefect, fork3_licensed_terminalMultiplicity_eq_one]

/-- Single canonical bad branch. -/
def minimalBadDefects : Finset (Fin 1) := Finset.univ

/-- Single canonical guard closes the single defect. -/
def minimalRepairCoverage (_ : Fin 1) : Finset (Fin 1) := Finset.univ

/-- Full intervention set covers the defect. -/
theorem minimalRepair_coverable :
    IsRepairCover minimalBadDefects minimalRepairCoverage Finset.univ := by
  intro b _
  rw [Finset.mem_biUnion]
  exact ⟨0, Finset.mem_univ _, by fin_cases b; simp [minimalRepairCoverage]⟩

/-- Exactly one intervention is necessary and sufficient in the declared repair family. -/
theorem minimalFork_repairCoverNumber_eq_one :
    repairCoverNumber minimalBadDefects minimalRepairCoverage
      minimalRepair_coverable = 1 := by
  apply le_antisymm
  · calc
      repairCoverNumber minimalBadDefects minimalRepairCoverage
          minimalRepair_coverable ≤ (Finset.univ : Finset (Fin 1)).card :=
        repairCoverNumber_le_card minimalRepair_coverable minimalRepair_coverable
      _ = 1 := by simp
  · have hbound := repairCoverNumber_lower_bound minimalRepair_coverable
      (M := 1) (by omega) (fun _ => by simp [minimalRepairCoverage])
    have hcard : minimalBadDefects.card = 1 := by
      simp [minimalBadDefects]
    calc
      1 = minimalBadDefects.card ⌈/⌉ 1 := by simp [hcard]
      _ ≤ repairCoverNumber minimalBadDefects minimalRepairCoverage
          minimalRepair_coverable := hbound
/-- Raw comparison adequacy: grade zero lacks the disequality witness; every
positive grade carries it. -/
def minimalRawAdequacy : GradedAdequacy where
  adequate := fun i => 1 ≤ i
  upward := by
    intro i j hij hi
    exact hi.trans hij
  inhabited := ⟨1, le_rfl⟩

/-- Licensed adequacy: the guard is already built into the relation, so grade zero suffices. -/
def minimalLicensedAdequacy : GradedAdequacy where
  adequate := fun _ => True
  upward := by intros; trivial
  inhabited := ⟨0, trivial⟩

/-- Raw witness rank is one. -/
theorem minimalFork_raw_witnessRank_eq_one :
    witnessRank minimalRawAdequacy = 1 := by
  apply le_antisymm
  · exact witnessRank_le_of_adequate minimalRawAdequacy le_rfl
  · have hnot : ¬ minimalRawAdequacy.adequate 0 := by
      simp [minimalRawAdequacy]
    by_contra h
    have hz : witnessRank minimalRawAdequacy = 0 := Nat.eq_zero_of_not_pos h
    exact hnot (hz ▸ witnessRank_adequate minimalRawAdequacy)
/-- Licensed witness rank is zero. -/
theorem minimalFork_licensed_witnessRank_eq_zero :
    witnessRank minimalLicensedAdequacy = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact witnessRank_le_of_adequate minimalLicensedAdequacy trivial

/-- Empty licensed defect set on the canonical one-action carrier. -/
def minimalLicensedBadDefects : Finset (Fin 1) := ∅

/-- The empty canonical defect set is covered by the empty intervention set. -/
theorem minimalLicensedRepair_coverable :
    IsRepairCover minimalLicensedBadDefects minimalRepairCoverage
      (Finset.univ : Finset (Fin 1)) := by
  intro b hb
  simp [minimalLicensedBadDefects] at hb

/-- No further intervention is required after the canonical guard is installed. -/
theorem minimalLicensed_repairCoverNumber_eq_zero :
    repairCoverNumber minimalLicensedBadDefects minimalRepairCoverage
      minimalLicensedRepair_coverable = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply repairCoverNumber_le_card minimalLicensedRepair_coverable
    (chosen := (∅ : Finset (Fin 1)))
  intro b hb
  simp [minimalLicensedBadDefects] at hb

/-- Empty licensed KO7 defect set, retaining the live KO7 repair-action carrier. -/
def ko7LicensedBadDefects :
    Finset OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7RepairCover.CanonicalDefect := ∅

/-- The empty licensed KO7 defect set is coverable. -/
theorem ko7LicensedRepair_coverable :
    IsRepairCover ko7LicensedBadDefects
      OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7RepairCover.closes
      (Finset.univ : Finset
        OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7RepairCover.RepairAction) := by
  intro b hb
  simp [ko7LicensedBadDefects] at hb

/-- No additional KO7 repair action is needed after licensing. -/
theorem ko7Licensed_repairCoverNumber_eq_zero :
    repairCoverNumber ko7LicensedBadDefects
      OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7RepairCover.closes
      ko7LicensedRepair_coverable = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply repairCoverNumber_le_card ko7LicensedRepair_coverable
    (chosen := (∅ : Finset
      OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7RepairCover.RepairAction))
  intro b hb
  simp [ko7LicensedBadDefects] at hb

/-- Licensed KO7 adequacy: the exact guard is already in the relation. -/
def ko7LicensedAdequacy : GradedAdequacy where
  adequate := fun _ => True
  upward := by intros; trivial
  inhabited := ⟨0, trivial⟩

/-- The licensed KO7 witness rank is therefore zero. -/
theorem ko7Licensed_witnessRank_eq_zero :
    witnessRank ko7LicensedAdequacy = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact witnessRank_le_of_adequate ko7LicensedAdequacy trivial

/-- Quantitative tuple whose coordinates retain their separate meanings. -/
structure MinimalForkDefectProfile where
  terminalMultiplicity : Nat
  terminalDefect : Nat
  repairCover : Nat
  witnessRank : Nat
  deriving DecidableEq, Repr

/-- Canonical raw profile computed from the canonical relation and its intrinsic
repair/witness structures. -/
noncomputable def minimal_raw_profile : MinimalForkDefectProfile where
  terminalMultiplicity := terminalMultiplicity Fork3Step .source
  terminalDefect := terminalDefect Fork3Step .source
  repairCover := repairCoverNumber minimalBadDefects minimalRepairCoverage
    minimalRepair_coverable
  witnessRank := witnessRank minimalRawAdequacy

/-- Canonical licensed profile computed after deleting the bad diagonal edge. -/
noncomputable def minimal_licensed_profile : MinimalForkDefectProfile where
  terminalMultiplicity := terminalMultiplicity Fork3LicensedStep .source
  terminalDefect := terminalDefect Fork3LicensedStep .source
  repairCover := repairCoverNumber minimalLicensedBadDefects
    minimalRepairCoverage minimalLicensedRepair_coverable
  witnessRank := witnessRank minimalLicensedAdequacy

/-- Exact raw profile coordinates. -/
theorem minimal_raw_profile_exact :
    minimal_raw_profile =
      { terminalMultiplicity := 2, terminalDefect := 1,
        repairCover := 1, witnessRank := 1 } := by
  simp [minimal_raw_profile,
    fork3_raw_terminalMultiplicity_eq_two,
    minimalFork_raw_terminalDefect_eq_one,
    minimalFork_repairCoverNumber_eq_one,
    minimalFork_raw_witnessRank_eq_one]

/-- Exact licensed profile coordinates. -/
theorem minimal_licensed_profile_exact :
    minimal_licensed_profile =
      { terminalMultiplicity := 1, terminalDefect := 0,
        repairCover := 0, witnessRank := 0 } := by
  simp [minimal_licensed_profile,
    fork3_licensed_terminalMultiplicity_eq_one,
    minimalFork_licensed_terminalDefect_eq_zero,
    minimalLicensed_repairCoverNumber_eq_zero,
    minimalFork_licensed_witnessRank_eq_zero]

/-- KO7 raw profile, computed on the live local relation and live KO7
repair/witness definitions. -/
noncomputable def ko7_raw_profile : MinimalForkDefectProfile where
  terminalMultiplicity := terminalMultiplicity
    OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7LocalCone.LocalRaw .source
  terminalDefect := terminalMultiplicity
    OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7LocalCone.LocalRaw .source - 1
  repairCover := repairCoverNumber
    OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7RepairCover.bad
    OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7RepairCover.closes
    OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7RepairCover.coverable
  witnessRank := witnessRank
    OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7WitnessRank.ko7Adequacy

/-- KO7 licensed profile, computed on the live licensed local relation. -/
noncomputable def ko7_licensed_profile : MinimalForkDefectProfile where
  terminalMultiplicity := terminalMultiplicity
    OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7LocalCone.LocalLicensed .source
  terminalDefect := terminalMultiplicity
    OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7LocalCone.LocalLicensed .source - 1
  repairCover := repairCoverNumber ko7LicensedBadDefects
    OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7RepairCover.closes
    ko7LicensedRepair_coverable
  witnessRank := witnessRank ko7LicensedAdequacy

/-- Exact live KO7 raw coordinates, with multiplicity supplied by the relation
isomorphism transport theorem. -/
theorem ko7_raw_profile_exact :
    ko7_raw_profile =
      { terminalMultiplicity := 2, terminalDefect := 1,
        repairCover := 1, witnessRank := 1 } := by
  simp [ko7_raw_profile,
    ko7_raw_terminalMultiplicity_transport,
    OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7RepairCover.canonical_breaker_repairCoverNumber_eq_one,
    OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7WitnessRank.ko7_distinction_witnessRank_eq_one]

/-- Exact live KO7 licensed coordinates. -/
theorem ko7_licensed_profile_exact :
    ko7_licensed_profile =
      { terminalMultiplicity := 1, terminalDefect := 0,
        repairCover := 0, witnessRank := 0 } := by
  simp [ko7_licensed_profile,
    ko7_licensed_terminalMultiplicity_transport,
    ko7Licensed_repairCoverNumber_eq_zero,
    ko7Licensed_witnessRank_eq_zero]

/-- The KO7 raw/licensed local profiles are exactly the canonical minimal-fork
profiles, coordinate by coordinate. -/
theorem ko7_profile_eq_minimal_profile :
    ko7_raw_profile = minimal_raw_profile ∧
      ko7_licensed_profile = minimal_licensed_profile :=
  ⟨ko7_raw_profile_exact.trans minimal_raw_profile_exact.symm,
    ko7_licensed_profile_exact.trans minimal_licensed_profile_exact.symm⟩

/-- Complete small quantitative profile, with coordinate meanings kept separate. -/
theorem minimalFork_defect_cover_rank_profile :
    terminalDefect Fork3Step .source = 1 ∧
    terminalDefect Fork3LicensedStep .source = 0 ∧
    repairCoverNumber minimalBadDefects minimalRepairCoverage
      minimalRepair_coverable = 1 ∧
    witnessRank minimalRawAdequacy = 1 ∧
    witnessRank minimalLicensedAdequacy = 0 :=
  ⟨minimalFork_raw_terminalDefect_eq_one,
    minimalFork_licensed_terminalDefect_eq_zero,
    minimalFork_repairCoverNumber_eq_one,
    minimalFork_raw_witnessRank_eq_one,
    minimalFork_licensed_witnessRank_eq_zero⟩

end OperatorKO7.Meta.DistinctionBoundary.MinimalFork
