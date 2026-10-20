import OperatorKO7.Meta.DistinctionBoundary.MinimalFork.Core
import OperatorKO7.Meta.DistinctionBoundary.Quantitative.TerminalMultiplicity

/-!
# Quantitative profile of the canonical minimal fork

Raw relation: two terminal exits.
Licensed relation: equal exit only.
The exact terminal support collapses from two elements to one, hence the
scheduler-free Hartley ambiguity falls from one bit to zero and the structural
collapse equals exactly one bit.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.DistinctionBoundary.MinimalFork

open OperatorKO7.Meta.DistinctionBoundary.Quantitative

/-- Canonical licensed repair relation: delete only the diagonal difference edge. -/
inductive Fork3LicensedStep : Fork3 → Fork3 → Prop where
  | toEqual : Fork3LicensedStep .source .equal

/-- The licensed relation is a subrelation of the raw fork. -/
theorem fork3Licensed_sub_raw :
    IsLicensedSubrelation Fork3LicensedStep Fork3Step := by
  intro x y h
  cases h
  exact Fork3Step.toEqual

/-- Licensed equal verdict is normal. -/
theorem fork3Licensed_equal_normal : NormalForm Fork3LicensedStep .equal := by
  intro y h
  cases h

/-- Raw normalization from every state below the source. -/
theorem fork3_raw_normalizingAt_source : NormalizingAt Fork3Step .source := by
  intro x _
  cases x with
  | source => exact ⟨.equal, reach_step Fork3Step.toEqual, fork3_equal_normal⟩
  | equal => exact ⟨.equal, reach_refl _, fork3_equal_normal⟩
  | different => exact ⟨.different, reach_refl _, fork3_different_normal⟩

/-- Licensed normalization from every reachable state below source. -/
theorem fork3_licensed_normalizingAt_source :
    NormalizingAt Fork3LicensedStep .source := by
  intro x hx
  cases x with
  | source =>
      exact ⟨.equal, reach_step Fork3LicensedStep.toEqual,
        fork3Licensed_equal_normal⟩
  | equal =>
      exact ⟨.equal, reach_refl _, fork3Licensed_equal_normal⟩
  | different =>
      rcases hx with ⟨n, hn⟩
      cases hn with
      | succ h rest =>
          cases h
          have heq := eq_of_normalForm_reach fork3Licensed_equal_normal ⟨_, rest⟩
          contradiction

/-- Exact raw terminal support. -/
theorem fork3_raw_terminalSupport_eq :
    terminalSupport Fork3Step .source = {.equal, .different} := by
  classical
  ext x
  cases x with
  | source =>
      constructor
      · intro hx
        exact False.elim ((mem_terminalSupport.mp hx).2 _ Fork3Step.toEqual)
      · simp
  | equal =>
      constructor
      · intro _; simp
      · intro _
        exact mem_terminalSupport.mpr
          ⟨reach_step Fork3Step.toEqual, fork3_equal_normal⟩
  | different =>
      constructor
      · intro _; simp
      · intro _
        exact mem_terminalSupport.mpr
          ⟨reach_step Fork3Step.toDifferent, fork3_different_normal⟩

/-- Exact licensed terminal support. -/
theorem fork3_licensed_terminalSupport_eq :
    terminalSupport Fork3LicensedStep .source = {.equal} := by
  classical
  ext x
  cases x with
  | source =>
      constructor
      · intro hx
        exact False.elim ((mem_terminalSupport.mp hx).2 _ Fork3LicensedStep.toEqual)
      · simp
  | equal =>
      constructor
      · intro _; simp
      · intro _
        exact mem_terminalSupport.mpr
          ⟨reach_step Fork3LicensedStep.toEqual, fork3Licensed_equal_normal⟩
  | different =>
      constructor
      · intro hx
        rcases (mem_terminalSupport.mp hx).1 with ⟨n, hn⟩
        cases hn with
        | succ h rest =>
            cases h
            have heq := eq_of_normalForm_reach fork3Licensed_equal_normal ⟨_, rest⟩
            contradiction
      · simp

/-- Raw terminal multiplicity is exactly two. -/
theorem fork3_raw_terminalMultiplicity_eq_two :
    terminalMultiplicity Fork3Step .source = 2 := by
  simp [terminalMultiplicity, fork3_raw_terminalSupport_eq]

/-- Licensed terminal multiplicity is exactly one. -/
theorem fork3_licensed_terminalMultiplicity_eq_one :
    terminalMultiplicity Fork3LicensedStep .source = 1 := by
  simp [terminalMultiplicity, fork3_licensed_terminalSupport_eq]

/-- Raw Hartley terminal ambiguity is exactly one bit. -/
theorem fork3_raw_terminalHartleyEntropy_eq_one :
    terminalHartleyEntropy Fork3Step .source = 1 := by
  rw [terminalHartleyEntropy, fork3_raw_terminalMultiplicity_eq_two]
  exact Real.logb_self_eq_one (by norm_num)

/-- Licensed Hartley terminal ambiguity is zero. -/
theorem fork3_licensed_terminalHartleyEntropy_eq_zero :
    terminalHartleyEntropy Fork3LicensedStep .source = 0 := by
  rw [terminalHartleyEntropy, fork3_licensed_terminalMultiplicity_eq_one]
  simp [Real.logb]

/-- The raw-to-licensed terminal support collapse is exactly one Hartley bit. -/
theorem fork3_structuralHartleyCollapse_eq_one :
    structuralHartleyCollapse Fork3Step Fork3LicensedStep .source = 1 := by
  rw [structuralHartleyCollapse,
    fork3_raw_terminalMultiplicity_eq_two,
    fork3_licensed_terminalMultiplicity_eq_one]
  norm_num only [Nat.cast_ofNat, div_one]
  exact Real.logb_self_eq_one (by norm_num)

/-- Licensed canonical fork is source-confluent. -/
theorem fork3_licensed_confluentAt_source :
    ConfluentAt Fork3LicensedStep .source :=
  confluentAt_of_terminalMultiplicity_eq_one
    fork3_licensed_normalizingAt_source
    fork3_licensed_terminalMultiplicity_eq_one

/-- Crown quantitative bundle. -/
theorem minimalFork_quantitative_crown :
    terminalMultiplicity Fork3Step .source = 2 ∧
    terminalMultiplicity Fork3LicensedStep .source = 1 ∧
    terminalHartleyEntropy Fork3Step .source = 1 ∧
    terminalHartleyEntropy Fork3LicensedStep .source = 0 ∧
    structuralHartleyCollapse Fork3Step Fork3LicensedStep .source = 1 :=
  ⟨fork3_raw_terminalMultiplicity_eq_two,
    fork3_licensed_terminalMultiplicity_eq_one,
    fork3_raw_terminalHartleyEntropy_eq_one,
    fork3_licensed_terminalHartleyEntropy_eq_zero,
    fork3_structuralHartleyCollapse_eq_one⟩

end OperatorKO7.Meta.DistinctionBoundary.MinimalFork
