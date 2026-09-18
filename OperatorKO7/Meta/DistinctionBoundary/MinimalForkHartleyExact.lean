import OperatorKO7.Meta.DistinctionBoundary.MinimalForkQuantitativeKO7Transport

/-!
# Exact one-bit terminal ambiguity collapse

This file contains only structural Hartley information. It makes no physical
Landauer claim: a physical energy interpretation requires a separately licensed
irreversible implementation.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.DistinctionBoundary.MinimalFork

open OperatorKO7.Meta.DistinctionBoundary.Quantitative

/-- Canonical raw support requires one binary terminal-choice bit. -/
theorem fork3_raw_terminalCeilLog2_eq_one :
    terminalCeilLog2 Fork3Step .source = 1 := by
  rw [terminalCeilLog2, fork3_raw_terminalMultiplicity_eq_two]
  exact Nat.clog_eq_one (by decide) (by decide)

/-- Canonical licensed support requires zero terminal-choice bits. -/
theorem fork3_licensed_terminalCeilLog2_eq_zero :
    terminalCeilLog2 Fork3LicensedStep .source = 0 := by
  rw [terminalCeilLog2, fork3_licensed_terminalMultiplicity_eq_one]
  simp [Nat.clog_one_right]

/-- Exact structural one-bit reduction in ceiling-log code length. -/
theorem fork3_terminalCeilLog2_drop_eq_one :
    terminalCeilLog2 Fork3Step .source -
      terminalCeilLog2 Fork3LicensedStep .source = 1 := by
  rw [fork3_raw_terminalCeilLog2_eq_one,
    fork3_licensed_terminalCeilLog2_eq_zero]

/-- Transported KO7 raw ceiling-log profile. -/
theorem ko7_raw_terminalCeilLog2_transport :
    terminalCeilLog2 OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7LocalCone.LocalRaw .source = 1 := by
  rw [terminalCeilLog2, ko7_raw_terminalMultiplicity_transport]
  exact Nat.clog_eq_one (by decide) (by decide)

/-- Transported KO7 licensed ceiling-log profile. -/
theorem ko7_licensed_terminalCeilLog2_transport :
    terminalCeilLog2 OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7LocalCone.LocalLicensed .source = 0 := by
  rw [terminalCeilLog2, ko7_licensed_terminalMultiplicity_transport]
  simp [Nat.clog_one_right]

/-- The canonical structural Hartley collapse is exactly one bit. -/
theorem minimalFork_exact_structural_one_bit :
    terminalHartleyEntropy Fork3Step .source -
      terminalHartleyEntropy Fork3LicensedStep .source = 1 ∧
    terminalCeilLog2 Fork3Step .source -
      terminalCeilLog2 Fork3LicensedStep .source = 1 := by
  constructor
  · rw [fork3_raw_terminalHartleyEntropy_eq_one,
      fork3_licensed_terminalHartleyEntropy_eq_zero]
    norm_num
  · exact fork3_terminalCeilLog2_drop_eq_one

/-- The KO7 local cone inherits the same exact one-bit ceiling-log drop by transport. -/
theorem ko7_local_exact_structural_one_bit :
    terminalCeilLog2 OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7LocalCone.LocalRaw .source -
      terminalCeilLog2 OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7LocalCone.LocalLicensed .source = 1 := by
  rw [ko7_raw_terminalCeilLog2_transport,
    ko7_licensed_terminalCeilLog2_transport]

/-- Explicit scope wall: the theorem is about a dimensionless structural bit
count. This proposition intentionally contains no temperature, Boltzmann
constant, heat, work, or physical substrate. -/
theorem structural_one_bit_scope :
    structuralHartleyCollapse Fork3Step Fork3LicensedStep .source = 1 :=
  fork3_structuralHartleyCollapse_eq_one

end OperatorKO7.Meta.DistinctionBoundary.MinimalFork

