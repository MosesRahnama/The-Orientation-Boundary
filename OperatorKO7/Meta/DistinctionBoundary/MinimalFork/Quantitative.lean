import OperatorKO7.Meta.DistinctionBoundary.MinimalForkQuantitative

/-! Roadmap-stable quantitative front for the canonical minimal fork. -/

set_option autoImplicit false

namespace OperatorKO7.Meta.DistinctionBoundary.MinimalFork

open OperatorKO7.Meta.DistinctionBoundary.Quantitative

/-- Stable name for the canonical licensed repair relation. -/
abbrev minimalForkLicensedStep := Fork3LicensedStep

/-- Stable raw multiplicity theorem. -/
theorem minimalFork_raw_terminalMultiplicity_eq_two :
    terminalMultiplicity Fork3Step .source = 2 :=
  fork3_raw_terminalMultiplicity_eq_two

/-- Stable licensed multiplicity theorem. -/
theorem minimalFork_licensed_terminalMultiplicity_eq_one :
    terminalMultiplicity Fork3LicensedStep .source = 1 :=
  fork3_licensed_terminalMultiplicity_eq_one

/-- Stable raw Hartley theorem. -/
theorem minimalFork_raw_hartley_eq_one :
    terminalHartleyEntropy Fork3Step .source = 1 :=
  fork3_raw_terminalHartleyEntropy_eq_one

/-- Stable licensed Hartley theorem. -/
theorem minimalFork_licensed_hartley_eq_zero :
    terminalHartleyEntropy Fork3LicensedStep .source = 0 :=
  fork3_licensed_terminalHartleyEntropy_eq_zero

/-- Roadmap-stable raw Hartley name. -/
theorem fork3_raw_hartley_eq_one :
    terminalHartleyEntropy Fork3Step .source = 1 :=
  fork3_raw_terminalHartleyEntropy_eq_one

/-- Roadmap-stable licensed Hartley name. -/
theorem fork3_licensed_hartley_eq_zero :
    terminalHartleyEntropy Fork3LicensedStep .source = 0 :=
  fork3_licensed_terminalHartleyEntropy_eq_zero

end OperatorKO7.Meta.DistinctionBoundary.MinimalFork
