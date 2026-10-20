import OperatorKO7.Meta.LicensedBoundaryCalculus.Quantitative.GuardedRates

/-!
This module defines a terminal-support-collapse certificate conditional on normalization and a
multiplicity bound. Theorems project and apply those stored hypotheses.










-/

set_option autoImplicit false

namespace OperatorKO7.Meta.LicensedBoundaryCalculus

universe u

open OperatorKO7.Meta.DistinctionBoundary.Quantitative

noncomputable section

/-- Definition with formal content given by the displayed type and body.
-/
def terminalHartleyLogRatio?
    {A : ARS.{u}} [Fintype A.Carrier]
    (raw licensed : SemanticScope A) : Option Real :=
  structuralHartleyCollapse? raw licensed

/-- Data record whose requirements are the fields displayed below.
-/
structure TerminalSupportCollapse
    {A : ARS.{u}} [Fintype A.Carrier]
    (raw licensed : SemanticScope A) : Prop where
  rawNormalizing : NormalizingAt raw.relation raw.source
  licensedNormalizing : NormalizingAt licensed.relation licensed.source
  multiplicity_le :
    SemanticScope.terminalMultiplicity licensed ≤
      SemanticScope.terminalMultiplicity raw

namespace TerminalSupportCollapse

/-- Definition with formal content given by the displayed type and body. -/
def value
    {A : ARS.{u}} [Fintype A.Carrier]
    {raw licensed : SemanticScope A}
    (_certificate : TerminalSupportCollapse raw licensed) : Real :=
  Real.logb 2
    ((SemanticScope.terminalMultiplicity raw : Real) /
      (SemanticScope.terminalMultiplicity licensed : Real))

/-- The displayed proposition follows from the stated hypotheses. -/
theorem logRatio_eq_some
    {A : ARS.{u}} [Fintype A.Carrier]
    {raw licensed : SemanticScope A}
    (certificate : TerminalSupportCollapse raw licensed) :
    terminalHartleyLogRatio? raw licensed = some certificate.value := by
  have hraw : 0 < SemanticScope.terminalMultiplicity raw :=
    terminalMultiplicity_pos_of_normalizingAt certificate.rawNormalizing
  have hlicensed : 0 < SemanticScope.terminalMultiplicity licensed :=
    terminalMultiplicity_pos_of_normalizingAt certificate.licensedNormalizing
  exact structuralHartleyCollapse?_eq_some_of_pos raw licensed hraw hlicensed

/-- The displayed proposition follows from the stated hypotheses.
-/
theorem value_nonneg
    {A : ARS.{u}} [Fintype A.Carrier]
    {raw licensed : SemanticScope A}
    (certificate : TerminalSupportCollapse raw licensed) :
    0 ≤ certificate.value := by
  unfold value
  apply Real.logb_nonneg (by norm_num : (1 : Real) < 2)
  have hpositive : 0 < SemanticScope.terminalMultiplicity licensed :=
    terminalMultiplicity_pos_of_normalizingAt certificate.licensedNormalizing
  have hdenominator :
      0 < (SemanticScope.terminalMultiplicity licensed : Real) := by
    exact_mod_cast hpositive
  have hle :
      (SemanticScope.terminalMultiplicity licensed : Real) ≤
        (SemanticScope.terminalMultiplicity raw : Real) := by
    exact_mod_cast certificate.multiplicity_le
  rw [le_div_iff₀ hdenominator]
  simpa using hle

end TerminalSupportCollapse

#check @TerminalSupportCollapse.logRatio_eq_some
#check @TerminalSupportCollapse.value_nonneg
#print axioms TerminalSupportCollapse.logRatio_eq_some
#print axioms TerminalSupportCollapse.value_nonneg

end
end OperatorKO7.Meta.LicensedBoundaryCalculus
