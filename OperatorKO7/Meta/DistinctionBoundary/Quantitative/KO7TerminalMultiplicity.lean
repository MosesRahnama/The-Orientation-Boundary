import OperatorKO7.Meta.DistinctionBoundary.Quantitative.TerminalMultiplicity
import OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7LocalCone

set_option autoImplicit false

namespace OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7TerminalMultiplicity

open KO7LocalCone

theorem raw_refl_normal : NormalForm LocalRaw .reflVerdict := by intro y h; cases h
theorem raw_diff_normal : NormalForm LocalRaw .diffVerdict := by intro y h; cases h
theorem licensed_refl_normal : NormalForm LocalLicensed .reflVerdict := by intro y h; cases h

theorem raw_normalizingAt_source : NormalizingAt LocalRaw .source := by
  intro x hx
  cases x with
  | source => exact ⟨.reflVerdict, reach_step LocalRaw.refl, raw_refl_normal⟩
  | reflVerdict => exact ⟨.reflVerdict, reach_refl _, raw_refl_normal⟩
  | diffVerdict => exact ⟨.diffVerdict, reach_refl _, raw_diff_normal⟩

theorem licensed_normalizingAt_source : NormalizingAt LocalLicensed .source := by
  intro x hx
  cases x with
  | source => exact ⟨.reflVerdict, reach_step LocalLicensed.refl, licensed_refl_normal⟩
  | reflVerdict => exact ⟨.reflVerdict, reach_refl _, licensed_refl_normal⟩
  | diffVerdict =>
      rcases hx with ⟨n, hn⟩
      cases hn with
      | succ h rest =>
          cases h
          have heq := eq_of_normalForm_reach licensed_refl_normal ⟨_, rest⟩
          contradiction

theorem raw_terminalSupport_eq :
    terminalSupport LocalRaw .source = {.reflVerdict, .diffVerdict} := by
  classical
  ext x
  cases x with
  | source =>
      constructor
      · intro hx
        exact False.elim ((mem_terminalSupport.mp hx).2 _ LocalRaw.refl)
      · simp
  | reflVerdict =>
      simp only [Finset.mem_insert, Finset.mem_singleton, true_or, iff_true]
      exact mem_terminalSupport.mpr ⟨reach_step LocalRaw.refl, raw_refl_normal⟩
  | diffVerdict =>
      simp only [Finset.mem_insert, Finset.mem_singleton, or_true, iff_true]
      exact mem_terminalSupport.mpr ⟨reach_step LocalRaw.diff, raw_diff_normal⟩

theorem licensed_terminalSupport_eq :
    terminalSupport LocalLicensed .source = {.reflVerdict} := by
  classical
  ext x
  cases x with
  | source =>
      constructor
      · intro hx
        exact False.elim ((mem_terminalSupport.mp hx).2 _ LocalLicensed.refl)
      · simp
  | reflVerdict =>
      simp only [Finset.mem_singleton, iff_true]
      exact mem_terminalSupport.mpr ⟨reach_step LocalLicensed.refl, licensed_refl_normal⟩
  | diffVerdict =>
      constructor
      · intro hx
        rcases (mem_terminalSupport.mp hx).1 with ⟨n, hn⟩
        cases hn with
        | succ hs rest =>
            cases hs
            have heq := eq_of_normalForm_reach licensed_refl_normal ⟨_, rest⟩
            contradiction
      · simp

theorem raw_terminalMultiplicity_eq_two : terminalMultiplicity LocalRaw .source = 2 := by
  simp [terminalMultiplicity, raw_terminalSupport_eq]

theorem licensed_terminalMultiplicity_eq_one : terminalMultiplicity LocalLicensed .source = 1 := by
  simp [terminalMultiplicity, licensed_terminalSupport_eq]

theorem raw_terminalHartleyEntropy_eq_one : terminalHartleyEntropy LocalRaw .source = 1 := by
  rw [terminalHartleyEntropy, raw_terminalMultiplicity_eq_two]
  have hlog : Real.log (2 : Real) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  simp [Real.logb, hlog]

theorem licensed_terminalHartleyEntropy_eq_zero : terminalHartleyEntropy LocalLicensed .source = 0 := by
  rw [terminalHartleyEntropy, licensed_terminalMultiplicity_eq_one]
  simp [Real.logb]

theorem ko7_structuralHartleyCollapse_eq_one :
    structuralHartleyCollapse LocalRaw LocalLicensed .source = 1 := by
  rw [structuralHartleyCollapse, raw_terminalMultiplicity_eq_two,
    licensed_terminalMultiplicity_eq_one]
  have hlog : Real.log (2 : Real) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  simp [Real.logb, hlog]

#print axioms raw_terminalMultiplicity_eq_two
#print axioms licensed_terminalMultiplicity_eq_one
#print axioms raw_terminalHartleyEntropy_eq_one
#print axioms ko7_structuralHartleyCollapse_eq_one

end OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7TerminalMultiplicity
