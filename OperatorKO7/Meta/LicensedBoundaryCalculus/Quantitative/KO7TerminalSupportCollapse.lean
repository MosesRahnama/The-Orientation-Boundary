import OperatorKO7.Meta.LicensedBoundaryCalculus.Quantitative.TerminalSupportCollapse
import OperatorKO7.Meta.LicensedBoundaryCalculus.Quantitative.KO7SemanticAdequacy

/-!
This module specializes terminal-support collapse to a finite cone fixture. The theorem follows
from the displayed fixture definitions and imported generic result.









-/

set_option autoImplicit false

namespace OperatorKO7.Meta.LicensedBoundaryCalculus
namespace KO7DistinctionAdapter

noncomputable section

/-- Definition with formal content given by the displayed type and body.
-/
def ko7TerminalSupportCollapse :
    TerminalSupportCollapse rawData.scope licensedData.scope where
  rawNormalizing := rawScope_normalizing
  licensedNormalizing := licensedScope_normalizing
  multiplicity_le := by
    change (semanticProfile licensedData).terminalMultiplicity ≤
      (semanticProfile rawData).terminalMultiplicity
    rw [raw_terminalMultiplicity_exact, licensed_terminalMultiplicity_exact]
    norm_num

/-- The displayed proposition follows from the stated hypotheses. -/
theorem ko7_terminalHartleyLogRatio_defined_fixture :
    terminalHartleyLogRatio? rawData.scope licensedData.scope =
      some ko7TerminalSupportCollapse.value :=
  TerminalSupportCollapse.logRatio_eq_some ko7TerminalSupportCollapse

/-- The displayed proposition follows from the stated hypotheses. -/
theorem ko7_terminalSupportCollapse_nonneg_fixture :
    0 ≤ ko7TerminalSupportCollapse.value :=
  TerminalSupportCollapse.value_nonneg ko7TerminalSupportCollapse

#check ko7TerminalSupportCollapse
#check ko7_terminalHartleyLogRatio_defined_fixture
#check ko7_terminalSupportCollapse_nonneg_fixture
#print axioms ko7_terminalHartleyLogRatio_defined_fixture
#print axioms ko7_terminalSupportCollapse_nonneg_fixture

end
end KO7DistinctionAdapter
end OperatorKO7.Meta.LicensedBoundaryCalculus
