import OperatorKO7.Meta.DistinctionBoundary.MinimalFork.Quantitative
import OperatorKO7.Meta.DistinctionBoundary.MinimalForkQuantitativeKO7Transport
import OperatorKO7.Meta.DistinctionBoundary.MinimalForkHartleyExact

/-!
# Structural information-collapse surface

All results here concern terminal-support multiplicity/Hartley information. No
thermodynamic Landauer cost is inferred without a separately licensed physical
implementation.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.DistinctionBoundary.MinimalFork

open OperatorKO7.Meta.DistinctionBoundary.Quantitative

/-- The licensed repair removes exactly one terminal alternative. -/
theorem minimalFork_support_two_to_one :
    terminalMultiplicity Fork3Step .source = 2 ∧
      terminalMultiplicity Fork3LicensedStep .source = 1 :=
  ⟨fork3_raw_terminalMultiplicity_eq_two,
    fork3_licensed_terminalMultiplicity_eq_one⟩

/-- The corresponding structural Hartley collapse is exactly one bit. -/
theorem minimalFork_one_bit_structural_collapse :
    structuralHartleyCollapse Fork3Step Fork3LicensedStep .source = 1 :=
  fork3_structuralHartleyCollapse_eq_one

/-- Roadmap-stable one-bit structural-collapse name. -/
theorem fork3_structuralCollapse_eq_one :
    structuralHartleyCollapse Fork3Step Fork3LicensedStep .source = 1 :=
  fork3_structuralHartleyCollapse_eq_one

/-- The raw KO7 terminal-support finset is exactly the image of canonical
`Fork3` support under the proved carrier/relation equivalence. -/
theorem ko7_terminalSupport_transport :
    (terminalSupport Fork3Step Fork3.source).map
        OperatorKO7.Meta.DistinctionBoundary.MinimalFork.KO7LocalConeBridge.fork3EquivKO7Node.toEmbedding =
      terminalSupport
        OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7LocalCone.LocalRaw
        OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7LocalCone.EqWBreakerNode.source := by
  classical
  ext y
  constructor
  · intro hy
    rcases Finset.mem_map.mp hy with ⟨x, hx, hxy⟩
    subst y
    exact
      (OperatorKO7.Meta.DistinctionBoundary.MinimalFork.KO7LocalConeBridge.fork3LocalRawIso.mem_terminalSupport_iff
        (source := Fork3.source) (x := x)).mp hx
  · intro hy
    let x :=
      OperatorKO7.Meta.DistinctionBoundary.MinimalFork.KO7LocalConeBridge.fork3EquivKO7Node.symm y
    have hxy :
        OperatorKO7.Meta.DistinctionBoundary.MinimalFork.KO7LocalConeBridge.fork3LocalRawIso.toEquiv x = y := by
      change
        OperatorKO7.Meta.DistinctionBoundary.MinimalFork.KO7LocalConeBridge.fork3EquivKO7Node x = y
      simp [x]
    have hsource :
        OperatorKO7.Meta.DistinctionBoundary.MinimalFork.KO7LocalConeBridge.fork3LocalRawIso.toEquiv Fork3.source =
          OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7LocalCone.EqWBreakerNode.source := rfl
    have hy' :
        OperatorKO7.Meta.DistinctionBoundary.MinimalFork.KO7LocalConeBridge.fork3LocalRawIso.toEquiv x ∈
          terminalSupport
            OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7LocalCone.LocalRaw
            (OperatorKO7.Meta.DistinctionBoundary.MinimalFork.KO7LocalConeBridge.fork3LocalRawIso.toEquiv Fork3.source) := by
      rw [hxy, hsource]
      exact hy
    have hx : x ∈ terminalSupport Fork3Step Fork3.source :=
      (OperatorKO7.Meta.DistinctionBoundary.MinimalFork.KO7LocalConeBridge.fork3LocalRawIso.mem_terminalSupport_iff
        (source := Fork3.source) (x := x)).mpr hy'
    exact Finset.mem_map.mpr ⟨x, hx, by simp [x]⟩

/-- Same 2→1 local support profile transported to the existing KO7 local cone. -/
theorem ko7_local_support_two_to_one_by_isomorphism :
    terminalMultiplicity
        OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7LocalCone.LocalRaw
        OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7LocalCone.EqWBreakerNode.source = 2 ∧
      terminalMultiplicity
        OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7LocalCone.LocalLicensed
        OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7LocalCone.EqWBreakerNode.source = 1 :=
  ko7_terminalMultiplicity_two_to_one_by_transport

/-- KO7 and canonical structural collapses agree by transported terminal
multiplicities, not by an unrelated numeral computation. -/
theorem ko7_structuralCollapse_eq_fork3 :
    structuralHartleyCollapse
        OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7LocalCone.LocalRaw
        OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7LocalCone.LocalLicensed
        OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7LocalCone.EqWBreakerNode.source =
      structuralHartleyCollapse Fork3Step Fork3LicensedStep Fork3.source := by
  simp only [structuralHartleyCollapse,
    ko7_raw_terminalMultiplicity_transport,
    ko7_licensed_terminalMultiplicity_transport,
    fork3_raw_terminalMultiplicity_eq_two,
    fork3_licensed_terminalMultiplicity_eq_one]

/-- Explicit scope-wall theorem alias: this is a dimensionless structural bit. -/
theorem minimalFork_structural_not_physical_energy_claim :
    structuralHartleyCollapse Fork3Step Fork3LicensedStep .source = 1 :=
  structural_one_bit_scope

end OperatorKO7.Meta.DistinctionBoundary.MinimalFork
