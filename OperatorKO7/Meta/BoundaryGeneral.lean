import OperatorKO7.Meta.BoundaryGeneral.ProvenanceLicense
import OperatorKO7.Meta.BoundaryGeneral.WholeTermIndistinguishability
import OperatorKO7.Meta.BoundaryGeneral.CostedConfession
import OperatorKO7.Meta.BoundaryGeneral.UniversalityGate
import OperatorKO7.Meta.BoundaryGeneral.PayloadStress
import OperatorKO7.Meta.BoundaryGeneral.C4Classifier
import OperatorKO7.Meta.BoundaryGeneral.WitnessFirst
import OperatorKO7.Meta.BoundaryGeneral.EndogenousProvenance
import OperatorKO7.Meta.BoundaryGeneral.DiagonalMirror
import OperatorKO7.Meta.BoundaryGeneral.DistinctionRecord
import OperatorKO7.Meta.BoundaryGeneral.DirectMeasureGrammarClosure
import OperatorKO7.Meta.BoundaryGeneral.Wavepacket

/-!
# Boundary-general cross-paper formalization (mechanized theories)

Aggregator for the Lean modules of the boundary-general cross-paper packet
(`2026-05-31_boundary_general_cross_paper_formalization.tex`). Twelve of the packet's theories are
mechanized here (Theory I's carrier-burden half is `PayloadStress`, its entropy half is already in
the Informational Incompleteness stack; Theory XIII is empirical telemetry by design, not a Lean
theorem). Each module is fully proved (no `sorry`/`axiom`/`native_decide`) with audited axiom
closure inside `{propext, Classical.choice, Quot.sound}`; most are fully constructive (no axioms),
and each carries a concrete non-vacuity witness.

| Theory | Module | Headline |
|---|---|---|
| II | `ProvenanceLicense` | provenance capture does not license the verdict |
| III | `WholeTermIndistinguishability` | mass observer cannot separate recursor from circular carrier; step projection can |
| IV | `CostedConfession` | composition burden `≤` sum, equality iff disjoint; canonical lower bound |
| V | `UniversalityGate` | universal claim licensed iff every declared row complete; one missing row breaks it |
| VI | `PayloadStress` | carrier burden linear in payload, quadratic in depth, diverges at fixed entropy |
| VII | `C4Classifier` | total layer classifier; recursor is interface-inexpressibility, not undecidability |
| VIII | `WitnessFirst` | witness-first acceptance gate; provenance-without-license and carrier-blind projection rejected |
| IX | `EndogenousProvenance` | non-vacuous query with endogenous answer has zero exogenous information gain |
| X | `DiagonalMirror` | mirror test as `eqW a a` recognition; misrecognition pays burden for zero distinction |
| XI | `DistinctionRecord` | distinction is the record-generating primitive; equality is record-inert |
| XII | `DirectMeasureGrammarClosure` | exact scalar characterization: orientation iff payload-blind plus counter-strict; pure payload-blindness iff on the counter-admissible class; effective-payload syntax and exact Boolean checker discharge the pump hypothesis |
| XIV | `Wavepacket` | amplitude bridge `|ψ|²=g`; the Born density (mixture) does not determine the phase/amplitude |
-/
