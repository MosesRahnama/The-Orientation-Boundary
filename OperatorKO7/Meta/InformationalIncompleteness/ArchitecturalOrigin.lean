import OperatorKO7.Meta.RepShift_BottleneckPredicate
import OperatorKO7.Meta.SchemaWitnessOrder

/-!
# Architectural-Origin Carrier (ENG-WCC sub-block 12, Brief A-073)

Carrier module for the architectural-origin / FFL-structurally-forced
anchor cited by the engine's witness-carrier certificate. NO new
mathematical content: this module is a thin definitional carrier that
names existing substrate so the engine can emit one stable theorem
reference per cert.

Substrate citations (already mechanized; no new proofs):
- `OperatorKO7.RepShift.PreUndecidabilityFracture` (the four-clause
  pre-undecidability fracture predicate);
- `OperatorKO7.StepDuplicating.StepDuplicatingSchema.SchemaWitnessTower.OB`
  (orientation-boundary predicate at the schema level);
- `OperatorKO7.StepDuplicating.StepDuplicatingSchema.SchemaWitnessTower.OB_iff_no_directWhole`
  (orientation boundary iff direct-whole witness language is empty).

The manuscript anchor is
`Rahnama_Informational_Incompleteness.tex` Theorem `thm:architectural-origin`
(architectural origin of false formal legitimacy on the step-duplicating
recursor).

Relation tag: NA (metadata / carrier module).
Property: definition.
Trust: kernel-only.
-/

namespace OperatorKO7.Meta.InformationalIncompleteness.ArchitecturalOrigin

/-- Architectural-origin anchor record. The fields are string-typed
qualified names of upstream declarations; the engine cites them by name
on every cert that triggers the FFL detector. -/
structure ArchitecturalOriginAnchor where
  /-- Module that owns the pre-undecidability fracture predicate. -/
  preUndecidabilityFractureModule : String
  /-- Module that owns the orientation-boundary predicate. -/
  schemaWitnessOrderModule : String
  /-- Name of the pre-undecidability fracture predicate. -/
  preUndecidabilityFracturePredicateName : String
  /-- Name of the orientation-boundary predicate. -/
  obPredicateName : String
  /-- Name of the orientation-boundary characterization theorem. -/
  obIffNoDirectWholeTheoremName : String
  /-- Manuscript anchor identifier. -/
  manuscriptAnchor : String

/-- Canonical anchor used by the engine on every T3 / T4 emission that
needs to cite the architectural-origin / FFL-structurally-forced
theorem. -/
def canonicalArchitecturalOriginAnchor : ArchitecturalOriginAnchor where
  preUndecidabilityFractureModule :=
    "OperatorKO7.Meta.RepShift_BottleneckPredicate"
  schemaWitnessOrderModule :=
    "OperatorKO7.Meta.SchemaWitnessOrder"
  preUndecidabilityFracturePredicateName :=
    "OperatorKO7.RepShift.PreUndecidabilityFracture"
  obPredicateName :=
    "OperatorKO7.StepDuplicating.StepDuplicatingSchema.SchemaWitnessTower.OB"
  obIffNoDirectWholeTheoremName :=
    "OperatorKO7.StepDuplicating.StepDuplicatingSchema.SchemaWitnessTower.OB_iff_no_directWhole"
  manuscriptAnchor :=
    "Rahnama_Informational_Incompleteness.thm:architectural-origin"

/-- The canonical architectural-origin anchor names a non-empty manuscript
reference. -/
theorem canonicalArchitecturalOriginAnchor_manuscriptAnchor_nonempty :
    canonicalArchitecturalOriginAnchor.manuscriptAnchor ≠ "" := by
  intro h
  have hlen :
      canonicalArchitecturalOriginAnchor.manuscriptAnchor.length = 0 := by
    rw [h]; rfl
  have :
      canonicalArchitecturalOriginAnchor.manuscriptAnchor.length =
      "Rahnama_Informational_Incompleteness.thm:architectural-origin".length := by rfl
  rw [this] at hlen
  exact absurd hlen (by decide)

/-! ## Real theorem (anchor upgraded from anchor-only to anchor + theorem) -/

open OperatorKO7.StepDuplicating.StepDuplicatingSchema
open OperatorKO7.StepDuplicating.StepDuplicatingSchema.SchemaWitnessTower

/--
Proves: the architectural origin of false formal legitimacy (`thm:architectural-origin`):
  at the orientation boundary there is no direct whole-term witness, so a forced
  definite verdict that claims direct-interface support is structurally unbacked
  (false formal legitimacy is forced, not statistical). This is the direct-interface
  face of the published orientation-boundary biconditional.
Does not prove: the full four-axis PRT failure classification; this is the
  witness-availability core (no direct-whole witness exists to back the verdict).
Relation: schema-level witness tower over a `StepDuplicatingSchema`.
Closure: not applicable (Prop-level).
Strategy: not applicable.
Trust: kernel-only (`OB_iff_no_directWhole` forward direction).
Scope: every tower `Tw : SchemaWitnessTower S` and instance `x : S.T` with `OB Tw x`.
-/
theorem false_formal_legitimacy_no_direct_witness
    {S : OperatorKO7.StepDuplicating.StepDuplicatingSchema}
    (Tw : SchemaWitnessTower S) (x : S.T) (hOB : OB Tw x) :
    ¬ HasWitness Tw x WLevel.directWhole :=
  (OB_iff_no_directWhole Tw x).mp hOB

end OperatorKO7.Meta.InformationalIncompleteness.ArchitecturalOrigin
