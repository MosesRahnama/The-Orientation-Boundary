import OperatorKO7.Meta.CompositionalMeasure_Impossibility
import OperatorKO7.Meta.InformationalIncompleteness.UnivDeficitViaChar
import OperatorKO7.Meta.InformationalIncompleteness.CertFragmentWitness
import OperatorKO7.Meta.OperationalInexpressibility.KO7StepArgumentInstance
import OperatorKO7.Meta.WitnessOrder

/-!
# Concrete KO7 semantic-to-witness-order bridge

This repair fixes the bridge to the actual KO7 schema and to one named source
input.  Its transformed-call branch is inhabited only at that input and stores
the existing dependency-pair well-foundedness witness through a typed adapter
from `WitnessOrder.ko7_has_transformedCall_witness`.  No branch is a constant
tautology, and no transformed-call theorem is discharged by an arbitrary
inhabitant.

The direct side is the reflected direct-grammar obstruction for the exact
counter-drop, payload-duplicating carrier step.  Consequently both branches now
name the concrete KO7 source: direct support would require a payload-sensitive
orienter for that duplicating relation, while transformed-call support carries
the actual dependency-pair certificate.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.InformationalIncompleteness.SemanticWitnessBridge

open OperatorKO7
open OperatorKO7.Trace
open OperatorKO7.CompositionalImpossibility
open OperatorKO7.StepDuplicating.StepDuplicatingSchema
open OperatorKO7.StepDuplicating.StepDuplicatingSchema.SchemaWitnessTower
open OperatorKO7.Meta.BoundaryGeneral.DirectMeasureGrammarClosure
open OperatorKO7.Meta.OperationalInexpressibility.DirectGrammarBoundary
open OperatorKO7.Meta.OperationalInexpressibility.KO7StepArgumentInstance
open OperatorKO7.Meta.InformationalIncompleteness.WitnessChannelBoundary

/-- The concrete KO7 source input used by this bridge: the successor case of
the duplicating recursor at the smallest counter. -/
def semanticBridgeInput : ko7Schema.T :=
  recΔ void void (delta void)

/-- The actual transformed-call proposition supplied by the KO7
dependency-pair relation.  This is the coarse `WitnessOrder` level, not the
schema-local level tag. -/
def KO7TransformedCallWitness : Prop :=
  OperatorKO7.WitnessOrder.HasWitness
    OperatorKO7.WitnessOrder.ko7Tower
    OperatorKO7.WitnessOrder.WLevel.transformedCall

/-- Typed adapter from the existing dependency-pair well-foundedness witness.
Its result is definitionally
`WellFounded OperatorKO7.MetaDependencyPairs.DPPairRev`. -/
theorem witnessOrder_transformedCall_adapter : KO7TransformedCallWitness :=
  OperatorKO7.WitnessOrder.ko7_has_transformedCall_witness

/-- Concrete KO7 witness tower. Direct-whole availability requires the exact
named input and a reflected grammar expression that both reads `pi_y` and
orients the fixed duplicating carrier step. Transformed-call availability
requires the same input and the actual dependency-pair witness. -/
def semanticBridgeTower : SchemaWitnessTower ko7Schema :=
  fun x level =>
    match level with
    | WLevel.directWhole =>
        x = semanticBridgeInput ∧
          exists e : MeasureExpr,
            ko7StepArgumentQuestion.derivable e ∧
              UsesPayload e ∧ AdequateForDupOrientation e
    | WLevel.transformedCall =>
        x = semanticBridgeInput ∧ KO7TransformedCallWitness
    | _ => False

/-- The semantic impossibility excludes a direct-whole witness at every KO7
input in the concrete tower. -/
theorem semanticBridge_no_directWhole_at (x : ko7Schema.T) :
    Not (HasWitness semanticBridgeTower x WLevel.directWhole) := by
  intro h
  obtain ⟨_hx, e, _hderivable, huses, horients⟩ := h
  exact no_directGrammar_measure_usesPayload_and_orients e
    ⟨huses, horients⟩

/-- Public fixed-input direct-side theorem. -/
theorem semanticBridge_no_directWhole :
    Not (HasWitness semanticBridgeTower semanticBridgeInput
      WLevel.directWhole) :=
  semanticBridge_no_directWhole_at semanticBridgeInput

/-- The orientation boundary at the named KO7 source is derived from the
semantic obstruction. -/
theorem semanticBridge_OB :
    OB semanticBridgeTower semanticBridgeInput :=
  (OB_iff_no_directWhole semanticBridgeTower semanticBridgeInput).2
    semanticBridge_no_directWhole

/-- The named KO7 source carries the transformed-call certificate through the
typed dependency-pair adapter. -/
theorem semanticBridge_transformedCall :
    HasWitness semanticBridgeTower semanticBridgeInput
      WLevel.transformedCall := by
  exact ⟨rfl, witnessOrder_transformedCall_adapter⟩

/-- At the concrete KO7 source, the direct witness-channel deficit is positive
and the minimal witness order exceeds the direct order. -/
theorem semanticBridge_deficit_positive :
    witnessChannelDeficitPos semanticBridgeTower semanticBridgeInput ∧
      minimalWitnessOrderGtDirect semanticBridgeTower semanticBridgeInput :=
  UnivDeficitViaChar.univ_deficit_via_char_direct
    semanticBridgeTower semanticBridgeInput semanticBridge_OB

/-- Concrete two-sided complement: direct-whole absence is derived from the
semantic theorem, while transformed-call presence is carried by the actual DP
well-foundedness proof. -/
theorem semanticBridge_cert_complement :
    witnessChannelDeficitPos semanticBridgeTower semanticBridgeInput ∧
      HasWitness semanticBridgeTower semanticBridgeInput
        WLevel.transformedCall :=
  CertFragmentWitness.cert_fragment_complement
    semanticBridgeTower semanticBridgeInput
      semanticBridge_no_directWhole semanticBridge_transformedCall

/-- The transformed-call branch is input-sensitive: inhabitation identifies
the input with the named KO7 source and carries the DP witness. -/
theorem semanticBridge_transformedCall_iff (x : ko7Schema.T) :
    HasWitness semanticBridgeTower x WLevel.transformedCall <->
      x = semanticBridgeInput ∧ KO7TransformedCallWitness :=
  Iff.rfl

/-- Audit anchor for the repaired concrete bridge. -/
def semantic_witness_bridge_anchor : String :=
  "OperatorKO7.Meta.InformationalIncompleteness.SemanticWitnessBridge.semanticBridge_deficit_positive"

end OperatorKO7.Meta.InformationalIncompleteness.SemanticWitnessBridge
