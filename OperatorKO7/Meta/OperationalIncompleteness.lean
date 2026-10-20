import OperatorKO7.Meta.WitnessOrder
import OperatorKO7.Meta.CompositionalMeasure_Impossibility
import OperatorKO7.Meta.ConfessionMethod
import OperatorKO7.Meta.SchemaForgettingWitness

/-!
# Operational incompleteness for the duplicated payload coordinate

## Formal Scope

The package combines imported witness-threshold bounds with existence of one certified-forgetting witness. It does not prove that every admissible witness requires forgetting.
-/

namespace OperatorKO7.MetaOperationalIncompleteness

open OperatorKO7
open OperatorKO7.Trace
open OperatorKO7.WitnessOrder
open OperatorKO7.ConfessionMethodFamily

/-- A rank together with duplicating-step orientation and explicit witnesses of
two wrapper-sensitivity failures. The structure records their conjunction; it
does not assert a causal relation among the fields. -/
structure CertifiedForgettingWitness where
  rank : Trace → Nat
  orientsDupStep :
    ∀ b s n, rank (app s (recΔ b s n)) < rank (recΔ b s (delta n))
  violatesPayloadLeft :
    ∃ x y : Trace, ¬ (rank (app x y) > rank x)
  violatesPayloadRight :
    ∃ x y : Trace, ¬ (rank (app x y) > rank y)

/-- Package the dependency-pair projection with its proved orientation and
sensitivity-violation fields. -/
def dpCertifiedForgettingWitness : CertifiedForgettingWitness where
  rank := OperatorKO7.CompositionalImpossibility.dpProjection
  orientsDupStep := OperatorKO7.CompositionalImpossibility.dp_projection_orients_rec_succ
  violatesPayloadLeft := OperatorKO7.CompositionalImpossibility.dp_projection_violates_sensitivity
  violatesPayloadRight := OperatorKO7.CompositionalImpossibility.dp_projection_violates_subterm2

/-- Explicit equivalence between the schema carrier of `ko7Schema` and the
    concrete kernel syntax `Trace`. Making this map explicit avoids relying on
    reducibility heuristics in downstream packaging lemmas. -/
def ko7CarrierEquivTrace : OperatorKO7.CompositionalImpossibility.ko7Schema.T ≃ Trace := by
  dsimp [OperatorKO7.CompositionalImpossibility.ko7Schema]
  exact Equiv.refl _

/-- Any KO7 confession method yields a certified-forgetting witness: the
underlying projection rank already orients the duplicating step and violates
wrapper sensitivity on both payload coordinates. -/
def CertifiedForgettingWitness.ofConfessionMethod
    (C : ConfessionMethod OperatorKO7.CompositionalImpossibility.ko7Schema) :
    CertifiedForgettingWitness where
  rank := fun t => C.rank (ko7CarrierEquivTrace.symm t)
  orientsDupStep := by
    intro b s n
    simpa [ko7CarrierEquivTrace, OperatorKO7.CompositionalImpossibility.ko7Schema] using
      confession_orients C
        (ko7CarrierEquivTrace.symm b)
        (ko7CarrierEquivTrace.symm s)
        (ko7CarrierEquivTrace.symm n)
  violatesPayloadLeft := by
    rcases confession_violates_wrap1 C with ⟨x, y, hxy⟩
    refine ⟨ko7CarrierEquivTrace x, ko7CarrierEquivTrace y, ?_⟩
    simpa [ko7CarrierEquivTrace, OperatorKO7.CompositionalImpossibility.ko7Schema] using hxy
  violatesPayloadRight := by
    rcases confession_violates_wrap2 C with ⟨x, y, hxy⟩
    refine ⟨ko7CarrierEquivTrace x, ko7CarrierEquivTrace y, ?_⟩
    simpa [ko7CarrierEquivTrace, OperatorKO7.CompositionalImpossibility.ko7Schema] using hxy

/-- Any generic forgetting witness on `ko7Schema` yields a KO7 certified
    forgetting witness. This is the route used by the richer route-local
    evidence layer once it has been converted to a generic
    `ForgettingWitness ko7Schema`. -/
def CertifiedForgettingWitness.ofForgettingWitness
    (W : OperatorKO7.StepDuplicating.StepDuplicatingSchema.ForgettingWitness
      OperatorKO7.CompositionalImpossibility.ko7Schema) :
    CertifiedForgettingWitness where
  rank := fun t => W.rank (ko7CarrierEquivTrace.symm t)
  orientsDupStep := by
    intro b s n
    simpa [ko7CarrierEquivTrace, OperatorKO7.CompositionalImpossibility.ko7Schema] using
      W.orientsDupStep
        (ko7CarrierEquivTrace.symm b)
        (ko7CarrierEquivTrace.symm s)
        (ko7CarrierEquivTrace.symm n)
  violatesPayloadLeft := by
    rcases W.violatesPayloadLeft with ⟨x, y, hxy⟩
    refine ⟨ko7CarrierEquivTrace x, ko7CarrierEquivTrace y, ?_⟩
    simpa [ko7CarrierEquivTrace, OperatorKO7.CompositionalImpossibility.ko7Schema] using hxy
  violatesPayloadRight := by
    rcases W.violatesPayloadRight with ⟨x, y, hxy⟩
    refine ⟨ko7CarrierEquivTrace x, ko7CarrierEquivTrace y, ?_⟩
    simpa [ko7CarrierEquivTrace, OperatorKO7.CompositionalImpossibility.ko7Schema] using hxy

@[simp] theorem CertifiedForgettingWitness.ofConfessionMethod_rank
    (C : ConfessionMethod OperatorKO7.CompositionalImpossibility.ko7Schema) :
    (CertifiedForgettingWitness.ofConfessionMethod C).rank =
      fun t => C.rank (ko7CarrierEquivTrace.symm t) := rfl

@[simp] theorem CertifiedForgettingWitness.ofForgettingWitness_rank
    (W : OperatorKO7.StepDuplicating.StepDuplicatingSchema.ForgettingWitness
      OperatorKO7.CompositionalImpossibility.ko7Schema) :
    (CertifiedForgettingWitness.ofForgettingWitness W).rank =
      fun t => W.rank (ko7CarrierEquivTrace.symm t) := rfl

/-- Narrow formal package for operational incompleteness at the duplicated
payload coordinate.

Interpretation:
- there is no witness in the direct whole-term KO7 witness universe;
- truth-level witnesses exist above that universe;
- under the benchmark contract the first admissible witness sits at the
  transformed-call layer;
- one certified-forgetting witness is supplied at the transformed-call layer. -/
structure PayloadOperationalIncompleteness where
  noDirectWhole :
    ¬ HasWitness ko7Tower WLevel.directWhole
  truthWitnessImported :
    HasWitness ko7Tower WLevel.importedWhole
  noContractWitnessBelowImportedWhole :
    kappaGt (contractTower ko7Tower benchmarkContract) WLevel.importedWhole
  contractWitnessAtTransformedCall :
    kappaLe (contractTower ko7Tower benchmarkContract) WLevel.transformedCall
  certifiedForgetting :
    CertifiedForgettingWitness

/-- KO7 exhibits payload-level operational incompleteness in the sense above. -/
def ko7PayloadOperationalIncompleteness : PayloadOperationalIncompleteness where
  noDirectWhole := ko7_no_directWhole_witness
  truthWitnessImported := ko7_has_importedWhole_witness_poly
  noContractWitnessBelowImportedWhole := ko7_kappaContract_gt_importedWhole
  contractWitnessAtTransformedCall := ko7_kappaContract_le_transformedCall
  certifiedForgetting := dpCertifiedForgettingWitness

/-- public packaged constant for the same formal object. -/
def ko7_operationally_incomplete_at_payload :
    PayloadOperationalIncompleteness :=
  ko7PayloadOperationalIncompleteness

/-- Conjunction of the imported threshold bounds and existence of one
certified-forgetting witness. Despite its historical name, this theorem does
not quantify over every admissible witness. -/
theorem ko7_admissible_witness_requires_certified_forgetting :
    kappaGt (contractTower ko7Tower benchmarkContract) WLevel.importedWhole
      ∧ kappaLe (contractTower ko7Tower benchmarkContract) WLevel.transformedCall
      ∧ (∃ _ : CertifiedForgettingWitness, True) := by
  refine ⟨ko7_kappaContract_gt_importedWhole, ko7_kappaContract_le_transformedCall, ?_⟩
  exact ⟨dpCertifiedForgettingWitness, trivial⟩

/-- The dependency-pair projection witness is explicit evidence that the
successful transformed-call layer is not wrapper-sensitive on the duplicated
payload coordinate. -/
theorem dp_projection_exhibits_certified_forgetting :
    ∃ fw : CertifiedForgettingWitness, fw.rank = OperatorKO7.CompositionalImpossibility.dpProjection := by
  exact ⟨dpCertifiedForgettingWitness, rfl⟩

end OperatorKO7.MetaOperationalIncompleteness
