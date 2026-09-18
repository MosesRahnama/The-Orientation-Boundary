import OperatorKO7.Meta.Methods.OrientationClosure.DirectFamilyHypothesisNecessity
import OperatorKO7.Meta.Methods.OrientationClosure.MethodHypothesisNecessityCatalog

/-!
# Hypothesis necessity capstone

One theorem collecting the hypothesis-necessity results of the Orientation Boundary:

* the twelve direct barrier families, their twenty consumed premises, a deleted-premise
  countermodel for each premise, the restore-and-refute pair for each premise, and the three
  families with an empty premise list;
* both growth hypotheses of the barrier cell;
* the seventy-six method rows of the declared method universe, each with its necessity statement
  and proof, and the row count of each necessity class.

Relation: the schema duplicating step `recur b s (succ n) → wrap s (recur b s n)` at the root.
Property: premise necessity of the barrier theorems and of the method rows.
External trust: none.
-/

set_option autoImplicit false

namespace OperatorKO7.Methods.OrientationClosure.HypothesisNecessity

open OperatorKO7.RDRSTerminationMethodUniverse
open CellClassification

/-- **Hypothesis necessity capstone.** -/
theorem orientationHypothesisNecessity_catalog :
    allDirectBarrierFamilies.length = 12 ∧
    allDirectBarrierFamilies.Nodup ∧
    (∀ f : DirectBarrierFamily, f ∈ allDirectBarrierFamilies) ∧
    (allDirectBarrierFamilies.map (fun f => (familySlots f).length)).sum = 20 ∧
    (∀ (f : DirectBarrierFamily) (h : HypothesisSlot f), Nonempty (NecessityEvidence f h)) ∧
    (∀ (f : DirectBarrierFamily) (h : HypothesisSlot f),
      (∀ M : (slotSpec h).Carrier, (slotSpec h).Deleted M → ¬ (slotSpec h).Orients M) ∧
        ¬ ∀ M : (slotSpec h).Carrier, ¬ (slotSpec h).Orients M) ∧
    IsEmpty (HypothesisSlot .maxPlus) ∧
    IsEmpty (HypothesisSlot .maxDepth) ∧
    IsEmpty (HypothesisSlot .headPrecedence) ∧
    ((¬ ∀ (M : (SchemaCore.freeSchema Empty).T → Nat) (b n : (SchemaCore.freeSchema Empty).T),
      GainBoundedAt M b n →
        ¬ ∀ s : (SchemaCore.freeSchema Empty).T,
          M ((SchemaCore.freeSchema Empty).wrap s ((SchemaCore.freeSchema Empty).recur b s n)) <
            M ((SchemaCore.freeSchema Empty).recur b s ((SchemaCore.freeSchema Empty).succ n))) ∧
    (¬ ∀ (M : (SchemaCore.freeSchema Empty).T → Nat) (b n : (SchemaCore.freeSchema Empty).T),
      WrapUnboundedAt M b n →
        ¬ ∀ s : (SchemaCore.freeSchema Empty).T,
          M ((SchemaCore.freeSchema Empty).wrap s ((SchemaCore.freeSchema Empty).recur b s n)) <
            M ((SchemaCore.freeSchema Empty).recur b s ((SchemaCore.freeSchema Empty).succ n)))) ∧
    methodCatalogRows.length = 76 ∧
    methodCatalogRows.Nodup ∧
    (∀ f : RDRSMethodFamily, f ∈ methodCatalogRows) ∧
    (∀ f : RDRSMethodFamily, RowNecessityStatement f) ∧
    ((methodCatalogRows.filter (fun f => rowNecessityKind f = .deletedBarrierPremise)).length = 14 ∧
    (methodCatalogRows.filter (fun f => rowNecessityKind f = .lawFreeBarrierControl)).length = 7 ∧
    (methodCatalogRows.filter (fun f => rowNecessityKind f = .deletedEscapeFeature)).length = 42 ∧
    (methodCatalogRows.filter
      (fun f => rowNecessityKind f = .noApplicableHypothesis)).length = 13) :=
  ⟨allDirectBarrierFamilies_length, allDirectBarrierFamilies_nodup, mem_allDirectBarrierFamilies,
    familySlots_total, used_hypothesis_has_countermodel,
    fun _ h => slot_premise_exactly_necessary h,
    maxPlus_has_no_slot, maxDepth_has_no_slot, headPrecedence_has_no_slot,
    barrier_cell_hypotheses_individually_necessary,
    methodCatalogRows_length, methodCatalogRows_nodup, methodCatalogRows_complete,
    rowNecessityEvidence, rowNecessityKind_counts⟩

end OperatorKO7.Methods.OrientationClosure.HypothesisNecessity
