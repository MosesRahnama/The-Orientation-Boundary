import OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorWitnessOrder

/-!
# Certificate hierarchies with sound transport maps

Proves: a certificate hierarchy with transport maps is a witness hierarchy whose classes come
with maps from each layer to the next that preserve acceptance; the truth and boundary
hierarchies of the free recursor carry such maps, so every certificate at a layer yields an
accepted certificate at every higher layer.
Relation: root steps of the free recursor, through the certificates of each layer.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: the two declared hierarchies of `FreeRecursorWitnessOrder.lean`.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.OperationalInexpressibility.AuditUpgrades.HierarchyTransport

open OperatorKO7.RepShift
open OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel
open OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorWitnessOrder
open OperatorKO7.Meta.Recursor.RecursorFreeAlgebra
open OperatorKO7.Meta.Recursor.DPConfessionLicense

universe u

/-- A witness hierarchy together with acceptance-preserving maps from each layer to the next. -/
structure TransportingHierarchy (S : Type u) where
  hierarchy : WitnessHierarchy S
  transport : ∀ {k : Nat} {P : S → Prop} {x : S}, hierarchy.W k P x → hierarchy.W (k + 1) P x
  transport_accepts : ∀ {k : Nat} {P : S → Prop} {x : S} (w : hierarchy.W k P x),
    hierarchy.accepts w → hierarchy.accepts (transport w)

/-- Iterated transport from layer `k` to layer `k + j`. -/
def TransportingHierarchy.lift {S : Type u} (H : TransportingHierarchy S) {P : S → Prop} {x : S} :
    {k : Nat} → (j : Nat) → H.hierarchy.W k P x → H.hierarchy.W (k + j) P x
  | _, 0, w => w
  | _, j + 1, w => H.transport (H.lift j w)

theorem TransportingHierarchy.lift_accepts {S : Type u} (H : TransportingHierarchy S)
    {P : S → Prop} {x : S} {k : Nat} (j : Nat) (w : H.hierarchy.W k P x)
    (hw : H.hierarchy.accepts w) : H.hierarchy.accepts (H.lift j w) := by
  induction j with
  | zero => exact hw
  | succ j ih => exact H.transport_accepts _ ih

/-- An accepted certificate at a layer yields the target at every higher layer. -/
theorem TransportingHierarchy.sound_above {S : Type u} (H : TransportingHierarchy S)
    {P : S → Prop} {x : S} {k : Nat} (j : Nat) (w : H.hierarchy.W k P x)
    (hw : H.hierarchy.accepts w) : P x :=
  H.hierarchy.sound (H.lift j w) (H.lift_accepts j w hw)

/-- Transport of the truth evidence of the free recursor to the next layer. -/
def truthTransport : (k : Nat) → TruthEvidence k → TruthEvidence (k + 1)
  | 0, w => (freeRecursor_no_directWhole ⟨w⟩).elim
  | 1, _ => transformedCallWitness
  | 2, _ => externalWitness
  | _ + 3, w => w

/-- Transport of the boundary evidence of the free recursor to the next layer. -/
def boundaryTransport : (k : Nat) → BoundaryEvidence k → BoundaryEvidence (k + 1)
  | 0, w => (freeRecursor_no_directWhole ⟨w⟩).elim
  | 1, w => (no_erasedCounterDecoder ⟨w.2⟩).elim
  | 2, _ => externalWitness
  | _ + 3, w => w

/-- The truth hierarchy of the free recursor with its transport maps. -/
def truthTransportingHierarchy : TransportingHierarchy RecursorTerm where
  hierarchy := truthHierarchy
  transport := fun {k} _ _ w => truthTransport k w
  transport_accepts := fun _ hw => hw

/-- The boundary hierarchy of the free recursor with its transport maps. -/
def boundaryTransportingHierarchy : TransportingHierarchy RecursorTerm where
  hierarchy := boundaryHierarchy
  transport := fun {k} _ _ w => boundaryTransport k w
  transport_accepts := fun _ hw => hw

/-- Every layer at or above one of the truth hierarchy holds an accepted certificate of
termination, reached by transport from the imported certificate. -/
theorem truth_transport_from_imported (t : RecursorTerm) (j : Nat) :
    ∃ w : truthHierarchy.W (1 + j) RootTerminates t, truthHierarchy.accepts w :=
  ⟨truthTransportingHierarchy.lift (k := 1) j (show TruthEvidence 1 from importedWholeWitness),
    truthTransportingHierarchy.lift_accepts (k := 1) j
      (show TruthEvidence 1 from importedWholeWitness) rfl⟩

/-- Every layer at or above two of the boundary hierarchy holds an accepted certificate of
termination, reached by transport from the extracted-call certificate. -/
theorem boundary_transport_from_transformedCall (t : RecursorTerm) (j : Nat) :
    ∃ w : boundaryHierarchy.W (2 + j) RootTerminates t, boundaryHierarchy.accepts w :=
  ⟨boundaryTransportingHierarchy.lift (k := 2) j
      (show BoundaryEvidence 2 from transformedCallWitness),
    boundaryTransportingHierarchy.lift_accepts (k := 2) j
      (show BoundaryEvidence 2 from transformedCallWitness) rfl⟩

end OperatorKO7.Meta.OperationalInexpressibility.AuditUpgrades.HierarchyTransport
