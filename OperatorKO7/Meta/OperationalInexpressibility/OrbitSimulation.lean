import OperatorKO7.Meta.OperationalInexpressibility.ObserverKernel
import OperatorKO7.Meta.LicensedBoundaryCalculus.LicensedReductionMorphism

/-!
# Observer-quotient orbit simulation

The quotient relation records an edge whenever it has source representatives
joined by a raw edge.  The canonical quotient projection is therefore a real
relation simulation.  Finite admitted paths map to quotient paths of the same
length.

## Audit slots

Relation: source `ARS.step` and its representative-generated quotient relation.
Closure: one-step simulation, length-indexed paths, and reflexive-transitive reach.
Trust: kernel-only; quotient equality stays within the baseline axiom surface.
Scope: a forward simulation.  Reverse simulation requires a separate lifting
hypothesis and is absent from this module.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.OperationalInexpressibility.OrbitSimulation

open OperatorKO7.Meta.LicensedBoundaryCalculus
open OperatorKO7.Meta.OperationalInexpressibility.ObserverKernel

universe u v

/-- Quotient states are adjacent when some representatives are adjacent. -/
def observerQuotientStep (A : ARS.{u}) {Y : Type v}
    (observe : A.Carrier -> Y)
    (q r : ObserverQuotient observe) : Prop :=
  exists x y : A.Carrier,
    quotientMap observe x = q ∧ quotientMap observe y = r ∧ A.step x y

/-- The observer quotient as an abstract reduction system. -/
def observerQuotientARS (A : ARS.{u}) {Y : Type v}
    (observe : A.Carrier -> Y) : ARS.{u} where
  Carrier := ObserverQuotient observe
  step := observerQuotientStep A observe
  scope := { A.scope with admission := .guarded, layer := .projected }

/-- Canonical observer projection, admitting every raw source edge. -/
def quotientProjection (A : ARS.{u}) {Y : Type v}
    (observe : A.Carrier -> Y) :
    LicensedReductionMorphism A (observerQuotientARS A observe) where
  admitted := A.step
  admitted_sub_raw := fun h => h
  map := quotientMap observe
  map_step := by
    intro x y hxy
    exact ⟨x, y, rfl, rfl, hxy⟩

/-- The canonical projection transports every source path to a quotient path of
the same length. -/
theorem quotientProjection_maps_steps (A : ARS.{u}) {Y : Type v}
    (observe : A.Carrier -> Y) {n : Nat} {x y : A.Carrier}
    (h : Steps A n x y) :
    Steps (observerQuotientARS A observe) n
      (quotientMap observe x) (quotientMap observe y) :=
  Steps.map (A := A) (B := observerQuotientARS A observe)
    (quotientMap observe)
    (by
      intro a b hab
      exact ⟨a, b, rfl, rfl, hab⟩)
    h

/-- The canonical projection transports reflexive-transitive reachability. -/
theorem quotientProjection_maps_reach (A : ARS.{u}) {Y : Type v}
    (observe : A.Carrier -> Y) {x y : A.Carrier}
    (h : Reach A x y) :
    Reach (observerQuotientARS A observe)
      (quotientMap observe x) (quotientMap observe y) := by
  rcases h with ⟨n, hn⟩
  exact ⟨n, quotientProjection_maps_steps A observe hn⟩

/-! ## Non-vacuity fixture -/

/-- A two-valued observer on the chain fixture. -/
def chainObserver_fixture : ChainNode -> Bool
  | .source => false
  | .target => true

/-- The genuine chain edge survives in the observer quotient. -/
theorem chainObserver_edge_fixture :
    (observerQuotientARS chainARS_fixture chainObserver_fixture).step
      (quotientMap chainObserver_fixture ChainNode.source)
      (quotientMap chainObserver_fixture ChainNode.target) :=
  (quotientProjection chainARS_fixture chainObserver_fixture).map_step
    ChainStep.descend

/-- The quotient fixture contains a mapped one-step reachability witness. -/
theorem chainObserver_reach_fixture :
    Reach (observerQuotientARS chainARS_fixture chainObserver_fixture)
      (quotientMap chainObserver_fixture ChainNode.source)
      (quotientMap chainObserver_fixture ChainNode.target) :=
  quotientProjection_maps_reach chainARS_fixture chainObserver_fixture
    chainARS_reach_fixture

#check @quotientProjection
#check @quotientProjection_maps_steps
#check @quotientProjection_maps_reach
#check chainObserver_reach_fixture
#print axioms quotientProjection_maps_steps
#print axioms quotientProjection_maps_reach
#print axioms chainObserver_edge_fixture
#print axioms chainObserver_reach_fixture

end OperatorKO7.Meta.OperationalInexpressibility.OrbitSimulation
