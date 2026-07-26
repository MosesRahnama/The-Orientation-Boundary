import Mathlib

/-!
# Observer-kernel quotients and finite deterministic channels

The observer kernel identifies source states carrying equal observer values.
Its quotient projection has a universal factorization property.  The finite
channel layer derives pushforward, Shannon-functional, and Hartley-support
equalities from a proved factorization through that quotient.

## Audit slots

Relation: equality of observer outputs, represented as a `Setoid`.
Closure: equivalence closure supplied by equality; finite deterministic channels
use pointwise maps and finite sums.
Trust: kernel-only; quotient equality uses `Quot.sound`, and extensional channel
equalities use baseline function extensionality.
Scope: observer quotients and deterministic finite pushforwards.  Physical energy
and thermodynamic valuations lie outside this module.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.OperationalInexpressibility.ObserverKernel

universe u v w

/-- The kernel equivalence of an observer. -/
def observerSetoid {X : Type u} {Y : Type v} (observe : X -> Y) : Setoid X where
  r x y := observe x = observe y
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun hxy hyz => hxy.trans hyz⟩

/-- Quotient of source states by equality of observer outputs. -/
abbrev ObserverQuotient {X : Type u} {Y : Type v} (observe : X -> Y) : Type u :=
  Quotient (observerSetoid observe)

/-- Canonical observer-kernel projection. -/
def quotientMap {X : Type u} {Y : Type v} (observe : X -> Y) (x : X) :
    ObserverQuotient observe :=
  Quotient.mk (observerSetoid observe) x

/-- The observer descends to its kernel quotient. -/
def quotientObserver {X : Type u} {Y : Type v} (observe : X -> Y) :
    ObserverQuotient observe -> Y :=
  Quotient.lift observe (fun _ _ h => h)

@[simp] theorem quotientObserver_quotientMap {X : Type u} {Y : Type v}
    (observe : X -> Y) (x : X) :
    quotientObserver observe (quotientMap observe x) = observe x := rfl

/-- Two projected states agree precisely when the observer agrees. -/
theorem quotientMap_eq_iff {X : Type u} {Y : Type v} (observe : X -> Y) (x y : X) :
    quotientMap observe x = quotientMap observe y <-> observe x = observe y := by
  constructor
  · intro h
    exact congrArg (quotientObserver observe) h
  · intro h
    exact Quotient.sound h

/-- A function factors through an observer kernel when it is constant on every
observer fiber. -/
def FactorsThrough {X : Type u} {Y : Type v} {Z : Type w}
    (observe : X -> Y) (f : X -> Z) : Prop :=
  forall {x y}, observe x = observe y -> f x = f y

/-- Universal factor induced by a kernel-respecting function. -/
def factor {X : Type u} {Y : Type v} {Z : Type w}
    (observe : X -> Y) (f : X -> Z) (hf : FactorsThrough observe f) :
    ObserverQuotient observe -> Z :=
  Quotient.lift f (fun _ _ h => hf h)

@[simp] theorem factor_quotientMap {X : Type u} {Y : Type v} {Z : Type w}
    (observe : X -> Y) (f : X -> Z) (hf : FactorsThrough observe f) (x : X) :
    factor observe f hf (quotientMap observe x) = f x := rfl

/-- Universal factorization equation. -/
theorem factorization {X : Type u} {Y : Type v} {Z : Type w}
    (observe : X -> Y) (f : X -> Z) (hf : FactorsThrough observe f) :
    factor observe f hf ∘ quotientMap observe = f := by
  funext x
  rfl

/-- The universal factor is unique among maps satisfying the factorization
equation. -/
theorem factor_unique {X : Type u} {Y : Type v} {Z : Type w}
    (observe : X -> Y) (f : X -> Z) (hf : FactorsThrough observe f)
    (g : ObserverQuotient observe -> Z)
    (hg : g ∘ quotientMap observe = f) :
    g = factor observe f hf := by
  funext q
  induction q using Quotient.inductionOn with
  | _ x =>
      have hx := congrFun hg x
      exact hx

/-! ## Explicit finite deterministic channels -/

/-- A finite probability mass function. -/
structure FiniteDistribution (X : Type u) [Fintype X] where
  mass : X -> Real
  nonnegative : forall x, 0 <= mass x
  total : (Finset.univ.sum mass) = 1

/-- Pushforward mass of a deterministic finite channel. -/
def pushforward {X : Type u} {Y : Type v} [Fintype X] [Fintype Y]
    [DecidableEq Y] (f : X -> Y) (p : FiniteDistribution X) (y : Y) : Real :=
  ∑ x, if f x = y then p.mass x else 0

/-- Shannon functional in natural-log units for a finite mass function. -/
noncomputable def shannonFunctional {Y : Type v} [Fintype Y]
    (q : Y -> Real) : Real :=
  ∑ y, if q y = 0 then 0 else -(q y * Real.log (q y))

/-- Hartley support size of a finite mass function. -/
noncomputable def hartleySupportCard {Y : Type v} [Fintype Y] [DecidableEq Y]
    (q : Y -> Real) : Nat :=
  (Finset.univ.filter fun y => q y != 0).card

/-- Pointwise-equal deterministic channels have equal pushforwards. -/
theorem pushforward_eq_of_pointwise {X : Type u} {Y : Type v}
    [Fintype X] [Fintype Y] [DecidableEq Y]
    (f g : X -> Y) (p : FiniteDistribution X)
    (hfg : forall x, f x = g x) :
    pushforward f p = pushforward g p := by
  funext y
  apply Finset.sum_congr rfl
  intro x _
  rw [hfg x]

/-- A kernel-respecting finite channel has the same pushforward as its quotient
factor composed with the canonical projection. -/
theorem pushforward_through_observerKernel
    {X : Type u} {Y : Type v} {Z : Type w}
    [Fintype X] [Fintype Z] [DecidableEq Z]
    (observe : X -> Y) (f : X -> Z) (hf : FactorsThrough observe f)
    (p : FiniteDistribution X) :
    pushforward f p =
      pushforward (factor observe f hf ∘ quotientMap observe) p := by
  apply pushforward_eq_of_pointwise
  intro x
  rfl

/-- The Shannon functional is preserved by the proved observer-kernel
factorization. -/
theorem shannon_through_observerKernel
    {X : Type u} {Y : Type v} {Z : Type w}
    [Fintype X] [Fintype Z] [DecidableEq Z]
    (observe : X -> Y) (f : X -> Z) (hf : FactorsThrough observe f)
    (p : FiniteDistribution X) :
    shannonFunctional (pushforward f p) =
      shannonFunctional
        (pushforward (factor observe f hf ∘ quotientMap observe) p) := by
  rw [pushforward_through_observerKernel observe f hf p]

/-- The Hartley support size is preserved by the proved observer-kernel
factorization. -/
theorem hartley_through_observerKernel
    {X : Type u} {Y : Type v} {Z : Type w}
    [Fintype X] [Fintype Z] [DecidableEq Z]
    (observe : X -> Y) (f : X -> Z) (hf : FactorsThrough observe f)
    (p : FiniteDistribution X) :
    hartleySupportCard (pushforward f p) =
      hartleySupportCard
        (pushforward (factor observe f hf ∘ quotientMap observe) p) := by
  rw [pushforward_through_observerKernel observe f hf p]

/-! ## Nonconstant finite fixture -/

/-- Parity is a nonconstant observer on four states. -/
def parityObserver_fixture (i : Fin 4) : Bool := decide (i.val % 2 = 0)

/-- The observer kernel identifies the two even fixture states. -/
theorem parityObserver_identifies_even_fixture :
    quotientMap parityObserver_fixture (0 : Fin 4) =
      quotientMap parityObserver_fixture (2 : Fin 4) := by
  apply (quotientMap_eq_iff parityObserver_fixture _ _).2
  decide

/-- The observer kernel separates an even state from an odd state. -/
theorem parityObserver_separates_parity_fixture :
    Not (quotientMap parityObserver_fixture (0 : Fin 4) =
      quotientMap parityObserver_fixture (1 : Fin 4)) := by
  intro h
  have hp := (quotientMap_eq_iff parityObserver_fixture _ _).1 h
  norm_num [parityObserver_fixture] at hp

#check @quotientMap_eq_iff
#check @factorization
#check @factor_unique
#check @pushforward_through_observerKernel
#check @shannon_through_observerKernel
#check @hartley_through_observerKernel
#check parityObserver_separates_parity_fixture
#print axioms quotientMap_eq_iff
#print axioms factorization
#print axioms factor_unique
#print axioms pushforward_through_observerKernel
#print axioms shannon_through_observerKernel
#print axioms hartley_through_observerKernel
#print axioms parityObserver_separates_parity_fixture

end OperatorKO7.Meta.OperationalInexpressibility.ObserverKernel
