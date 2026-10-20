import Mathlib
import OperatorKO7.Meta.OperationalInexpressibility.ObserverKernel

set_option autoImplicit false

/-!
# Canonical finite probability distributions

Relation: equality and pointwise order on finite real probability masses.
Closure: nonnegative masses normalized by a finite sum.
Trust: kernel-only finite algebra.
Scope: finite classical probability; no measure-theoretic or physical transport.
-/

namespace OperatorKO7.Meta.UUET.Probability

open scoped BigOperators

/-- A normalized real probability mass function on a finite carrier. -/
structure FiniteDistribution (α : Type) [Fintype α] where
  mass : α -> ℝ
  nonnegative : forall x, 0 <= mass x
  total : (∑ x, mass x) = 1

namespace FiniteDistribution

theorem mass_le_one {α : Type} [Fintype α]
    (p : FiniteDistribution α) (x : α) : p.mass x <= 1 := by
  classical
  calc
    p.mass x <= ∑ y, p.mass y :=
      Finset.single_le_sum (fun y _ => p.nonnegative y) (Finset.mem_univ x)
    _ = 1 := p.total

/-- Deterministic mass at one finite outcome. -/
def pointMass {α : Type} [Fintype α] [DecidableEq α]
    (x0 : α) : FiniteDistribution α where
  mass := fun x => if x = x0 then 1 else 0
  nonnegative := by
    intro x
    split <;> norm_num
  total := by simp

@[simp] theorem pointMass_at {α : Type} [Fintype α] [DecidableEq α]
    (x0 : α) : (pointMass x0).mass x0 = 1 := by
  simp [pointMass]

@[simp] theorem pointMass_away {α : Type} [Fintype α] [DecidableEq α]
    {x x0 : α} (h : Not (x = x0)) : (pointMass x0).mass x = 0 := by
  simp [pointMass, h]

/-- Adapter from the pre-crown observer-kernel distribution. -/
def ofLegacy {α : Type} [Fintype α]
    (p : OperatorKO7.Meta.OperationalInexpressibility.ObserverKernel.FiniteDistribution α) :
    FiniteDistribution α where
  mass := p.mass
  nonnegative := p.nonnegative
  total := p.total

/-- Adapter to the pre-crown observer-kernel distribution. -/
def toLegacy {α : Type} [Fintype α] (p : FiniteDistribution α) :
    OperatorKO7.Meta.OperationalInexpressibility.ObserverKernel.FiniteDistribution α where
  mass := p.mass
  nonnegative := p.nonnegative
  total := p.total

end FiniteDistribution

/-- Positive finite fixture: the fair binary law. -/
noncomputable def binaryUniform : FiniteDistribution (Fin 2) where
  mass := fun _ => 1 / 2
  nonnegative := by intro i; norm_num
  total := by norm_num [Fin.sum_univ_two]

theorem binaryUniform_mass (i : Fin 2) : binaryUniform.mass i = 1 / 2 := rfl

/-- Negative fixture: no normalized finite law assigns mass greater than one. -/
theorem no_mass_above_one {α : Type} [Fintype α]
    (p : FiniteDistribution α) (x : α) : Not (1 < p.mass x) := by
  exact not_lt_of_ge (FiniteDistribution.mass_le_one p x)

/-! Imported NameGate and TypeGate. -/
#check @Finset.single_le_sum
#check @OperatorKO7.Meta.OperationalInexpressibility.ObserverKernel.FiniteDistribution
#check @FiniteDistribution.mass
#check @FiniteDistribution.pointMass

#check @FiniteDistribution.mass_le_one
#check @FiniteDistribution.pointMass_at
#check @FiniteDistribution.pointMass_away
#check @binaryUniform_mass
#check @no_mass_above_one
#print axioms FiniteDistribution.mass_le_one
#print axioms FiniteDistribution.pointMass_at
#print axioms FiniteDistribution.pointMass_away
#print axioms binaryUniform_mass
#print axioms no_mass_above_one

end OperatorKO7.Meta.UUET.Probability
