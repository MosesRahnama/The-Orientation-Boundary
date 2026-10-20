import OperatorKO7.Meta.LicensedBoundaryCalculus.Core.AdmittedEdgeARS
import OperatorKO7.Meta.OperationalInexpressibility.ObserverKernel

/-!
# Kernel-quotient reduction systems

The third canonical factor identifies exactly those domain states with equal
state-map values.  Its quotient relation is the direct image of admitted source
steps, so the canonical projection is a forward simulation without any lifting
hypothesis.

## Audit slots

Relation: direct image of admitted edges under the observer-kernel quotient.
Closure: one step; finite-path transport follows from the morphism API.
Trust: kernel-only; quotient equality uses baseline `Quot.sound`.
Scope: universal kernel quotient, projection, and quotient universal property.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.LicensedBoundaryCalculus
namespace PartialLicensedReductionMorphism

open OperatorKO7.Meta.OperationalInexpressibility.ObserverKernel

universe u v w

variable {A : ARS.{u}} {B : ARS.{v}}

/-- Quotient of the domain by equality of state-map outputs. -/
abbrev KernelQuotient (F : PartialLicensedReductionMorphism A B) :=
  ObserverQuotient F.map

/-- Canonical projection to the state-map kernel quotient. -/
def kernelProjection (F : PartialLicensedReductionMorphism A B) :
    DomainCarrier F -> KernelQuotient F :=
  quotientMap F.map

/-- The admitted relation pushed to kernel classes by existential representatives. -/
def kernelQuotientARS (F : PartialLicensedReductionMorphism A B) : ARS.{u} where
  Carrier := KernelQuotient F
  step := fun q r =>
    exists x y : DomainCarrier F,
      F.admitted x.val y.val ∧ F.kernelProjection x = q ∧
        F.kernelProjection y = r
  scope := { A.scope with admission := .guarded, layer := .projected }

/-- Canonical quotient projection as a licensed reduction morphism. -/
def kernelProjectionMorphism (F : PartialLicensedReductionMorphism A B) :
    LicensedReductionMorphism F.admittedEdgeARS F.kernelQuotientARS where
  admitted := F.admittedEdgeARS.step
  admitted_sub_raw := fun h => h
  map := F.kernelProjection
  map_step := by
    intro x y h
    exact ⟨x, y, h, rfl, rfl⟩

/-- Kernel classes agree exactly when state-map outputs agree. -/
theorem kernelProjection_eq_iff
    (F : PartialLicensedReductionMorphism A B) (x y : DomainCarrier F) :
    F.kernelProjection x = F.kernelProjection y <-> F.map x = F.map y :=
  quotientMap_eq_iff F.map x y

/-- The canonical kernel projection is surjective. -/
theorem kernelProjection_surjective
    (F : PartialLicensedReductionMorphism A B) :
    Function.Surjective F.kernelProjection := by
  intro q
  induction q using Quotient.inductionOn with
  | _ x => exact ⟨x, rfl⟩

/-- Any map constant on state-map fibers factors uniquely through the canonical
kernel quotient. -/
theorem kernel_factorization_unique
    (F : PartialLicensedReductionMorphism A B)
    {Z : Type w} (g : DomainCarrier F -> Z)
    (hg : FactorsThrough F.map g) :
    ∃! lift : KernelQuotient F -> Z,
      lift ∘ F.kernelProjection = g := by
  refine ⟨factor F.map g hg, factorization F.map g hg, ?_⟩
  intro lift hlift
  exact factor_unique F.map g hg lift hlift

/-- Pure state collapse identifies the two chain states in the kernel quotient. -/
theorem pureStateCollapse_kernel_identifies_fixture :
    pureStateCollapse_fixture.kernelProjection
        ⟨ChainNode.source, trivial⟩ =
      pureStateCollapse_fixture.kernelProjection
        ⟨ChainNode.target, trivial⟩ := by
  apply (kernelProjection_eq_iff pureStateCollapse_fixture _ _).2
  rfl

#check @kernelQuotientARS
#check @kernelProjectionMorphism
#check @kernelProjection_eq_iff
#check @kernelProjection_surjective
#check @kernel_factorization_unique
#check pureStateCollapse_kernel_identifies_fixture
#print axioms kernelQuotientARS
#print axioms kernelProjectionMorphism
#print axioms kernelProjection_eq_iff
#print axioms kernelProjection_surjective
#print axioms kernel_factorization_unique
#print axioms pureStateCollapse_kernel_identifies_fixture

end PartialLicensedReductionMorphism
end OperatorKO7.Meta.LicensedBoundaryCalculus
