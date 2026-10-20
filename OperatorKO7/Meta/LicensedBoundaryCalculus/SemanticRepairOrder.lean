import OperatorKO7.Meta.DistinctionBoundary.PersistentLicense
import OperatorKO7.Meta.DistinctionBoundary.WriteClosure

set_option autoImplicit false

/-!
# Semantic repair order

This module replaces scalar repair rankings with semantic comparison data.
The finite positional-policy instance is the live KO7 `EqGuardedStep` closure.
No claim is made outside the stated predicate and positional-policy classes.
-/

namespace OperatorKO7.Meta.LicensedBoundaryCalculus.SemanticRepairOrder

open OperatorKO7
open OperatorKO7.EqGuardedConfluence
open OperatorKO7.Meta.DistinctionBoundary.PersistentLicense
open OperatorKO7.Meta.DistinctionBoundary.FreezePositions
open OperatorKO7.Meta.DistinctionBoundary.WriteClosure

universe u v w

/-- A semantic repair profile exposes the four comparison coordinates used by
the Licensing Boundary: retained domain, admitted dynamics, observer, and
license predicate. -/
structure SemanticRepairProfile (X : Type u) (Obs : Type v) (Lic : Type w) where
  retainedDomain : X → Prop
  admitted : X → X → Prop
  observer : X → Obs
  license : Lic → Prop

/-- Pareto comparison contains no scalarization. `A ≤ B` says that `B` retains
at least the domain and dynamics of `A`, observes enough to reconstruct `A`'s
observer, and accepts every license accepted by `A`. -/
structure ParetoLE {X : Type u} {ObsA : Type v} {ObsB : Type w} {Lic : Type*}
    (A : SemanticRepairProfile X ObsA Lic) (B : SemanticRepairProfile X ObsB Lic) : Prop where
  retained : ∀ x, A.retainedDomain x → B.retainedDomain x
  admitted : ∀ x y, A.admitted x y → B.admitted x y
  observerFactor : ∃ factor : ObsB → ObsA, A.observer = factor ∘ B.observer
  licenseImplication : ∀ l, A.license l → B.license l

/-- Reflexivity of the semantic Pareto order. -/
theorem pareto_refl {X : Type u} {Obs : Type v} {Lic : Type w}
    (A : SemanticRepairProfile X Obs Lic) : ParetoLE A A := by
  refine ⟨fun _ h => h, fun _ _ h => h, ⟨id, ?_⟩, fun _ h => h⟩
  funext x
  rfl

/-- Transitivity of the semantic Pareto order. -/
theorem pareto_trans {X : Type u} {ObsA : Type v} {ObsB : Type w}
    {ObsC : Type*} {Lic : Type*}
    {A : SemanticRepairProfile X ObsA Lic}
    {B : SemanticRepairProfile X ObsB Lic}
    {C : SemanticRepairProfile X ObsC Lic}
    (hAB : ParetoLE A B) (hBC : ParetoLE B C) : ParetoLE A C := by
  rcases hAB.observerFactor with ⟨f, hf⟩
  rcases hBC.observerFactor with ⟨g, hg⟩
  refine ⟨fun x hx => hBC.retained x (hAB.retained x hx),
    fun x y hxy => hBC.admitted x y (hAB.admitted x y hxy),
    ⟨f ∘ g, ?_⟩,
    fun l hl => hBC.licenseImplication l (hAB.licenseImplication l hl)⟩
  rw [hf, hg]
  rfl

/-- The semantic Pareto comparison is a preorder on repair profiles sharing an
observer type: reflexive by `pareto_refl`, transitive by `pareto_trans`.  This
is the anchor behind the sentence that repairs are compared by a semantic order
carrying no scalarization. -/
theorem paretoLE_preorder {X : Type u} {Obs : Type v} {Lic : Type w} :
    (∀ A : SemanticRepairProfile X Obs Lic, ParetoLE A A) ∧
    (∀ {A B C : SemanticRepairProfile X Obs Lic},
      ParetoLE A B → ParetoLE B C → ParetoLE A C) :=
  ⟨pareto_refl, fun hAB hBC => pareto_trans hAB hBC⟩

/-! ### Incomparability

A Pareto order carries content when some pair stays unordered, with a coordinate
naming the failure in each direction.  The two profiles below sit on a two-point
carrier: the first keeps the whole domain and admits no edge, the second keeps
half the domain and admits every edge. -/

/-- Whole retained domain, empty admitted relation. -/
def wideDomainProfile : SemanticRepairProfile Bool Unit Unit where
  retainedDomain := fun _ => True
  admitted := fun _ _ => False
  observer := fun _ => ()
  license := fun _ => True

/-- Half retained domain, full admitted relation. -/
def wideDynamicsProfile : SemanticRepairProfile Bool Unit Unit where
  retainedDomain := fun b => b = true
  admitted := fun _ _ => True
  observer := fun _ => ()
  license := fun _ => True

/-- The retained-domain coordinate blocks one direction: the wide-domain profile
keeps `false`, which the wide-dynamics profile drops. -/
theorem pareto_retained_coordinate_blocks :
    ¬ ParetoLE wideDomainProfile wideDynamicsProfile := by
  intro h
  have hfalse : wideDynamicsProfile.retainedDomain false :=
    h.retained false trivial
  exact Bool.false_ne_true hfalse

/-- The admitted-dynamics coordinate blocks the other direction: the
wide-dynamics profile admits an edge that the wide-domain profile refuses. -/
theorem pareto_admitted_coordinate_blocks :
    ¬ ParetoLE wideDynamicsProfile wideDomainProfile := by
  intro h
  exact h.admitted true true trivial

/-- Incomparability witness for the semantic repair order, with the failing
coordinate named in each direction. -/
theorem pareto_incomparable_witness :
    ¬ ParetoLE wideDomainProfile wideDynamicsProfile ∧
      ¬ ParetoLE wideDynamicsProfile wideDomainProfile :=
  ⟨pareto_retained_coordinate_blocks, pareto_admitted_coordinate_blocks⟩

/-- Predicate-only repairs are ordered by pointwise inclusion. -/
def PredicateRepairLE {α : Type} (Q P : α → Prop) : Prop :=
  ∀ x, Q x → P x

/-- The persistent license `Box R P` is the greatest forward-invariant
predicate-only repair contained in `P`. -/
theorem box_maximal_predicate_repair {α : Type} {R : α → α → Prop}
    {P Q : α → Prop}
    (hSub : PredicateRepairLE Q P)
    (hInv : ForwardInvariant R Q) :
    PredicateRepairLE Q (Box R P) := by
  intro x hx
  exact box_greatest hSub hInv hx

/-- Thin morphisms between positional policies are semantic inclusions. -/
structure PolicyHom (S T : CtorPos → Prop) : Prop where
  le : SelectionLE S T

namespace PolicyHom

/-- Identity policy morphism. -/
theorem id (S : CtorPos → Prop) : PolicyHom S S :=
  ⟨fun _ h => h⟩

/-- Composition of policy inclusions. -/
theorem comp {S T U : CtorPos → Prop} (hST : PolicyHom S T)
    (hTU : PolicyHom T U) : PolicyHom S U :=
  ⟨fun c hc => hTU.le c (hST.le c hc)⟩

end PolicyHom

/-- The live repair compiler is monotone on the finite positional-policy
subcategory. -/
theorem confluenceRepair_monotone {S T : CtorPos → Prop}
    (hST : SelectionLE S T) :
    SelectionLE (confluenceRepair S) (confluenceRepair T) := by
  apply writeClosure_monotone
  intro c hc
  exact ⟨hST c hc.1, hc.2⟩

/-- Object-and-arrow action of the repair compiler on the thin policy category. -/
def repairMap {S T : CtorPos → Prop} (h : PolicyHom S T) :
    PolicyHom (confluenceRepair S) (confluenceRepair T) :=
  ⟨confluenceRepair_monotone h.le⟩

/-- The repair action preserves identity morphisms in the thin policy category. -/
theorem repairMap_id (S : CtorPos → Prop) :
    repairMap (PolicyHom.id S) = PolicyHom.id (confluenceRepair S) := by
  exact Subsingleton.elim _ _

/-- The repair action preserves composition in the thin policy category. -/
theorem repairMap_comp {S T U : CtorPos → Prop}
    (hST : PolicyHom S T) (hTU : PolicyHom T U) :
    repairMap (PolicyHom.comp hST hTU) =
      PolicyHom.comp (repairMap hST) (repairMap hTU) := by
  exact Subsingleton.elim _ _

/-- Finite positional-policy functoriality package. This is the proved finite
subcategory instance of the Licensing Boundary functor target. -/
theorem finite_policy_completion_functorial :
    (∀ S : CtorPos → Prop,
      repairMap (PolicyHom.id S) = PolicyHom.id (confluenceRepair S)) ∧
    (∀ {S T U : CtorPos → Prop} (hST : PolicyHom S T) (hTU : PolicyHom T U),
      repairMap (PolicyHom.comp hST hTU) =
        PolicyHom.comp (repairMap hST) (repairMap hTU)) :=
  ⟨repairMap_id, fun hST hTU => repairMap_comp hST hTU⟩

/-- Every compiled repair is a live confluent positional policy. -/
theorem repairMap_target_confluent (S : CtorPos → Prop) :
    ConfluentOnPos (confluenceRepair S) EqGuardedStep :=
  confluenceRepair_confluent S

/-- Minimality of the compiled repair among confluent extensions of the
requested non-`eqW` positions. This is the semantic order statement used by
the finite functoriality theorem. -/
theorem confluenceRepair_minimal_write_closed {S T : CtorPos → Prop}
    (hT : ConfluentOnPos T EqGuardedStep)
    (hExt : ∀ c, S c → c ≠ .eqW → T c) :
    PolicyHom (confluenceRepair S) T :=
  ⟨confluenceRepair_least hT hExt⟩

/-- The compiled repair is idempotent on objects. -/
theorem repairMap_idempotent (S : CtorPos → Prop) :
    confluenceRepair (confluenceRepair S) = confluenceRepair S :=
  confluenceRepair_idempotent S

end OperatorKO7.Meta.LicensedBoundaryCalculus.SemanticRepairOrder



