import OperatorKO7.Meta.LicensedBoundaryCalculus.Quantitative.EdgeDefect

/-!
# Finite fiber composition

## Formal Scope

The fiber equivalence and multiplicative cardinality bound apply under the displayed finite and partial-domain hypotheses.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.LicensedBoundaryCalculus
namespace PartialLicensedReductionMorphism

universe u v w

noncomputable section

/-- A composite fiber is the dependent sum of first-stage fibers over the
corresponding second-stage fiber. -/
def compositeFiberEquiv {α : Type u} {β : Type v} {γ : Type w}
    (f : α → β) (g : β → γ) (z : γ) :
    FiniteFiber (g ∘ f) z ≃
      (Sigma fun y : FiniteFiber g z => FiniteFiber f y.val) where
  toFun x :=
    ⟨⟨f x.val, x.property⟩, ⟨x.val, rfl⟩⟩
  invFun s :=
    ⟨s.2.val, by
      calc
        g (f s.2.val) = g s.1.val := congrArg g s.2.property
        _ = z := s.1.property⟩
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv s := by
    rcases s with ⟨⟨y, hy⟩, ⟨x, hx⟩⟩
    dsimp
    cases hx
    rfl

/-- The dependent sum of all first-stage fiber cardinalities over one
second-stage fiber.  Classical finite instances remain internal. -/
def compositeFiberCardSum
    {α : Type u} {β : Type v} {γ : Type w}
    [Fintype α] [Fintype β] [Fintype γ]
    (f : α → β) (g : β → γ) (z : γ) : Nat := by
  classical
  exact ∑ y : FiniteFiber g z, finiteFiberCard f y.val

/-- specified finite-cardinality formula for one composite fiber. -/
theorem finiteFiberCard_comp_eq_sum
    {α : Type u} {β : Type v} {γ : Type w}
    [Fintype α] [Fintype β] [Fintype γ]
    (f : α → β) (g : β → γ) (z : γ) :
    finiteFiberCard (g ∘ f) z =
      compositeFiberCardSum f g z := by
  classical
  unfold finiteFiberCard compositeFiberCardSum
  calc
    Fintype.card (FiniteFiber (g ∘ f) z) =
        Fintype.card (Sigma fun y : FiniteFiber g z => FiniteFiber f y.val) :=
      Fintype.card_congr (compositeFiberEquiv f g z)
    _ = ∑ y : FiniteFiber g z, Fintype.card (FiniteFiber f y.val) := by
      exact Fintype.card_sigma

/-- Pointwise product bound for a composite fiber. -/
theorem finiteFiberCard_comp_le_mul
    {α : Type u} {β : Type v} {γ : Type w}
    [Fintype α] [Fintype β] [Fintype γ]
    (f : α → β) (g : β → γ) (z : γ) :
    finiteFiberCard (g ∘ f) z ≤
      maximumFiberCardinalityOf f * maximumFiberCardinalityOf g := by
  classical
  calc
    finiteFiberCard (g ∘ f) z =
        compositeFiberCardSum f g z :=
      finiteFiberCard_comp_eq_sum f g z
    _ ≤ finiteFiberCard g z * maximumFiberCardinalityOf f := by
      unfold compositeFiberCardSum
      calc
        (∑ y : FiniteFiber g z, finiteFiberCard f y.val) ≤
            ∑ _y : FiniteFiber g z, maximumFiberCardinalityOf f := by
          exact Finset.sum_le_sum fun _ _ => finiteFiberCard_le_maximum f _
        _ = finiteFiberCard g z * maximumFiberCardinalityOf f := by
          simp [finiteFiberCard]
    _ ≤ maximumFiberCardinalityOf g * maximumFiberCardinalityOf f := by
      exact Nat.mul_le_mul_right _ (finiteFiberCard_le_maximum g z)
    _ = maximumFiberCardinalityOf f * maximumFiberCardinalityOf g :=
      Nat.mul_comm _ _

/-- Universal maximum-fiber product bound for finite functions. -/
theorem maximumFiberCardinality_comp_le_mul
    {α : Type u} {β : Type v} {γ : Type w}
    [Fintype α] [Fintype β] [Fintype γ]
    (f : α → β) (g : β → γ) :
    maximumFiberCardinalityOf (g ∘ f) ≤
      maximumFiberCardinalityOf f * maximumFiberCardinalityOf g := by
  classical
  unfold maximumFiberCardinalityOf
  apply Finset.sup_le
  intro z _
  exact finiteFiberCard_comp_le_mul f g z

/-- Injectively restricting a function's source cannot enlarge its maximum
fiber. -/
theorem maximumFiberCardinality_precomp_le
    {α' : Type u} {α : Type v} {β : Type w}
    [Fintype α'] [Fintype α] [Fintype β]
    (e : α' → α) (he : Function.Injective e) (f : α → β) :
    maximumFiberCardinalityOf (f ∘ e) ≤ maximumFiberCardinalityOf f := by
  classical
  unfold maximumFiberCardinalityOf
  apply Finset.sup_le
  intro y _
  calc
    finiteFiberCard (f ∘ e) y ≤ finiteFiberCard f y := by
      unfold finiteFiberCard
      apply (Fintype.card_le_of_injective
        (fun x : FiniteFiber (f ∘ e) y =>
          (⟨e x.val, x.property⟩ : FiniteFiber f y)))
      intro x₁ x₂ h
      apply Subtype.ext
      apply he
      exact congrArg Subtype.val h
    _ ≤ (Finset.univ : Finset β).sup (finiteFiberCard f) :=
      Finset.le_sup (Finset.mem_univ y)

/-- Keeping a proof-carrying codomain cannot increase the maximum fiber over
the underlying codomain. -/
theorem maximumFiberCardinality_subtypeCodomain_le
    {α : Type u} {β : Type v} [Fintype α] [Fintype β]
    {P : β → Prop} [DecidablePred P] (f : α → {y : β // P y}) :
    maximumFiberCardinalityOf f ≤
      maximumFiberCardinalityOf (fun x => (f x).val) := by
  classical
  letI : DecidableEq {y : β // P y} := Classical.decEq _
  unfold maximumFiberCardinalityOf
  apply Finset.sup_le
  intro y _
  calc
    finiteFiberCard f y =
        finiteFiberCard (fun x => (f x).val) y.val := by
      unfold finiteFiberCard
      exact Fintype.card_congr
        { toFun := fun x => ⟨x.val, congrArg Subtype.val x.property⟩
          invFun := fun x => ⟨x.val, Subtype.ext x.property⟩
          left_inv := fun x => by apply Subtype.ext; rfl
          right_inv := fun x => by apply Subtype.ext; rfl }
    _ ≤ (Finset.univ : Finset β).sup
        (finiteFiberCard (fun x => (f x).val)) :=
      Finset.le_sup (Finset.mem_univ y.val)

/-- Inclusion of the composite domain into the first morphism's domain. -/
def compositeToFirstDomain
    {A : ARS.{u}} {B : ARS.{v}} {C : ARS.{w}}
    (F : PartialLicensedReductionMorphism A B)
    (G : PartialLicensedReductionMorphism B C) :
    DomainState (comp F G) → DomainState F :=
  fun x => ⟨x.val, x.property.1⟩

theorem compositeToFirstDomain_injective
    {A : ARS.{u}} {B : ARS.{v}} {C : ARS.{w}}
    (F : PartialLicensedReductionMorphism A B)
    (G : PartialLicensedReductionMorphism B C) :
    Function.Injective (compositeToFirstDomain F G) := by
  intro x y h
  apply Subtype.ext
  exact congrArg (fun q : DomainState F => q.val) h

/-- First-stage map restricted to states that survive both domains. -/
def compositeIntermediateMap
    {A : ARS.{u}} {B : ARS.{v}} {C : ARS.{w}}
    (F : PartialLicensedReductionMorphism A B)
    (G : PartialLicensedReductionMorphism B C) :
    DomainState (comp F G) → {y : B.Carrier // G.domain y} :=
  fun x =>
    ⟨F.map (compositeToFirstDomain F G x), x.property.2 x.property.1⟩

/-- The second morphism's state map on its actual domain. -/
def downstreamDomainMap
    {B : ARS.{v}} {C : ARS.{w}}
    (G : PartialLicensedReductionMorphism B C) :
    {y : B.Carrier // G.domain y} → C.Carrier :=
  G.map

/-- The restricted first-stage maximum is bounded by the original first-stage
maximum. -/
def compositeIntermediateMaximumFiber
    {A : ARS.{u}} {B : ARS.{v}} {C : ARS.{w}}
    [Fintype A.Carrier] [Fintype B.Carrier]
    (F : PartialLicensedReductionMorphism A B)
    (G : PartialLicensedReductionMorphism B C) : Nat := by
  classical
  exact maximumFiberCardinalityOf (compositeIntermediateMap F G)

theorem compositeIntermediate_maximumFiber_le
    {A : ARS.{u}} {B : ARS.{v}} {C : ARS.{w}}
    [Fintype A.Carrier] [Fintype B.Carrier]
    (F : PartialLicensedReductionMorphism A B)
    (G : PartialLicensedReductionMorphism B C) :
    compositeIntermediateMaximumFiber F G ≤
      maximumFiberCardinality F := by
  classical
  unfold compositeIntermediateMaximumFiber
  calc
    maximumFiberCardinalityOf (compositeIntermediateMap F G) ≤
        maximumFiberCardinalityOf
          (fun x => (compositeIntermediateMap F G x).val) :=
      maximumFiberCardinality_subtypeCodomain_le _
    _ = maximumFiberCardinalityOf
        (F.map ∘ compositeToFirstDomain F G) := rfl
    _ ≤ maximumFiberCardinalityOf F.map :=
      maximumFiberCardinality_precomp_le _
        (compositeToFirstDomain_injective F G) F.map
    _ = maximumFiberCardinality F := rfl

/-- Universal multiplicative state-fiber law for partial licensed morphisms. -/
theorem maximumFiberCardinality_comp_le
    {A : ARS.{u}} {B : ARS.{v}} {C : ARS.{w}}
    [Fintype A.Carrier] [Fintype B.Carrier] [Fintype C.Carrier]
    (F : PartialLicensedReductionMorphism A B)
    (G : PartialLicensedReductionMorphism B C) :
    maximumFiberCardinality (comp F G) ≤
      maximumFiberCardinality F * maximumFiberCardinality G := by
  classical
  calc
    maximumFiberCardinality (comp F G) =
        maximumFiberCardinalityOf
          (downstreamDomainMap G ∘ compositeIntermediateMap F G) := rfl
    _ ≤ maximumFiberCardinalityOf (compositeIntermediateMap F G) *
        maximumFiberCardinalityOf (downstreamDomainMap G) :=
      maximumFiberCardinality_comp_le_mul _ _
    _ ≤ maximumFiberCardinality F * maximumFiberCardinality G := by
      change compositeIntermediateMaximumFiber F G * maximumFiberCardinality G ≤
        maximumFiberCardinality F * maximumFiberCardinality G
      exact Nat.mul_le_mul (compositeIntermediate_maximumFiber_le F G) le_rfl

/-- The collapse fixture contains two distinct defined states with the same
image, so the fiber phenomenon is non-vacuous. -/
theorem pureStateCollapse_nontrivialFiber_fixture :
    ∃ x y : DomainState pureStateCollapse_fixture,
      x ≠ y ∧ pureStateCollapse_fixture.map x = pureStateCollapse_fixture.map y := by
  refine ⟨⟨ChainNode.source, trivial⟩, ⟨ChainNode.target, trivial⟩, ?_, rfl⟩
  intro h
  have hval := congrArg Subtype.val h
  cases hval

#check @compositeFiberEquiv
#check @compositeFiberCardSum
#check @finiteFiberCard_comp_eq_sum
#check @maximumFiberCardinality_comp_le_mul
#check @maximumFiberCardinality_comp_le
#check pureStateCollapse_nontrivialFiber_fixture
#print axioms compositeFiberEquiv
#print axioms finiteFiberCard_comp_eq_sum
#print axioms maximumFiberCardinality_comp_le_mul
#print axioms maximumFiberCardinality_comp_le
#print axioms pureStateCollapse_nontrivialFiber_fixture

end
end PartialLicensedReductionMorphism
end OperatorKO7.Meta.LicensedBoundaryCalculus
