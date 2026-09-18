import OperatorKO7.Meta.DistinctionBoundary.DynamicDiagonalGrade

set_option autoImplicit false

/-!
# Transport prerequisites for dynamic diagonal grades

The module states the transport laws used by the diagonal-grade crown.
Static distinction moves along an observer factorization. Persistent distinction
reflects along a one-step simulation and transports along a one-step lifting.
D2 transport between comparator languages requires an explicit code map whose
denotation commutes.

Relation: caller-supplied one-step relations.
Closure: `Relation.ReflTransGen`.
Strategy: not applicable.
External trust: none.
-/

namespace OperatorKO7.Meta.DistinctionBoundary.DynamicDiagonalGradeTransport

open OperatorKO7.Meta.DistinctionBoundary.DynamicDiagonalGrade

variable {α β γ : Type}

/-- The source observer factors through the state map and target observer. -/
def ObserverFactorsThrough (f : α → β) (q : α → γ) (q' : β → γ) : Prop :=
  ∀ x, q x = q' (f x)

/-- One-step forward simulation of a relation by a state map. -/
def StepSimulation (f : α → β) (R : α → α → Prop) (S : β → β → Prop) : Prop :=
  ∀ ⦃x y⦄, R x y → S (f x) (f y)

/-- One-step lifting of every target step leaving an image point. -/
def StepLifting (f : α → β) (R : α → α → Prop) (S : β → β → Prop) : Prop :=
  ∀ ⦃x : α⦄ ⦃y' : β⦄, S (f x) y' → ∃ y : α, R x y ∧ f y = y'

/-- A one-step simulation maps every reflexive-transitive source path. -/
theorem stepSimulation_reflTransGen
    {f : α → β} {R : α → α → Prop} {S : β → β → Prop}
    (hsim : StepSimulation f R S) {x y : α}
    (h : Relation.ReflTransGen R x y) :
    Relation.ReflTransGen S (f x) (f y) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      exact Relation.ReflTransGen.tail ih (hsim hstep)

/-- A one-step lifting lifts every reflexive-transitive target path starting in
an image point. -/
theorem stepLifting_reflTransGen
    {f : α → β} {R : α → α → Prop} {S : β → β → Prop}
    (hlift : StepLifting f R S) {x : α} {y' : β}
    (h : Relation.ReflTransGen S (f x) y') :
    ∃ y : α, Relation.ReflTransGen R x y ∧ f y = y' := by
  induction h with
  | refl => exact ⟨x, Relation.ReflTransGen.refl, rfl⟩
  | @tail y z hpre hstep ih =>
      obtain ⟨m, hm, hfm⟩ := ih
      have hstep' : S (f m) z := by simpa [hfm] using hstep
      obtain ⟨n, hmn, hfn⟩ := hlift hstep'
      exact ⟨n, Relation.ReflTransGen.tail hm hmn, hfn⟩

/-- Static distinction transports along an observer factorization. -/
theorem d1s_transport_of_observerFactor
    {f : α → β} {q : α → γ} {q' : β → γ} {x y : α}
    (hfac : ObserverFactorsThrough f q q')
    (h : D1s q x y) : D1s q' (f x) (f y) := by
  intro heq
  apply h
  calc
    q x = q' (f x) := hfac x
    _ = q' (f y) := heq
    _ = q y := (hfac y).symm

/-- Static distinction reflects along the same observer factorization. -/
theorem d1s_reflect_of_observerFactor
    {f : α → β} {q : α → γ} {q' : β → γ} {x y : α}
    (hfac : ObserverFactorsThrough f q q')
    (h : D1s q' (f x) (f y)) : D1s q x y := by
  intro heq
  apply h
  calc
    q' (f x) = q x := (hfac x).symm
    _ = q y := heq
    _ = q' (f y) := hfac y

/-- Persistent distinction reflects from the target along a one-step
simulation and an observer factorization. -/
theorem d1p_reflect_of_stepSimulation
    {f : α → β} {R : α → α → Prop} {S : β → β → Prop}
    {q : α → γ} {q' : β → γ} {x y : α}
    (hfac : ObserverFactorsThrough f q q')
    (hsim : StepSimulation f R S)
    (h : D1p S q' (f x) (f y)) : D1p R q x y := by
  intro x' y' hx hy
  have hx' := stepSimulation_reflTransGen hsim hx
  have hy' := stepSimulation_reflTransGen hsim hy
  have hsep := h (f x') (f y') hx' hy'
  intro heq
  apply hsep
  calc
    q' (f x') = q x' := (hfac x').symm
    _ = q y' := heq
    _ = q' (f y') := hfac y'

/-- Persistent distinction transports to the target when target paths lift to
source paths and the observer factors through the state map. -/
theorem d1p_transport_of_stepLifting
    {f : α → β} {R : α → α → Prop} {S : β → β → Prop}
    {q : α → γ} {q' : β → γ} {x y : α}
    (hfac : ObserverFactorsThrough f q q')
    (hlift : StepLifting f R S)
    (h : D1p R q x y) : D1p S q' (f x) (f y) := by
  intro x' y' hx hy
  obtain ⟨sx, hsx, hfx⟩ := stepLifting_reflTransGen hlift hx
  obtain ⟨sy, hsy, hfy⟩ := stepLifting_reflTransGen hlift hy
  have hsep := h sx sy hsx hsy
  intro heq
  apply hsep
  calc
    q sx = q' (f sx) := hfac sx
    _ = q' x' := by rw [hfx]
    _ = q' y' := heq
    _ = q' (f sy) := by rw [hfy]
    _ = q sy := (hfac sy).symm

/-- A predicate is represented by a concrete code and denotation function. -/
def RepresentedBy (Code : Type) (denote : Code → α → α → Prop)
    (cmp : α → α → Prop) : Prop :=
  ∃ code : Code, denote code = cmp

/-- A code map preserves denotation extensionally. -/
def CodeDenotationPreserving
    {Code₁ Code₂ : Type}
    (mapCode : Code₁ → Code₂)
    (denote₁ : Code₁ → α → α → Prop)
    (denote₂ : Code₂ → α → α → Prop) : Prop :=
  ∀ code, denote₂ (mapCode code) = denote₁ code

/-- D2 transports between comparator languages only through an explicit code
map with a denotation-preservation law. The state relation and observer are held
fixed here, isolating the representation-language obligation. -/
theorem d2At_transport_codeDenotation
    {Code₁ Code₂ : Type}
    {denote₁ : Code₁ → α → α → Prop}
    {denote₂ : Code₂ → α → α → Prop}
    (mapCode : Code₁ → Code₂)
    (hmap : CodeDenotationPreserving mapCode denote₁ denote₂)
    {R : α → α → Prop} {q : α → γ} {x y : α}
    (h : D2At (RepresentedBy Code₁ denote₁) R q x y) :
    D2At (RepresentedBy Code₂ denote₂) R q x y := by
  refine ⟨h.1, ?_⟩
  rcases h.2 with ⟨cmp, ⟨code, hcode⟩, hcmp⟩
  refine ⟨cmp, ⟨mapCode code, ?_⟩, hcmp⟩
  exact (hmap code).trans hcode

#check @ObserverFactorsThrough
#check @StepSimulation
#check @StepLifting
#check @stepSimulation_reflTransGen
#check @stepLifting_reflTransGen
#check @d1s_transport_of_observerFactor
#check @d1s_reflect_of_observerFactor
#check @d1p_reflect_of_stepSimulation
#check @d1p_transport_of_stepLifting
#check @RepresentedBy
#check @CodeDenotationPreserving
#check @d2At_transport_codeDenotation

#print axioms ObserverFactorsThrough
#print axioms StepSimulation
#print axioms StepLifting
#print axioms stepSimulation_reflTransGen
#print axioms stepLifting_reflTransGen
#print axioms d1s_transport_of_observerFactor
#print axioms d1s_reflect_of_observerFactor
#print axioms d1p_reflect_of_stepSimulation
#print axioms d1p_transport_of_stepLifting
#print axioms RepresentedBy
#print axioms CodeDenotationPreserving
#print axioms d2At_transport_codeDenotation

end OperatorKO7.Meta.DistinctionBoundary.DynamicDiagonalGradeTransport
