/-!
This module defines an abstract confession-move interface together with refinement and
mutual-refinement relations. Every result is conditional on the fields supplied by an
inhabitant; route coverage requires separate instances.




-/

namespace OperatorKO7.Meta.GenericConfessionMove

universe u v w z

/-- Data record whose requirements are the fields displayed below.
-/
structure GenericConfessionMove
    (X : Type u)
    (P : X → Prop)
    (License : Type v) where
  licenseWitness : License
  sourceBarrier : X → Prop
  Quotient : Type w
  projection : X → Quotient
  residualObstruction : Quotient → Prop
  Certificate : Type z
  certificateOf : Quotient → Certificate
  verifier : Certificate → Prop
  verifier_sound : ∀ q, verifier (certificateOf q) → residualObstruction q
  barrier_covers_residual : ∀ x, residualObstruction (projection x) → sourceBarrier x
  soundness : ∀ x, residualObstruction (projection x) → P x
  verdictSufficient : ∀ x x', projection x = projection x' → (P x ↔ P x')

namespace GenericConfessionMove

variable {X : Type u} {P : X → Prop} {License : Type v}

/-- The displayed proposition follows from the stated hypotheses.
-/
theorem certificate_projects_residual
  (M : GenericConfessionMove X P License)
    {q : M.Quotient}
    (h : M.verifier (M.certificateOf q)) :
    M.residualObstruction q :=
  M.verifier_sound q h

/-- The displayed proposition follows from the stated hypotheses. -/
theorem residual_projects_sourceBarrier
  (M : GenericConfessionMove X P License)
    {x : X}
    (h : M.residualObstruction (M.projection x)) :
    M.sourceBarrier x :=
  M.barrier_covers_residual x h

/-- The displayed proposition follows from the stated hypotheses. -/
theorem residual_implies_verdict
  (M : GenericConfessionMove X P License)
    {x : X}
    (h : M.residualObstruction (M.projection x)) :
    P x :=
  M.soundness x h

/-- Data record whose requirements are the fields displayed below. -/
structure RefinementWitness
  {License1 : Type v} {License2 : Type w}
  (M₁ : GenericConfessionMove X P License1)
  (M₂ : GenericConfessionMove X P License2) where
  factor : M₁.Quotient → M₂.Quotient
  commutes : ∀ x, factor (M₁.projection x) = M₂.projection x

/-- Abbreviation for the displayed type.

-/
abbrev Refines
  {License1 : Type v} {License2 : Type w}
  (M₁ : GenericConfessionMove X P License1)
  (M₂ : GenericConfessionMove X P License2) : Prop :=
  Nonempty (RefinementWitness M₁ M₂)

/-- The displayed proposition follows from the stated hypotheses. -/
theorem RefinementWitness.projects_projection
  {License1 : Type v} {License2 : Type w}
  {M₁ : GenericConfessionMove X P License1}
  {M₂ : GenericConfessionMove X P License2}
    (h : RefinementWitness M₁ M₂) (x : X) :
    h.factor (M₁.projection x) = M₂.projection x :=
  h.commutes x

/-- The displayed proposition follows from the stated hypotheses.
-/
theorem Refines.projects_projection
  {License1 : Type v} {License2 : Type w}
  {M₁ : GenericConfessionMove X P License1}
  {M₂ : GenericConfessionMove X P License2}
    (h : Refines M₁ M₂) (x : X) :
    ∃ factor : M₁.Quotient → M₂.Quotient,
      factor (M₁.projection x) = M₂.projection x := by
  rcases h with ⟨h⟩
  exact ⟨h.factor, h.projects_projection x⟩

/-- The displayed proposition follows from the stated hypotheses. -/
theorem Refines.refl
  {License1 : Type v}
  (M : GenericConfessionMove X P License1) : Refines M M := by
  exact ⟨{
    factor := id
    commutes := by
      intro x
      rfl
  }⟩

/-- The displayed proposition follows from the stated hypotheses. -/
theorem Refines.trans
  {License1 : Type v} {License2 : Type w} {License3 : Type z}
  {M₁ : GenericConfessionMove X P License1}
  {M₂ : GenericConfessionMove X P License2}
  {M₃ : GenericConfessionMove X P License3}
    (h₁₂ : Refines M₁ M₂)
    (h₂₃ : Refines M₂ M₃) : Refines M₁ M₃ := by
  rcases h₁₂ with ⟨h₁₂⟩
  rcases h₂₃ with ⟨h₂₃⟩
  exact ⟨{
    factor := h₂₃.factor ∘ h₁₂.factor
    commutes := by
      intro x
      calc
        (h₂₃.factor ∘ h₁₂.factor) (M₁.projection x) = h₂₃.factor (h₁₂.factor (M₁.projection x)) := by
          rfl
        _ = h₂₃.factor (M₂.projection x) := by
          rw [h₁₂.commutes x]
        _ = M₃.projection x := h₂₃.commutes x
  }⟩

/-- Data record whose requirements are the fields displayed below. -/
structure HEquivalenceWitness
  {License1 : Type v} {License2 : Type w}
  (M₁ : GenericConfessionMove X P License1)
  (M₂ : GenericConfessionMove X P License2) where
  forward : RefinementWitness M₁ M₂
  backward : RefinementWitness M₂ M₁

/-- Abbreviation for the displayed type. -/
abbrev HEquivalent
  {License1 : Type v} {License2 : Type w}
  (M₁ : GenericConfessionMove X P License1)
  (M₂ : GenericConfessionMove X P License2) : Prop :=
  Nonempty (HEquivalenceWitness M₁ M₂)

/-- The displayed proposition follows from the stated hypotheses. -/
theorem HEquivalent.refl
  {License1 : Type v}
  (M : GenericConfessionMove X P License1) : HEquivalent M M := by
  exact ⟨{
    forward := {
      factor := id
      commutes := by
        intro x
        rfl
    }
    backward := {
      factor := id
      commutes := by
        intro x
        rfl
    }
  }⟩

/-- The displayed proposition follows from the stated hypotheses. -/
theorem HEquivalent.symm
  {License1 : Type v} {License2 : Type w}
  {M₁ : GenericConfessionMove X P License1}
  {M₂ : GenericConfessionMove X P License2}
    (h : HEquivalent M₁ M₂) : HEquivalent M₂ M₁ := by
  rcases h with ⟨h⟩
  exact ⟨{
    forward := h.backward
    backward := h.forward
  }⟩

/-- The displayed proposition follows from the stated hypotheses. -/
theorem HEquivalent.trans
  {License1 : Type v} {License2 : Type w} {License3 : Type z}
  {M₁ : GenericConfessionMove X P License1}
  {M₂ : GenericConfessionMove X P License2}
  {M₃ : GenericConfessionMove X P License3}
    (h₁₂ : HEquivalent M₁ M₂)
    (h₂₃ : HEquivalent M₂ M₃) : HEquivalent M₁ M₃ := by
  rcases h₁₂ with ⟨h₁₂⟩
  rcases h₂₃ with ⟨h₂₃⟩
  exact ⟨{
    forward := Classical.choice (Refines.trans ⟨h₁₂.forward⟩ ⟨h₂₃.forward⟩)
    backward := Classical.choice (Refines.trans ⟨h₂₃.backward⟩ ⟨h₁₂.backward⟩)
  }⟩

/-- The displayed proposition follows from the stated hypotheses.
-/
theorem Refines.projection_eq_of_projection_eq
  {License1 : Type v} {License2 : Type w}
  {M₁ : GenericConfessionMove X P License1}
  {M₂ : GenericConfessionMove X P License2}
    (h : Refines M₁ M₂)
    {x x' : X}
    (hp : M₁.projection x = M₁.projection x') :
    M₂.projection x = M₂.projection x' := by
  rcases h with ⟨h⟩
  calc
    M₂.projection x = h.factor (M₁.projection x) := by
      symm
      exact h.commutes x
    _ = h.factor (M₁.projection x') := by simp [hp]
    _ = M₂.projection x' := h.commutes x'

/-- The displayed proposition follows from the stated hypotheses.
-/
theorem Refines.transport_verdict
  {License1 : Type v} {License2 : Type w}
  {M₁ : GenericConfessionMove X P License1}
  {M₂ : GenericConfessionMove X P License2}
    (h : Refines M₁ M₂)
    {x x' : X}
    (hp : M₁.projection x = M₁.projection x') :
    P x ↔ P x' :=
  M₂.verdictSufficient x x' (h.projection_eq_of_projection_eq hp)

end GenericConfessionMove

end OperatorKO7.Meta.GenericConfessionMove
