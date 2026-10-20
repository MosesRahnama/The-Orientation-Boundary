import OperatorKO7.Meta.OperationalInexpressibility.DefinitionUnification

/-!
# The Beth property of a proof language

A target licensed by the observer is implicitly defined; a derivable statement that denotes it
defines it explicitly. In a sound language every explicitly defined target is licensed. A target
without explicit definition is either unlicensed or a failure of the Beth property. A complete
language closed under post-composition has the Beth property.

Relation: denotation of derivable statements; the license of the observer.
Property: Padoa direction, gap decomposition, Beth property from completeness.
Trust: kernel only; the post-composition construction is classical.
Scope: arbitrary observed languages in independent universes.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.OperationalInexpressibility.DefinitionUnification

open OperatorKO7.Meta.OperationalInexpressibility.ObserverKernel
open OperatorKO7.Meta.OperationalInexpressibility.LicenseCriterion

universe uW uS uO uD uV

namespace ObservedLanguage

variable (L : ObservedLanguage.{uW, uS, uO, uD, uV})

/-- A derivable statement denotes the verdict map `P`. -/
def ExplicitlyDefines (P : L.World → L.Verdict) : Prop :=
  ∃ ψ, L.derivable ψ ∧ ∀ w, L.denotes ψ w = P w

/-- The Beth property on the class `C`: implicit definition gives explicit definition. -/
def BethPropertyOn (C : (L.World → L.Verdict) → Prop) : Prop :=
  ∀ P, C P → Licensed L.observe P → L.ExplicitlyDefines P

/-- Derivable statements compose with every map of verdicts. -/
def PostcompositionClosed : Prop :=
  ∀ ψ, L.derivable ψ → ∀ g : L.Verdict → L.Verdict,
    ∃ ψ', L.derivable ψ' ∧ ∀ w, L.denotes ψ' w = g (L.denotes ψ w)

variable {L}

/-- **Padoa direction.** -/
theorem licensed_of_explicitlyDefines (hsound : L.Sound) {P : L.World → L.Verdict}
    (h : L.ExplicitlyDefines P) : Licensed L.observe P := by
  obtain ⟨ψ, hψ, hden⟩ := h
  intro x y hxy
  rw [← hden x, ← hden y]
  exact hsound ψ hψ hxy

/-- **The gap splits into unlicensed targets and Beth failures.** -/
theorem not_explicitlyDefines_iff (hsound : L.Sound) (P : L.World → L.Verdict) :
    ¬ L.ExplicitlyDefines P ↔
      ¬ Licensed L.observe P ∨ (Licensed L.observe P ∧ ¬ L.ExplicitlyDefines P) := by
  by_cases h : Licensed L.observe P
  · constructor
    · intro h1
      exact Or.inr ⟨h, h1⟩
    · rintro (h1 | ⟨-, h1⟩)
      · exact False.elim (absurd h h1)
      · exact h1
  · constructor
    · intro _
      exact Or.inl h
    · rintro (h1 | ⟨h1, -⟩)
      · intro hdef
        exact h1 (licensed_of_explicitlyDefines hsound hdef)
      · exact False.elim (absurd h1 h)

theorem not_explicitlyDefines_iff_not_licensed (hsound : L.Sound)
    {C : (L.World → L.Verdict) → Prop} (hbeth : L.BethPropertyOn C) {P : L.World → L.Verdict}
    (hC : C P) : ¬ L.ExplicitlyDefines P ↔ ¬ Licensed L.observe P := by
  constructor
  · intro hdef hlic
    exact hdef (hbeth P hC hlic)
  · intro hlic hdef
    exact hlic (licensed_of_explicitlyDefines hsound hdef)

/-- **Completeness and post-composition give the Beth property.** -/
theorem bethPropertyOn_of_complete [Nonempty L.Verdict] (hcomplete : L.Complete)
    (hclosed : L.PostcompositionClosed) : L.BethPropertyOn fun _ => True := by
  classical
  obtain ⟨ψ, hψ, hsep⟩ := hcomplete
  intro P _ hP
  let g : L.Verdict → L.Verdict := fun v => if h : ∃ w, L.denotes ψ w = v then
    P (Classical.choose h) else Classical.arbitrary L.Verdict
  obtain ⟨ψ', hψ', hden⟩ := hclosed ψ hψ g
  refine ⟨ψ', hψ', fun w => ?_⟩
  rw [hden]
  dsimp only [g]
  have hex : ∃ w', L.denotes ψ w' = L.denotes ψ w := ⟨w, rfl⟩
  rw [dif_pos hex]
  exact hP (Classical.choose hex) w (hsep (Classical.choose hex) w (Classical.choose_spec hex))

/-- **Soundness is required** for the Padoa direction. -/
theorem padoa_sound_is_required :
    unsoundStatementLanguage.ExplicitlyDefines (fun w => w) ∧
      ¬ Licensed unsoundStatementLanguage.observe (fun w => w) := by
  constructor
  · exact ⟨(), trivial, fun _ => rfl⟩
  · intro h
    exact absurd (h (false, false) (false, true) rfl) (fun hc => by cases hc)

/-- **Completeness is required** for the Beth property. -/
theorem beth_complete_is_required :
    ¬ constantStatementLanguage.BethPropertyOn fun _ => True := by
  intro h
  have hlic : Licensed constantStatementLanguage.observe (fun w => w) := fun _ _ hxy => hxy
  obtain ⟨ψ, -, hden⟩ := h (fun w => w) trivial hlic
  exact Bool.noConfusion (hden true)

/-- A complete language whose only statement denotes the identity of `Bool`. -/
def identityStatementLanguage : ObservedLanguage.{0, 0, 0, 0, 0} where
  World := Bool
  Statement := Unit
  Observation := Bool
  Dimension := Bool
  Verdict := Bool
  denotes := fun _ w => w
  derivable := fun _ => True
  observe := id
  dimension := id
  target := id
  sameContext := fun _ _ => True

/-- **Post-composition is required**: negation is licensed and not explicitly defined. -/
theorem beth_postcomposition_is_required :
    identityStatementLanguage.Complete ∧ ¬ identityStatementLanguage.BethPropertyOn fun _ => True := by
  constructor
  · exact ⟨(), trivial, fun _ _ h => h⟩
  · intro h
    have hlic : Licensed identityStatementLanguage.observe (fun w => !w) := by
      intro x y hxy
      have hxy' : x = y := hxy
      rw [hxy']
    obtain ⟨ψ, -, hden⟩ := h (fun w => !w) trivial hlic
    exact Bool.noConfusion (hden false)

end ObservedLanguage

end OperatorKO7.Meta.OperationalInexpressibility.DefinitionUnification
