import OperatorKO7.Meta.OperationalInexpressibility.DefinitionUnification

/-!
# The Beth property of a proof language

A target licensed by the observer is implicitly defined; a derivable statement that denotes it
defines it explicitly. In a sound language every explicitly defined target is licensed. A target
without explicit definition is either unlicensed or a failure of the Beth property. A complete
language closed under post-composition has the Beth property. Completeness and post-composition
closure are each necessary: each of the two necessity fixtures keeps soundness, the nonempty
answer type, and the other hypothesis.

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

/-- The language of constant functions on `Bool`: each statement `b : Bool` denotes the
constant function with value `b`, every statement is derivable, and the observer, dimension and
target are the identity of `Bool`.

Proves: nothing (definition).
Does not prove: any property; see `beth_complete_is_required`.
Relation: denotation and observer kernel. Closure: not applicable. Strategy: not applicable.
Trust: kernel only. Scope: this one fixture on `Bool`. -/
def constantFunctionLanguage : ObservedLanguage.{0, 0, 0, 0, 0} where
  World := Bool
  Statement := Bool
  Observation := Bool
  Dimension := Bool
  Verdict := Bool
  denotes := fun b _ => b
  derivable := fun _ => True
  observe := id
  dimension := id
  target := id
  sameContext := fun _ _ => True

/-- **Completeness is required** for the Beth property, with every other hypothesis of
`bethPropertyOn_of_complete` kept: the constant-function language is sound, closed under
post-composition, and has a nonempty answer type; it is not complete, and the identity target
is licensed and not explicitly defined.

Proves: `Sound ∧ PostcompositionClosed ∧ Nonempty Verdict ∧ ¬ Complete ∧
¬ BethPropertyOn (fun _ => True)` for `constantFunctionLanguage`.
Does not prove: failure of the Beth property on a restricted class of targets.
Relation: denotation and observer kernel. Closure: not applicable. Strategy: not applicable.
Trust: kernel only. Scope: this one fixture (Theorem `thm:beth-gap`(c), necessity of
completeness). -/
theorem beth_complete_is_required :
    constantFunctionLanguage.Sound ∧ constantFunctionLanguage.PostcompositionClosed ∧
      Nonempty constantFunctionLanguage.Verdict ∧ ¬ constantFunctionLanguage.Complete ∧
      ¬ constantFunctionLanguage.BethPropertyOn fun _ => True := by
  refine ⟨fun _ _ _ _ _ => rfl, fun ψ _ g => ⟨g ψ, trivial, fun _ => rfl⟩,
    ⟨(false : Bool)⟩, ?_, ?_⟩
  · rintro ⟨ψ, -, hsep⟩
    exact Bool.noConfusion (hsep false true rfl)
  · intro h
    have hlic : Licensed constantFunctionLanguage.observe (fun w => w) := fun _ _ hxy => hxy
    obtain ⟨ψ, -, hden⟩ := h (fun w => w) trivial hlic
    have h0 : ψ = false := hden false
    have h1 : ψ = true := hden true
    rw [h0] at h1
    exact Bool.noConfusion h1

/-- **The constant-statement language drops two hypotheses at once.** Its one statement denotes
the constant `false`, so the language is neither complete nor closed under post-composition,
and the Beth property fails. This fixture does not separate completeness from post-composition
closure; `beth_complete_is_required` does.

Proves: `¬ Complete ∧ ¬ PostcompositionClosed ∧ ¬ BethPropertyOn (fun _ => True)` for
`constantStatementLanguage`.
Does not prove: necessity of completeness alone.
Relation: denotation and observer kernel. Closure: not applicable. Strategy: not applicable.
Trust: kernel only. Scope: this one fixture. -/
theorem constantStatement_beth_fails_without_complete_and_postcomposition :
    ¬ constantStatementLanguage.Complete ∧ ¬ constantStatementLanguage.PostcompositionClosed ∧
      ¬ constantStatementLanguage.BethPropertyOn fun _ => True := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, _, hsep⟩
    exact Bool.noConfusion (hsep false true rfl)
  · intro h
    obtain ⟨ψ', -, hden⟩ := h () trivial (fun b => !b)
    exact Bool.noConfusion (hden true)
  · intro h
    have hlic : Licensed constantStatementLanguage.observe (fun w => w) := fun _ _ hxy => hxy
    obtain ⟨ψ, -, hden⟩ := h (fun w => w) trivial hlic
    exact Bool.noConfusion (hden true)

/-- **Post-composition is required** for the Beth property, with every other hypothesis of
`bethPropertyOn_of_complete` kept: the identity-statement language (defined in
`DefinitionUnification.lean`) is sound, complete, and has a nonempty answer type; it is not
closed under post-composition, and negation is licensed and not explicitly defined.

Proves: `Sound ∧ Complete ∧ Nonempty Verdict ∧ ¬ PostcompositionClosed ∧
¬ BethPropertyOn (fun _ => True)` for `identityStatementLanguage`.
Does not prove: failure of the Beth property on a restricted class of targets.
Relation: denotation and observer kernel. Closure: not applicable. Strategy: not applicable.
Trust: kernel only. Scope: this one fixture (Theorem `thm:beth-gap`(c), necessity of
post-composition closure). -/
theorem beth_postcomposition_is_required :
    identityStatementLanguage.Sound ∧ identityStatementLanguage.Complete ∧
      Nonempty identityStatementLanguage.Verdict ∧
      ¬ identityStatementLanguage.PostcompositionClosed ∧
      ¬ identityStatementLanguage.BethPropertyOn fun _ => True := by
  obtain ⟨hsound, hcomplete, -⟩ := identityStatement_unification_hypotheses
  refine ⟨hsound, hcomplete, ⟨(false : Bool)⟩, ?_, ?_⟩
  · intro h
    obtain ⟨ψ', -, hden⟩ := h () trivial (fun b => !b)
    exact Bool.noConfusion (hden false)
  · intro h
    have hlic : Licensed identityStatementLanguage.observe (fun w => !w) := by
      intro x y hxy
      have hxy' : x = y := hxy
      rw [hxy']
    obtain ⟨ψ, -, hden⟩ := h (fun w => !w) trivial hlic
    exact Bool.noConfusion (hden false)

end ObservedLanguage

end OperatorKO7.Meta.OperationalInexpressibility.DefinitionUnification
