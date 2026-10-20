import OperatorKO7.Meta.Decision.EchoStoppingMDP

/-!
# The finite-horizon Snell envelope

The Bellman values of a finite-horizon stopping model are the least sequence that dominates the
stopping value and every legal continuation one horizon down, they are the greatest expected
returns of adaptive policies, and the rule that stops where the value meets the stopping value
attains them.

Relation: pointwise order of value sequences.
Property: least excessive majorant; attainment by the envelope stopping rule.
Trust: kernel only; action choice is classical.
Scope: arbitrary state and action types with decidable equality; real rewards.
-/

set_option autoImplicit false

open scoped BigOperators

namespace OperatorKO7.Meta.OperationalInexpressibility.SnellEnvelope

open OperatorKO7.Meta.Decision.EchoStopping.Stochastic

universe u v

variable {S : Type u} {A : Type v} [DecidableEq S] [DecidableEq A]

/-- A value sequence dominating stopping at every horizon and every legal continuation. -/
def IsExcessiveMajorant (M : Model S A) (W : ℕ → S → ℝ) : Prop :=
  (∀ s, M.stopValue s ≤ W 0 s) ∧
    ∀ n s, M.stopValue s ≤ W (n + 1) s ∧ ∀ a ∈ M.actions s, expected M (W n) s a ≤ W (n + 1) s

theorem value_isExcessiveMajorant (M : Model S A) : IsExcessiveMajorant M (value M) := by
  constructor
  · intro s
    rfl
  · intro n s
    exact ⟨stop_le_bellman M (value M n) s,
      fun a ha => expected_le_bellman M (value M n) ha⟩

theorem value_le_of_isExcessiveMajorant (M : Model S A) {W : ℕ → S → ℝ}
    (hW : IsExcessiveMajorant M W) : ∀ n s, value M n s ≤ W n s := by
  intro n
  induction n with
  | zero =>
      intro s
      exact hW.1 s
  | succ n ih =>
      intro s
      show (choices M s).sup' (choices_nonempty M s) (choiceValue M (value M n) s) ≤ W (n + 1) s
      apply Finset.sup'_le
      intro c hc
      rcases c with _ | a
      · exact (hW.2 n s).1
      · have ha : a ∈ M.actions s := by
          have hc' : some a ∈ (M.actions s).image some := by
            rw [choices] at hc
            rcases Finset.mem_insert.1 hc with h | h
            · exact absurd h (by simp)
            · exact h
          obtain ⟨b, hb, hsome⟩ := Finset.mem_image.1 hc'
          cases hsome
          exact hb
        exact (expected_mono M ha (fun t _ => ih t)).trans ((hW.2 n s).2 a ha)

/-- **Finite-horizon Snell envelope.** -/
theorem value_isLeast_excessiveMajorant (M : Model S A) :
    IsExcessiveMajorant M (value M) ∧
      ∀ W, IsExcessiveMajorant M W → ∀ n s, value M n s ≤ W n s :=
  ⟨value_isExcessiveMajorant M, fun _ hW => value_le_of_isExcessiveMajorant M hW⟩

theorem exists_action_of_value_ne_stop (M : Model S A) {n : ℕ} {s : S}
    (h : value M (n + 1) s ≠ M.stopValue s) :
    ∃ a ∈ M.actions s, expected M (value M n) s a = value M (n + 1) s := by
  obtain ⟨c, hc, hceq⟩ := Finset.exists_mem_eq_sup' (choices_nonempty M s)
    (choiceValue M (value M n) s)
  have hcval : value M (n + 1) s = choiceValue M (value M n) s c := hceq
  rcases c with _ | a
  · exact (h hcval).elim
  · refine ⟨a, ?_, ?_⟩
    · have ha : a ∈ M.actions s := by
        have hc' : some a ∈ (M.actions s).image some := by
          rw [choices] at hc
          rcases Finset.mem_insert.1 hc with h' | h'
          · exact absurd h' (by simp)
          · exact h'
        obtain ⟨b, hb, hsome⟩ := Finset.mem_image.1 hc'
        cases hsome
        exact hb
      exact ha
    · exact hcval.symm

/-- The envelope stopping rule: stop exactly where the value meets the stopping value. -/
noncomputable def envelopePolicy (M : Model S A) : (n : ℕ) → (s : S) → Policy M n s
  | 0, s => Policy.stop 0 s
  | n + 1, s =>
      if h : value M (n + 1) s = M.stopValue s then Policy.stop (n + 1) s
      else
        Policy.compute s (Classical.choose (exists_action_of_value_ne_stop M h))
          (Classical.choose_spec (exists_action_of_value_ne_stop M h)).1
          (fun t => envelopePolicy M n t)

/-- **The envelope stopping rule attains the value.** -/
theorem envelopePolicy_value (M : Model S A) (n : ℕ) (s : S) :
    (envelopePolicy M n s).value = value M n s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      rw [envelopePolicy]
      by_cases h : value M (n + 1) s = M.stopValue s
      · rw [dif_pos h]
        exact h.symm
      · rw [dif_neg h]
        simp only [Policy.value]
        rw [expected_congr M (fun t _ => ih t)]
        exact (Classical.choose_spec (exists_action_of_value_ne_stop M h)).2

theorem envelopePolicy_stops_iff (M : Model S A) (n : ℕ) (s : S) :
    envelopePolicy M (n + 1) s = Policy.stop (n + 1) s ↔ value M (n + 1) s = M.stopValue s := by
  rw [envelopePolicy]
  by_cases h : value M (n + 1) s = M.stopValue s
  · rw [dif_pos h]
    exact ⟨fun _ => h, fun _ => rfl⟩
  · rw [dif_neg h]
    constructor
    · intro hcon
      cases hcon
    · intro hcon
      exact absurd hcon h

end OperatorKO7.Meta.OperationalInexpressibility.SnellEnvelope
