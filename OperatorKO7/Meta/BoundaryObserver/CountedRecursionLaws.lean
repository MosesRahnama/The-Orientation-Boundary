import OperatorKO7.Meta.BoundaryObserver.BoundaryPole

set_option autoImplicit false

/-!
# The three counted-recursion laws

V1 L5. The carrier of the content is arbitrary, with full universe scope.
The zero-information statement concerns actual finite-law protocols, including
adaptive policies and every history bank, with no positive-cost premise.

All entropy is in natural units before division by Real.log 2.
-/

namespace OperatorKO7.Meta.BoundaryObserver.CountedRecursionLaws

universe u

open scoped BigOperators
open OperatorKO7.Meta.BoundaryObserver.RecursorDecidability
open OperatorKO7.Meta.BoundaryObserver.BoundaryPole
open OperatorKO7.Meta.BoundaryObserver.ProtocolResolution
open OperatorKO7.Meta.BoundaryObserver.BoundarySingularity
open OperatorKO7.Meta.BoundaryObserver.PairResolution

noncomputable section

/-- The content-determined rows of an arbitrary adaptive protocol have no
information about two counted states of the same content, at any horizon or in
the information limit. The two pass counts need not be distinct. -/
theorem countedRecursion_adaptive_zero_information {T : Type u} (R : T) (j k : ℕ)
    {A Y : Type} [Fintype A] [Fintype Y] (p : FiniteProtocol Bool A Y)
    (K : List (A × Y) → A → Reading (T × ℕ) Y)
    (hdet : ∀ h a, RecordDetermined (content (T := T)) (K h a))
    (hobs : ∀ h a b,
      p.observation h a b = K h a (if b then (R, j) else (R, k))) :
    (∀ n bank, HistoryBank n bank → terminalMI p n bank = 0) ∧
      informationLimit p = 0 := by
  have hread : ∀ h a b, p.observation h a b = K h a (R, j) := by
    intro h a b
    rw [hobs h a b]
    cases b with
    | false => exact hdet h a (R, k) (R, j) rfl
    | true => rfl
  have hcap : LocalCapacityBound p 0 := by
    intro h a hw _ _
    have hrow :
        (fun zy : Bool × Y =>
          posterior p h zy.1 * (p.observation h a zy.1).mass zy.2) =
        (fun zy : Bool × Y =>
          posterior p h zy.1 * (K h a (R, j)).mass zy.2) := by
      funext zy
      rw [hread h a zy.1]
    have hz : localGain p h a = 0 := by
      unfold localGain
      rw [hrow]
      exact jointMI_product_zero (posterior p h) (K h a (R, j)).mass
        (posterior_total p h hw) (K h a (R, j)).total
    simpa only [hz, zero_mul] using (le_refl (0 : ℝ))
  refine ⟨?_, informationLimit_zero_capacity p hcap⟩
  intro n bank hb
  have hupper := terminalMI_le_expectedCost p 0 n bank hb hcap
  have hlower := terminalMI_nonnegative p n bank hb
  exact le_antisymm (by simpa only [zero_mul] using hupper) hlower

/-- One pass yields exactly one base-two bit of hidden place information. -/
theorem countedRecursion_one_pass_bit :
    leftEntropy (fun _ : Fin 2 => ()) / Real.log 2 = 1 := by
  rw [one_pass_one_bit]
  exact div_self (ne_of_gt (Real.log_pos one_lt_two))

/-- With `n + 1` possible passes the hidden count is log base two of the
number of passes, with no factor from the content type. -/
theorem countedRecursion_passes_logb_two (n : ℕ) :
    leftEntropy (fun _ : Fin (n + 1) => ()) / Real.log 2 =
      Real.logb 2 (n + 1) := by
  rw [content_leaves_log]
  rfl

/-- The three laws in the 2021 formulation: observed-test equivalence,
zero finite and limiting information from any content-determined reading,
and exact finite-count information measured in base-two bits. The second
law contains both repeated protocols and arbitrary adaptive protocols. -/
def Laws (T : Type u) : Prop :=
  (∀ (R : T) (j k : ℕ),
    observed (R, j) = observed (R, k) ↔ (j = 0 ↔ k = 0)) ∧
  (∀ (Y : Type) [Fintype Y] (K : Reading (T × ℕ) Y),
    RecordDetermined (content (T := T)) K →
      ∀ (R : T) (j k : ℕ),
        readingDiscrimination K (R, j) (R, k) = 0 ∧
        ∀ N : ℕ,
          terminalMI (repeatProtocol (K (R, j)) (K (R, k)) N) N
            (historyBank Unit Y N) = 0) ∧
  (∀ (R : T) (j k : ℕ) (A Y : Type) [Fintype A] [Fintype Y]
      (p : FiniteProtocol Bool A Y)
      (K : List (A × Y) → A → Reading (T × ℕ) Y),
    (∀ h a, RecordDetermined (content (T := T)) (K h a)) →
    (∀ h a b,
      p.observation h a b = K h a (if b then (R, j) else (R, k))) →
      (∀ n bank, HistoryBank n bank → terminalMI p n bank = 0) ∧
        informationLimit p = 0) ∧
  (leftEntropy (fun _ : Fin 2 => ()) = Real.log 2 ∧
    leftEntropy (fun _ : Fin 2 => ()) / Real.log 2 = 1) ∧
  (∀ n : ℕ, leftEntropy (fun _ : Fin (n + 1) => ()) / Real.log 2 =
      Real.logb 2 (n + 1)) ∧
  ∀ n : ℕ, leftEntropy (fun i : Fin (n + 1) => i) = 0

/-- The complete counted-recursion bundle, with no assumption on T. -/
theorem countedRecursion_laws (T : Type u) : Laws T := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro R j k
    exact observed_eq_iff_zero_iff R j k
  · intro Y _ K hdet R j k
    exact orientationPoleGoal T Y K hdet R j k
  · intro R j k A Y _ _ p K hdet hobs
    exact countedRecursion_adaptive_zero_information R j k p K hdet hobs
  · exact ⟨one_pass_one_bit, countedRecursion_one_pass_bit⟩
  · intro n
    exact countedRecursion_passes_logb_two n
  · intro n
    exact counter_leaves_zero n

end
end OperatorKO7.Meta.BoundaryObserver.CountedRecursionLaws
