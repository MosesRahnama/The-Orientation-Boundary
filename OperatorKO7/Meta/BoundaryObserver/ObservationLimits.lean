import OperatorKO7.Meta.BoundaryObserver.FourTestTables
import OperatorKO7.Meta.BoundaryObserver.NoReturn

set_option autoImplicit false

/-!
# Explicit distinctions needed for observation transport

Tagged occurrences and independent systems have different state spaces. Two positive normalized
real matrix states can have the same label probabilities and exchange symmetry while differing
under the swap observable. No-return dynamics can remain injective. A bare many-to-one map puts
no condition on an independently assigned real cost.
These are mathematical countermodels to unrestricted transports, not empirical claims or a
violation of a physical heat theorem.
Relation: finite state spaces, real matrix states, successor steps, and arbitrary assigned costs.
Trust: kernel-only.
-/

namespace OperatorKO7.Meta.BoundaryObserver.ObservationLimits

open FourTestTables

/-- A content state with a binary occurrence tag has twice the content-state count. -/
theorem tagged_cardinality (n : ℕ) : Fintype.card (Fin n × Bool) = n * 2 := by simp

/-- Two independently varying content systems have the square of the state count. -/
theorem independent_cardinality (n : ℕ) : Fintype.card (Fin n × Fin n) = n * n := by simp

/-- Above two content values the independent pair has strictly greater capacity. -/
theorem independent_larger_than_tagged {n : ℕ} (hn : 2 < n) :
    Fintype.card (Fin n × Bool) < Fintype.card (Fin n × Fin n) := by
  rw [tagged_cardinality, independent_cardinality]
  exact Nat.mul_lt_mul_of_pos_left hn (by omega)

/-- The small cases are different: one content value gives two tagged states but one
independent pair; two content values happen to give the same count. -/
theorem tagged_independent_small_cases :
    Fintype.card (Fin 1 × Bool) = 2 ∧ Fintype.card (Fin 1 × Fin 1) = 1 ∧
      Fintype.card (Fin 2 × Bool) = Fintype.card (Fin 2 × Fin 2) := by simp

/-- The normalized coherent state in the two-dimensional occurrence subspace. -/
noncomputable def coherentState : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(1 : ℝ) / 2, (1 : ℝ) / 2; (1 : ℝ) / 2, (1 : ℝ) / 2]

/-- The uniform classical mixture in the same subspace. -/
noncomputable def mixedState : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal (fun _ => (1 : ℝ) / 2)

/-- The coherent state is a positive matrix, witnessed by its own Gram factor. -/
theorem coherentState_posSemidef : coherentState.PosSemidef := by
  have h : coherentState.conjTranspose * coherentState = coherentState := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [coherentState, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two]
  simpa only [h] using Matrix.posSemidef_conjTranspose_mul_self coherentState

/-- The mixture is positive because all its diagonal weights are nonnegative. -/
theorem mixedState_posSemidef : mixedState.PosSemidef := by
  apply Matrix.PosSemidef.diagonal
  intro i
  norm_num

/-- Both states are normalized, so the comparison does not use an invalid state matrix. -/
theorem state_traces : coherentState.trace = 1 ∧ mixedState.trace = 1 := by
  constructor <;> norm_num [coherentState, mixedState, Matrix.trace, Fin.sum_univ_two]

/-- Label measurements have identical probabilities in the two states. -/
theorem same_label_probabilities : ∀ i : Fin 2, coherentState i i = mixedState i i := by
  intro i
  fin_cases i <;> norm_num [coherentState, mixedState]

/-- Both states obey exactly the same exchange symmetry. -/
theorem both_exchange_invariant :
    swapMat * coherentState * swapMat = coherentState ∧
      swapMat * mixedState * swapMat = mixedState := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [swapMat, coherentState, mixedState, Matrix.mul_apply, Fin.sum_univ_two]

/-- The swap observable distinguishes the states: its expected value is one in the coherent
state and zero in the mixture. -/
theorem swap_distinguishes_states :
    (coherentState * swapMat).trace = 1 ∧ (mixedState * swapMat).trace = 0 := by
  constructor <;>
    norm_num [swapMat, coherentState, mixedState, Matrix.mul_apply, Matrix.trace, Fin.sum_univ_two]

/-- The identical label probabilities and identical exchange symmetry do not determine the
state; both incompatible choices are positive and normalized. -/
theorem symmetry_does_not_determine_coherence :
    coherentState.PosSemidef ∧ mixedState.PosSemidef ∧
      coherentState.trace = 1 ∧ mixedState.trace = 1 ∧
      (∀ i : Fin 2, coherentState i i = mixedState i i) ∧
      swapMat * coherentState * swapMat = coherentState ∧
      swapMat * mixedState * swapMat = mixedState ∧ coherentState ≠ mixedState := by
  refine ⟨coherentState_posSemidef, mixedState_posSemidef, state_traces.1, state_traces.2,
    same_label_probabilities, both_exchange_invariant.1, both_exchange_invariant.2, ?_⟩
  intro h
  have he := congrArg (fun r : Matrix (Fin 2) (Fin 2) ℝ => (r * swapMat).trace) h
  change (coherentState * swapMat).trace = (mixedState * swapMat).trace at he
  rw [swap_distinguishes_states.1, swap_distinguishes_states.2] at he
  norm_num at he

/-- No forward return does not imply erasure: successor is injective and never returns.
Its absence of return is imported from the manuscript's existing proof. -/
theorem no_return_without_information_loss : Function.Injective Nat.succ ∧
    ∀ n : ℕ, ¬ Relation.TransGen (fun a b : ℕ => b = a + 1) n n :=
  ⟨Nat.succ_injective, NoReturn.succ_no_return_and_infinite.1⟩

/-- A bare erasure map and a real cost can be specified independently. Thus a positive heat
bound needs physical hypotheses in addition to the many-to-one map. -/
theorem erasure_with_zero_assigned_cost :
    ∃ (q : Bool → Unit) (cost : Bool → ℝ), ¬ Function.Injective q ∧
      (∀ x, cost x = 0) := by
  refine ⟨fun _ => (), fun _ => 0, ?_, fun _ => rfl⟩
  intro h
  exact Bool.false_ne_true (@h false true rfl)

end OperatorKO7.Meta.BoundaryObserver.ObservationLimits
