import OperatorKO7.Meta.BoundaryObserver.RecursorDecidability
import OperatorKO7.Meta.BoundaryObserver.Instances.KernelCases
import OperatorKO7.Meta.BoundaryObserver.BoundaryPole
import OperatorKO7.Meta.BoundaryObserver.DemandTransport

set_option autoImplicit false

/-!
# The rewriting instance of the counted recursor

This module retains the original theorem names and namespace for the root-step
recursor on Trace. The counted-pass mathematics on arbitrary carriers belongs
to RecursorDecidability.lean and requires no KernelCases import.

Relation: Step, the root rewriting relation, not contextual rewriting.
-/

open OperatorKO7 Trace

namespace OperatorKO7.Meta.BoundaryObserver.RecursorDecidability

open OperatorKO7.Meta.BoundaryObserver.KernelCases

/-- The generic model pass accompanies the recursor's actual root step.
Relation: Step. Property: one_step. -/
theorem pass_realized (R s : Trace) (k : ℕ) :
    Pass (R, k + 1) (R, k) ∧ Step (O R s (k + 1)) (app s (O R s k)) :=
  ⟨⟨rfl, rfl⟩, O_succ R s k⟩

/-- The only root reduct of a recursor at a positive counter is the step-rule right side.
Relation: Step. Property: one_step. -/
theorem rec_succ_root_reduct {b s n t : Trace} (h : Step (recΔ b s (delta n)) t) :
    t = app s (recΔ b s n) := by
  cases h
  rfl

/-- A finite term is not the application of a step to its own recursor. -/
theorem ne_app_rec (R s n : Trace) : R ≠ app s (recΔ R s n) := by
  intro h
  have hn := congrArg nodes h
  simp only [nodes] at hn
  omega

/-- The recursor returns its content in one root step exactly at counter zero.
Relation: Step. Property: one_step. -/
theorem returns_iff_observed (R s : Trace) (k : ℕ) :
    Step (O R s k) R ↔ k = 0 := by
  constructor
  · intro h
    cases k with
    | zero => rfl
    | succ j =>
      have h' : Step (recΔ R s (delta (numeral j))) R := h
      exact absurd (rec_succ_root_reduct h') (ne_app_rec R s (numeral j))
  · rintro rfl
    exact O_zero R s

/-- The root return test has a decision procedure through the counter. -/
def returnsDecidable (R s : Trace) (k : ℕ) : Decidable (Step (O R s k) R) :=
  decidable_of_iff (k = 0) (returns_iff_observed R s k).symm

end OperatorKO7.Meta.BoundaryObserver.RecursorDecidability

namespace OperatorKO7.Meta.BoundaryObserver.BoundaryPole

open OperatorKO7.Meta.BoundaryObserver.PairResolution
open OperatorKO7.Meta.BoundaryObserver.ProtocolResolution

/-- The original Trace-specific deterministic counter protocol statement,
now isolated from the universal boundary core. -/
theorem counterSideSymbol_trace (R : OperatorKO7.Trace) (j k : ℕ) (hjk : j ≠ k) :
    1 ≤ terminalMI (repeatProtocol
        (deterministicRow (fun p : OperatorKO7.Trace × ℕ => decide (p.2 = j)) (R, j))
        (deterministicRow (fun p : OperatorKO7.Trace × ℕ => decide (p.2 = j)) (R, k)) 1) 1
      (historyBank Unit Bool 1) := by
  let test : OperatorKO7.Trace × ℕ → Bool := fun p => decide (p.2 = j)
  have hk : k ≠ j := Ne.symm hjk
  have hsplit : test (R, j) ≠ test (R, k) := by
    simp [test, hk]
  exact (split_pair_one_reading test (R, j) (R, k) hsplit).2.1

end OperatorKO7.Meta.BoundaryObserver.BoundaryPole

/-! ## The original Trace-specific demand transport recursor adapter -/
namespace UniversalObservation.Transport
namespace RecursorAdapter
open UniversalObservation.Demand
open OperatorKO7
open OperatorKO7.Meta.BoundaryObserver.RecursorDecidability

def contentProblem : Problem (Trace × ℕ) {f : Trace → Bool // f ∈ (Set.univ : Set (Trace → Bool))} :=
  readoutProblem (content (T := Trace)) (observed (T := Trace)) Set.univ

theorem content_zero_test_obstruction : ¬ Good contentProblem Set.univ := by
  rintro ⟨f, hf⟩
  have h0 := hf (Trace.void, 0) (Set.mem_univ _)
  have h1 := hf (Trace.void, 1) (Set.mem_univ _)
  change f.val Trace.void = true at h0
  change f.val Trace.void = false at h1
  have h := h0.symm.trans h1
  cases h

theorem counter_zero_test_witness :
    Good (readoutProblem (counter (T := Trace)) (observed (T := Trace))
      (Set.univ : Set (ℕ → Bool))) Set.univ := by
  refine ⟨⟨fun k => decide (k = 0), Set.mem_univ _⟩, ?_⟩
  intro x _
  rfl

/-- Eventual completion has a constant truth value on the declared finite-counter family. -/
theorem termination_and_content_blindness :
    (∀ (R : Trace) (k : ℕ), Relation.ReflTransGen (Pass (T := Trace)) (R, k) (R, 0)) ∧
    Good (readoutProblem (content (T := Trace)) (fun _ => true) (Set.univ : Set (Trace → Bool))) Set.univ ∧
    ¬ Good contentProblem Set.univ := by
  refine ⟨passes_reach_zero, ?_, content_zero_test_obstruction⟩
  exact ⟨⟨fun _ => true, Set.mem_univ _⟩, fun _ _ => rfl⟩

/-- The failed orientation demand is the actual pass relation, with content-only witnesses. -/
def contentOrientationProblem :
    Problem {xy : (Trace × ℕ) × (Trace × ℕ) // Pass (T := Trace) xy.1 xy.2} (Trace → ℕ) where
  sat f xy := f ((content (T := Trace)) xy.val.2) < f ((content (T := Trace)) xy.val.1)

theorem content_orientation_obstruction : ¬ Good contentOrientationProblem Set.univ := by
  rintro ⟨f, hf⟩
  have h := hf ⟨((Trace.void, 1), (Trace.void, 0)), ⟨rfl, rfl⟩⟩ (Set.mem_univ _)
  exact Nat.lt_irrefl (f Trace.void) h

theorem native_one_step_return (R s : Trace) (k : ℕ) :
    Step (OperatorKO7.Meta.BoundaryObserver.KernelCases.O R s k) R ↔ k = 0 :=
  returns_iff_observed R s k

theorem depth_alphabet_minimum (n m : ℕ) :
    (∃ s : Fin (n + 1) → Fin m, Function.Injective (fun i => ((), s i))) ↔ n + 1 ≤ m :=
  counter_least_coordinate n m
end RecursorAdapter

end UniversalObservation.Transport
