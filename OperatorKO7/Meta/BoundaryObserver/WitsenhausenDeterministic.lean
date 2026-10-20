import OperatorKO7.Meta.BoundaryObserver.StochasticGraph
import OperatorKO7.Meta.BoundaryObserver.PlaceCoordinates

set_option autoImplicit false

/-!
# The chromatic bound of a deterministic record

For a deterministic observation, a zero-error side record separates exactly the
different target values attained in each observation fiber. The identity target
recovers the place-coordinate bound.

Proof graph: Audit/ledgers/boundary-theorem/BOUNDARY-THEOREM-MATH-COMPLETION-PROOF-GRAPH.md,
node N14. Scope: arbitrary inputs and targets with finite observation output.
-/

namespace OperatorKO7.Meta.BoundaryObserver.WitsenhausenDeterministic

/-- A deterministic channel has an `n`-coloring exactly when every record
fiber attains finitely many target values and their number is at most `n`.
The fiber target values are represented by the subtype of attained values. -/
theorem deterministic_colorable_iff
    {X Y V : Type*} [Fintype Y] [DecidableEq Y]
    (q : X → Y) (P : X → V) (n : ℕ) :
    (StochasticGraph.conflictGraph (StochasticGraph.deterministic q).prob P).Colorable n ↔
      ∀ y : Y,
        Finite (OperatorKO7.Meta.OperationalInexpressibility.Confusability.FiberTargetValues q P y) ∧
        Nat.card (OperatorKO7.Meta.OperationalInexpressibility.Confusability.FiberTargetValues q P y) ≤ n := by
  rw [StochasticGraph.deterministic_graph]
  exact OperatorKO7.Meta.OperationalInexpressibility.Confusability.colorable_iff_fiber_capacity q P n

/-- For the identity target, deterministic zero-error coloring has precisely the
place-coordinate bound. Every observer fiber contains at most `n` states
exactly when a resolving `Fin n` place coordinate exists. -/
theorem deterministic_identity_colorable_iff_place
    {X Y : Type*} [Fintype Y] [DecidableEq Y]
    (q : X → Y) (n : ℕ) :
    ((StochasticGraph.conflictGraph (StochasticGraph.deterministic q).prob
        (id : X → X)).Colorable n ↔
      ∀ y : Y, (q ⁻¹' {y}).Finite ∧ (q ⁻¹' {y}).ncard ≤ n) ∧
    ((∀ y : Y, (q ⁻¹' {y}).Finite ∧ (q ⁻¹' {y}).ncard ≤ n) ↔
      ∃ p : X → Fin n, Function.Injective (fun x => (q x, p x))) := by
  have hplace :
      (StochasticGraph.conflictGraph (StochasticGraph.deterministic q).prob
          (id : X → X)).Colorable n ↔
        ∃ p : X → Fin n, Function.Injective (fun x => (q x, p x)) := by
    rw [StochasticGraph.deterministic_graph,
      OperatorKO7.Meta.OperationalInexpressibility.Confusability.colorable_iff_exists_fin_resolving_channel]
    rfl
  have hsize :
      (∃ p : X → Fin n, Function.Injective (fun x => (q x, p x))) ↔
        ∀ y : Y, (q ⁻¹' {y}).Finite ∧ (q ⁻¹' {y}).ncard ≤ n :=
    PlaceCoordinates.exists_place_coordinate_iff q n
  exact ⟨hplace.trans hsize, hsize.symm⟩

end OperatorKO7.Meta.BoundaryObserver.WitsenhausenDeterministic
