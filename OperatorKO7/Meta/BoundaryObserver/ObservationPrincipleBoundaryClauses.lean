import OperatorKO7.Meta.BoundaryObserver.KalmanObservability
import OperatorKO7.Meta.BoundaryObserver.PairBell

set_option autoImplicit false

/-!
# Three clauses of the two boundary theorems

Clause (28) of Theorem `thm:boundary-theorem`: the hidden-state quotient of a linear system, with
its induced action and record, is the minimal observer up to a bijection that preserves the read
maps and the actions. Clause (39) of Theorem `thm:boundary-quantum`: the Bell table at angle
`π / 4` has correlation `1 / √2` at three settings and `-1 / √2` at the fourth, and score `2 √2`.
-/

namespace OperatorKO7.Meta.BoundaryObserver.ObservationPrincipleBoundaryClauses

open OperatorKO7.Meta.BoundaryObserver
open OperatorKO7.Meta.BoundaryObserver.KalmanObservability

noncomputable section

/-- The hidden-state quotient and the minimal observer are one record: a bijection carries the
class of each state to its minimal description, commutes with the two read maps and commutes
with the two actions. -/
theorem quotient_minimal_equiv (K : Type*) [Field K] {V W : Type*}
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (A : V →ₗ[K] V) (C : V →ₗ[K] W) :
    ∃ e : (V ⧸ unobservable K A C) ≃
        AdmissibleObservation.MinimalState (C : V → W) (fun _ : Unit => (A : V → V)),
      (∀ x : V, e ((unobservable K A C).mkQ x) =
          AdmissibleObservation.minimalRecord (C : V → W) (fun _ : Unit => (A : V → V)) x) ∧
      (∀ z, AdmissibleObservation.minimalRead (C : V → W) (fun _ : Unit => (A : V → V)) (e z) =
          quotientRecord K A C z) ∧
      ∀ z, AdmissibleObservation.minimalStep (C : V → W) (fun _ : Unit => (A : V → V)) ()
          (e z) = e (quotientAction K A C z) := by
  obtain ⟨hrec, hact, f, hf, -⟩ := unobservable_quotient_universal K A C
  have hinj : Function.Injective f := by
    intro z w hzw
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (unobservable K A C) z
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (unobservable K A C) w
    rw [hf x, hf y] at hzw
    exact (quotient_eq_iff_futureEq K A C x y).mpr
      (Quotient.exact (s := AdmissibleObservation.futureSetoid (C : V → W)
        (fun _ : Unit => (A : V → V))) hzw)
  have hsurj : Function.Surjective f := by
    intro m
    obtain ⟨x, rfl⟩ := Quotient.exists_rep m
    exact ⟨(unobservable K A C).mkQ x, hf x⟩
  refine ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, fun x => hf x, ?_, ?_⟩
  · intro z
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (unobservable K A C) z
    rw [Equiv.ofBijective_apply, hf x, hrec x]
    rfl
  · intro z
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (unobservable K A C) z
    rw [Equiv.ofBijective_apply, hf x, hact x, Equiv.ofBijective_apply, hf (A x)]
    rfl

/-- At angle `π / 4` the Bell state has correlation `-1 / √2` at the pair of second tests and
`1 / √2` at the other three settings. -/
theorem bell_table_correlations (x y : Bool) :
    PairBell.stateCorrelation PairQubit.bellState (Real.pi / 4) x y =
      if x && y then -(1 / Real.sqrt 2) else 1 / Real.sqrt 2 := by
  rw [PairBell.bellTable x y]
  cases x <;> cases y <;> simp [FourTestTables.corr, FourTestTables.extremeTable] <;> ring

/-- The Bell table at angle `π / 4` has score `2 √2`, the score of the extreme table. -/
theorem bell_table_score :
    PairBell.chshScore PairQubit.bellState (Real.pi / 4) = 2 * Real.sqrt 2 := by
  rw [PairBell.chshScore, PairBell.bellTable false false, PairBell.bellTable false true,
    PairBell.bellTable true false, PairBell.bellTable true true]
  exact FourTestTables.extremeTable_score

end

end OperatorKO7.Meta.BoundaryObserver.ObservationPrincipleBoundaryClauses
