import OperatorKO7.Meta.OperationalInexpressibility.SequentialMemoryRecovery
import OperatorKO7.Meta.OperationalInexpressibility.TargetKernelQuotient

/-!
Draft of the P2.4 additions to `SequentialMemoryRecovery.lean`: first sufficient horizon and
coarsest licensing memory.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.OperationalInexpressibility.SequentialMemoryRecovery

open OperatorKO7.Meta.OperationalInexpressibility.LicenseCriterion
open OperatorKO7.Meta.OperationalInexpressibility.TargetKernel

universe u v w z

/-! ## First sufficient horizon -/

/-- A license held by the history at one horizon holds at every longer horizon. -/
theorem licensed_history_of_le {X : Type u} {Q : Type v} {V : Type w}
    (q : Nat → X → Q) (P : X → V) {m n : Nat} (hmn : m ≤ n)
    (hm : Licensed (historyObserver q m) P) : Licensed (historyObserver q n) P := by
  induction hmn with
  | refl => exact hm
  | step _ ih => exact licensed_history_monotone q P _ ih

/-- **First sufficient horizon.** Along retained histories, either no horizon licenses the
target, or there is a horizon `N₀` such that exactly the horizons at or above `N₀` license it. -/
theorem first_sufficient_horizon_dichotomy {X : Type u} {Q : Type v} {V : Type w}
    (q : Nat → X → Q) (P : X → V) :
    (∀ N, ¬ Licensed (historyObserver q N) P) ∨
      ∃ N₀, ∀ N, Licensed (historyObserver q N) P ↔ N₀ ≤ N := by
  classical
  by_cases h : ∃ N, Licensed (historyObserver q N) P
  · right
    refine ⟨Nat.find h, fun N => ⟨fun hN => Nat.find_min' h hN, fun hle => ?_⟩⟩
    exact licensed_history_of_le q P hle (Nat.find_spec h)
  · left
    intro N hN
    exact h ⟨N, hN⟩

/-- The first sufficient horizon is unique. -/
theorem first_sufficient_horizon_unique {X : Type u} {Q : Type v} {V : Type w}
    (q : Nat → X → Q) (P : X → V) {a b : Nat}
    (ha : ∀ N, Licensed (historyObserver q N) P ↔ a ≤ N)
    (hb : ∀ N, Licensed (historyObserver q N) P ↔ b ≤ N) : a = b :=
  le_antisymm ((ha b).1 ((hb b).2 le_rfl)) ((hb a).1 ((ha a).2 le_rfl))

/-! ## Coarsest licensing memory -/

/-- **Coarsest licensing memory.** When the history at horizon `N` licenses the target, the
target-kernel quotient is a function of that history, licenses the target, and is refined by every
memory of the history that licenses the target. -/
theorem historyTargetKernel_coarsest_memory {X : Type u} {Q : Type v} {V : Type w}
    (q : Nat → X → Q) (P : X → V) (N : Nat) (hlic : Licensed (historyObserver q N) P) :
    ObserverRefines (historyObserver q N) (targetKernelQuotientMap P) ∧
      Licensed (targetKernelQuotientMap P) P ∧
      ∀ {M : Type z} (memory : (Fin (N + 1) → Q) → M),
        Licensed (fun x => memory (historyObserver q N x)) P →
          ObserverRefines (fun x => memory (historyObserver q N x)) (targetKernelQuotientMap P) :=
  ⟨(licensed_iff_refines_targetKernelQuotient _ P).1 hlic,
    targetKernelQuotient_licenses_target P,
    fun _ hmem => (licensed_iff_refines_targetKernelQuotient _ P).1 hmem⟩

/-! ## Revealing control -/

/-- Stage zero hides the Boolean state; every later stage reveals it. -/
def revealingObserver (stage : Nat) (x : Bool) : Bool :=
  if stage = 0 then false else x

/-- The identity target reaches its first sufficient horizon at one under the revealing
observer. -/
theorem revealingObserver_first_sufficient_horizon (N : Nat) :
    Licensed (historyObserver revealingObserver N) (fun x : Bool => x) ↔ 1 ≤ N := by
  constructor
  · intro h
    by_contra hN
    have hN0 : N = 0 := by omega
    subst hN0
    have hhist : historyObserver revealingObserver 0 false =
        historyObserver revealingObserver 0 true := by
      funext i
      simp [historyObserver, revealingObserver]
    have hbad : (false : Bool) = true := h false true hhist
    cases hbad
  · intro hN
    have h1 : Licensed (revealingObserver 1) (fun x : Bool => x) := by
      intro x y hxy
      simpa [revealingObserver] using hxy
    exact licensed_history_of_le _ _ hN
      (licensed_stage_implies_licensed_history revealingObserver (fun x : Bool => x)
        (stage := 1) (horizon := 1) le_rfl h1)

/-- The identity target reaches its first sufficient horizon at zero under the forgetting
observer, whose current observation later forgets the state. -/
theorem forgettingObserver_first_sufficient_horizon (N : Nat) :
    Licensed (historyObserver forgettingObserver N) (fun x : Bool => x) ↔ 0 ≤ N :=
  ⟨fun _ => Nat.zero_le N, fun _ =>
    licensed_stage_implies_licensed_history forgettingObserver (fun x : Bool => x)
      (stage := 0) (horizon := N) (Nat.zero_le N) forgettingObserver_stage0_licenses_identity⟩

end OperatorKO7.Meta.OperationalInexpressibility.SequentialMemoryRecovery
