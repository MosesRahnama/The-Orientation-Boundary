import OperatorKO7.Meta.PolyInterpretation_FullStep
import OperatorKO7.Meta.Rewriting.RankedNormalization

/-! # Executable root strategies for the unguarded KO7 relation -/

namespace OperatorKO7.RootStrategyNormalization

open Trace PolyInterpretation Meta.Rewriting

/-- The Boolean selects the reflexive verdict at a diagonal equality test. -/
def rootNext (preferRefl : Bool) : Trace → Option Trace
  | .integrate (.delta _) => some .void
  | .merge a b =>
      if a = .void then some b else
      if b = .void then some a else
      if a = b then some a else none
  | .recΔ b _ .void => some b
  | .recΔ b s (.delta n) => some (.app s (.recΔ b s n))
  | .eqW a b =>
      if preferRefl = true ∧ a = b then some .void
      else some (.integrate (.merge a b))
  | _ => none

theorem rootNext_sound (p : Bool) {a b : Trace} (h : rootNext p a = some b) :
    Step a b := by
  cases a with
  | void => simp [rootNext] at h
  | delta a => simp [rootNext] at h
  | app a c => simp [rootNext] at h
  | integrate a =>
      cases a <;> simp [rootNext] at h
      subst b
      exact Step.R_int_delta _
  | merge a c =>
      by_cases ha : a = .void
      · subst a
        simp [rootNext] at h
        subst b
        exact Step.R_merge_void_left _
      · by_cases hc : c = .void
        · subst c
          simp [rootNext, ha] at h
          subst b
          exact Step.R_merge_void_right _
        · by_cases he : a = c
          · subst c
            simp [rootNext, ha] at h
            subst b
            exact Step.R_merge_cancel _
          · simp [rootNext, ha, hc, he] at h
  | recΔ a s n =>
      cases n <;> simp [rootNext] at h
      · subst b; exact Step.R_rec_zero _ _
      · subst b; exact Step.R_rec_succ _ _ _
  | eqW a c =>
      by_cases he : p = true ∧ a = c
      · simp [rootNext, he] at h
        subst b
        rw [he.2]
        exact Step.R_eq_refl _
      · simp [rootNext, he] at h
        subst b
        exact Step.R_eq_diff _ _

theorem rootNext_complete (p : Bool) {a b : Trace} (h : Step a b) :
    ∃ c, rootNext p a = some c := by
  cases h <;> simp [rootNext]
  all_goals split <;> simp_all

def rootMachine (p : Bool) : RankedMachine Trace where
  next := rootNext p
  rank := W
  decreases := fun h => W_orients_step (rootNext_sound p h)

def normalizeRoot (p : Bool) : Trace → Trace := (rootMachine p).normalize

theorem normalizeRoot_reachable (p : Bool) (a : Trace) :
    Relation.ReflTransGen Step a (normalizeRoot p a) := by
  have transport : ∀ {x y}, Relation.ReflTransGen (rootMachine p).Step x y →
      Relation.ReflTransGen Step x y := by
    intro x y h
    induction h with
    | refl => rfl
    | tail _ hs ih => exact ih.tail (rootNext_sound p hs)
  exact transport ((rootMachine p).normalize_reachable a)

theorem normalizeRoot_normal (p : Bool) (a : Trace) : NormalForm (normalizeRoot p a) := by
  rintro ⟨b, hb⟩
  obtain ⟨c, hc⟩ := rootNext_complete p hb
  have hn := (rootMachine p).normalize_normal a
  change rootNext p (normalizeRoot p a) = none at hn
  rw [hn] at hc
  contradiction

theorem normalizeRoot_idempotent (p : Bool) (a : Trace) :
    normalizeRoot p (normalizeRoot p a) = normalizeRoot p a :=
  (rootMachine p).normalize_idempotent a

theorem normalizeRoot_cost_le_W (p : Bool) (a : Trace) :
    (rootMachine p).cost a ≤ W a := (rootMachine p).cost_le_rank a

theorem normalizeRoot_reflexive_choice : normalizeRoot true (.eqW .void .void) = .void := by
  exact ((rootMachine true).normalize_step (by rfl)).trans
    ((rootMachine true).normalize_terminal (a := .void) rfl)

theorem normalizeRoot_difference_choice :
    normalizeRoot false (.eqW .void .void) = .integrate (.merge .void .void) := by
  exact ((rootMachine false).normalize_step (by rfl)).trans
    ((rootMachine false).normalize_terminal (a := .integrate (.merge .void .void)) rfl)

theorem root_normalization_depends_on_strategy :
    normalizeRoot true (.eqW .void .void) ≠ normalizeRoot false (.eqW .void .void) := by
  rw [normalizeRoot_reflexive_choice, normalizeRoot_difference_choice]
  decide

end OperatorKO7.RootStrategyNormalization
