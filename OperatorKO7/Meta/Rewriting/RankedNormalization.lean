import Mathlib.Logic.Relation
import Mathlib.Order.WellFounded
import Mathlib.Tactic

/-! # Normalization and path length for deterministic ranked relations -/

namespace OperatorKO7.Meta.Rewriting

universe u

/-- A decidable next step with a natural rank that decreases on its graph. -/
structure RankedMachine (α : Type u) where
  next : α → Option α
  rank : α → Nat
  decreases : ∀ {a b}, next a = some b → rank b < rank a

namespace RankedMachine

variable {α : Type u} (M : RankedMachine α)

def Step (a b : α) : Prop := M.next a = some b

def normalize (a : α) : α :=
  match _h : M.next a with
  | none => a
  | some b => normalize b
termination_by M.rank a
decreasing_by exact M.decreases ‹_›

def cost (a : α) : Nat :=
  match h : M.next a with
  | none => 0
  | some b => cost b + 1
termination_by M.rank a
decreasing_by exact M.decreases h

theorem deterministic {a b c : α} (h : M.Step a b) (g : M.Step a c) : b = c := by
  exact Option.some.inj (h.symm.trans g)

theorem normalize_terminal {a : α} (h : M.next a = none) : M.normalize a = a := by
  rw [normalize, h]

theorem normalize_step {a b : α} (h : M.Step a b) : M.normalize a = M.normalize b := by
  rw [normalize, h]

theorem cost_terminal {a : α} (h : M.next a = none) : M.cost a = 0 := by
  rw [cost, h]

theorem cost_step {a b : α} (h : M.Step a b) : M.cost a = M.cost b + 1 := by
  rw [cost, h]

theorem normalize_reachable (a : α) : Relation.ReflTransGen M.Step a (M.normalize a) := by
  induction n : M.rank a using Nat.strong_induction_on generalizing a with
  | h n ih =>
    cases hn : M.next a with
    | none => rw [M.normalize_terminal hn]
    | some b =>
      rw [M.normalize_step hn]
      exact .head hn (ih (M.rank b) (by simpa [n] using M.decreases hn) b rfl)

theorem normalize_normal (a : α) : M.next (M.normalize a) = none := by
  induction n : M.rank a using Nat.strong_induction_on generalizing a with
  | h n ih =>
    cases hn : M.next a with
    | none => simpa [M.normalize_terminal hn] using hn
    | some b =>
      rw [M.normalize_step hn]
      exact ih (M.rank b) (by simpa [n] using M.decreases hn) b rfl

theorem normalize_star {a b : α} (h : Relation.ReflTransGen M.Step a b) :
    M.normalize a = M.normalize b := by
  induction h with
  | refl => rfl
  | tail _ hs ih => exact ih.trans (M.normalize_step hs)

theorem confluent {a b c : α} (hab : Relation.ReflTransGen M.Step a b)
    (hac : Relation.ReflTransGen M.Step a c) :
    ∃ d, Relation.ReflTransGen M.Step b d ∧ Relation.ReflTransGen M.Step c d := by
  refine ⟨M.normalize a, ?_, ?_⟩
  · rw [M.normalize_star hab]; exact M.normalize_reachable b
  · rw [M.normalize_star hac]; exact M.normalize_reachable c

theorem unique_normal_form {a b : α} (h : Relation.ReflTransGen M.Step a b)
    (hb : M.next b = none) : b = M.normalize a := by
  exact (M.normalize_terminal hb).symm.trans (M.normalize_star h).symm

theorem normalize_idempotent (a : α) : M.normalize (M.normalize a) = M.normalize a :=
  M.normalize_terminal (M.normalize_normal a)

theorem joinable_iff_normalize_eq (a b : α) :
    (∃ c, Relation.ReflTransGen M.Step a c ∧ Relation.ReflTransGen M.Step b c) ↔
      M.normalize a = M.normalize b := by
  constructor
  · rintro ⟨c, ha, hb⟩
    exact (M.normalize_star ha).trans (M.normalize_star hb).symm
  · intro h
    exact ⟨M.normalize b, h ▸ M.normalize_reachable a, M.normalize_reachable b⟩

theorem invariant_normalizer_unique (nf : α → α)
    (hinv : ∀ {a b}, M.Step a b → nf a = nf b)
    (hfix : ∀ a, M.next a = none → nf a = a) : nf = M.normalize := by
  funext a
  have hstar : ∀ {x y}, Relation.ReflTransGen M.Step x y → nf x = nf y := by
    intro x y h
    induction h with
    | refl => rfl
    | tail _ hs ih => exact ih.trans (hinv hs)
  exact (hstar (M.normalize_reachable a)).trans (hfix _ (M.normalize_normal a))

theorem reverse_wellFounded : WellFounded (fun a b => M.Step b a) :=
  Subrelation.wf (fun h => M.decreases h) (measure M.rank).wf

/-- A sequence with its number of steps. -/
inductive Steps : Nat → α → α → Prop
  | refl (a : α) : Steps 0 a a
  | cons {n : Nat} {a b c : α} : M.Step a b → Steps n b c → Steps (n + 1) a c

theorem steps_cost {n : Nat} {a b : α} (h : M.Steps n a b) :
    M.cost a = M.cost b + n := by
  induction h with
  | refl => omega
  | cons hs _ ih => rw [M.cost_step hs, ih]; omega

theorem normalizing_steps (a : α) : M.Steps (M.cost a) a (M.normalize a) := by
  induction n : M.rank a using Nat.strong_induction_on generalizing a with
  | h n ih =>
    cases hn : M.next a with
    | none => rw [M.normalize_terminal hn, M.cost_terminal hn]; exact .refl a
    | some b =>
      rw [M.normalize_step hn, M.cost_step hn]
      exact .cons hn (ih (M.rank b) (by simpa [n] using M.decreases hn) b rfl)

theorem steps_to_normal_length {n : Nat} {a b : α} (h : M.Steps n a b)
    (hb : M.next b = none) : n = M.cost a := by
  have := M.steps_cost h
  rw [M.cost_terminal hb] at this
  omega

theorem cost_le_rank (a : α) : M.cost a ≤ M.rank a := by
  induction n : M.rank a using Nat.strong_induction_on generalizing a with
  | h n ih =>
    cases hn : M.next a with
    | none => rw [M.cost_terminal hn]; exact Nat.zero_le _
    | some b =>
      have hd := M.decreases hn
      have hb := ih (M.rank b) (by simpa [n] using hd) b rfl
      rw [M.cost_step hn]
      omega

end RankedMachine
end OperatorKO7.Meta.Rewriting
