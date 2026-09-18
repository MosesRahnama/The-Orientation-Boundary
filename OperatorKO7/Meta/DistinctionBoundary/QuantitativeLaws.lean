import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

set_option autoImplicit false

/-!
# Quantitative laws for finite distinction surfaces (registry rows QD-02/04/05/09/11)

Generic carriers only; no KO7 constructor is a premise, per the foundation rule
of `QUANTITATIVE_LAWS_ROADMAP_2026-07-13.md`. Packaging deviation, recorded: the
registry names five module files; the five laws are delivered as five
namespaces named after those files, in one consolidated compilation unit.

* QD-02 `DiagonalRarity`: the diagonal of the `n × n` square has `n` of the
  `n²` cells, so uniform probing misses it at the per-sample rate `1 - 1/n`.
* QD-04 `ReplayInstability`: replay disagreement `D₂ = 1 - Σ pᵢ²`; zero at a
  point mass, nonnegative for every subprobability scheduler.
* QD-05 `JoinabilityDistance`: bounded-depth joinability, monotone in the
  bound; depth-indexed reachability exhausts reflexive-transitive reachability.
* QD-09 `CertificateLowerBound`: `e` distinguishable alternatives need
  `e ≤ 2^L` under any injective length-`L` binary code; four alternatives do
  not fit one bit.
* QD-11 `EqualityQueryLowerBound`: the unqueried-pair adversary; a pair the
  equality-query protocol skips supports two assignments with identical
  answers at every other pair, one injective and one not, so no sound
  all-distinct certification can skip a pair.

Trust: kernel only, Mathlib baseline.
-/

namespace OperatorKO7.Meta.DistinctionBoundary.QuantitativeLaws

/-! ## QD-02: diagonal rarity -/
namespace DiagonalRarity

open Finset

/-- The diagonal of the `n × n` square has `n` cells. -/
theorem diag_card (n : ℕ) :
    ((univ : Finset (Fin n × Fin n)).filter fun p => p.1 = p.2).card = n := by
  have h : ((univ : Finset (Fin n × Fin n)).filter fun p => p.1 = p.2)
      = (univ : Finset (Fin n)).image fun i => (i, i) := by
    ext p
    simp only [mem_filter, mem_univ, true_and, mem_image]
    constructor
    · intro h
      exact ⟨p.1, by cases p with | mk a b => cases h; rfl⟩
    · rintro ⟨i, rfl⟩
      rfl
  rw [h, card_image_of_injective _ fun a b hab => congrArg Prod.fst hab,
    card_univ, Fintype.card_fin]

/-- The square has `n²` cells. -/
theorem square_card (n : ℕ) :
    (univ : Finset (Fin n × Fin n)).card = n ^ 2 := by
  simp [card_univ, sq]

/-- Rate identity over `ℚ`: the per-sample miss fraction is `1 - 1/n`, so `N`
independent uniform samples miss the diagonal at rate `(1 - 1/n)^N` and a
targeted diagonal suite needs `n` probes, one per diagonal cell (QD-02). -/
theorem miss_fraction (n : ℕ) (hn : 0 < n) :
    ((n ^ 2 - n : ℚ)) / (n ^ 2 : ℚ) = 1 - 1 / n := by
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp
  ring

end DiagonalRarity

/-! ## QD-04: replay instability -/
namespace ReplayInstability

open Finset

/-- Two-replay disagreement of a scheduler `p` on `k` outcomes. -/
def replayDisagreement {k : ℕ} (p : Fin k → ℚ) : ℚ :=
  1 - ∑ i, (p i) ^ 2

/-- A point mass replays identically: zero disagreement. -/
theorem replayDisagreement_pointMass {k : ℕ} (j : Fin k) :
    replayDisagreement (fun i => if i = j then (1 : ℚ) else 0) = 0 := by
  unfold replayDisagreement
  have h : (∑ i, (if i = j then (1 : ℚ) else 0) ^ 2) = 1 := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      simp [hb]
    · intro h
      exact absurd (Finset.mem_univ j) h
  rw [h]
  ring

/-- Disagreement is nonnegative for a subprobability scheduler: pointwise
weights in `[0, 1]` give `Σ pᵢ² ≤ Σ pᵢ ≤ 1`. -/
theorem replayDisagreement_nonneg {k : ℕ} (p : Fin k → ℚ)
    (h0 : ∀ i, 0 ≤ p i) (h1 : ∀ i, p i ≤ 1) (hsum : ∑ i, p i ≤ 1) :
    0 ≤ replayDisagreement p := by
  unfold replayDisagreement
  have hsq : ∑ i, (p i) ^ 2 ≤ ∑ i, p i := by
    apply Finset.sum_le_sum
    intro i _
    have h := mul_le_of_le_one_left (h0 i) (h1 i)
    calc (p i) ^ 2 = p i * p i := sq (p i) ▸ rfl
      _ ≤ p i := by nlinarith [h0 i, h1 i]
  linarith

end ReplayInstability

/-! ## QD-05: joinability distance -/
namespace JoinabilityDistance

variable {α : Type*}

/-- Reachability within `n` steps. -/
def ReachIn (R : α → α → Prop) : ℕ → α → α → Prop
  | 0, x, y => x = y
  | n + 1, x, y => x = y ∨ ∃ z, R x z ∧ ReachIn R n z y

/-- Joinability at depth `n`: a common reduct within `n` steps on each side. -/
def JoinableIn (R : α → α → Prop) (n : ℕ) (u v : α) : Prop :=
  ∃ d, ReachIn R n u d ∧ ReachIn R n v d

variable (R : α → α → Prop)

theorem reachIn_refl (n : ℕ) (x : α) : ReachIn R n x x := by
  cases n with
  | zero => rfl
  | succ n => exact Or.inl rfl

/-- One extra step of budget is free. -/
theorem reachIn_succ_of_reachIn {n : ℕ} {x y : α}
    (h : ReachIn R n x y) : ReachIn R (n + 1) x y := by
  induction n generalizing x with
  | zero => exact Or.inl h
  | succ n ih =>
      rcases h with h | ⟨z, hz, hr⟩
      · exact Or.inl h
      · exact Or.inr ⟨z, hz, ih hr⟩

/-- Depth monotonicity of bounded reachability. -/
theorem reachIn_mono {n m : ℕ} (hnm : n ≤ m) {x y : α}
    (h : ReachIn R n x y) : ReachIn R m x y := by
  induction hnm with
  | refl => exact h
  | step _ ih => exact reachIn_succ_of_reachIn R ih

/-- Joinability latency is monotone: a depth-`n` join is a depth-`m` join for
every `m ≥ n` (QD-05 latency law). -/
theorem joinableIn_mono {n m : ℕ} (hnm : n ≤ m) {u v : α}
    (h : JoinableIn R n u v) : JoinableIn R m u v := by
  obtain ⟨d, h1, h2⟩ := h
  exact ⟨d, reachIn_mono R hnm h1, reachIn_mono R hnm h2⟩

/-- Appending one step to a bounded reduction. -/
theorem reachIn_snoc {n : ℕ} {x b c : α}
    (h : ReachIn R n x b) (hbc : R b c) : ReachIn R (n + 1) x c := by
  induction n generalizing x with
  | zero => exact Or.inr ⟨c, h ▸ hbc, rfl⟩
  | succ n ih =>
      rcases h with rfl | ⟨z, hz, hr⟩
      · exact Or.inr ⟨c, hbc, reachIn_refl R _ c⟩
      · exact Or.inr ⟨z, hz, ih hr⟩

/-- Bounded reachability at some depth is reflexive-transitive reachability,
so joinability at some finite latency is joinability (QD-05 exhaustion). -/
theorem reachIn_iff_reflTransGen {x y : α} :
    (∃ n, ReachIn R n x y) ↔ Relation.ReflTransGen R x y := by
  constructor
  · rintro ⟨n, h⟩
    induction n generalizing x with
    | zero => exact h ▸ Relation.ReflTransGen.refl
    | succ n ih =>
        rcases h with rfl | ⟨z, hz, hr⟩
        · exact Relation.ReflTransGen.refl
        · exact Relation.ReflTransGen.head hz (ih hr)
  · intro h
    induction h with
    | refl => exact ⟨0, reachIn_refl R 0 x⟩
    | @tail b c _ hbc ih =>
        obtain ⟨n, hn⟩ := ih
        exact ⟨n + 1, reachIn_snoc R hn hbc⟩

end JoinabilityDistance

/-! ## QD-09: certificate coding floor -/
namespace CertificateLowerBound

/-- `e` distinguishable alternatives injectively coded by length-`L` binary
words force `e ≤ 2^L` (QD-09 floor). -/
theorem card_le_of_injective_code {e L : ℕ}
    (f : Fin e → (Fin L → Bool)) (hf : Function.Injective f) :
    e ≤ 2 ^ L := by
  have h := Fintype.card_le_of_injective f hf
  simpa using h

/-- Negative control: four alternatives do not fit one-bit codes. -/
theorem four_alternatives_exceed_one_bit :
    ¬ ∃ f : Fin 4 → (Fin 1 → Bool), Function.Injective f := by
  rintro ⟨f, hf⟩
  have h := card_le_of_injective_code f hf
  omega

end CertificateLowerBound

/-! ## QD-11: equality-query lower bound -/
namespace EqualityQueryLowerBound

/-- **The unqueried-pair adversary.** For any pair `i ≠ j` there are two
assignments on the carrier, one injective and one not, whose pairwise equality
answers agree at every pair other than `(i, j)` and `(j, i)`. A deterministic
sound all-distinct certification that reads only pairwise equality answers
therefore cannot skip a pair: on the skipped pair the two worlds are
indistinguishable and only one of them is all-distinct. With `n(n-1)/2`
unordered pairs this is the QD-11 query floor. -/
theorem unqueried_pair_adversary {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    ∃ f g : Fin n → Fin n,
      Function.Injective f ∧ ¬ Function.Injective g ∧
        ∀ a b : Fin n, ¬(a = i ∧ b = j) → ¬(a = j ∧ b = i) →
          ((f a = f b) ↔ (g a = g b)) := by
  refine ⟨id, fun a => if a = j then i else a, fun a b h => h, ?_, ?_⟩
  · intro hg
    have hgi : (if i = j then i else i) = i := by simp
    have hgj : (if j = j then i else j) = i := by simp
    have h := hg (a₁ := i) (a₂ := j) (by simp)
    exact hij h
  · intro a b hab hba
    by_cases ha : a = j <;> by_cases hb : b = j
    · subst ha; subst hb; simp
    · subst ha
      have hbi : b ≠ i := fun h => hba ⟨rfl, h.symm ▸ rfl⟩
      simp only [if_neg hb, id]
      constructor
      · intro h; exact absurd h.symm hb
      · intro h; exact absurd h.symm hbi
    · subst hb
      have hai : a ≠ i := fun h => hab ⟨h, rfl⟩
      simp only [if_neg ha, id]
      constructor
      · intro h; exact absurd h ha
      · intro h; exact absurd h hai
    · simp only [if_neg ha, if_neg hb, id]

end EqualityQueryLowerBound

end OperatorKO7.Meta.DistinctionBoundary.QuantitativeLaws
