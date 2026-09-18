import OperatorKO7.Meta.UniqueNormalization.DecreasingPastingMeasure
import Mathlib.Data.Multiset.Sort

/-!
# RTA #79 route R2: cancellation for the Dershowitz-Manna order

The Isabelle proof of decreasing-diagram pasting uses cancellation of a common
multiset from the reflexive DM order. Mathlib supplies the DM relation and its
well-foundedness, but not this cancellation theorem.

For the route-R2 carrier `LevelKey`, whose order is linear, the strict DM order
is total on unequal finite multisets. We prove that by descending canonical
sorts. Cancellation then follows from totality, additive monotonicity, and
irreflexivity. The result is lifted to `DMLe` by collapsing its reflexive-
transitive closure to equality or one strict DM step, using transitivity of the
strict DM relation.

Trust: kernel checked. No external certificate or new axiom.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniqueNormalization

/-- The strict DM order is irreflexive on `LevelKey` multisets. -/
theorem dmLt_irrefl (M : Multiset LevelKey) :
    ¬ Multiset.IsDershowitzMannaLT M M := by
  exact Multiset.wellFounded_isDershowitzMannaLT.induction
    (C := fun X : Multiset LevelKey => ¬ Multiset.IsDershowitzMannaLT X X)
    M (fun X ih hXX => ih X hXX hXX)

/-- Empty is strictly DM-below every nonempty multiset. -/
theorem dmLt_zero_of_ne_zero {N : Multiset LevelKey} (hne : N ≠ 0) :
    Multiset.IsDershowitzMannaLT 0 N := by
  refine ⟨0, 0, N, hne, by simp, by simp, ?_⟩
  intro y hy
  simp at hy

/-- If one member of `N` strictly dominates every member of `M`, then `M` is
strictly DM-below `N`. -/
theorem dmLt_of_all_lt_mem {M N : Multiset LevelKey} {z : LevelKey}
    (hz : z ∈ N) (hall : ∀ y ∈ M, y < z) :
    Multiset.IsDershowitzMannaLT M N := by
  have hne : N ≠ 0 := by
    intro hN
    rw [hN] at hz
    exact (Multiset.notMem_zero z) hz
  refine ⟨0, M, N, hne, by simp, by simp, ?_⟩
  intro y hy
  exact ⟨z, hz, hall y hy⟩

/-- Trichotomy for multisets presented by descending sorted lists. -/
theorem dmTrichotomy_sorted :
    ∀ (xs ys : List LevelKey),
      xs.Pairwise (fun a b => b ≤ a) →
      ys.Pairwise (fun a b => b ≤ a) →
      ((xs : Multiset LevelKey) = (ys : Multiset LevelKey)) ∨
        Multiset.IsDershowitzMannaLT (xs : Multiset LevelKey) (ys : Multiset LevelKey) ∨
        Multiset.IsDershowitzMannaLT (ys : Multiset LevelKey) (xs : Multiset LevelKey) := by
  intro xs
  induction xs with
  | nil =>
      intro ys hxs hys
      cases ys with
      | nil => exact Or.inl rfl
      | cons b bs =>
          exact Or.inr (Or.inl (dmLt_zero_of_ne_zero (by simp)))
  | cons a as ih =>
      intro ys hxs hys
      cases ys with
      | nil =>
          exact Or.inr (Or.inr (dmLt_zero_of_ne_zero (by simp)))
      | cons b bs =>
          have hxs' := (List.pairwise_cons.mp hxs)
          have hys' := (List.pairwise_cons.mp hys)
          rcases lt_trichotomy a b with hab | heq | hba
          · have hall : ∀ y ∈ (a :: as : List LevelKey), y < b := by
              intro y hy
              rcases List.mem_cons.mp hy with rfl | hy
              · exact hab
              · exact lt_of_le_of_lt (hxs'.1 y hy) hab
            exact Or.inr (Or.inl
              (dmLt_of_all_lt_mem (M := (a :: as : List LevelKey))
                (N := (b :: bs : List LevelKey)) (z := b) (by simp) (by simpa using hall)))
          · subst b
            rcases ih bs hxs'.2 hys'.2 with hEq | hlt | hgt
            · exact Or.inl (by simpa using congrArg (fun m : Multiset LevelKey => {a} + m) hEq)
            · exact Or.inr (Or.inl (by
                have h := dmLt_add_left ({a} : Multiset LevelKey) hlt
                simpa using h))
            · exact Or.inr (Or.inr (by
                have h := dmLt_add_left ({a} : Multiset LevelKey) hgt
                simpa using h))
          · have hall : ∀ y ∈ (b :: bs : List LevelKey), y < a := by
              intro y hy
              rcases List.mem_cons.mp hy with rfl | hy
              · exact hba
              · exact lt_of_le_of_lt (hys'.1 y hy) hba
            exact Or.inr (Or.inr
              (dmLt_of_all_lt_mem (M := (b :: bs : List LevelKey))
                (N := (a :: as : List LevelKey)) (z := a) (by simp) (by simpa using hall)))

/-- The strict DM order is total on unequal `LevelKey` multisets. -/
theorem dmTrichotomy (M N : Multiset LevelKey) :
    M = N ∨ Multiset.IsDershowitzMannaLT M N ∨
      Multiset.IsDershowitzMannaLT N M := by
  let xs := Multiset.sort (fun a b : LevelKey => b ≤ a) M
  let ys := Multiset.sort (fun a b : LevelKey => b ≤ a) N
  have hxs : xs.Pairwise (fun a b : LevelKey => b ≤ a) := by
    dsimp [xs]
    exact Multiset.sort_sorted (fun a b : LevelKey => b ≤ a) M
  have hys : ys.Pairwise (fun a b : LevelKey => b ≤ a) := by
    dsimp [ys]
    exact Multiset.sort_sorted (fun a b : LevelKey => b ≤ a) N
  have hxcoe : (xs : Multiset LevelKey) = M := by
    dsimp [xs]
    exact Multiset.sort_eq (fun a b : LevelKey => b ≤ a) M
  have hycoe : (ys : Multiset LevelKey) = N := by
    dsimp [ys]
    exact Multiset.sort_eq (fun a b : LevelKey => b ≤ a) N
  rcases dmTrichotomy_sorted xs ys hxs hys with hEq | hlt | hgt
  · exact Or.inl (by simpa [hxcoe, hycoe] using hEq)
  · exact Or.inr (Or.inl (by simpa [hxcoe, hycoe] using hlt))
  · exact Or.inr (Or.inr (by simpa [hxcoe, hycoe] using hgt))

/-- The reflexive-transitive closure `DMLe` collapses to equality or one strict
DM comparison because the strict DM relation is itself transitive. -/
theorem dmLe_iff_eq_or_lt {M N : Multiset LevelKey} :
    DMLe M N ↔ M = N ∨ Multiset.IsDershowitzMannaLT M N := by
  constructor
  · intro h
    induction h with
    | refl => exact Or.inl rfl
    | tail hAB hBC ih =>
        rcases ih with rfl | hlt
        · exact Or.inr hBC
        · exact Or.inr (Multiset.IsDershowitzMannaLT.trans hlt hBC)
  · rintro (rfl | hlt)
    · exact DMLe.refl M
    · exact DMLe.of_lt hlt

/-- Strict DM cancellation of an arbitrary common additive context. -/
theorem dmLt_cancel_left (Q : Multiset LevelKey) {M N : Multiset LevelKey}
    (h : Multiset.IsDershowitzMannaLT (Q + M) (Q + N)) :
    Multiset.IsDershowitzMannaLT M N := by
  have hne : M ≠ N := by
    intro hMN
    subst N
    exact dmLt_irrefl (Q + M) h
  rcases dmTrichotomy M N with hEq | hlt | hgt
  · exact False.elim (hne hEq)
  · exact hlt
  · have hrev : Multiset.IsDershowitzMannaLT (Q + N) (Q + M) :=
      dmLt_add_left Q hgt
    exact False.elim (dmLt_irrefl (Q + M)
      (Multiset.IsDershowitzMannaLT.trans h hrev))

/-- Non-strict DM cancellation of an arbitrary common additive context. -/
theorem DMLe.cancel_left (Q : Multiset LevelKey) {M N : Multiset LevelKey}
    (h : DMLe (Q + M) (Q + N)) : DMLe M N := by
  rcases dmLe_iff_eq_or_lt.mp h with hEq | hlt
  · have hMN : M = N := by
      exact add_left_cancel hEq
    subst N
    exact DMLe.refl M
  · exact DMLe.of_lt (dmLt_cancel_left Q hlt)

/-- Right cancellation, by commutativity. -/
theorem DMLe.cancel_right (Q : Multiset LevelKey) {M N : Multiset LevelKey}
    (h : DMLe (M + Q) (N + Q)) : DMLe M N := by
  apply DMLe.cancel_left Q
  simpa [add_comm] using h

end OperatorKO7.Meta.UniqueNormalization

#check @OperatorKO7.Meta.UniqueNormalization.dmLt_irrefl
#check @OperatorKO7.Meta.UniqueNormalization.dmLt_zero_of_ne_zero
#check @OperatorKO7.Meta.UniqueNormalization.dmLt_of_all_lt_mem
#check @OperatorKO7.Meta.UniqueNormalization.dmTrichotomy_sorted
#check @OperatorKO7.Meta.UniqueNormalization.dmTrichotomy
#check @OperatorKO7.Meta.UniqueNormalization.dmLe_iff_eq_or_lt
#check @OperatorKO7.Meta.UniqueNormalization.dmLt_cancel_left
#check @OperatorKO7.Meta.UniqueNormalization.DMLe.cancel_left
#check @OperatorKO7.Meta.UniqueNormalization.DMLe.cancel_right

#print axioms OperatorKO7.Meta.UniqueNormalization.dmLt_irrefl
#print axioms OperatorKO7.Meta.UniqueNormalization.dmLt_zero_of_ne_zero
#print axioms OperatorKO7.Meta.UniqueNormalization.dmLt_of_all_lt_mem
#print axioms OperatorKO7.Meta.UniqueNormalization.dmTrichotomy_sorted
#print axioms OperatorKO7.Meta.UniqueNormalization.dmTrichotomy
#print axioms OperatorKO7.Meta.UniqueNormalization.dmLe_iff_eq_or_lt
#print axioms OperatorKO7.Meta.UniqueNormalization.dmLt_cancel_left
#print axioms OperatorKO7.Meta.UniqueNormalization.DMLe.cancel_left
#print axioms OperatorKO7.Meta.UniqueNormalization.DMLe.cancel_right
