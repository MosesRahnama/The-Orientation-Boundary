import OperatorKO7.Meta.BoundaryObserver.Boundary
import OperatorKO7.Meta.BoundaryObserver.BoundaryPole
import OperatorKO7.Meta.BoundaryObserver.BoundarySingularity
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

set_option autoImplicit false

/-!
# Data processing for triangular discrimination

-/

namespace OperatorKO7.Meta.BoundaryObserver.DiscriminationGarbling

open scoped BigOperators
open OperatorKO7.Meta.BoundaryObserver.Boundary
open OperatorKO7.Meta.BoundaryObserver.BoundaryPole
open OperatorKO7.Meta.BoundaryObserver.BoundarySingularity
open OperatorKO7.Meta.BoundaryObserver.ProtocolResolution
open OperatorKO7.Meta.BoundaryObserver.PairResolution

/-- A finite input row is mapped through a kernel from input labels to output labels. -/
noncomputable def garble {Y Z : Type} [Fintype Y]
    (G : Y → Z → ℝ) (P : Y → ℝ) : Z → ℝ :=
  fun z => ∑ y, P y * G y z

/-- Multiplying both masses by the same real weight scales the triangular term. -/
private theorem weighted_term_eq (a b w : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ((a - b) * w) ^ 2 / ((a + b) * w) =
      (a - b) ^ 2 / (a + b) * w := by
  by_cases hs : a + b = 0
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    simp [ha0, hb0]
  · by_cases hw : w = 0
    · simp [hw]
    · field_simp [hs, hw]
      ring

/-- A nonnegative finite mixture contracts the triangular term, including zero weights. -/
private theorem weighted_discrimination_le {Y : Type} [Fintype Y]
    (P Q W : Y → ℝ) (hP : ∀ y, 0 ≤ P y)
    (hQ : ∀ y, 0 ≤ Q y) (hW : ∀ y, 0 ≤ W y) :
    (∑ y, (P y - Q y) * W y) ^ 2 / (∑ y, (P y + Q y) * W y) ≤
      ∑ y, ((P y - Q y) ^ 2 / (P y + Q y)) * W y := by
  classical
  let A : Y → ℝ := fun y => (P y - Q y) * W y
  let B : Y → ℝ := fun y => (P y + Q y) * W y
  let s : Finset Y := Finset.univ.filter (fun y => 0 < B y)
  have hB (y : Y) : 0 ≤ B y := mul_nonneg (add_nonneg (hP y) (hQ y)) (hW y)
  have hA_zero (y : Y) (hy : B y = 0) : A y = 0 := by
    have hy' : (P y + Q y) * W y = 0 := hy
    rcases mul_eq_zero.mp hy' with hsum | hw
    · have hp0 : P y = 0 := by linarith [hP y, hQ y]
      have hq0 : Q y = 0 := by linarith [hP y, hQ y]
      simp [A, hp0, hq0]
    · simp [A, hw]
  have hB_out (y : Y) (hy : y ∉ s) : B y = 0 := by
    have hn : ¬ 0 < B y := by
      intro hpos
      exact hy (Finset.mem_filter.mpr ⟨Finset.mem_univ y, hpos⟩)
    exact le_antisymm (le_of_not_gt hn) (hB y)
  have hsumA : (∑ y ∈ s, A y) = ∑ y, A y := by
    apply Finset.sum_subset (Finset.subset_univ s)
    intro y _ hy
    exact hA_zero y (hB_out y hy)
  have hsumB : (∑ y ∈ s, B y) = ∑ y, B y := by
    apply Finset.sum_subset (Finset.subset_univ s)
    intro y _ hy
    exact hB_out y hy
  have hsumTerm :
      (∑ y ∈ s, A y ^ 2 / B y) =
        ∑ y, ((P y - Q y) ^ 2 / (P y + Q y)) * W y := by
    calc
      (∑ y ∈ s, A y ^ 2 / B y) = ∑ y, A y ^ 2 / B y := by
        apply Finset.sum_subset (Finset.subset_univ s)
        intro y _ hy
        simp [hB_out y hy, hA_zero y (hB_out y hy)]
      _ = ∑ y, ((P y - Q y) ^ 2 / (P y + Q y)) * W y := by
        apply Finset.sum_congr rfl
        intro y _
        exact weighted_term_eq (P y) (Q y) (W y) (hP y) (hQ y)
  have hs : (∑ y ∈ s, A y) ^ 2 / (∑ y ∈ s, B y) ≤
      ∑ y ∈ s, A y ^ 2 / B y := by
    apply Finset.sq_sum_div_le_sum_sq_div s A
    intro y hy
    exact (Finset.mem_filter.mp hy).2
  rw [hsumA, hsumB, hsumTerm] at hs
  exact hs

/-- A finite nonnegative input pair loses no less triangular discrimination after
a stochastic garbling than it had before the garbling. -/
theorem discrimination_garbling_le {Y Z : Type} [Fintype Y] [Fintype Z]
    (G : Y → Z → ℝ) (P Q : Y → ℝ)
    (hP : ∀ y, 0 ≤ P y) (hQ : ∀ y, 0 ≤ Q y)
    (hG : ∀ y z, 0 ≤ G y z) (hGtotal : ∀ y, ∑ z, G y z = 1) :
    discrimination (garble G P) (garble G Q) ≤ discrimination P Q := by
  have hnum (z : Z) :
      garble G P z - garble G Q z = ∑ y, (P y - Q y) * G y z := by
    simp only [garble, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro y _
    ring
  have hden (z : Z) :
      garble G P z + garble G Q z = ∑ y, (P y + Q y) * G y z := by
    simp only [garble, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro y _
    ring
  calc
    discrimination (garble G P) (garble G Q) =
        ∑ z, (garble G P z - garble G Q z) ^ 2 /
          (garble G P z + garble G Q z) := rfl
    _ ≤ ∑ z, ∑ y, ((P y - Q y) ^ 2 / (P y + Q y)) * G y z := by
      apply Finset.sum_le_sum
      intro z _
      rw [hnum z, hden z]
      exact weighted_discrimination_le P Q (fun y => G y z) hP hQ (fun y => hG y z)
    _ = ∑ y, ((P y - Q y) ^ 2 / (P y + Q y)) * ∑ z, G y z := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.mul_sum]
    _ = discrimination P Q := by
      simp [discrimination, hGtotal]

/-- The deterministic row on the true range of a record has unit mass at that record. -/
noncomputable def deterministicRecordRow {X Q : Type} (q : X → Q) (x : X) :
    ↥(Set.range q) → ℝ := by
  classical
  exact fun r => if r = (⟨q x, ⟨x, rfl⟩⟩ : ↥(Set.range q)) then 1 else 0

/-- A finite record carrier induces a finite type on the attained record values. -/
private noncomputable instance finiteRecordRange {X Q : Type} [Fintype Q]
    (q : X → Q) : Fintype (↥(Set.range q)) :=
  Fintype.ofFinite _

/-- Every fiber-constant finite reading is a stochastic garbling of its
deterministic record row. Its discrimination is bounded by the record
discrimination, and both discriminations vanish on every merged pair. -/
theorem recordDetermined_is_garbling {X Q Y : Type} [Fintype Q] [Fintype Y]
    (q : X → Q) (K : Reading X Y) (hdet : RecordDetermined q K) :
    ∃ Kq : ↥(Set.range q) → FiniteLaw Y,
      (∀ x, K x = Kq ⟨q x, ⟨x, rfl⟩⟩) ∧
      (∀ x y, (K x).mass y =
        garble (fun r (y : Y) => (Kq r).mass y) (deterministicRecordRow q x) y) ∧
      (∀ x x', readingDiscrimination K x x' ≤
        discrimination (deterministicRecordRow q x) (deterministicRecordRow q x')) ∧
      (∀ x x', q x = q x' →
        readingDiscrimination K x x' = 0 ∧
        discrimination (deterministicRecordRow q x) (deterministicRecordRow q x') = 0) := by
  classical
  obtain ⟨Kq, hKq⟩ := (recordDetermined_iff_range_factor q K).mp hdet
  have hrep (x : X) (y : Y) :
      (K x).mass y =
        garble (fun r (z : Y) => (Kq r).mass z) (deterministicRecordRow q x) y := by
    calc
      (K x).mass y = (Kq ⟨q x, ⟨x, rfl⟩⟩).mass y :=
        congrArg (fun L : FiniteLaw Y => L.mass y) (hKq x)
      _ = garble (fun r (z : Y) => (Kq r).mass z) (deterministicRecordRow q x) y := by
        simp [garble, deterministicRecordRow]
  have hrow_nonneg (x : X) (r : ↥(Set.range q)) :
      0 ≤ deterministicRecordRow q x r := by
    unfold deterministicRecordRow
    split_ifs <;> norm_num
  have hbound (x x' : X) :
      readingDiscrimination K x x' ≤
        discrimination (deterministicRecordRow q x) (deterministicRecordRow q x') := by
    have hrx : (K x).mass =
        garble (fun r (z : Y) => (Kq r).mass z) (deterministicRecordRow q x) :=
      funext (hrep x)
    have hrx' : (K x').mass =
        garble (fun r (z : Y) => (Kq r).mass z) (deterministicRecordRow q x') :=
      funext (hrep x')
    change discrimination (K x).mass (K x').mass ≤ _
    rw [hrx, hrx']
    exact discrimination_garbling_le (fun r (z : Y) => (Kq r).mass z)
      (deterministicRecordRow q x) (deterministicRecordRow q x')
      (hrow_nonneg x) (hrow_nonneg x')
      (fun r z => (Kq r).nonnegative z) (fun r => (Kq r).total)
  have hmerged (x x' : X) (hq : q x = q x') :
      readingDiscrimination K x x' = 0 ∧
        discrimination (deterministicRecordRow q x) (deterministicRecordRow q x') = 0 := by
    have hrecord :
        (⟨q x, ⟨x, rfl⟩⟩ : ↥(Set.range q)) =
          (⟨q x', ⟨x', rfl⟩⟩ : ↥(Set.range q)) :=
      Subtype.ext hq
    have hrow : deterministicRecordRow q x = deterministicRecordRow q x' := by
      funext r
      change (if r = (⟨q x, ⟨x, rfl⟩⟩ : ↥(Set.range q)) then (1 : ℝ) else 0) =
        (if r = (⟨q x', ⟨x', rfl⟩⟩ : ↥(Set.range q)) then 1 else 0)
      rw [hrecord]
    have hz : discrimination (deterministicRecordRow q x)
        (deterministicRecordRow q x') = 0 := by
      rw [hrow]
      simp [discrimination]
    have hle := hbound x x'
    have hnonneg : 0 ≤ readingDiscrimination K x x' :=
      discrimination_nonneg (K x).mass (K x').mass
        (K x).nonnegative (K x').nonnegative
    exact ⟨le_antisymm (by simpa only [hz] using hle) hnonneg, hz⟩
  exact ⟨Kq, hKq, hrep, hbound, hmerged⟩

end OperatorKO7.Meta.BoundaryObserver.DiscriminationGarbling

namespace OperatorKO7.Meta.BoundaryObserver.BoundarySingularity

open scoped BigOperators

/-- Triangular discrimination contracts under every nonnegative finite stochastic garbling kernel. -/
theorem discrimination_garbling_le {Y Z : Type} [Fintype Y] [Fintype Z]
    (G : Y → Z → ℝ) (P Q : Y → ℝ)
    (hP : ∀ y, 0 ≤ P y) (hQ : ∀ y, 0 ≤ Q y)
    (hG : ∀ y z, 0 ≤ G y z) (hGtotal : ∀ y, ∑ z, G y z = 1) :
    discrimination (DiscriminationGarbling.garble G P) (DiscriminationGarbling.garble G Q) ≤
      discrimination P Q := by
  exact DiscriminationGarbling.discrimination_garbling_le G P Q hP hQ hG hGtotal

end OperatorKO7.Meta.BoundaryObserver.BoundarySingularity
