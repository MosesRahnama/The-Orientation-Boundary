import Mathlib

/-!
# Finite distinction surfaces

The definitions count non-null records on diagonal inputs and absent non-null records on distinct
ordered pairs. The carrier and verdict types are finite and generic, independently of KO7 syntax or
a reduction relation.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.DistinctionBoundary.Quantitative

universe u v

/-- A finite comparison surface together with the Boolean predicate selecting
non-null distinction records. -/
structure FiniteDistinctionSurface (A : Type u) (V : Type v)
    [Fintype A] [DecidableEq A] [Fintype V] [DecidableEq V] where
  emits : A -> A -> Finset V
  nonnull : V -> Bool

namespace FiniteDistinctionSurface

variable {A : Type u} {V : Type v}
variable [Fintype A] [DecidableEq A] [Fintype V] [DecidableEq V]

/-- The non-null records emitted on an input. -/
def nonNullRecords (S : FiniteDistinctionSurface A V) (a b : A) : Finset V :=
  (S.emits a b).filter fun record => S.nonnull record = true

/-- Whether the surface can emit at least one non-null record on an input. -/
def emitsNonNull (S : FiniteDistinctionSurface A V) (a b : A) : Bool :=
  decide (S.nonNullRecords a b).Nonempty

/-- Diagonal condition requiring `emitsNonNull a a = false` at every carrier point. -/
def DiagonalSound (S : FiniteDistinctionSurface A V) : Prop :=
  forall a, S.emitsNonNull a a = false

/-- Off-diagonal condition requiring a non-null record at every distinct ordered pair. -/
def OffDiagonalProductive (S : FiniteDistinctionSurface A V) : Prop :=
  forall a b, a ≠ b -> S.emitsNonNull a b = true

/-- The number of carrier points with an illegal non-null diagonal record. -/
def diagonalFalsePositive (S : FiniteDistinctionSurface A V) : Nat :=
  (Finset.univ.filter fun a => S.emitsNonNull a a = true).card

/-- The number of ordered distinct pairs with no non-null emitted record. -/
def offDiagonalFalseNegative (S : FiniteDistinctionSurface A V) : Nat :=
  ((Finset.univ.product Finset.univ).filter fun ab =>
    ab.1 ≠ ab.2 ∧ S.emitsNonNull ab.1 ab.2 = false).card

/-- Characterize zero diagonal false positives by `DiagonalSound`. -/
theorem diagonalFalsePositive_eq_zero_iff_sound
    (S : FiniteDistinctionSurface A V) :
    S.diagonalFalsePositive = 0 <-> S.DiagonalSound := by
  constructor
  · intro hzero a
    have hempty :
        Finset.univ.filter (fun x => S.emitsNonNull x x = true) = ∅ :=
      Finset.card_eq_zero.mp hzero
    cases hvalue : S.emitsNonNull a a with
    | false => rfl
    | true =>
        have hmem : a ∈ Finset.univ.filter
            (fun x => S.emitsNonNull x x = true) := by
          simp [hvalue]
        rw [hempty] at hmem
        simp at hmem
  · intro hsound
    apply Finset.card_eq_zero.mpr
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.notMem_empty, iff_false]
    rw [hsound a]
    simp

/-- Characterize zero off-diagonal false negatives by `OffDiagonalProductive`. -/
theorem offDiagonalFalseNegative_eq_zero_iff_productive
    (S : FiniteDistinctionSurface A V) :
    S.offDiagonalFalseNegative = 0 <-> S.OffDiagonalProductive := by
  constructor
  · intro hzero a b hab
    have hempty :
        (Finset.univ.product Finset.univ).filter (fun ab =>
          ab.1 ≠ ab.2 ∧ S.emitsNonNull ab.1 ab.2 = false) = ∅ :=
      Finset.card_eq_zero.mp hzero
    cases hvalue : S.emitsNonNull a b with
    | true => rfl
    | false =>
        have hmem : (a, b) ∈
            (Finset.univ.product Finset.univ).filter (fun ab =>
              ab.1 ≠ ab.2 ∧ S.emitsNonNull ab.1 ab.2 = false) := by
          simp [hab, hvalue]
        rw [hempty] at hmem
        simp at hmem
  · intro hproductive
    apply Finset.card_eq_zero.mpr
    ext ab
    simp only [Finset.mem_filter, Finset.notMem_empty, iff_false]
    intro hbad
    have htrue := hproductive ab.1 ab.2 hbad.2.1
    rw [htrue] at hbad
    simp at hbad

/-- Rational diagonal false-positive rate. Lean's rational division assigns value zero when the
carrier cardinality, and hence the denominator, is zero. -/
def diagonalFalsePositiveRate (S : FiniteDistinctionSurface A V) : Rat :=
  S.diagonalFalsePositive / Fintype.card A

/-- Rational off-diagonal false-negative rate over ordered distinct pairs. Its denominator is
positive for carriers of cardinality at least two and is zero for cardinalities zero and one; Lean's
rational division assigns value zero in the latter cases. -/
def offDiagonalFalseNegativeRate (S : FiniteDistinctionSurface A V) : Rat :=
  S.offDiagonalFalseNegative /
    (Fintype.card A * (Fintype.card A - 1))

/-- Diagonal rate with a `Nonempty` instance supplying a positive sample count. -/
def diagonalFalsePositiveRateGuarded [Nonempty A]
    (S : FiniteDistinctionSurface A V) : Rat :=
  if h : 0 < Fintype.card A then S.diagonalFalsePositive / Fintype.card A
  else False.elim (h Fintype.card_pos)

/-- Guarded off-diagonal rate on carriers with at least two points. -/
def offDiagonalFalseNegativeRateGuarded
    (S : FiniteDistinctionSurface A V) (hcard : 2 <= Fintype.card A) : Rat :=
  if h : 2 <= Fintype.card A then
    S.offDiagonalFalseNegative / (Fintype.card A * (Fintype.card A - 1))
  else False.elim (h hcard)

omit [DecidableEq A] in
theorem offDiagonal_denominator_pos (hcard : 2 <= Fintype.card A) :
    0 < Fintype.card A * (Fintype.card A - 1) := by
  have hleft : 0 < Fintype.card A := by omega
  have hright : 0 < Fintype.card A - 1 := by omega
  exact Nat.mul_pos hleft hright

/-- Equality comparator with null diagonal records and non-null records on distinct pairs. -/
def exactEqualitySurface : FiniteDistinctionSurface A Bool where
  emits a b := if a = b then {false} else {true}
  nonnull := id

theorem exactEqualitySurface_sound :
    (exactEqualitySurface (A := A)).DiagonalSound := by
  intro a
  simp [exactEqualitySurface, emitsNonNull, nonNullRecords]
  decide

theorem exactEqualitySurface_productive :
    (exactEqualitySurface (A := A)).OffDiagonalProductive := by
  intro a b hab
  simp [exactEqualitySurface, emitsNonNull, nonNullRecords, hab]
  exact ⟨true, by simp⟩

theorem exactEqualitySurface_counts :
    (exactEqualitySurface (A := A)).diagonalFalsePositive = 0 /\
      (exactEqualitySurface (A := A)).offDiagonalFalseNegative = 0 := by
  exact
    ⟨(diagonalFalsePositive_eq_zero_iff_sound _).2 exactEqualitySurface_sound,
      (offDiagonalFalseNegative_eq_zero_iff_productive _).2
        exactEqualitySurface_productive⟩

/-- A totalized comparator that emits `different` on every ordered pair. -/
def alwaysDifferentSurface : FiniteDistinctionSurface A Bool where
  emits _ _ := {true}
  nonnull := id

theorem alwaysDifferent_diagonalFalsePositive :
    (alwaysDifferentSurface (A := A)).diagonalFalsePositive = Fintype.card A := by
  have hnonempty :
      ({record ∈ ({true} : Finset Bool) | record = true}).Nonempty := by
    exact ⟨true, by simp⟩
  simp [alwaysDifferentSurface, diagonalFalsePositive, emitsNonNull,
    nonNullRecords, hnonempty]

/-- The number of uniformly weighted ordered pairs classified correctly by the
always-different comparator. -/
def alwaysDifferentCorrectPairCount : Nat :=
  ((Finset.univ : Finset A).offDiag).card

theorem alwaysDifferent_correctPairCount :
    alwaysDifferentCorrectPairCount (A := A) =
      Fintype.card A * Fintype.card A - Fintype.card A := by
  simp [alwaysDifferentCorrectPairCount, Finset.offDiag_card]

/-- On a nonempty `n`-point carrier, the always-different comparator has aggregate accuracy
`1 - 1/n`; its diagonal false-positive count is `n` by `alwaysDifferent_diagonalFalsePositive`. -/
theorem alwaysDifferent_uniform_accuracy [Nonempty A] :
    (alwaysDifferentCorrectPairCount (A := A) : Rat) /
        ((Fintype.card A : Rat) ^ 2) =
      1 - 1 / (Fintype.card A : Rat) := by
  have hn : 0 < Fintype.card A := Fintype.card_pos
  have hn1 : 1 ≤ Fintype.card A := hn
  have hle : Fintype.card A ≤ Fintype.card A * Fintype.card A := by
    nlinarith
  have hn0 : (Fintype.card A : Rat) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  rw [alwaysDifferent_correctPairCount]
  rw [Nat.cast_sub hle]
  push_cast
  field_simp
  ring

/-! ## Finite fixtures -/

/-- Two-point fixture with one non-null diagonal cell. -/
def oneIllegalDiagonalSurface : FiniteDistinctionSurface (Fin 2) Bool where
  emits a b :=
    if a = 0 && b = 0 then {true}
    else if a = b then {false}
    else {true}
  nonnull := id

theorem oneIllegalDiagonalSurface_falsePositive :
    oneIllegalDiagonalSurface.diagonalFalsePositive = 1 := by
  norm_num [diagonalFalsePositive, emitsNonNull, nonNullRecords,
    oneIllegalDiagonalSurface]
  decide

theorem oneIllegalDiagonalSurface_not_sound :
    Not oneIllegalDiagonalSurface.DiagonalSound := by
  intro hsound
  have hzero := (diagonalFalsePositive_eq_zero_iff_sound _).2 hsound
  rw [oneIllegalDiagonalSurface_falsePositive] at hzero
  omega

theorem alwaysDifferent_fin8_accuracy :
    (alwaysDifferentCorrectPairCount (A := Fin 8) : Rat) /
        ((Fintype.card (Fin 8) : Rat) ^ 2) = 7 / 8 := by
  norm_num [alwaysDifferentCorrectPairCount, Finset.offDiag_card]

#print axioms diagonalFalsePositive_eq_zero_iff_sound
#print axioms offDiagonalFalseNegative_eq_zero_iff_productive
#print axioms alwaysDifferent_uniform_accuracy
#print axioms exactEqualitySurface_counts
#print axioms oneIllegalDiagonalSurface_falsePositive

end FiniteDistinctionSurface

end OperatorKO7.Meta.DistinctionBoundary.Quantitative
