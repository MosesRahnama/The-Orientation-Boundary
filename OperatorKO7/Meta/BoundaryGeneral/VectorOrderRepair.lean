import Mathlib.Data.DFinsupp.WellFounded
import OperatorKO7.Meta.BoundaryGeneral.VectorGrammarClosure
import OperatorKO7.Meta.MatrixBarrierLexD_Schema

/-!
# Genuine vector-order repair

This module preserves the existing `PrimaryFirstLt` relation under a name that
describes its actual semantics, records its finite two-cycle, and separately
registers the genuine prefix-equality lexicographic relation `VecLexLt`.

The matrix-facing corollaries below expose their scalar functional explicitly.
They do not treat a fixed row or a row sum as an independent ambient-order
theorem.

Trust: kernel-checked definitions and proofs over Mathlib and the imported KO7
schema modules; no external certificate or native computation.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.BoundaryGeneral.VectorOrderRepair

open OperatorKO7.StepDuplicating.StepDuplicatingSchema
open OperatorKO7.Meta.BoundaryGeneral.DirectMeasureGrammarClosure
open OperatorKO7.Meta.BoundaryGeneral.VectorGrammarClosure

/-! ## The compatibility relation is not a lexicographic order -/

/-- Compatibility name for the pre-existing relation: the primary coordinate
strictly decreases, or it ties while some secondary coordinate decreases. -/
def PrimarySomeDecreaseLt {d : Nat} (i : Fin d)
    (u v : Fin d → Nat) : Prop :=
  PrimaryFirstLt i u v

/-- An explicit two-cycle in dimension three. The primary coordinate is zero
on both vectors; coordinates one and two decrease in opposite directions. -/
theorem primarySomeDecrease_has_two_cycle :
    ∃ u v : Fin 3 → Nat,
      PrimarySomeDecreaseLt (0 : Fin 3) u v ∧
        PrimarySomeDecreaseLt (0 : Fin 3) v u := by
  let u : Fin 3 → Nat := fun i => if i = (2 : Fin 3) then 1 else 0
  let v : Fin 3 → Nat := fun i => if i = (1 : Fin 3) then 1 else 0
  refine ⟨u, v, ?_, ?_⟩
  · refine Or.inr ⟨?_, ⟨(1 : Fin 3), ?_, ?_⟩⟩
    · simp [u, v]
    · decide
    · simp [u, v]
  · refine Or.inr ⟨?_, ⟨(2 : Fin 3), ?_, ?_⟩⟩
    · simp [u, v]
    · decide
    · simp [u, v]

/-- The old `PrimaryFirstLt` name denotes the same cyclic relation. -/
theorem primaryFirstLt_fin3_two_cycle :
    ∃ u v : Fin 3 → Nat,
      PrimaryFirstLt (0 : Fin 3) u v ∧
        PrimaryFirstLt (0 : Fin 3) v u := by
  simpa [PrimarySomeDecreaseLt] using primarySomeDecrease_has_two_cycle

/-- The dimension-three compatibility relation is not well-founded. -/
theorem not_wellFounded_primaryFirstLt_fin3 :
    ¬ WellFounded (@PrimaryFirstLt 3 (0 : Fin 3)) := by
  intro hwf
  obtain ⟨u, v, huv, hvu⟩ := primaryFirstLt_fin3_two_cycle
  exact (hwf.asymmetric u v huv) hvu

/-- Every finite coordinate type of cardinality at least three contains two
distinct secondary coordinates relative to any designated primary one. -/
theorem exists_two_secondary_coordinates_of_three_le
    (d : Nat) (hd : 3 ≤ d) (i : Fin d) :
    ∃ j k : Fin d, j ≠ i ∧ k ≠ i ∧ j ≠ k := by
  have h0d : 0 < d :=
    lt_of_lt_of_le (by decide : 0 < 3) hd
  have h1d : 1 < d :=
    lt_of_lt_of_le (by decide : 1 < 3) hd
  have h2d : 2 < d :=
    lt_of_lt_of_le (by decide : 2 < 3) hd
  let i0 : Fin d := ⟨0, h0d⟩
  let i1 : Fin d := ⟨1, h1d⟩
  let i2 : Fin d := ⟨2, h2d⟩
  have h01 : i0 ≠ i1 := by
    simp [i0, i1]
  have h02 : i0 ≠ i2 := by
    simp [i0, i2]
  have h12 : i1 ≠ i2 := by
    simp [i1, i2]
  by_cases hi0 : i = i0
  · subst i
    exact ⟨i1, i2, Ne.symm h01, Ne.symm h02, h12⟩
  · by_cases hi1 : i = i1
    · subst i
      exact ⟨i0, i2, h01, Ne.symm h12, h02⟩
    · exact ⟨i0, i1, Ne.symm hi0, Ne.symm hi1, h01⟩

/-- Any two distinct secondary coordinates generate a two-cycle for
`PrimaryFirstLt`: each vector decreases on one secondary coordinate and
increases on the other while the primary coordinate ties. -/
theorem primaryFirstLt_two_cycle_of_secondary_coordinates
    {d : Nat} (i j k : Fin d)
    (hji : j ≠ i) (hki : k ≠ i) (hjk : j ≠ k) :
    ∃ u v : Fin d → Nat,
      PrimaryFirstLt i u v ∧ PrimaryFirstLt i v u := by
  let u : Fin d → Nat := fun x => if x = k then 1 else 0
  let v : Fin d → Nat := fun x => if x = j then 1 else 0
  refine ⟨u, v, ?_, ?_⟩
  · refine Or.inr ⟨?_, ⟨j, hji, ?_⟩⟩
    · simp [u, v, Ne.symm hki, Ne.symm hji]
    · simp [u, v, hjk]
  · refine Or.inr ⟨?_, ⟨k, hki, ?_⟩⟩
    · simp [u, v, Ne.symm hki, Ne.symm hji]
    · simp [u, v, Ne.symm hjk]

/-- In every dimension at least three and for every designated primary
coordinate, the compatibility relation contains an explicit two-cycle. -/
theorem primaryFirstLt_has_two_cycle_of_three_le
    (d : Nat) (hd : 3 ≤ d) (i : Fin d) :
    ∃ u v : Fin d → Nat,
      PrimaryFirstLt i u v ∧ PrimaryFirstLt i v u := by
  obtain ⟨j, k, hji, hki, hjk⟩ :=
    exists_two_secondary_coordinates_of_three_le d hd i
  exact primaryFirstLt_two_cycle_of_secondary_coordinates
    i j k hji hki hjk

/-- `PrimaryFirstLt` is not well-founded in any dimension at least three,
uniformly over the choice of designated primary coordinate.

Property: non-well-foundedness of the explicitly named compatibility relation.
Does not prove: any failure of the genuine prefix lexicographic order
`VecLexLt`, which is treated separately below. -/
theorem primaryFirstLt_not_wellFounded_of_three_le
    (d : Nat) (hd : 3 ≤ d) (i : Fin d) :
    ¬ WellFounded (@PrimaryFirstLt d i) := by
  intro hwf
  obtain ⟨u, v, huv, hvu⟩ :=
    primaryFirstLt_has_two_cycle_of_three_le d hd i
  exact (hwf.asymmetric u v huv) hvu

/-! ## The genuine finite lexicographic order -/

/-- Transitivity of the existing prefix-equality finite lexicographic order. -/
theorem vecLexLt_transitive (d : Nat) :
    Transitive (@VecLexLt d) := by
  intro u v w huv hvw
  rcases huv with ⟨i, hiPrefix, hui⟩
  rcases hvw with ⟨k, hkPrefix, hvk⟩
  rcases lt_trichotomy i k with hik | hik | hik
  · refine ⟨i, ?_, ?_⟩
    · intro j hj
      exact (hiPrefix j hj).trans (hkPrefix j (hj.trans hik))
    · exact hui.trans_eq (hkPrefix i hik)
  · subst k
    refine ⟨i, ?_, hui.trans hvk⟩
    intro j hj
    exact (hiPrefix j hj).trans (hkPrefix j hj)
  · refine ⟨k, ?_, ?_⟩
    · intro j hj
      exact (hiPrefix j (hj.trans hik)).trans (hkPrefix j hj)
    · exact (hiPrefix k hik).trans_lt hvk

/-- Well-foundedness of the existing finite prefix-equality lexicographic
order, obtained from Mathlib's well-founded finite `Pi.Lex` relation. -/
theorem vecLexLt_wellFounded (d : Nat) :
    WellFounded (@VecLexLt d) := by
  have hPi :
      WellFounded
        (Pi.Lex (fun i j : Fin (d + 1) => i < j)
          (fun {_ : Fin (d + 1)} (a b : Nat) => a < b)) :=
    Pi.Lex.wellFounded (r := fun i j : Fin (d + 1) => i < j)
      (fun _ => Nat.lt_wfRel.wf)
  simpa [VecLexLt, Pi.Lex] using hPi

/-- Genuine lexicographic comparison is dominated by its first coordinate. -/
theorem vecLexLt_dominatedByPrimary (d : Nat) :
    DominatedByScalar (@VecLexLt d)
      (fun u => u (primaryIdx d)) := by
  intro u v h
  exact primary_le_of_vecLexLt h

/-- Orientation by the genuine finite lexicographic order forces the primary
grammar coordinate to be payload-blind. -/
theorem vecLex_orients_implies_primary_payloadBlind (d : Nat)
    (M : VecMeasure (d + 1))
    (h : VecOrients M (@VecLexLt d)) :
    PayloadBlind (M (primaryIdx d)).eval := by
  exact
    dominated_scalar_orients_implies_payload_blind
      M (@VecLexLt d) (fun u => u (primaryIdx d))
      (M (primaryIdx d)) (fun _ _ => rfl)
      (vecLexLt_dominatedByPrimary d) h

/-! ## The paper's strict-primary, weak-remaining matrix order -/

/-- First-coordinate strictness together with componentwise weakness. This is
the concrete standard matrix order used here; it is distinct from strict-all
componentwise order and from `PrimarySomeDecreaseLt`. -/
def PrimaryStrictWeakLt {d : Nat}
    (u v : Fin (d + 1) → Nat) : Prop :=
  u (primaryIdx d) < v (primaryIdx d) ∧ ∀ i, u i ≤ v i

/-- The strict-primary, weak-remaining order is transitive. -/
theorem primaryStrictWeakLt_transitive (d : Nat) :
    Transitive (@PrimaryStrictWeakLt d) := by
  intro u v w huv hvw
  exact ⟨huv.1.trans hvw.1, fun i => (huv.2 i).trans (hvw.2 i)⟩

/-- Strict-primary, weak-remaining comparison is a subrelation of genuine
lexicographic comparison, with the first coordinate as the witness. -/
theorem primaryStrictWeakLt_sub_vecLexLt {d : Nat}
    {u v : Fin (d + 1) → Nat}
    (h : PrimaryStrictWeakLt u v) : VecLexLt u v := by
  refine ⟨primaryIdx d, ?_, h.1⟩
  intro j hj
  simp [primaryIdx] at hj

/-- The concrete strict-primary, weak-remaining order is well-founded. -/
theorem primaryStrictWeakLt_wellFounded (d : Nat) :
    WellFounded (@PrimaryStrictWeakLt d) :=
  Subrelation.wf (fun {_ _} h => primaryStrictWeakLt_sub_vecLexLt h)
    (vecLexLt_wellFounded d)

/-- Every fixed coordinate is a dominated scalar functional for the concrete
matrix order. -/
theorem primaryStrictWeakLt_dominatedByCoordinate (d : Nat)
    (i : Fin (d + 1)) :
    DominatedByScalar (@PrimaryStrictWeakLt d) (fun u => u i) := by
  intro u v h
  exact h.2 i

/-- The primary-coordinate specialization of scalar dominance. -/
theorem primaryStrictWeakLt_dominatedByPrimary (d : Nat) :
    DominatedByScalar (@PrimaryStrictWeakLt d)
      (fun u => u (primaryIdx d)) :=
  primaryStrictWeakLt_dominatedByCoordinate d (primaryIdx d)

/-- The concrete matrix order inherits the primary grammar barrier through its
explicit primary-coordinate scalarization. -/
theorem primaryStrictWeak_orients_implies_primary_payloadBlind (d : Nat)
    (M : VecMeasure (d + 1))
    (h : VecOrients M (@PrimaryStrictWeakLt d)) :
    PayloadBlind (M (primaryIdx d)).eval := by
  exact
    dominated_scalar_orients_implies_payload_blind
      M (@PrimaryStrictWeakLt d) (fun u => u (primaryIdx d))
      (M (primaryIdx d)) (fun _ _ => rfl)
      (primaryStrictWeakLt_dominatedByPrimary d) h

/-! ## Fixed-row and row-sum scalar-functional corollaries -/

/-- A fixed row is explicitly a scalar coordinate projection. -/
theorem fixedRow_orients_implies_payloadBlind {d : Nat}
    (M : VecMeasure d) (i : Fin d)
    (R : (Fin d → Nat) → (Fin d → Nat) → Prop)
    (hdom : DominatedByScalar R (fun u => u i))
    (h : VecOrients M R) :
    PayloadBlind (M i).eval := by
  exact
    dominated_scalar_orients_implies_payload_blind
      M R (fun u => u i) (M i) (fun _ _ => rfl) hdom h

/-- The canonical list of all coordinates in a finite vector. -/
def allCoordinates (d : Nat) : List (Fin d) :=
  List.ofFn (fun i : Fin d => i)

/-- Row-sum scalar projection, expressed through the existing weighted
projection interface with unit weights. -/
def rowSumProjection {d : Nat} (u : Fin d → Nat) : Nat :=
  weightedProj (fun _ => 1) (allCoordinates d) u

/-- Grammar expression denoting the row sum of a vector grammar measure. -/
def rowSumExpr {d : Nat} (M : VecMeasure d) : MeasureExpr :=
  weightedExpr (fun _ => 1) M (allCoordinates d)

/-- Pointwise weakness implies monotonicity of every nonnegative weighted
projection. -/
theorem weightedProj_le_of_pointwise {d : Nat}
    (w : Fin d → Nat) (l : List (Fin d))
    {u v : Fin d → Nat} (h : ∀ i, u i ≤ v i) :
    weightedProj w l u ≤ weightedProj w l v := by
  induction l with
  | nil => simp [weightedProj]
  | cons i rest ih =>
      simp only [weightedProj, List.map_cons, List.sum_cons]
      exact Nat.add_le_add (Nat.mul_le_mul_left (w i) (h i)) ih

/-- The concrete matrix order is dominated by the explicit row-sum scalar
functional. -/
theorem primaryStrictWeakLt_dominatedByRowSum (d : Nat) :
    DominatedByScalar (@PrimaryStrictWeakLt d)
      (@rowSumProjection (d + 1)) := by
  intro u v h
  exact weightedProj_le_of_pointwise (fun _ => 1) (allCoordinates (d + 1)) h.2

/-- A row-sum claim is the unit-weight instance of the generic scalar-functional
barrier, not a separate ambient-order theorem. -/
theorem rowSum_orients_implies_payloadBlind {d : Nat}
    (M : VecMeasure d)
    (R : (Fin d → Nat) → (Fin d → Nat) → Prop)
    (hdom : DominatedByScalar R (@rowSumProjection d))
    (h : VecOrients M R) :
    PayloadBlind (rowSumExpr M).eval := by
  simpa [rowSumProjection, rowSumExpr] using
    (weighted_orients_implies_payload_blind
      M (fun _ => 1) (allCoordinates d) R hdom h)

/-! ## Non-vacuity of the two registered standard orders -/

/-- A vector all of whose coordinates are the counter grammar expression. -/
def counterVectorMeasure (d : Nat) : VecMeasure (d + 1) :=
  fun _ => MeasureExpr.counter

/-- The counter vector genuinely orients the duplicating step under `VecLexLt`.
The first coordinate supplies the strict comparison. -/
theorem counterVector_orients_vecLexLt (d : Nat) :
    VecOrients (counterVectorMeasure d) (@VecLexLt d) := by
  intro c p L hL
  refine ⟨primaryIdx d, ?_, ?_⟩
  · intro j hj
    simp [primaryIdx] at hj
  · simp [counterVectorMeasure, VecMeasure.eval, MeasureExpr.eval]

/-- The same counter vector genuinely orients under strict-primary,
weak-remaining comparison. -/
theorem counterVector_orients_primaryStrictWeakLt (d : Nat) :
    VecOrients (counterVectorMeasure d) (@PrimaryStrictWeakLt d) := by
  intro c p L hL
  refine ⟨?_, ?_⟩
  · simp [counterVectorMeasure, VecMeasure.eval, MeasureExpr.eval]
  · intro i
    simp [counterVectorMeasure, VecMeasure.eval, MeasureExpr.eval]

/-- Non-vacuity package for every fixed-row scalar adapter of the concrete
matrix order. -/
theorem counterVector_fixedRow_adapter_nonvacuous (d : Nat)
    (i : Fin (d + 1)) :
    VecOrients (counterVectorMeasure d) (@PrimaryStrictWeakLt d) ∧
      DominatedByScalar (@PrimaryStrictWeakLt d) (fun u => u i) :=
  ⟨counterVector_orients_primaryStrictWeakLt d,
    primaryStrictWeakLt_dominatedByCoordinate d i⟩

/-- Non-vacuity package for the row-sum scalar adapter of the concrete matrix
order. -/
theorem counterVector_rowSum_adapter_nonvacuous (d : Nat) :
    VecOrients (counterVectorMeasure d) (@PrimaryStrictWeakLt d) ∧
      DominatedByScalar (@PrimaryStrictWeakLt d)
        (@rowSumProjection (d + 1)) :=
  ⟨counterVector_orients_primaryStrictWeakLt d,
    primaryStrictWeakLt_dominatedByRowSum d⟩

end OperatorKO7.Meta.BoundaryGeneral.VectorOrderRepair
