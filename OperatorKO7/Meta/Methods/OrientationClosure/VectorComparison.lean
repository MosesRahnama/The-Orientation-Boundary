import OperatorKO7.Meta.BoundaryGeneral.VectorOrderRepair

/-!
# Vector comparison boundary

The theorem below records the three distinct vector comparison regimes already
proved in the vector grammar development and keeps the cyclic compatibility
relation separate from genuine lexicographic comparison.
-/

set_option autoImplicit false

namespace OperatorKO7.Methods.OrientationClosure.VectorComparison

open OperatorKO7.Meta.BoundaryGeneral.DirectMeasureGrammarClosure
open OperatorKO7.Meta.BoundaryGeneral.VectorGrammarClosure
open OperatorKO7.Meta.BoundaryGeneral.VectorOrderRepair
open OperatorKO7.StepDuplicating.StepDuplicatingSchema

/-- All-coordinate strict comparison forces every grammar coordinate to be
payload-independent. -/
theorem allStrict_requires_all_payloadBlind {d : Nat}
    (M : VecMeasure d) (h : VecOrients M VecLt) :
    ∀ i : Fin d, PayloadBlind (M i).eval := by
  intro i
  exact componentwise_orients_implies_all_payload_blind M h i

/-- Genuine finite lexicographic comparison forces its first coordinate to be
payload-independent. -/
theorem lex_requires_primary_payloadBlind (d : Nat)
    (M : VecMeasure (d + 1)) (h : VecOrients M (@VecLexLt d)) :
    PayloadBlind (M (primaryIdx d)).eval :=
  vecLex_orients_implies_primary_payloadBlind d M h

/-- Strict-primary, weak-remaining comparison forces the primary coordinate to
be payload-independent. -/
theorem strictPrimaryWeak_requires_primary_payloadBlind (d : Nat)
    (M : VecMeasure (d + 1)) (h : VecOrients M (@PrimaryStrictWeakLt d)) :
    PayloadBlind (M (primaryIdx d)).eval :=
  primaryStrictWeak_orients_implies_primary_payloadBlind d M h

/-- The compatibility relation historically called `PrimaryFirstLt` is cyclic
for every finite dimension at least three. -/
theorem primarySomeDecrease_cyclic
    (d : Nat) (hd : 3 ≤ d) (i : Fin d) :
    ∃ u v : Fin d → Nat,
      PrimaryFirstLt i u v ∧ PrimaryFirstLt i v u :=
  primaryFirstLt_has_two_cycle_of_three_le d hd i

/-- The three relations differ semantically: the first two registered standard
orders are well-founded, while the some-secondary-decrease compatibility
relation is not well-founded in dimension at least three. -/
theorem vector_order_separation (d : Nat) :
    WellFounded (@VecLexLt d) ∧
      WellFounded (@PrimaryStrictWeakLt d) ∧
      (3 ≤ d + 1 → ∀ i : Fin (d + 1),
        ¬ WellFounded (@PrimaryFirstLt (d + 1) i)) := by
  exact ⟨vecLexLt_wellFounded d, primaryStrictWeakLt_wellFounded d,
    fun hd i => primaryFirstLt_not_wellFounded_of_three_le (d + 1) hd i⟩

/-- The counter-only vector supplies a non-vacuous orienting example for both
well-founded registered standard orders. -/
theorem counter_vector_orients_both_standard_orders (d : Nat) :
    VecOrients (counterVectorMeasure d) (@VecLexLt d) ∧
      VecOrients (counterVectorMeasure d) (@PrimaryStrictWeakLt d) :=
  ⟨counterVector_orients_vecLexLt d, counterVector_orients_primaryStrictWeakLt d⟩

/-- A payload-reading primary coordinate blocks genuine lexicographic
orientation. -/
theorem payload_primary_blocks_lex (d : Nat) (M : VecMeasure (d + 1))
    (hread : ¬ PayloadBlind (M (primaryIdx d)).eval) :
    ¬ VecOrients M (@VecLexLt d) := by
  intro h
  exact hread (lex_requires_primary_payloadBlind d M h)

/-- A payload-reading coordinate blocks all-coordinate strict orientation. -/
theorem payload_coordinate_blocks_allStrict {d : Nat} (M : VecMeasure d)
    (i : Fin d) (hread : ¬ PayloadBlind (M i).eval) :
    ¬ VecOrients M VecLt := by
  intro h
  exact hread (allStrict_requires_all_payloadBlind M h i)

/-- Fixed-row and row-sum matrix readings are instances of scalar domination,
not new ambient orders. -/
theorem matrix_scalarizations_are_dominated (d : Nat)
    (i : Fin (d + 1)) :
    DominatedByScalar (@PrimaryStrictWeakLt d) (fun u => u i) ∧
      DominatedByScalar (@PrimaryStrictWeakLt d)
        (@rowSumProjection (d + 1)) :=
  ⟨primaryStrictWeakLt_dominatedByCoordinate d i,
    primaryStrictWeakLt_dominatedByRowSum d⟩


/-- C09: counter in the primary coordinate and payload in every later coordinate. -/
def counterThenPayloadMeasure (d : Nat) : VecMeasure (d + 2) :=
  fun i => if i.val = 0 then MeasureExpr.counter else MeasureExpr.payload

/-- C09: genuine lexicographic comparison orients a vector that keeps the payload in its
later coordinates. -/
theorem counterThenPayload_orients_vecLexLt (d : Nat) :
    VecOrients (counterThenPayloadMeasure d) (@VecLexLt (d + 1)) := by
  intro c p L hL
  refine ⟨primaryIdx (d + 1), ?_, ?_⟩
  · intro j hj
    simp [primaryIdx] at hj
  · simp [counterThenPayloadMeasure, VecMeasure.eval, MeasureExpr.eval, primaryIdx]

/-- C09: the second coordinate of that vector reads the payload. -/
theorem counterThenPayload_secondary_reads_payload (d : Nat) :
    ¬ PayloadBlind (counterThenPayloadMeasure d ⟨1, by omega⟩).eval := by
  intro h
  have h01 := h 0 0 1
  simp [counterThenPayloadMeasure, MeasureExpr.eval] at h01

/-- C09: lexicographic orientation forces payload-blindness of the primary coordinate only;
later coordinates may retain the payload. -/
theorem lex_orientation_keeps_later_payload (d : Nat) :
    VecOrients (counterThenPayloadMeasure d) (@VecLexLt (d + 1)) ∧
      PayloadBlind (counterThenPayloadMeasure d (primaryIdx (d + 1))).eval ∧
      ¬ PayloadBlind (counterThenPayloadMeasure d ⟨1, by omega⟩).eval :=
  ⟨counterThenPayload_orients_vecLexLt d,
    lex_requires_primary_payloadBlind (d + 1) (counterThenPayloadMeasure d)
      (counterThenPayload_orients_vecLexLt d),
    counterThenPayload_secondary_reads_payload d⟩

end OperatorKO7.Methods.OrientationClosure.VectorComparison
