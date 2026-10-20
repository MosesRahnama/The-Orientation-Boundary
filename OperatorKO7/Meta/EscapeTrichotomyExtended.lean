import OperatorKO7.Meta.EscapeTrichotomy_PumpFree
import OperatorKO7.Meta.MatrixBarrierArcticNatural
import OperatorKO7.Meta.MatrixBarrierTropicalNatural_Schema
import OperatorKO7.Meta.NonlinearUnconstrainedExactLaw
import OperatorKO7.Meta.DominancePremiseSharpness
import OperatorKO7.Meta.TextbookDupInstance_FullStack
import OperatorKO7.Meta.Step_Complexity_LowerBound
import OperatorKO7.Meta.KBO_Impossible
import OperatorKO7.Meta.SymbolicComparatorBarrier_Weighted_Schema

/-!
# The escape universe extended, and the TTT2 rows explained

`Meta/EscapeTrichotomy_PumpFree.lean` states the trichotomy over the pump-free scalar and tracked
vector families. This run added four more families, and this module records the verdict for each
so the universe the trichotomy is stated over and the universe of families that exist stay the
same set.

| Family | Verdict |
|---|---|
| arctic matrices | finite diagonals are blocked, and the complementary class contains an escape |
| tropical matrices | escapes; the barrier is false and the orienter is compiled |
| the unconstrained direct law | blocked |
| the textbook duplicating rule | blocked by the whole stack |

The tropical row is the one that changes the shape of the universe: it is the first family in the
catalog whose barrier is refuted rather than proved, so the trichotomy's third branch, leaving the
formalized families, is now inhabited by a family with a compiled witness.

The second half separates four method-family barriers from the FBI row.  POLY, KBO, MAT(2), and
MAT(3) carry universal obstruction theorems on their stated interfaces.  The FBI tool outcome has
no typed transport from forward/backward instantiation to the independent no-linear-bound theorem;
that theorem is retained as an invariant, not relabelled as an explanation of the tool outcome.

Relation: the KO7 root relation and the schema duplicating step. Closure: root.
External trust: the TTT2 tool runs themselves, which are inputs and not proofs.
-/

namespace OperatorKO7.EscapeTrichotomyExtended

open OperatorKO7
open OperatorKO7.StepDuplicating
open OperatorKO7.StepDuplicating.StepDuplicatingSchema
open OperatorKO7.CompositionalImpossibility

/-! ## The four families this run added -/

/-- The families added to the catalog beyond the pump-free trichotomy universe. -/
inductive AddedFamily where
  | arcticMatrix
  | tropicalMatrix
  | unconstrainedDirect
  | textbookInstance
  deriving DecidableEq, Repr

/-- The verdict a family carries. -/
inductive FamilyVerdict where
  /-- Every member of the family fails to orient the duplicating step. -/
  | blocked
  /-- A compiled member of the family orients it, so the barrier is false there. -/
  | escapes
  /-- A proved subfamily is blocked and a compiled member outside it escapes. -/
  | split
  deriving DecidableEq, Repr

/-- The verdict per added family. -/
def addedFamilyVerdict : AddedFamily → FamilyVerdict
  | .arcticMatrix => .split
  | .tropicalMatrix => .escapes
  | .unconstrainedDirect => .blocked
  | .textbookInstance => .blocked

/-- Strict orientation of the schema duplicating step by one arctic coordinate. -/
def ArcticStrictOrientation {S : StepDuplicatingSchema} {d : Nat}
    (M : ArcticNatMatrixMeasure S d) (i : Fin d) : Prop :=
  ∀ b s n : S.T,
    ArcticLt (M.eval (S.wrap s (S.recur b s n)) i)
      (M.eval (S.recur b s (S.succ n)) i)

/-- **The finite-diagonal arctic subfamily is blocked, with no positivity premise.** -/
theorem arctic_family_blocked
    {S : StepDuplicatingSchema} {d : Nat} (M : ArcticNatMatrixMeasure S d) {i : Fin d}
    (hi : ArcticWrapDiagFinite M i) :
    ¬ (∀ (b s n : S.T),
      ArcticLt (M.eval (S.wrap s (S.recur b s n)) i) (M.eval (S.recur b s (S.succ n)) i)) :=
  no_arcticMatrix_orients_dup_step_of_tracked_strict_pumpFree M hi (fun h => h)

/-- Strict arctic orientation universally forces failure of the finite-diagonal condition. -/
theorem arctic_strict_orientation_forces_nonfinite
    {S : StepDuplicatingSchema} {d : Nat} (M : ArcticNatMatrixMeasure S d) {i : Fin d}
    (h : ArcticStrictOrientation M i) : ¬ ArcticWrapDiagFinite M i :=
  fun hi => arctic_family_blocked M hi h

/-- The bottom-diagonal part of the same arctic family contains a strict orienter. -/
theorem arctic_bottom_diagonal_member_escapes :
    ∃ M : ArcticNatMatrixMeasure freeSchema 1,
      ¬ ArcticWrapDiagFinite M 0 ∧ ArcticStrictOrientation M 0 :=
  ⟨arcticBotRightMeasure, arcticBotRightMeasure_not_wrapDiagFinite,
    arcticBotRightMeasure_strictly_orients⟩

/-- The full arctic family is not universally blocked. -/
theorem arctic_family_not_universally_blocked :
    ¬ ∀ M : ArcticNatMatrixMeasure freeSchema 1, ¬ ArcticStrictOrientation M 0 := by
  intro h
  exact h arcticBotRightMeasure arcticBotRightMeasure_strictly_orients

/-- The full arctic family is not universally escaping either: the constant finite-diagonal
interpretation cannot orient the strict step. -/
theorem arctic_family_not_universally_escaping :
    ¬ ∀ M : ArcticNatMatrixMeasure freeSchema 1, ArcticStrictOrientation M 0 := by
  intro h
  have hfinite : ArcticWrapDiagFinite (constantArcticMeasure freeSchema) 0 :=
    ⟨⟨0, rfl⟩, ⟨0, rfl⟩⟩
  exact arctic_family_blocked (constantArcticMeasure freeSchema) hfinite
    (h (constantArcticMeasure freeSchema))

/-- Unconditional two-sided classification of the arctic family used here: finite diagonals are
universally impossible, any strict orienter must lie outside that subclass, and both an orienting
outside witness and a failing finite witness exist. -/
structure ArcticFamilySplit : Prop where
  finiteDiagonalBlocked :
    ∀ {S : StepDuplicatingSchema} {d : Nat} (M : ArcticNatMatrixMeasure S d) {i : Fin d},
      ArcticWrapDiagFinite M i → ¬ ArcticStrictOrientation M i
  orientationForcesNonfinite :
    ∀ {S : StepDuplicatingSchema} {d : Nat} (M : ArcticNatMatrixMeasure S d) {i : Fin d},
      ArcticStrictOrientation M i → ¬ ArcticWrapDiagFinite M i
  bottomDiagonalEscapes :
    ∃ M : ArcticNatMatrixMeasure freeSchema 1,
      ¬ ArcticWrapDiagFinite M 0 ∧ ArcticStrictOrientation M 0
  notUniversallyBlocked :
    ¬ ∀ M : ArcticNatMatrixMeasure freeSchema 1, ¬ ArcticStrictOrientation M 0
  notUniversallyEscaping :
    ¬ ∀ M : ArcticNatMatrixMeasure freeSchema 1, ArcticStrictOrientation M 0

theorem arctic_family_exact_split : ArcticFamilySplit where
  finiteDiagonalBlocked := fun {_} {_} M {_} hi => arctic_family_blocked M hi
  orientationForcesNonfinite := fun {_} {_} M {_} h =>
    arctic_strict_orientation_forces_nonfinite M h
  bottomDiagonalEscapes := arctic_bottom_diagonal_member_escapes
  notUniversallyBlocked := arctic_family_not_universally_blocked
  notUniversallyEscaping := arctic_family_not_universally_escaping

/-- **The tropical family escapes.** A compiled min-plus interpretation with positive wrapper
diagonal entries and a finite coordinate everywhere orients the duplicating step strictly. -/
theorem tropical_family_escapes :
    ∃ (M : TropicalNatMatrixMeasure freeSchema 1),
      TropicalWrapDiagPositive M 0 ∧
        (∃ (t : FreeTerm) (a : Nat), M.eval t 0 = TropicalNat.fin a) ∧
        (∀ (b s n : FreeTerm),
          TropicalLt (M.eval (freeSchema.wrap s (freeSchema.recur b s n)) 0)
            (M.eval (freeSchema.recur b s (freeSchema.succ n)) 0)) :=
  certificate_free_tropical_barrier_false

/-- **The unconstrained direct law is blocked.** -/
theorem unconstrainedDirect_family_blocked
    {S : StepDuplicatingSchema} (L : UnconstrainedDirectLaw S) :
    ¬ (∀ (b s n : S.T),
      L.eval (S.wrap s (S.recur b s n)) < L.eval (S.recur b s (S.succ n))) :=
  no_unconstrainedDirect_orients_dup_step L

/-- **The textbook instance is blocked by the whole stack.** -/
theorem textbook_family_blocked : OperatorKO7.TextbookDupInstance.TextbookFullBarrierStack :=
  OperatorKO7.TextbookDupInstance.textbook_rule_carries_full_barrier_stack

/-- Proof-bearing evidence for every entry in `addedFamilyVerdict`. The fields carry the actual
universal obstruction or escape proposition; enum equalities alone are not accepted as evidence. -/
structure AddedFamilyVerdictEvidence : Prop where
  verdicts :
    addedFamilyVerdict .arcticMatrix = .split
      ∧ addedFamilyVerdict .tropicalMatrix = .escapes
      ∧ addedFamilyVerdict .unconstrainedDirect = .blocked
      ∧ addedFamilyVerdict .textbookInstance = .blocked
  arctic : ArcticFamilySplit
  tropical :
    ∃ (M : TropicalNatMatrixMeasure freeSchema 1),
      TropicalWrapDiagPositive M 0 ∧
        (∃ (t : FreeTerm) (a : Nat), M.eval t 0 = TropicalNat.fin a) ∧
        (∀ b s n : FreeTerm,
          TropicalLt (M.eval (freeSchema.wrap s (freeSchema.recur b s n)) 0)
            (M.eval (freeSchema.recur b s (freeSchema.succ n)) 0))
  unconstrained :
    ∀ {S : StepDuplicatingSchema} (L : UnconstrainedDirectLaw S),
      ¬ (∀ b s n : S.T,
        L.eval (S.wrap s (S.recur b s n)) < L.eval (S.recur b s (S.succ n)))
  textbook : OperatorKO7.TextbookDupInstance.TextbookFullBarrierStack

/-- **Every added family carries its exact verdict.** -/
theorem added_families_carry_their_verdict : AddedFamilyVerdictEvidence where
  verdicts := ⟨rfl, rfl, rfl, rfl⟩
  arctic := arctic_family_exact_split
  tropical := tropical_family_escapes
  unconstrained := unconstrainedDirect_family_blocked
  textbook := textbook_family_blocked

/-! ## The TTT2 rows -/

/-- A proposed linear derivational-complexity certificate for the actual full contextual KO7
relation. This is a property of the rewrite relation, not a proxy definition of FBI. -/
def LinearDerivationalBound (C : Nat) : Prop :=
  ∀ (t u : Trace) (m : Nat), MetaSN_KO7.StepCtxFullPow t m u →
    m ≤ C * MetaSN_KO7.termSize t

/-- The actual contextual KO7 relation admits no linear derivational bound. -/
theorem ko7_has_no_linear_derivational_bound (C : Nat) :
    ¬ LinearDerivationalBound C := by
  intro hC
  obtain ⟨t, u, m, hpow, hgt⟩ := MetaSN_KO7.step_not_linear_derivational_complexity C
  exact (Nat.not_lt_of_ge (hC t u m hpow)) hgt

/-- The five TTT2 strategies that returned MAYBE on the eight-rule KO7 system. -/
inductive TTT2MaybeRow where
  | poly
  | kbo
  | mat2
  | mat3
  | fbi
  deriving DecidableEq, Repr

/-- All finite dimensions of the natural-matrix MAYBE family carry the same tracked-coordinate
barrier. -/
theorem natural_matrix_maybe_family_explained
    (S : StepDuplicatingSchema) (d : Nat) (M : NatMatrixMeasure S d) (i : Fin d)
    (hi : WrapDiagPositive M i) :
    ¬ (∀ b s n : S.T,
      M.eval (S.wrap s (S.recur b s n)) i < M.eval (S.recur b s (S.succ n)) i) :=
  no_natMatrix_orients_dup_step_of_tracked_strict M hi (fun h => h)

/-- Evidence boundary for the five MAYBE rows.  Four fields are method-family obstructions.  The
FBI field is deliberately typed as an independent invariant of the contextual relation, because no
formal FBI-to-linear-complexity transport exists in this development. -/
structure TTT2MaybeEvidenceBoundary : Prop where
  /-- POLY: the formalized direct polynomial families are blocked, under the frozen base
  dominance the general family carries, with the premise's necessity compiled. -/
  polyExplained :
    ∀ (S : StepDuplicatingSchema) (M : BoundedPolynomialMeasure S),
      EventuallyDominatedAtBase M →
        ¬ (∀ (b s n : S.T),
          M.eval (S.wrap s (S.recur b s n)) < M.eval (S.recur b s (S.succ n)))
  /-- KBO: a comparator satisfying the coefficient-weighted variable condition rejects the
  duplicating orientation at the rule schema. -/
  kboExplained :
    ¬ ∃ (C : OperatorKO7.SymbolicComparatorBarrier.SubtermCoefficients)
        (O : OperatorKO7.SymbolicComparatorBarrier.WeightedVariableConditionOrder C),
        O.gt OperatorKO7.SymbolicComparatorBarrier.dupSrc
          OperatorKO7.SymbolicComparatorBarrier.dupTgt
  /-- MAT(2): the dimension-two row. -/
  mat2Explained :
    ∀ (S : StepDuplicatingSchema) (M : NatMatrixMeasure S 2) (i : Fin 2),
      WrapDiagPositive M i →
        ¬ (∀ (b s n : S.T),
          M.eval (S.wrap s (S.recur b s n)) i < M.eval (S.recur b s (S.succ n)) i)
  /-- MAT(3): the dimension-three row. -/
  mat3Explained :
    ∀ (S : StepDuplicatingSchema) (M : NatMatrixMeasure S 3) (i : Fin 3),
      WrapDiagPositive M i →
        ¬ (∀ (b s n : S.T),
          M.eval (S.wrap s (S.recur b s n)) i < M.eval (S.recur b s (S.succ n)) i)
  /-- FBI boundary: the contextual relation has no linear derivational bound.  This field does not
  formalize FBI and is not an explanation of TTT2's MAYBE result. -/
  fbiIndependentInvariant :
    ∀ C : Nat, ¬ LinearDerivationalBound C

/-- Four direct-method rows carry exactly the typed obstructions in the record, with every
dominance, variable-condition, and positivity premise preserved; the fifth row carries only the
separately proved contextual complexity invariant. This theorem prevents the invariant from being
promoted to an FBI soundness or impossibility theorem. -/
theorem ttt2_maybe_rows_evidence_boundary : TTT2MaybeEvidenceBoundary where
  polyExplained := fun _ M hdom => no_polynomial_orients_dup_step_of_dominated M hdom
  kboExplained :=
    OperatorKO7.SymbolicComparatorBarrier.no_subtermCoefficient_variable_condition_orients_dup_step
  mat2Explained := fun S M i hi => natural_matrix_maybe_family_explained S 2 M i hi
  mat3Explained := fun S M i hi => natural_matrix_maybe_family_explained S 3 M i hi
  fbiIndependentInvariant := ko7_has_no_linear_derivational_bound

/-- The row list, with each row mapped to the field of the explanation record that carries it. -/
def ttt2MaybeRows : List TTT2MaybeRow := [.poly, .kbo, .mat2, .mat3, .fbi]

theorem ttt2MaybeRows_length : ttt2MaybeRows.length = 5 := by decide

theorem ttt2MaybeRows_nodup : ttt2MaybeRows.Nodup := by decide

theorem ttt2MaybeRows_complete (r : TTT2MaybeRow) : r ∈ ttt2MaybeRows := by
  cases r <;> decide

end OperatorKO7.EscapeTrichotomyExtended
