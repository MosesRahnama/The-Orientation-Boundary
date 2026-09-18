import OperatorKO7.Meta.EscapeTrichotomyExtended
import OperatorKO7.Meta.MatrixBarrierOrderedField_Schema
import OperatorKO7.Meta.MatrixBarrierNatural_EWZ
import OperatorKO7.Meta.DependencyPairs_Works
import OperatorKO7.Meta.Recursor.RaryDuplicatorLaws

/-!
# One theorem per scope bullet

The scope subsection lists what lies outside the claim surface. Each item there is now backed by a
theorem naming the exact object that puts it outside, so the scope is a set of compiled statements
rather than a prose disclaimer. `scope_boundary_witnesses` collects the six.

| Bullet | What puts it outside |
|---|---|
| dependency-pair metatheory | rank-based pair soundness is generic; pair termination alone does not imply source termination |
| matrix interpretations over other carriers, beyond the strict reading | the weak reading has a compiled orienter: the zero interpretation |
| natural matrices with a zero wrapper diagonal at every coordinate | the constant-zero interpretation orients weakly |
| arbitrary semantic methods | a quasi-interpretation alone certifies no step |
| duplicating-rule shapes beyond one wrapper | the `r`-ary shape is now covered; the boundary moved to the mutual interfaces |
| nonlinear polynomials with cross-term coupling | a compiled member of that class orients the duplicating step |

Two of the six moved in this run. The `r`-ary shape is no longer outside: every quantitative law is
carried to arbitrary frame arity in `Meta/Recursor/RaryDuplicatorLaws.lean`, with `r = 1` recovering
the published statement. And the cross-term bullet now has a compiled witness rather than a
reference to an informal example: `crossCoupledWeight` is a nonlinear polynomial with cross-term
coupling that orients the duplicating step strictly.

Relation: the schema duplicating step and the KO7 root relation. Closure: root.
External trust: none. Mathlib only.
-/

namespace OperatorKO7.ScopeBoundaryWitnesses

open OperatorKO7
open OperatorKO7.StepDuplicating
open OperatorKO7.StepDuplicating.StepDuplicatingSchema
open OperatorKO7.CompositionalImpossibility
open OperatorKO7.MetaDependencyPairs

/-- A reduction-pair certificate on the actual KO7 dependency-pair relation. -/
structure KO7DPReductionPair where
  rank : Trace → Nat
  decreases : ∀ {a b : Trace}, DPPair a b → rank b < rank a

def counterKO7DPReductionPair : KO7DPReductionPair where
  rank := dpRank
  decreases := dpPair_decreases

def doubledCounterKO7DPReductionPair : KO7DPReductionPair where
  rank := fun t => 2 * dpRank t
  decreases := fun h => by
    have hd := dpPair_decreases h
    omega

theorem ko7_dp_reduction_pair_ranks_differ :
    counterKO7DPReductionPair.rank ≠ doubledCounterKO7DPReductionPair.rank := by
  intro h
  have hv := congrFun h (Trace.recΔ Trace.void Trace.void (Trace.delta Trace.void))
  simp [counterKO7DPReductionPair, doubledCounterKO7DPReductionPair, dpRank, dpProjection]
    at hv

/-- Exact non-uniqueness certificate for the actual extracted KO7 pair problem.
This is data, not a proposition: the two concrete reduction-pair objects must remain
projectable by downstream code, while `ranksDiffer` is the proof component. -/
structure KO7DPReductionPairNonUnique where
  first : KO7DPReductionPair
  second : KO7DPReductionPair
  ranksDiffer : first.rank ≠ second.rank

def ko7_dp_reduction_pair_nonunique : KO7DPReductionPairNonUnique :=
  ⟨counterKO7DPReductionPair, doubledCounterKO7DPReductionPair,
    ko7_dp_reduction_pair_ranks_differ⟩

/-- A pair problem with no pairs. Its reverse pair relation is well founded by the generic
rank-based dependency-pair theorem. -/
def emptyNatDPProjection : OperatorKO7.DependencyPairsFragment.DPProjection Nat where
  Pair := fun _ _ => False
  rank := id
  decreases := by
    intro _ _ h
    exact False.elim h

/-- A nonterminating source reverse relation, deliberately independent of the empty pair problem.
It isolates the source-to-pair transport datum that pair well-foundedness alone cannot supply. -/
def successorSourceRev (x y : Nat) : Prop := x = y + 1

theorem successorSourceRev_not_wellFounded :
    ¬ WellFounded successorSourceRev := by
  intro hwf
  exact (WellFounded.wellFounded_iff_no_descending_seq.1 hwf).elim
    ⟨fun n => n, fun n => rfl⟩

/-- Generic rank-based pair soundness, together with a sharp counterexample showing that a
source-to-pair transport theorem is necessary before pair termination can imply source
termination. -/
theorem rank_based_dp_generic_and_source_transport_sharp :
    (∀ (α : Type) (P : OperatorKO7.DependencyPairsFragment.DPProjection α),
        WellFounded P.Rev)
      ∧ (WellFounded emptyNatDPProjection.Rev
        ∧ ¬ WellFounded successorSourceRev) :=
  ⟨fun _ P => P.wfRev,
    ⟨emptyNatDPProjection.wfRev, successorSourceRev_not_wellFounded⟩⟩

/-- The minimal semantic interface used by the scope statement: only weak comparison on the live
duplicating rule is required. -/
structure WeakSemanticReading where
  eval : Trace → Nat
  weak : ∀ b s n : Trace,
    eval (Trace.app s (Trace.recΔ b s n)) ≤
      eval (Trace.recΔ b s (Trace.delta n))

def constantWeakSemanticReading : WeakSemanticReading where
  eval := fun _ => 0
  weak := fun _ _ _ => le_rfl

/-- The weak semantic interface alone does not force strict orientation. -/
theorem weak_semantic_reading_does_not_force_strict :
    ¬ ∀ Q : WeakSemanticReading, ∀ b s n : Trace,
        Q.eval (Trace.app s (Trace.recΔ b s n)) <
          Q.eval (Trace.recΔ b s (Trace.delta n)) := by
  intro h
  have hs := h constantWeakSemanticReading Trace.void Trace.void Trace.void
  simp [constantWeakSemanticReading] at hs

/-- One compiled witness per scope bullet. -/
structure ScopeBoundary : Prop where
  /-- Rank-based dependency-pair soundness is fully generic. The remaining boundary is
  source-to-pair transport: a terminating pair relation alone does not force an unrelated source
  relation to terminate. -/
  dependencyPairMetatheory :
    (∀ (α : Type) (P : OperatorKO7.DependencyPairsFragment.DPProjection α),
        WellFounded P.Rev)
      ∧ (WellFounded emptyNatDPProjection.Rev
        ∧ ¬ WellFounded successorSourceRev)
  /-- Matrix interpretations over carriers other than the naturals are covered only in the strict
  tracked-coordinate reading. The weak reading has a compiled orienter. -/
  orderedFieldWeakReading :
    ∀ (b s n : OperatorKO7.StepDuplicating.StepDuplicatingSchema.FreeTerm),
      (zeroFieldNatMatrixMeasure (K := NNRat) freeSchema).eval
          (freeSchema.wrap s (freeSchema.recur b s n)) 0 ≤
        (zeroFieldNatMatrixMeasure (K := NNRat) freeSchema).eval
          (freeSchema.recur b s (freeSchema.succ n)) 0
  /-- Natural matrix interpretations whose wrapper diagonal vanishes at every coordinate are
  outside: the constant-zero interpretation orients the nonstrict comparison everywhere. -/
  zeroWrapperDiagonal :
    ∀ (b s n : OperatorKO7.StepDuplicating.StepDuplicatingSchema.FreeTerm),
      (constantZeroNatMatrixMeasure (S := freeSchema) (d := 1)).eval
          (freeSchema.wrap s (freeSchema.recur b s n)) 0 ≤
        (constantZeroNatMatrixMeasure (S := freeSchema) (d := 1)).eval
          (freeSchema.recur b s (freeSchema.succ n)) 0
  /-- Arbitrary semantic methods are outside: a weakly monotone semantic reading alone certifies
   no step, so the class carries no barrier without extra data. -/
  arbitrarySemanticMethods :
    Nonempty WeakSemanticReading
      ∧ ¬ ∀ Q : WeakSemanticReading,
          ∀ b s n : Trace,
            Q.eval (Trace.app s (Trace.recΔ b s n)) <
              Q.eval (Trace.recΔ b s (Trace.delta n))
  /-- The `r`-ary duplicating shape is no longer outside: every quantitative law carries to
   arbitrary frame arity and recovers the published statement at `r = 1`. -/
  raryShapeNowCovered :
    ∀ ia ib w cstar r : Nat,
      OperatorKO7.Meta.Recursor.RaryDuplicatorLaws.RaryQuantitativeLawPackage
        ia ib w cstar r
  /-- Nonlinear polynomial interpretations with cross-term coupling are outside, and the witness is
  compiled: a member of that class orients the duplicating step strictly. -/
  crossTermCoupling :
    ∀ (b s n : OperatorKO7.StepDuplicating.StepDuplicatingSchema.FreeTerm),
      crossCoupledWeight (freeSchema.wrap s (freeSchema.recur b s n)) <
        crossCoupledWeight (freeSchema.recur b s (freeSchema.succ n))

/-- **The six scope bullets, each with its compiled witness.** -/
theorem scope_boundary_witnesses : ScopeBoundary where
  dependencyPairMetatheory := rank_based_dp_generic_and_source_transport_sharp
  orderedFieldWeakReading :=
    zeroFieldNatMatrixMeasure_orients_nonincreasing (K := NNRat) (S := freeSchema)
  zeroWrapperDiagonal := constantZeroNatMatrixMeasure_nonstrict_orients freeSchema
  arbitrarySemanticMethods :=
    ⟨⟨constantWeakSemanticReading⟩, weak_semantic_reading_does_not_force_strict⟩
  raryShapeNowCovered :=
    OperatorKO7.Meta.Recursor.RaryDuplicatorLaws.rary_quantitative_laws_all_arities
  crossTermCoupling := crossCoupledWeight_strictly_orients

end OperatorKO7.ScopeBoundaryWitnesses
