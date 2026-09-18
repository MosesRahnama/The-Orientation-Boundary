import OperatorKO7.Kernel
import OperatorKO7.Meta.CompositionalMeasure_Impossibility
import OperatorKO7.Meta.DependencyPairs_Fragment
import Mathlib.Order.WellFounded

/-!
# Dependency Pairs Work on the KO7 Duplicating Recursor

This module gives a minimal formal witness that the pair problem associated
with the KO7 duplicating rule is handled by a dependency-pair style argument:

- State the single recursive-call pair corresponding to `rec_succ`.
- Use the DP projection rank (track only the recursion counter argument).
- Prove strict decrease on every DP step.
- Conclude well-foundedness of the reverse DP relation via `Nat.lt`.

The scope is the manually stated dependency-pair relation for the displayed
duplicating rule. Source-system transport and a generic DP framework require
additional definitions.
-/

namespace OperatorKO7.MetaDependencyPairs

open OperatorKO7 Trace
open OperatorKO7.CompositionalImpossibility
open OperatorKO7.DependencyPairsFragment

/-- The dependency-pair relation stated for `rec_succ`:
`recΔ b s (delta n) ↦ recΔ b s n`. -/
inductive DPPair : Trace → Trace → Prop
| rec_succ : ∀ b s n, DPPair (recΔ b s (delta n)) (recΔ b s n)

/-- DP rank used for the pair problem:
reuse the projection that keeps only recursion-counter depth. -/
@[simp] def dpRank : Trace → Nat := dpProjection

/-- Each dependency-pair step strictly decreases the DP rank. -/
theorem dpPair_decreases : ∀ {a b : Trace}, DPPair a b → dpRank b < dpRank a
  | _, _, DPPair.rec_succ b s n => by
      simp [dpRank, dpProjection]

/-- KO7's one-pair problem as an instance of the reusable DP projection fragment. -/
def ko7ProjectionProblem : DPProjection Trace where
  Pair := DPPair
  rank := dpRank
  decreases := by
    intro a b h
    exact dpPair_decreases h

/-- Reverse dependency-pair relation (the standard SN orientation). -/
def DPPairRev : Trace → Trace → Prop := ko7ProjectionProblem.Rev

/-- Reverse DP relation is a subrelation of `<` on the DP rank. -/
lemma dpPairRev_sub_rank :
    Subrelation DPPairRev (fun x y => dpRank x < dpRank y) :=
  ko7ProjectionProblem.rev_sub_rank

/-- Well-foundedness of the reverse relation for the extracted KO7 pair
problem. -/
theorem wf_DPPairRev : WellFounded DPPairRev := by
  simpa [DPPairRev] using ko7ProjectionProblem.wfRev

/-- The `rec_succ` source step and its corresponding manually stated pair both hold. -/
theorem rec_succ_extracts_dependency_pair (b s n : Trace) :
    Step (recΔ b s (delta n)) (app s (recΔ b s n))
    ∧ DPPair (recΔ b s (delta n)) (recΔ b s n) := by
  exact ⟨Step.R_rec_succ b s n, DPPair.rec_succ b s n⟩

/-! ## A concrete countdown embedded in the actual pair relation -/

/-- Iterated `delta` counter used to expose the full natural-number countdown
inside the actual KO7 dependency-pair relation. -/
@[simp] def dpCounterTower : Nat → Trace
  | 0 => void
  | n + 1 => delta (dpCounterTower n)

/-- A recursive-call term whose counter is the encoded natural number. -/
def dpCounterEncoding (n : Nat) : Trace :=
  recΔ void void (dpCounterTower n)

/-- The projection reads the iterated counter tower as its natural height. -/
@[simp] theorem dpProjection_dpCounterTower (n : Nat) :
    dpProjection (dpCounterTower n) = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [dpProjection, ih]

/-- The actual DP rank of the encoded call is exactly the encoded natural
number. -/
@[simp] theorem dpRank_dpCounterEncoding (n : Nat) :
    dpRank (dpCounterEncoding n) = n := by
  simp [dpCounterEncoding, dpRank, dpProjection]

/-- One successor in the encoding is one edge of the actual reverse pair
relation.  This is not a synthetic relation: the proof constructor is exactly
`DPPair.rec_succ`. -/
theorem dpCounterEncoding_succ_pairRev (n : Nat) :
    DPPairRev (dpCounterEncoding n) (dpCounterEncoding (n + 1)) := by
  exact DPPair.rec_succ void void (dpCounterTower n)

/-- Every strict natural decrease is represented by a nonempty path in the
actual reverse dependency-pair relation. -/
theorem dpCounterEncoding_transGen_of_lt {m n : Nat} (h : m < n) :
    Relation.TransGen DPPairRev
      (dpCounterEncoding m) (dpCounterEncoding n) := by
  induction n with
  | zero => omega
  | succ n ih =>
      have hle : m ≤ n := Nat.le_of_lt_succ h
      rcases Nat.lt_or_eq_of_le hle with hlt | heq
      · exact Relation.TransGen.tail (ih hlt)
          (by simpa [Nat.succ_eq_add_one] using
            dpCounterEncoding_succ_pairRev n)
      · subst m
        exact Relation.TransGen.single
          (by simpa [Nat.succ_eq_add_one] using
            dpCounterEncoding_succ_pairRev n)

/-- A well-foundedness certificate for the actual reverse KO7 pair relation
supplies well-founded induction on naturals through the concrete countdown
embedding.  The input certificate is the well-founded relation used by the
proof, rather than an ignored argument. -/
theorem natLt_wellFounded_of_DPPairRev
    (hPair : WellFounded DPPairRev) :
    WellFounded (fun m n : Nat => m < n) := by
  have hEncoded : WellFounded
      (fun m n : Nat =>
        Relation.TransGen DPPairRev
          (dpCounterEncoding m) (dpCounterEncoding n)) :=
    InvImage.wf (f := dpCounterEncoding) hPair.transGen
  exact Subrelation.wf
    (fun hlt => dpCounterEncoding_transGen_of_lt hlt)
    hEncoded

end OperatorKO7.MetaDependencyPairs
