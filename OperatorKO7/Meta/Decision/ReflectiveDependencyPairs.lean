/-
Copyright (c) 2026 Moses Rahnama. All rights reserved.
Source-available; see the file LICENSE. Free for individual research;
departmental academic use and commercial use require a paid license.
Authors: Moses Rahnama
-/
import OperatorKO7.Meta.ComputableMeasure
import Mathlib.Data.Multiset.DershowitzManna

/-!
# Reflective dependency pairs (Roadmap 09, Layer 7.3)

Licensed meta-deliberation is a well-founded relation on `MetaQueryState`.
The rank is lexicographic in `(budget, obligations)`: `Nat.lt` on budget, then
the Dershowitz-Manna order `MetaCM.DM` (`Multiset.IsDershowitzMannaLT`) on the
obligation multiset, reused from the ordinal-calibration stack
(`ComputableMeasure.lean`). LASOT K-check 6 / lex gate: a first-coordinate
tie is an equality on budget (`rfl`-grade) and is routed through DM; it is
never hand-waved.

The identity reflective pair (same state, query, obligations, and budget) is
not a licensed edge. That is the mechanized form of the zero-deficit
self-loop, preparing the RH vacancy self-loop `Ω → Ω` of roadmap section 8.

Cognitive reading (ANALOGY, with falsifier): refusing to re-ask the same
question at the same rank. Falsifier: an unlicensed rank-tie edge, exhibited
and blocked (`unlicensed_rank_tie_blocked`).

Relation: `ReflectiveStep` (licensed deliberation). Closure: `Relation.TransGen`.
Trust: kernel only, Mathlib baseline. No rewriting relation on `Trace`.
-/

set_option autoImplicit false

open OperatorKO7.MetaCM
open Multiset

namespace OperatorKO7.Meta.Decision.ReflectiveDependencyPairs

/-- Obligation identifier. Ordered as `Nat` so `MetaCM.DM` applies directly. -/
abbrev Obligation : Type := Nat

/-- Meta-query state `Q♯(m, q, o)` with a remaining budget. -/
structure MetaQueryState where
  metaState : Nat
  activeQuery : Nat
  obligations : Multiset Obligation
  budget : Nat
deriving DecidableEq

/-- Lexicographic rank: budget first, then the DM obligation multiset. -/
def rank (s : MetaQueryState) : Nat × Multiset Obligation :=
  (s.budget, s.obligations)

/-- Strict rank order: `Prod.Lex Nat.lt MetaCM.DM`. -/
def RankLT : Nat × Multiset Obligation → Nat × Multiset Obligation → Prop :=
  Prod.Lex (fun a b : Nat => a < b) (fun a b : Multiset Obligation => DM a b)

/-- Well-foundedness of the reused lex rank (Nat< × DM). The DM factor is
`MetaSN_DM.wf_dm`, the ordinal-calibration stack's named well-foundedness
of `Multiset.IsDershowitzMannaLT` on `Multiset Nat`. -/
theorem wf_RankLT : WellFounded RankLT :=
  WellFounded.prod_lex Nat.lt_wfRel.wf MetaSN_DM.wf_dm

/-- Licensed deliberation. Constructor `budgetDrop` decreases the first
coordinate. Constructor `obligationDrop` requires a budget equality
(`hBudget`, the `rfl`-grade tie) and a strict DM descent on obligations. -/
inductive ReflectiveStep : MetaQueryState → MetaQueryState → Prop
  | budgetDrop {s t : MetaQueryState} (h : t.budget < s.budget) :
      ReflectiveStep s t
  | obligationDrop {s t : MetaQueryState}
      (hBudget : t.budget = s.budget)
      (hDM : DM t.obligations s.obligations) :
      ReflectiveStep s t

/-- Every licensed edge strictly decreases the rank. Lex-left is a budget
drop; lex-right is a budget equality plus DM. -/
theorem reflective_pair_strict_rank {s t : MetaQueryState}
    (h : ReflectiveStep s t) : RankLT (rank t) (rank s) := by
  cases h with
  | budgetDrop hlt =>
      exact Prod.Lex.left
        (α := Nat) (β := Multiset Obligation)
        (ra := fun a b : Nat => a < b)
        (rb := fun a b : Multiset Obligation => DM a b)
        (a₁ := t.budget) (a₂ := s.budget)
        (b₁ := t.obligations) (b₂ := s.obligations)
        hlt
  | obligationDrop hBudget hDM =>
      have hr : rank t = (s.budget, t.obligations) := by
        simp [rank, hBudget]
      rw [hr]
      exact Prod.Lex.right
        (α := Nat) (β := Multiset Obligation)
        (ra := fun a b : Nat => a < b)
        (rb := fun a b : Multiset Obligation => DM a b)
        (a := s.budget)
        (b₁ := t.obligations) (b₂ := s.obligations)
        hDM

/-- `t` is strictly smaller than `s` in the licensed relation. -/
def ReflectiveLt (t s : MetaQueryState) : Prop :=
  ReflectiveStep s t

/-- The licensed relation is well-founded: every deliberation chain is finite. -/
theorem reflective_DP_wellFounded : WellFounded ReflectiveLt := by
  have hsub : Subrelation ReflectiveLt (InvImage RankLT rank) := by
    intro t s h
    exact reflective_pair_strict_rank h
  exact Subrelation.wf hsub (InvImage.wf rank wf_RankLT)

private theorem dm_irrefl (m : Multiset Obligation) : ¬ DM m m :=
  MetaSN_DM.wf_dm.induction (C := fun x : Multiset Obligation => ¬ DM x x) m
    (fun x ih hxx => ih x hxx hxx)

/-- The identity reflective pair is not a licensed edge. -/
theorem identity_reflective_pair_blocked (s : MetaQueryState) :
    ¬ ReflectiveStep s s := by
  intro h
  cases h with
  | budgetDrop hlt => exact Nat.lt_irrefl s.budget hlt
  | obligationDrop _ hDM => exact dm_irrefl s.obligations hDM

private theorem rank_transGen {s t : MetaQueryState}
    (h : Relation.TransGen ReflectiveStep s t) :
    Relation.TransGen RankLT (rank t) (rank s) := by
  induction h with
  | single hst =>
      exact Relation.TransGen.single (reflective_pair_strict_rank hst)
  | tail _ hst ih =>
      exact Relation.TransGen.head (reflective_pair_strict_rank hst) ih

/-- Any licensed finite path that returns to its source is impossible: some
coordinate would have to descend around the cycle, contradicting
well-foundedness of `RankLT`. -/
theorem mutual_reflective_cycle_requires_descent {s : MetaQueryState}
    (h : Relation.TransGen ReflectiveStep s s) : False :=
  (WellFounded.transGen wf_RankLT).induction
    (C := fun p : Nat × Multiset Obligation => ¬ Relation.TransGen RankLT p p)
    (rank s) (fun p ih hxx => ih p hxx hxx) (rank_transGen h)

/-! ## R5: three-state terminating deliberation, and an unlicensed rank tie -/

/-- Empty obligation multiset is DM-below a singleton (replace `n` by nothing). -/
theorem dm_empty_of_singleton (n : Nat) :
    DM (0 : Multiset Obligation) ({n} : Multiset Obligation) :=
  ⟨0, 0, ({n} : Multiset Obligation), singleton_ne_zero n, by simp, by simp,
    fun y hy => by simp at hy⟩

def demoS0 : MetaQueryState :=
  ⟨0, 0, ({1} : Multiset Obligation), 1⟩

def demoS1 : MetaQueryState :=
  ⟨0, 1, (0 : Multiset Obligation), 1⟩

def demoS2 : MetaQueryState :=
  ⟨1, 1, (0 : Multiset Obligation), 0⟩

/-- Step 0 → 1: budget tied (`rfl`), obligations drop under DM. -/
theorem demo_step01 : ReflectiveStep demoS0 demoS1 :=
  ReflectiveStep.obligationDrop rfl (dm_empty_of_singleton 1)

/-- Step 1 → 2: budget 1 → 0. -/
theorem demo_step12 : ReflectiveStep demoS1 demoS2 :=
  ReflectiveStep.budgetDrop (by decide)

/-- `demoS2` is terminal: budget 0 cannot drop, and the empty multiset is
DM-minimal. -/
theorem demoS2_terminal : ¬ ∃ t, ReflectiveStep demoS2 t := by
  rintro ⟨t, h⟩
  cases h with
  | budgetDrop hlt =>
      exact Nat.not_lt_zero t.budget hlt
  | obligationDrop _ hDM =>
      rcases hDM with ⟨X, Y, Z, hZ, _, hN, _⟩
      have h0 : X + Z = 0 := by
        simpa [demoS2] using hN.symm
      exact hZ (add_eq_zero.mp h0).2

/-- Three-state licensed deliberation that reaches a terminal state. -/
theorem demo_deliberation_terminates :
    ReflectiveStep demoS0 demoS1 ∧
    ReflectiveStep demoS1 demoS2 ∧
    ¬ ∃ t, ReflectiveStep demoS2 t :=
  ⟨demo_step01, demo_step12, demoS2_terminal⟩

/-- Rank-tie pair: same budget and obligations, different labels. -/
def tieA : MetaQueryState :=
  ⟨0, 0, ({1} : Multiset Obligation), 1⟩

def tieB : MetaQueryState :=
  ⟨9, 9, ({1} : Multiset Obligation), 1⟩

/-- An unlicensed edge (rank tie) is blocked. -/
theorem unlicensed_rank_tie_blocked : ¬ ReflectiveStep tieA tieB := by
  intro h
  cases h with
  | budgetDrop hlt =>
      exact Nat.lt_irrefl 1 hlt
  | obligationDrop _ hDM =>
      exact dm_irrefl ({1} : Multiset Obligation) hDM

theorem demo_identity_blocked : ¬ ReflectiveStep demoS0 demoS0 :=
  identity_reflective_pair_blocked demoS0

end OperatorKO7.Meta.Decision.ReflectiveDependencyPairs
