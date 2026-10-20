/-
Copyright (c) 2026 Moses Rahnama. All rights reserved.
Source-available; see the file LICENSE. Free for individual research;
departmental academic use and commercial use require a paid license.
Authors: Moses Rahnama
-/
import Mathlib.Computability.Halting
import Mathlib.Computability.PartrecCode

/-!
# The computability drop at structural grade C2

Intent: make the manuscript's `Comp` drop literal on Mathlib's live universal
partial-recursive code carrier. The evaluator exists as a partial-recursive
binary function. Equality of the finite syntax codes is computable. Equality of
the denoted partial function with even the constant-zero behavior is not
computable, by Rice's theorem.

This is a naturality-relative interface result. The behavioral predicate is
extensional under equality of denotations, while the syntactic predicate reads
the code object itself. The theorem does not identify syntactic equality with
behavioral equivalence.

Relation: not applicable.
Closure: not applicable.
Strategy: universal partial-recursive evaluation plus Rice's theorem.
External trust: Mathlib's `Nat.Partrec.Code` and `ComputablePred.rice₂`.
Non-vacuity witnesses: `Code.zero` belongs to the zero-behavior class and
`Code.succ` does not.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.DistinctionBoundary.DiagonalCompDrop

open Nat.Partrec
open Nat.Partrec.Code

abbrev Code := Nat.Partrec.Code

/-- Codes whose denotation is the constant-zero partial function. -/
def zeroBehavior : Set Code :=
  {c | c.eval = Code.zero.eval}

/-- Membership in `zeroBehavior` depends only on denotation. -/
theorem zeroBehavior_extensional {cf cg : Code}
    (h : cf.eval = cg.eval) : cf ∈ zeroBehavior ↔ cg ∈ zeroBehavior := by
  simp only [zeroBehavior, Set.mem_setOf_eq]
  constructor
  · intro hf
    exact h.symm.trans hf
  · intro hg
    exact h.trans hg

/-- The constant-zero code is a concrete member of the behavioral class. -/
theorem zero_mem_zeroBehavior : Code.zero ∈ zeroBehavior := by
  rfl

/-- The successor code is a concrete non-member of the behavioral class. -/
theorem succ_not_mem_zeroBehavior : Code.succ ∉ zeroBehavior := by
  intro h
  have h0 := congrFun h 0
  change Part.some 1 = Part.some 0 at h0
  have h10 : (1 : Nat) = 0 := Part.some_injective h0
  omega

/-- Equality of two finite syntax codes is a computable predicate. -/
theorem code_pair_equality_computable :
    ComputablePred (fun p : Code × Code => p.1 = p.2) := by
  letI : DecidableEq Code := Encodable.decidableEqOfEncodable Code
  refine ⟨inferInstance, ?_⟩
  exact (Primrec.eq.comp Primrec.fst Primrec.snd).to_comp

/-- A computable extensional predicate on universal partial-recursive codes is
trivial. This is the reusable structural-C2 form of Rice's theorem. -/
theorem comp_extensional_computable_predicate_trivial
    (C : Set Code)
    (hExt : ∀ cf cg, cf.eval = cg.eval → (cf ∈ C ↔ cg ∈ C))
    (hComp : ComputablePred fun c => c ∈ C) :
    C = ∅ ∨ C = Set.univ :=
  (ComputablePred.rice₂ C hExt).1 hComp

/-- Behavioral equality with the constant-zero denotation is not computable.
The two explicit codes `zero` and `succ` discharge the non-triviality premises
that Rice's theorem requires. -/
theorem comp_behaviour_comparison_not_computable :
    ¬ ComputablePred (fun c : Code => c.eval = Code.zero.eval) := by
  intro hcomp
  have htriv : zeroBehavior = ∅ ∨ zeroBehavior = Set.univ :=
    comp_extensional_computable_predicate_trivial zeroBehavior
      (fun cf cg h => zeroBehavior_extensional h) (by
        simpa only [zeroBehavior, Set.mem_setOf_eq] using hcomp)
  rcases htriv with hEmpty | hUniv
  · have hz := zero_mem_zeroBehavior
    rw [hEmpty] at hz
    exact hz
  · have hs : Code.succ ∈ zeroBehavior := by
      rw [hUniv]
      trivial
    exact succ_not_mem_zeroBehavior hs

/-- The naturality-relative computability drop at structural grade C2:
universal internal evaluation is present, syntactic code equality is
computable, and a non-trivial extensional behavioral comparison is not. -/
theorem comp_drop_mechanized :
    Partrec₂ Nat.Partrec.Code.eval ∧
    ComputablePred (fun p : Code × Code => p.1 = p.2) ∧
    ¬ ComputablePred (fun c : Code => c.eval = Code.zero.eval) :=
  ⟨Nat.Partrec.Code.eval_part, code_pair_equality_computable,
    comp_behaviour_comparison_not_computable⟩

end OperatorKO7.Meta.DistinctionBoundary.DiagonalCompDrop
