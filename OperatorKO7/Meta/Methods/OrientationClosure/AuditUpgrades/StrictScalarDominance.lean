import OperatorKO7.Meta.BarrierPumpDischarge_Schema

/-!
# Strict scalar dominance for the mixed-matrix barrier

Theorem 5.5 of the Orientation Boundary paper states the mixed-matrix barrier for an ambient
relation whose strict comparison forces strict decrease of the scalarization. The module
`BarrierPumpDischarge_Schema` proves the barrier for nonstrict dominance together with one positive
scalarized value. Under strict dominance the positive value follows from orientation at the base
instance, so the barrier holds with no positivity premise.
-/

set_option autoImplicit false

namespace OperatorKO7.Methods.OrientationClosure.AuditUpgrades.StrictScalarDominance

open OperatorKO7.StepDuplicating
open OperatorKO7.StepDuplicating.StepDuplicatingSchema

/--
Proves: a mixed-matrix interpretation of any finite dimension, whose scalarization along its weight
satisfies the affine interface, fails uniform orientation of the duplicating step under every
relation whose strict comparison forces strict decrease of that scalarization.
Does not prove: anything about relations that force only nonincrease; that case is
`no_matrixArbitrary_orients_dup_step_of_scalar_dominance_of_pos`.
Relation: the duplicating step of an arbitrary step-duplicating schema.
Closure: root single-step.
Strategy: orientation at the base instance gives a positive scalarized value, then the nonstrict
barrier applies.
Trust: Lean kernel with the axioms of the nonstrict barrier.
Scope: every schema, every dimension `d`, every `MatrixArbitraryMeasure`, every relation `R`.
-/
theorem no_matrixArbitrary_orients_dup_step_of_strict_scalar_dominance
    {S : StepDuplicatingSchema} {d : Nat} (M : MatrixArbitraryMeasure S d)
    {R : MatrixVec d → MatrixVec d → Prop}
    (hstrict : ∀ {u v : MatrixVec d}, R u v →
      matrixScalarize M.weight u < matrixScalarize M.weight v) :
    ¬ (∀ b s n : S.T,
      R (M.eval (S.wrap s (S.recur b s n))) (M.eval (S.recur b s (S.succ n)))) := by
  intro horient
  have hpos : ∃ t : S.T, 1 ≤ matrixScalarize M.weight (M.eval t) := by
    refine ⟨S.recur S.base S.base (S.succ S.base), ?_⟩
    have h := hstrict (horient S.base S.base S.base)
    omega
  exact no_matrixArbitrary_orients_dup_step_of_scalar_dominance_of_pos M
    { nonstrict := fun h => le_of_lt (hstrict h) } hpos horient

/--
Proves: both forms of the mixed-matrix barrier of Theorem 5.5 at once; the barrier holds when the
strict comparison of the ambient relation forces strict decrease of the scalarization, and when it
forces nonincrease and the scalarization takes a positive value at some term.
Does not prove: anything when the relation forces neither.
Relation: the duplicating step of an arbitrary step-duplicating schema.
Closure: root single-step.
Strategy: case split on the two hypotheses.
Trust: Lean kernel with the axioms of the two barriers.
Scope: every schema, every dimension, every `MatrixArbitraryMeasure`, every relation.
-/
theorem no_matrixArbitrary_orients_dup_step_of_scalar_dominance_either
    {S : StepDuplicatingSchema} {d : Nat} (M : MatrixArbitraryMeasure S d)
    {R : MatrixVec d → MatrixVec d → Prop}
    (h : (∀ {u v : MatrixVec d}, R u v →
        matrixScalarize M.weight u < matrixScalarize M.weight v) ∨
      (MatrixScalarDominance M.weight R ∧
        ∃ t : S.T, 1 ≤ matrixScalarize M.weight (M.eval t))) :
    ¬ (∀ b s n : S.T,
      R (M.eval (S.wrap s (S.recur b s n))) (M.eval (S.recur b s (S.succ n)))) := by
  rcases h with hstrict | ⟨D, hpos⟩
  · exact no_matrixArbitrary_orients_dup_step_of_strict_scalar_dominance M hstrict
  · exact no_matrixArbitrary_orients_dup_step_of_scalar_dominance_of_pos M D hpos

/--
Proves: the strict-dominance barrier on every step-duplicating system: no mixed-matrix
interpretation with an affine scalarization globally orients a system whose relation contains the
duplicating step, under a relation that forces strict decrease of the scalarization.
Does not prove: anything about systems without the duplicating step.
Relation: the step relation of an arbitrary step-duplicating system.
Closure: whatever closure the system's relation carries; it contains the duplicating step.
Strategy: restriction of global orientation to the duplicating step.
Trust: Lean kernel with the axioms of the schema barrier.
Scope: every system, every dimension, every `MatrixArbitraryMeasure`, every relation.
-/
theorem no_global_orients_matrixArbitrary_of_strict_scalar_dominance
    {Sys : StepDuplicatingSystem} {d : Nat}
    (M : MatrixArbitraryMeasure Sys.toStepDuplicatingSchema d)
    {R : MatrixVec d → MatrixVec d → Prop}
    (hstrict : ∀ {u v : MatrixVec d}, R u v →
      matrixScalarize M.weight u < matrixScalarize M.weight v) :
    ¬ GlobalOrients Sys M.eval R := by
  intro h
  exact no_matrixArbitrary_orients_dup_step_of_strict_scalar_dominance
    (S := Sys.toStepDuplicatingSchema) M hstrict (fun b s n => h (Sys.dup_step b s n))

end OperatorKO7.Methods.OrientationClosure.AuditUpgrades.StrictScalarDominance
