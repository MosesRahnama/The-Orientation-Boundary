import OperatorKO7.Meta.Methods.OrientationClosure.CellClassificationFamilies
import OperatorKO7.Meta.DepthBarrier_Schema
import OperatorKO7.Meta.EscapeTrichotomy_Schema

/-!
# The escape theorem over every step-duplicating schema

Theorem 5.22 of the Orientation Boundary paper states the escape trichotomy for a successful direct
orienter. The module `EscapeTrichotomy` proves it on CWS, and `EscapeTrichotomy_Schema` covers
eight pumped scalar families. This module proves the escape theorem on every step-duplicating
schema for the twelve direct families of Corollary 4.8, read without pump hypotheses, together with
the max-depth family: no uniform orienter of the duplicating step is representable in any of the
thirteen families.
-/

set_option autoImplicit false

namespace OperatorKO7.Methods.OrientationClosure.AuditUpgrades.SchemaEscapeUniverse

open OperatorKO7.StepDuplicating
open OperatorKO7.StepDuplicating.StepDuplicatingSchema
open OperatorKO7.Methods.OrientationClosure.CellClassificationFamilies

/-- A direct orienter on a schema: a natural-valued measure, a vector measure compared strictly in
every coordinate, a vector measure compared lexicographically, or a pair measure compared strictly
in both coordinates. -/
inductive SchemaDirectOrienter (S : StepDuplicatingSchema) where
  | nat (μ : S.T → Nat)
  | vec (d : Nat) (μ : S.T → Fin d → Nat)
  | lex (d : Nat) (μ : S.T → Fin (d + 1) → Nat)
  | pair (μ : S.T → Vec2)

namespace SchemaDirectOrienter

variable {S : StepDuplicatingSchema}

/-- Uniform strict orientation of the duplicating step in the order of the orienter. -/
def Orients : SchemaDirectOrienter S → Prop
  | .nat μ => ∀ b s n : S.T, μ (S.wrap s (S.recur b s n)) < μ (S.recur b s (S.succ n))
  | .vec _ μ => ∀ b s n : S.T, VecLt (μ (S.wrap s (S.recur b s n))) (μ (S.recur b s (S.succ n)))
  | .lex _ μ => ∀ b s n : S.T,
      VecLexLt (μ (S.wrap s (S.recur b s n))) (μ (S.recur b s (S.succ n)))
  | .pair μ => ∀ b s n : S.T, PairLt (μ (S.wrap s (S.recur b s n))) (μ (S.recur b s (S.succ n)))

/-- The tracked scalar of an orienter: the measure itself, the coordinate sum, the primary
coordinate, or the sum of the two pair coordinates. -/
def primaryScalar : SchemaDirectOrienter S → S.T → Nat
  | .nat μ => μ
  | .vec d μ => fun t => ∑ i : Fin d, μ t i
  | .lex d μ => fun t => μ t (primaryIdx d)
  | .pair μ => fun t => (μ t).1 + (μ t).2

end SchemaDirectOrienter

/-- The explicit direct universe on a schema: the twelve families of Corollary 4.8 of the paper
(additive, transparent compositional, affine, restricted quadratic, bounded cross-term quadratic,
bounded multilinear, generalized bounded polynomial, max-plus, tracked componentwise, tracked
lexicographic, balanced mixed-coordinate, weighted scalar projection) and the max-depth family. -/
inductive SchemaDirectRepresentable {S : StepDuplicatingSchema} : SchemaDirectOrienter S → Prop
  | additive (M : AdditiveMeasure S) : SchemaDirectRepresentable (.nat M.eval)
  | compositionalTransparent (CM : CompositionalMeasure S)
      (h : CM.c_succ CM.c_base = CM.c_base) : SchemaDirectRepresentable (.nat CM.eval)
  | affine (M : AffineMeasure S) : SchemaDirectRepresentable (.nat M.eval)
  | quadratic (M : QuadraticCounterMeasure S) : SchemaDirectRepresentable (.nat M.eval)
  | crossTerm (M : CrossTermQuadraticMeasure S) (h : CrossTermBoundedAtBase M) :
      SchemaDirectRepresentable (.nat M.eval)
  | multilinear (M : BoundedMultilinearMeasure S) (h : MultilinearDominatedAtBase M) :
      SchemaDirectRepresentable (.nat M.eval)
  | polynomial (M : BoundedPolynomialMeasure S) (h : EventuallyDominatedAtBase M) :
      SchemaDirectRepresentable (.nat M.eval)
  | maxPlus (M : MaxMeasure S) : SchemaDirectRepresentable (.nat M.eval)
  | maxDepth (M : MaxDepthMeasure S) : SchemaDirectRepresentable (.nat M.eval)
  | componentwise {d : Nat} {tracked : Fin d} (M : MatrixMeasureD S d tracked) :
      SchemaDirectRepresentable (.vec d M.eval)
  | lexicographic {d : Nat} (M : MatrixLexMeasureD S d)
      (hpos : ∃ t : S.T, 1 ≤ M.eval t (primaryIdx d)) :
      SchemaDirectRepresentable (.lex d M.eval)
  | balancedMixed (M : MatrixMix2Measure S) : SchemaDirectRepresentable (.pair M.eval)
  | weightedProjection {d : Nat} (M : MatrixFunctionalMeasure S d) :
      SchemaDirectRepresentable (.vec d M.eval)

/--
Proves: on every step-duplicating schema, a uniform orienter of the duplicating step is not
representable in any of the thirteen direct families: the twelve families of Corollary 4.8 and the
max-depth family.
Does not prove: anything about orienters outside the thirteen families; it consumes no wrapper
sensitivity and no successor transparency hypothesis.
Relation: the duplicating step of an arbitrary step-duplicating schema, compared by the order of
the orienter.
Closure: root single-step.
Strategy: each constructor of the universe is excluded by the barrier theorem of its family.
Trust: Lean kernel with the axioms of the thirteen barriers.
Scope: every schema; every constructor of `SchemaDirectRepresentable`.
-/
theorem schema_direct_escape_leaves_universe {S : StepDuplicatingSchema}
    {O : SchemaDirectOrienter S} (horient : O.Orients) : ¬ SchemaDirectRepresentable O := by
  intro hrepr
  cases hrepr with
  | additive M => exact not_orients_of_cellOrPointwiseFailure (additive_cellOrPointwiseFailure M) horient
  | compositionalTransparent CM h =>
      exact not_orients_of_cellOrPointwiseFailure (compositional_cellOrPointwiseFailure CM h) horient
  | affine M => exact not_orients_of_cellOrPointwiseFailure (affine_cellOrPointwiseFailure M) horient
  | quadratic M =>
      exact not_orients_of_cellOrPointwiseFailure (quadratic_cellOrPointwiseFailure M) horient
  | crossTerm M h =>
      exact not_orients_of_cellOrPointwiseFailure (crossTerm_cellOrPointwiseFailure M h) horient
  | multilinear M h =>
      exact not_orients_of_cellOrPointwiseFailure (multilinear_cellOrPointwiseFailure M h) horient
  | polynomial M h =>
      exact not_orients_of_cellOrPointwiseFailure (polynomial_cellOrPointwiseFailure M h) horient
  | maxPlus M => exact not_orients_of_cellOrPointwiseFailure (max_cellOrPointwiseFailure M) horient
  | maxDepth M => exact no_maxDepth_orients_dup_step M horient
  | componentwise M => exact no_matrixD_orients_dup_step_via_cells M horient
  | lexicographic M hpos => exact no_matrixLexD_orients_dup_step_via_cells M hpos horient
  | balancedMixed M => exact no_matrixMix2_orients_dup_step_via_cells M horient
  | weightedProjection M => exact no_matrixFunctional_orients_dup_step_via_cells M horient

/--
Proves: the escape trichotomy of Theorem 5.22 on every step-duplicating schema: a uniform orienter
of the duplicating step has a tracked scalar that fails wrapper-subterm sensitivity, or fails
successor transparency at the base point, or the orienter lies outside the thirteen direct
families; the proof gives the third disjunct for every orienter.
Does not prove: that the first two disjuncts hold for any orienter.
Relation: the duplicating step of an arbitrary step-duplicating schema.
Closure: root single-step.
Strategy: `schema_direct_escape_leaves_universe`.
Trust: Lean kernel with the axioms of the thirteen barriers.
Scope: every schema; every constructor of `SchemaDirectRepresentable`.
-/
theorem schema_direct_escape_trichotomy {S : StepDuplicatingSchema}
    {O : SchemaDirectOrienter S} (horient : O.Orients) :
    ¬ WrapSubtermSensitive S O.primaryScalar ∨
      ¬ TransparentAtBase S O.primaryScalar ∨ ¬ SchemaDirectRepresentable O :=
  Or.inr (Or.inr (schema_direct_escape_leaves_universe horient))

/--
Proves: on every step-duplicating system, a measure of the thirteen families orients no relation
that contains the duplicating step; the natural-valued form of the escape theorem for systems.
Does not prove: anything about measures outside the families.
Relation: the step relation of an arbitrary step-duplicating system.
Closure: whatever closure the system's relation carries; it contains the duplicating step.
Strategy: restriction of global orientation to the duplicating step.
Trust: Lean kernel with the axioms of the thirteen barriers.
Scope: every system and every natural-valued measure.
-/
theorem system_nat_escape_leaves_universe {Sys : StepDuplicatingSystem}
    {μ : Sys.toStepDuplicatingSchema.T → Nat} (horient : GlobalOrients Sys μ (· < ·)) :
    ¬ SchemaDirectRepresentable (S := Sys.toStepDuplicatingSchema) (.nat μ) :=
  schema_direct_escape_leaves_universe (O := .nat μ) (fun b s n => horient (Sys.dup_step b s n))

end OperatorKO7.Methods.OrientationClosure.AuditUpgrades.SchemaEscapeUniverse
