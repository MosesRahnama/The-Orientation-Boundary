import OperatorKO7.Meta.DistinctionBoundary.DiagonalJoinObstruction

set_option autoImplicit false

/-!
# Admissible repair of the determined diagonal fork

This module isolates the exact local obligation needed to repair the `eqW`
diagonal.  A candidate relation is admissible at a fixed diagonal source when it
stays inside the full kernel, retains the reflexive verdict, and is locally
joinable there in the ambient full-kernel closure.

The result is deliberately local.  It does not claim that local confluence alone
characterizes `SafeStep` globally.  It proves that every relation satisfying the
three displayed obligations must refuse the competing diagonal-difference edge,
and it supplies an explicit inhabited repair relation.

Audit scope (LASOT):
* relation: an arbitrary `Trace -> Trace -> Prop` subrelation of `Step`;
* closure used by local join: ambient `StepStar`;
* source: the fixed term `eqW a a`;
* non-vacuity: `ReflexiveDiagonalRepair a` is exhibited and proved admissible.
-/

open OperatorKO7
open OperatorKO7.Trace
open MetaSN_DM
open MetaSN_KO7

namespace OperatorKO7.Meta.DistinctionBoundary

/-- The non-circular local interface for an admissible repair at `eqW a a`. -/
structure AdmissibleAtDiagonal
    (R : Trace -> Trace -> Prop) (a : Trace) : Prop where
  /-- Every retained edge is an edge of the full kernel. -/
  sub_step : ∀ {x y}, R x y -> Step x y
  /-- The repair retains the reflexive diagonal verdict. -/
  retains_reflexive : R (eqW a a) void
  /-- Every pair of retained outputs at the source joins in `StepStar`. -/
  local_join : LocalJoinRel R (eqW a a)

/-- The competing diagonal-difference edge is impossible for every admissible
repair at the fixed diagonal source. -/
theorem admissibleAtDiagonal_excludes_difference
    {R : Trace -> Trace -> Prop} {a : Trace}
    (H : AdmissibleAtDiagonal R a) :
    ¬ R (eqW a a) (integrate (merge a a)) :=
  confluence_forces_no_diagonal_diff H.retains_reflexive H.local_join

/-- Canonical fixed-source instance at `eqW void void`. -/
theorem admissibleAtVoidDiagonal_excludes_difference
    {R : Trace -> Trace -> Prop}
    (H : AdmissibleAtDiagonal R void) :
    ¬ R (eqW void void) (integrate (merge void void)) :=
  admissibleAtDiagonal_excludes_difference H

/-- The smallest explicit repair used for the non-vacuity witness: it retains
only the reflexive verdict at the selected diagonal source. -/
def ReflexiveDiagonalRepair (a : Trace) : Trace -> Trace -> Prop :=
  fun x y => x = eqW a a ∧ y = void

/-- The explicit reflexive-only relation is an admissible repair. -/
theorem reflexiveDiagonalRepair_admissible (a : Trace) :
    AdmissibleAtDiagonal (ReflexiveDiagonalRepair a) a := by
  constructor
  · intro x y h
    rcases h with ⟨rfl, rfl⟩
    exact Step.R_eq_refl a
  · exact ⟨rfl, rfl⟩
  · intro b c hb hc
    rcases hb with ⟨_, rfl⟩
    rcases hc with ⟨_, rfl⟩
    exact ⟨void, StepStar.refl void, StepStar.refl void⟩

/-- The admissibility class is inhabited at every diagonal source. -/
theorem admissibleAtDiagonal_nonempty (a : Trace) :
    ∃ R : Trace -> Trace -> Prop, AdmissibleAtDiagonal R a :=
  ⟨ReflexiveDiagonalRepair a, reflexiveDiagonalRepair_admissible a⟩

/-- The explicit non-vacuity witness refuses the diagonal-difference edge. -/
theorem reflexiveDiagonalRepair_excludes_difference (a : Trace) :
    ¬ ReflexiveDiagonalRepair a (eqW a a) (integrate (merge a a)) :=
  admissibleAtDiagonal_excludes_difference
    (reflexiveDiagonalRepair_admissible a)

section AuditChecks

#check @AdmissibleAtDiagonal
#check @admissibleAtDiagonal_excludes_difference
#check @admissibleAtVoidDiagonal_excludes_difference
#check @ReflexiveDiagonalRepair
#check @reflexiveDiagonalRepair_admissible
#check @admissibleAtDiagonal_nonempty
#check @reflexiveDiagonalRepair_excludes_difference

#print axioms admissibleAtDiagonal_excludes_difference
#print axioms admissibleAtVoidDiagonal_excludes_difference
#print axioms reflexiveDiagonalRepair_admissible
#print axioms admissibleAtDiagonal_nonempty
#print axioms reflexiveDiagonalRepair_excludes_difference

end AuditChecks

end OperatorKO7.Meta.DistinctionBoundary
