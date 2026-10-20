import OperatorKO7.Meta.SafeStep.EqualityWitnessGeneralization

set_option autoImplicit false

namespace OperatorKO7.Meta.DistinctionBoundary.RepairBasis

open OperatorKO7.Meta.SafeStep.EqualityWitnessGeneralization
open OperatorKO7.Meta.SafeStep.GenericDiagonalFork
open OperatorKO7.Meta.SafeStep.DistinctionWitnessBoundary

universe u

inductive VerdictRepairRoute where
  | guard
  | delete
  | quotient
  | inert
  deriving DecidableEq

/-- Verdict-level repair: either the two verdicts are joined, or the source is inert. -/
def VerdictLevelRepair {T : Type u} (S : UnguardedEqWLike T) (a : T)
    (route : VerdictRepairRoute) : Prop :=
  match route with
  | .guard => DiagonalVerdictsJoin S a
  | .delete => S.D a a = S.Z
  | .quotient => S.Z = S.D a a
  | .inert => Not (S.R (S.E a a) S.Z) ∧ Not (S.R (S.E a a) (S.D a a))

/-- Guard, delete, and quotient are verdict-joining routes. -/
theorem repair_route_joins_verdicts {T : Type u}
    (S : UnguardedEqWLike T) (a : T) :
    VerdictLevelRepair S a VerdictRepairRoute.guard ->
      DiagonalVerdictsJoin S a :=
  fun h => h

/-- Delete joins by identifying the difference output with the null verdict. -/
theorem delete_route_joins {T : Type u}
    (S : UnguardedEqWLike T) (a : T)
    (h : VerdictLevelRepair S a VerdictRepairRoute.delete) :
    DiagonalVerdictsJoin S a :=
  delete_avoids_fork S a h

/-- Quotient joins by identifying the null verdict with the difference output. -/
theorem quotient_route_joins {T : Type u}
    (S : UnguardedEqWLike T) (a : T)
    (h : VerdictLevelRepair S a VerdictRepairRoute.quotient) :
    DiagonalVerdictsJoin S a :=
  quotient_avoids_fork S a h

/-- At a determined diagonal, the repair condition itself is exactly verdict joinability. -/
theorem determined_diagonal_repair_condition {T : Type u}
    (S : UnguardedEqWLike T) (a : T) (hdet : DiagonalDetermined S a) :
    LocalJoinAt S (S.E a a) <-> DiagonalVerdictsJoin S a :=
  diagonal_repair_exhaustive S a hdet

#print axioms repair_route_joins_verdicts
#print axioms delete_route_joins
#print axioms quotient_route_joins
#print axioms determined_diagonal_repair_condition

end OperatorKO7.Meta.DistinctionBoundary.RepairBasis
