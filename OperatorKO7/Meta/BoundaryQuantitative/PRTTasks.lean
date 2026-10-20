import OperatorKO7.Meta.BoundaryQuantitative.Profile
import OperatorKO7.Meta.DistinctionBoundary.Quantitative.CertificateLowerBound
import OperatorKO7.Meta.DistinctionBoundary.Quantitative.FiniteDistinctionSurface

/-!
# PRT quantitative task fixtures

Relation: benchmark task surfaces are mapped to quantitative boundary profiles.
Closure: finite task surfaces and finite fixed-length certificate words.
Trust: PROVEN-IN-LEAN, reusing the Distinction finite-surface and certificate
lower-bound modules.
Scope: task fixtures only. This is not an empirical model score.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.BoundaryQuantitative

open OperatorKO7.Meta.DistinctionBoundary.Quantitative

/-- PRT-facing task profile for a finite carrier: total pair burden plus the
diagonal failure coordinate. -/
def prtAlwaysDifferentProfile (A : Type) [Fintype A] [DecidableEq A] :
    ObstructionProfile where
  carrierBurden := Fintype.card A * Fintype.card A
  branchExcess :=
    (FiniteDistinctionSurface.alwaysDifferentSurface (A := A)).diagonalFalsePositive
  repairCover := 0
  witnessRank := 0

/-- The always-different comparator has high aggregate accuracy on eight
points while failing every diagonal cell. -/
theorem prt_alwaysDifferent_fin8_accuracy :
    (FiniteDistinctionSurface.alwaysDifferentCorrectPairCount (A := Fin 8) : Rat) /
        ((Fintype.card (Fin 8) : Rat) ^ 2) = 7 / 8 :=
  FiniteDistinctionSurface.alwaysDifferent_fin8_accuracy

theorem prt_alwaysDifferent_fin8_branchExcess :
    (prtAlwaysDifferentProfile (Fin 8)).branchExcess = 8 := by
  simpa [prtAlwaysDifferentProfile] using
    (FiniteDistinctionSurface.alwaysDifferent_diagonalFalsePositive (A := Fin 8))

/-- Four distinguishable task alternatives require at least two fixed bits. -/
theorem prt_four_alternative_certificate_floor :
    Nat.clog 2 (Fintype.card (Fin 4)) <= 2 := by
  simpa using
    injective_certificate_clog_floor (E := Fin 4) 2 codeFin4 codeFin4_injective

theorem prt_four_alternatives_do_not_fit_one_bit :
    Not (exists encode : Fin 4 -> BitWord 1, Function.Injective encode) :=
  four_alternatives_do_not_fit_one_bit

#print axioms prt_alwaysDifferent_fin8_accuracy
#print axioms prt_alwaysDifferent_fin8_branchExcess
#print axioms prt_four_alternative_certificate_floor
#print axioms prt_four_alternatives_do_not_fit_one_bit

end OperatorKO7.Meta.BoundaryQuantitative
