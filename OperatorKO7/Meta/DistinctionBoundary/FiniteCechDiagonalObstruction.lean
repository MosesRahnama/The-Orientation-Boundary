import OperatorKO7.Meta.DistinctionBoundary.DirectedReductionSpace
import OperatorKO7.Meta.DistinctionBoundary.FiniteGluingObstruction

/-!
# Finite Cech gluing obstruction at the KO7 diagonal

For the two-branch diagonal cover, the live obstruction is failed finite
zero-gluing, not a topological `H^1` theorem. This file names that finite Cech
object and proves guarded excision kills it.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.DistinctionBoundary.FiniteCechDiagonalObstruction

open OperatorKO7 Trace
open MetaSN_KO7

/-- The finite two-branch index used by the diagonal cover. -/
inductive TwoBranch
  | left
  | right
  deriving DecidableEq, Repr

/-- A finite cover by indexed predicates. -/
structure FiniteCover (X : Type) where
  I : Type
  opens : I -> X -> Prop

/-- A finite verdict presheaf over the cover. The `restrict` relation records
which local sections are compatible on overlaps. -/
structure VerdictPresheaf (X : Type) (C : FiniteCover X) where
  Section : C.I -> Type
  restrict : forall {i j}, Section i -> Section j -> Prop

/-- A zero-cochain on the two-branch cover, specialized to verdict traces. -/
structure CechZeroCochain where
  leftVerdict : Trace
  rightVerdict : Trace

/-- Finite Cech zero-gluing in a directed reduction space. -/
def CechZeroGlues (D : DirectedReductionSpace Trace)
    (γ : CechZeroCochain) : Prop :=
  exists d, D.path γ.leftVerdict d ∧ D.path γ.rightVerdict d

/-- The finite obstruction class for this two-branch cover: local data do not
glue to a common directed verdict. -/
def FiniteCechZeroObstruction (D : DirectedReductionSpace Trace)
    (γ : CechZeroCochain) : Prop :=
  ¬ CechZeroGlues D γ

def rawDiagonalCover : FiniteCover Trace where
  I := TwoBranch
  opens := fun _ _ => True

def guardedDiagonalCover : FiniteCover Trace where
  I := TwoBranch
  opens := fun _ _ => True

def rawVerdictPresheaf : VerdictPresheaf Trace rawDiagonalCover where
  Section := fun _ => Trace
  restrict := fun s t => StepStar s t ∨ StepStar t s

def guardedVerdictPresheaf : VerdictPresheaf Trace guardedDiagonalCover where
  Section := fun _ => Trace
  restrict := fun s t => SafeStepStar s t ∨ SafeStepStar t s

def rawDiagonalCochain : CechZeroCochain where
  leftVerdict := void
  rightVerdict := integrate (merge void void)

def guardedDiagonalCochain : CechZeroCochain where
  leftVerdict := void
  rightVerdict := void

/-- The raw diagonal carries a nonzero finite Cech zero-gluing obstruction. -/
theorem raw_diagonal_has_nonzero_finite_cech_obstruction :
    FiniteCechZeroObstruction rawStepDirectedSpace rawDiagonalCochain := by
  intro h
  rcases h with ⟨d, hdv, hdi⟩
  exact
    (FiniteGluingObstruction.raw_diagonal_sections_fail_to_glue void)
      ⟨d, hdv, hdi⟩

/-- Guarded excision kills the finite obstruction because both local diagonal
verdicts are the same safe verdict. -/
theorem guarded_excision_kills_finite_cech_obstruction :
    ¬ FiniteCechZeroObstruction safeStepDirectedSpace guardedDiagonalCochain := by
  intro h
  exact h ⟨void, SafeStepStar.refl void, SafeStepStar.refl void⟩

/-- The finite Cech obstruction is exactly the older finite gluing obstruction,
renamed at the cover/cochain level. -/
theorem finite_cech_obstruction_matches_gluing :
    FiniteCechZeroObstruction rawStepDirectedSpace rawDiagonalCochain ↔
      ¬ FiniteGluingObstruction.Glues
          (FiniteGluingObstruction.rawDiagonalSection void) := by
  rfl

#print axioms raw_diagonal_has_nonzero_finite_cech_obstruction
#print axioms guarded_excision_kills_finite_cech_obstruction
#print axioms finite_cech_obstruction_matches_gluing

end OperatorKO7.Meta.DistinctionBoundary.FiniteCechDiagonalObstruction
