import OperatorKO7.Meta.ProjectedPrimaryBarrier
import OperatorKO7.Meta.ScalarProjectionBarrier

/-!
This module re-exports two scalar-projection barriers through ProjectionStructure. Each result
is conditional on the projection hypotheses and the imported scalar barrier.






















-/

namespace OperatorKO7.Meta.BoundaryOperator.UniversalProjectionMetaTheorems

open OperatorKO7.StepDuplicating
open OperatorKO7.StepDuplicating.StepDuplicatingSchema

/-- Data record whose requirements are the fields displayed below.

-/
structure ProjectionStructure (S : StepDuplicatingSchema) where
  α : Type
  μ : S.T → α
  R : α → α → Prop
  π : α → Nat

/-- The displayed proposition follows from the stated hypotheses.

-/
theorem ProjectionStructure.universal_barrier_strict
    {S : StepDuplicatingSchema} (P : ProjectionStructure S)
    (hproj : ∀ {u v : P.α}, P.R u v → P.π u < P.π v)
    (hscalar : ¬ (∀ (b s n : S.T),
      P.π (P.μ (S.wrap s (S.recur b s n))) < P.π (P.μ (S.recur b s (S.succ n))))) :
    ¬ (∀ (b s n : S.T),
      P.R (P.μ (S.wrap s (S.recur b s n))) (P.μ (S.recur b s (S.succ n)))) :=
  no_orients_dup_step_of_scalar_projection P.μ P.R P.π hproj hscalar

/-- The displayed proposition follows from the stated hypotheses.

-/
theorem ProjectionStructure.universal_barrier_affine_primary
    {S : StepDuplicatingSchema} (P : ProjectionStructure S)
    (hdom : ∀ {u v : P.α}, P.R u v → P.π u ≤ P.π v)
    (M : AffineMeasure S)
    (heval : ∀ t : S.T, M.eval t = P.π (P.μ t))
    (hunbounded : HasUnboundedRange M) :
    ¬ (∀ (b s n : S.T),
      P.R (P.μ (S.wrap s (S.recur b s n))) (P.μ (S.recur b s (S.succ n)))) :=
  no_orients_dup_step_of_projected_primary_dominance P.μ P.R P.π hdom M heval hunbounded

/-- Definition with formal content given by the displayed type and body.
-/
def ProjectionStructure.ofNatMeasure {S : StepDuplicatingSchema} (μ : S.T → Nat) :
    ProjectionStructure S where
  α := Nat
  μ := μ
  R := (· < ·)
  π := fun n => n

/-- Definition with formal content given by the displayed type and body. -/
def universal_projection_meta_theorems_anchor : String :=
  "OperatorKO7.Meta.BoundaryOperator.UniversalProjectionMetaTheorems.ProjectionStructure.universal_barrier_strict"

end OperatorKO7.Meta.BoundaryOperator.UniversalProjectionMetaTheorems
