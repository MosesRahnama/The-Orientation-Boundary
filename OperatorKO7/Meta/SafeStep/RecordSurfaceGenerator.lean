import OperatorKO7.Meta.BoundaryGeneral.DistinctionRecord
import OperatorKO7.Meta.SafeStep.EqualityWitnessGeneralization

set_option autoImplicit false

namespace OperatorKO7.Meta.SafeStep.RecordSurfaceGenerator

open OperatorKO7.Meta.SafeStep.EqualityWitnessGeneralization

universe u

structure ProductiveRecordSurface (A : Type u) where
  emits : A -> A -> Prop
  sound : ∀ {a b}, emits a b -> a ≠ b
  productive : ∀ {a b}, a ≠ b -> emits a b

def ProductiveRecordSurface.toDistinctionGenerator
    {A : Type u} (S : ProductiveRecordSurface A) :
    DistinctionGenerator A where
  emitsDistinction := S.emits
  sound := S.sound
  generating := S.productive

theorem recordSurface_diagonal_inert
    {A : Type u} (S : ProductiveRecordSurface A) (a : A) :
    ¬ S.emits a a :=
  fun h => (S.sound h) rfl

def recordSurface_to_comparisonInterface
    {A : Type u} (S : ProductiveRecordSurface A) :
    ComparisonInterface A (A × A) :=
  (ProductiveRecordSurface.toDistinctionGenerator S).toComparisonInterface

#print axioms ProductiveRecordSurface.toDistinctionGenerator
#print axioms recordSurface_diagonal_inert
#print axioms recordSurface_to_comparisonInterface

end OperatorKO7.Meta.SafeStep.RecordSurfaceGenerator
