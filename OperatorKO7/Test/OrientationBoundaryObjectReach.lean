import OperatorKO7.Meta.Methods.OrientationClosure.OrientationBoundaryObject

set_option autoImplicit false

#check @OperatorKO7.Methods.OrientationClosure.OrientationBoundaryObject.orientationBoundary_eq
#print axioms OperatorKO7.Methods.OrientationClosure.OrientationBoundaryObject.orientationBoundary_eq

#check @OperatorKO7.Methods.OrientationClosure.OrientationBoundaryObject.orienters_carrier_independent
#print axioms OperatorKO7.Methods.OrientationClosure.OrientationBoundaryObject.orienters_carrier_independent

#check @OperatorKO7.Methods.OrientationClosure.OrientationBoundaryObject.orientationBoundary_allCarriers_eq
#print axioms OperatorKO7.Methods.OrientationClosure.OrientationBoundaryObject.orientationBoundary_allCarriers_eq

#check @OperatorKO7.Methods.OrientationClosure.OrientationBoundaryObject.counter_mem_orienters
#print axioms OperatorKO7.Methods.OrientationClosure.OrientationBoundaryObject.counter_mem_orienters

#check @OperatorKO7.Methods.OrientationClosure.OrientationBoundaryObject.payload_not_mem_orienters
#print axioms OperatorKO7.Methods.OrientationClosure.OrientationBoundaryObject.payload_not_mem_orienters

#check @OperatorKO7.Methods.OrientationClosure.OrientationBoundaryObject.const_not_mem_orienters
#print axioms OperatorKO7.Methods.OrientationClosure.OrientationBoundaryObject.const_not_mem_orienters

#check @OperatorKO7.Methods.OrientationClosure.OrientationBoundaryObject.exists_cell
#print axioms OperatorKO7.Methods.OrientationClosure.OrientationBoundaryObject.exists_cell

#check @OperatorKO7.Methods.OrientationClosure.OrientationBoundaryObject.cell_unique
#print axioms OperatorKO7.Methods.OrientationClosure.OrientationBoundaryObject.cell_unique

#check @OperatorKO7.Methods.OrientationClosure.OrientationBoundaryObject.barrier_cell_excludes
#print axioms OperatorKO7.Methods.OrientationClosure.OrientationBoundaryObject.barrier_cell_excludes

#check @OperatorKO7.Methods.OrientationClosure.OrientationBoundaryObject.growthCell_spec
#print axioms OperatorKO7.Methods.OrientationClosure.OrientationBoundaryObject.growthCell_spec

#check @OperatorKO7.Methods.OrientationClosure.OrientationBoundaryObject.growthCell_eq_iff
#print axioms OperatorKO7.Methods.OrientationClosure.OrientationBoundaryObject.growthCell_eq_iff

#check @OperatorKO7.Methods.OrientationClosure.OrientationBoundaryObject.orienters
#print axioms OperatorKO7.Methods.OrientationClosure.OrientationBoundaryObject.orienters

#check @OperatorKO7.Methods.OrientationClosure.OrientationBoundaryObject.payloadBlindCounterStrict
#print axioms OperatorKO7.Methods.OrientationClosure.OrientationBoundaryObject.payloadBlindCounterStrict

#check @OperatorKO7.Methods.OrientationClosure.OrientationBoundaryObject.GrowthCell
#print axioms OperatorKO7.Methods.OrientationClosure.OrientationBoundaryObject.GrowthCell

#check @OperatorKO7.Methods.OrientationClosure.OrientationBoundaryObject.InCell
#print axioms OperatorKO7.Methods.OrientationClosure.OrientationBoundaryObject.InCell

#check @OperatorKO7.Methods.OrientationClosure.OrientationBoundaryObject.growthCell
#print axioms OperatorKO7.Methods.OrientationClosure.OrientationBoundaryObject.growthCell

#check @OperatorKO7.Methods.OrientationClosure.OrientationBoundaryObject.not_wrapUnbounded_and_wrapBounded
#print axioms OperatorKO7.Methods.OrientationClosure.OrientationBoundaryObject.not_wrapUnbounded_and_wrapBounded

#check @OperatorKO7.Methods.OrientationClosure.OrientationBoundaryObject.not_gainBounded_and_gainUnbounded
#print axioms OperatorKO7.Methods.OrientationClosure.OrientationBoundaryObject.not_gainBounded_and_gainUnbounded

#check @OperatorKO7.Methods.OrientationClosure.OrientationBoundaryObject.GrowthCell.barrier
#print axioms OperatorKO7.Methods.OrientationClosure.OrientationBoundaryObject.GrowthCell.barrier

#check @OperatorKO7.Methods.OrientationClosure.OrientationBoundaryObject.GrowthCell.costUnboundedGainUnbounded
#print axioms OperatorKO7.Methods.OrientationClosure.OrientationBoundaryObject.GrowthCell.costUnboundedGainUnbounded

#check @OperatorKO7.Methods.OrientationClosure.OrientationBoundaryObject.GrowthCell.costBoundedGainBounded
#print axioms OperatorKO7.Methods.OrientationClosure.OrientationBoundaryObject.GrowthCell.costBoundedGainBounded

#check @OperatorKO7.Methods.OrientationClosure.OrientationBoundaryObject.GrowthCell.costBoundedGainUnbounded
#print axioms OperatorKO7.Methods.OrientationClosure.OrientationBoundaryObject.GrowthCell.costBoundedGainUnbounded

/-! ## Non-vacuity controls at the carriers `Bool` and `Nat` -/

open OperatorKO7.Meta.BoundaryGeneral.DirectMeasureGrammarClosure
open OperatorKO7.Methods.OrientationClosure.OrientationBoundaryObject

/-- Both sides of the boundary are inhabited at `Bool`. -/
example : MeasureExpr.counter ∈ orienters Bool ∧ MeasureExpr.payload ∉ orienters Bool :=
  ⟨counter_mem_orienters Bool, payload_not_mem_orienters Bool⟩

/-- The orienters at `Bool` and at `Nat` agree. -/
example : orienters Bool = orienters Nat := orienters_carrier_independent Bool Nat
