import OperatorKO7.Meta.DistinctionBoundary.ObstructionClassSeparation

/-! Paired reach and axiom gate for obstruction-class separation. -/

set_option autoImplicit false

namespace OperatorKO7.Test.ObstructionClassSeparationReach

open OperatorKO7.Meta.DistinctionBoundary.ObstructionClassSeparation

#check @DiagonalClosedLanguage
#check @IsUniversalEvaluator
#check @SelfEvaluationObstructed
#check @DiagonalClosedLanguage.Extends
#check @no_universal_evaluator_of_diagonal_closure
#check @every_diagonalClosedLanguage_obstructed
#check @diagonal_obstruction_stable_under_extension
#check @traceSigmaLanguage
#check @traceSigmaLanguage_obstructed
#check @traceSigmaLanguage_obstructed_via_generic
#check @OrientsDuplicatingStep
#check @PolynomialMeasureLanguage
#check @PolynomialMeasureLanguage.Extends
#check @PolynomialOrientationObstructed
#check @counterUncoupledPolynomialLanguage
#check @fullPolynomialLanguage
#check @counterUncoupled_extends_full
#check @counterUncoupledPolynomial_obstructed
#check @fullPolynomial_not_obstructed_freeSchema
#check @polynomial_extension_dissolves_obstruction
#check @ObstructionSystem
#check @ObstructionSystemEquiv
#check @ObstructionTruthMap
#check @ObstructionSystem.ExtensionStable
#check @ObstructionSystemEquiv.symm
#check @extensionStable_map
#check @extensionStable_iff
#check @diagonalObstructionSystem
#check @freePolynomialOrientationSystem
#check @diagonalObstructionSystem_extensionStable
#check @traceDiagonalObstructionSystem_extensionStable
#check @freePolynomialOrientationSystem_not_extensionStable
#check @diagonal_and_orientation_obstructions_not_equivalent_generic
#check @diagonal_and_orientation_obstructions_not_equivalent
#check @no_surjective_obstructionTruthMap_diagonal_to_orientation
#check @DefinableFrom
#check @collision_not_definable
#check @substitutionObstruction_not_definable
#check @distinction_license_not_definable_from_collapse
#check @orientation_license_not_definable_from_collapse
#check @obstruction_class_separation_complete

/-! A fixed-point-bearing shift is an exact control: diagonal closure alone does
not obstruct universal evaluation. -/

example :
    (¬ ∀ y : Unit, id y ≠ y) ∧
      ∃ L : DiagonalClosedLanguage Unit Unit id,
        ¬ SelfEvaluationObstructed L := by
  constructor
  · simp
  · let L : DiagonalClosedLanguage Unit Unit id :=
      { unary := fun _ => True
        binary := fun _ => True
        diagonal_closed := by intros; trivial }
    refine ⟨L, ?_⟩
    intro h
    apply h
    refine ⟨fun _ _ => (), ?_⟩
    constructor
    · trivial
    · intro f _
      exact ⟨(), fun x => Subsingleton.elim _ _⟩

#print axioms DiagonalClosedLanguage
#print axioms IsUniversalEvaluator
#print axioms SelfEvaluationObstructed
#print axioms DiagonalClosedLanguage.Extends
#print axioms no_universal_evaluator_of_diagonal_closure
#print axioms every_diagonalClosedLanguage_obstructed
#print axioms diagonal_obstruction_stable_under_extension
#print axioms traceSigmaLanguage
#print axioms traceSigmaLanguage_obstructed
#print axioms traceSigmaLanguage_obstructed_via_generic
#print axioms OrientsDuplicatingStep
#print axioms PolynomialMeasureLanguage
#print axioms PolynomialMeasureLanguage.Extends
#print axioms PolynomialOrientationObstructed
#print axioms counterUncoupledPolynomialLanguage
#print axioms fullPolynomialLanguage
#print axioms counterUncoupled_extends_full
#print axioms counterUncoupledPolynomial_obstructed
#print axioms fullPolynomial_not_obstructed_freeSchema
#print axioms polynomial_extension_dissolves_obstruction
#print axioms ObstructionSystem
#print axioms ObstructionSystemEquiv
#print axioms ObstructionTruthMap
#print axioms ObstructionSystem.ExtensionStable
#print axioms ObstructionSystemEquiv.symm
#print axioms extensionStable_map
#print axioms extensionStable_iff
#print axioms diagonalObstructionSystem
#print axioms freePolynomialOrientationSystem
#print axioms diagonalObstructionSystem_extensionStable
#print axioms traceDiagonalObstructionSystem_extensionStable
#print axioms freePolynomialOrientationSystem_not_extensionStable
#print axioms diagonal_and_orientation_obstructions_not_equivalent_generic
#print axioms diagonal_and_orientation_obstructions_not_equivalent
#print axioms no_surjective_obstructionTruthMap_diagonal_to_orientation
#print axioms DefinableFrom
#print axioms collision_not_definable
#print axioms substitutionObstruction_not_definable
#print axioms distinction_license_not_definable_from_collapse
#print axioms orientation_license_not_definable_from_collapse
#print axioms obstruction_class_separation_complete

end OperatorKO7.Test.ObstructionClassSeparationReach
