import OperatorKO7.Meta.ConstructionMethodClassification

namespace ConstructionMethodClassificationReach

open OperatorKO7.ConstructionMethodClassification
open OperatorKO7.StepDuplicating

#check ConstructionRoute
#check W1ImportClass
#check W1ImportEvidence
#check W1ConstructionSuccess
#check PermittedW1Import
#check poly_not_transparent_at_base
#check fullDuplicating_imported_whole_not_w0_direct
#check mpo_recursor_step_uses_precedence
#check w1_success_requires_permitted_import
#check mpo_w1_success
#check poly_w1_success
#check importedWhole_w1_success
#check transparency_w1_success
#check mpo_w1_success_requires_precedence_import
#check poly_w1_success_requires_global_polynomial_import
#check importedWhole_w1_success_requires_imported_whole
#check transparency_w1_success_requires_transparency_import
#check importedWhole_w1_success_separates_from_w0
#check poly_w1_success_escapes_direct_additive_affine_surface
#check canonical_w1_witness_catalog

example : OperatorKO7.MetaMPO.symPrec OperatorKO7.MetaMPO.Sym.app OperatorKO7.MetaMPO.Sym.recΔ := by
  exact mpo_recursor_step_uses_precedence

example : PermittedW1Import mpo_w1_success.importClass := by
  exact w1_success_requires_permitted_import mpo_w1_success

example : PermittedW1Import .precedence := by
  exact mpo_w1_success_requires_precedence_import

example : PermittedW1Import poly_w1_success.importClass := by
  exact w1_success_requires_permitted_import poly_w1_success

example : PermittedW1Import .globalPolynomial := by
  exact poly_w1_success_requires_global_polynomial_import

example : PermittedW1Import .importedWholeWitness := by
  exact importedWhole_w1_success_requires_imported_whole

example : PermittedW1Import .transparencyEssentiality := by
  exact transparency_w1_success_requires_transparency_import

example : OperatorKO7.BenchmarkedPRCFamily.HasImportedWholeWitness
    OperatorKO7.BenchmarkedPRCFamily.fullDuplicating := by
  exact fullDuplicating_imported_whole_not_w0_direct.1

example : ¬ OperatorKO7.BenchmarkedPRCFamily.HasDirectWitness
    OperatorKO7.BenchmarkedPRCFamily.fullDuplicating := by
  exact fullDuplicating_imported_whole_not_w0_direct.2

example : importedWhole_w1_success.route ≠ .W0 := by
  exact importedWhole_w1_success_separates_from_w0.1

example : ¬ StepDuplicatingSchema.TransparentAtBase
  OperatorKO7.CompositionalImpossibility.ko7Schema OperatorKO7.PolyInterpretation.W := by
  exact poly_w1_success_escapes_direct_additive_affine_surface.1

example : importedWhole_w1_success.importClass = .importedWholeWitness := by
  exact canonical_w1_witness_catalog.2.2.1.1

end ConstructionMethodClassificationReach
