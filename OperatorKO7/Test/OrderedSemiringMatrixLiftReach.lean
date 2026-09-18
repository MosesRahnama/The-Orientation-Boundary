import OperatorKO7.Meta.OrderedSemiringMatrixLift

set_option autoImplicit false

/-!
# Reach test for the ordered-semiring matrix-lift theory-expansion module

Forces elaboration of every public declaration of
`OperatorKO7/Meta/OrderedSemiringMatrixLift.lean` and exercises the
headline unconditional theorem on the seven-row closed universe.
-/

open OperatorKO7.OrderedSemiringMatrixLift

/-! ## Reach checks: every public declaration is named. -/

#check @BaseSemiringKind
#check @MatrixAlgebraKind
#check @MonotonicityStatus
#check @liftToMatrixAlgebra
#check @monotonicityOf
#check @baseSemiringList
#check @matrixAlgebraImage
#check @baseSemiringList_length
#check @baseSemiringList_nodup
#check @baseSemiringList_complete
#check @matrixAlgebraImage_length
#check @matrixAlgebraImage_nodup
#check @liftToMatrixAlgebra_mem_image
#check @monotonicityOf_preserves
#check @ordered_semiring_matrix_lift_universe_unconditional
#check @audit_theory_expansion_ordered_semiring_matrix_lift_module_anchor

/-! ## Smoke: the headline theorem destructures to the expected facts. -/

example :
    (∀ b : BaseSemiringKind, liftToMatrixAlgebra b ∈ matrixAlgebraImage) ∧
    (baseSemiringList.length = 7 ∧ baseSemiringList.Nodup ∧
      ∀ b : BaseSemiringKind, b ∈ baseSemiringList) ∧
    (matrixAlgebraImage.length = 7 ∧ matrixAlgebraImage.Nodup) ∧
    (∀ b : BaseSemiringKind,
        monotonicityOf b = MonotonicityStatus.preservesMonotonicity) ∧
    (∃ b : BaseSemiringKind, ∃ m : MatrixAlgebraKind,
        liftToMatrixAlgebra b = m) :=
  ordered_semiring_matrix_lift_universe_unconditional

/-! ## Concrete tag-level evaluation. -/

example : liftToMatrixAlgebra .naturalSemiring = .naturalMatrix := rfl
example : liftToMatrixAlgebra .arcticSemiring = .arcticMatrix := rfl
example : liftToMatrixAlgebra .booleanSemiring = .booleanMatrix := rfl

example :
    monotonicityOf .tropicalSemiring = MonotonicityStatus.preservesMonotonicity :=
  rfl

example : baseSemiringList.length = 7 := baseSemiringList_length

example :
    audit_theory_expansion_ordered_semiring_matrix_lift_module_anchor =
      "OperatorKO7.OrderedSemiringMatrixLift.ordered_semiring_matrix_lift_universe_unconditional" :=
  rfl
