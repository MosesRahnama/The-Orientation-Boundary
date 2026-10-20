import OperatorKO7.Meta.BoundaryOperator.LicensedQuotientFactorization

namespace BoundaryOperatorLicensedQuotientFactorizationReach

open OperatorKO7.Meta.BoundaryOperator

#check @ObservablesAgreePointwise
#check @LicensedQuotientFactorization_uniqueness_pointwise
#check @LicensedQuotientFactorization_engine_grade
#check @LicensedQuotientFactorization_unconditional
#check @LicensedQuotientFactorization_uniqueness_unconditional
#check @LicensedQuotientFactorization_universal_unconditional
#check toyBoundaryOperator_LicensedQuotientFactorization_engine_grade
#check toyBoundaryOperator_LicensedQuotientFactorization_universal_unconditional

example : (∃ (LQ : LicensedQuotient (Option Bool)) (O : LQ.quotient → Bool),
              ∀ x h, toyBoundaryOperator.apply x h = O (LQ.proj x))
          ∧
          (∀ C' : LicensedQuotientFactorizationCertificate toyBoundaryOperator,
              ObservablesAgreePointwise toyBoundaryOperator
                toyBoundaryOperator_factorization C') :=
  toyBoundaryOperator_LicensedQuotientFactorization_engine_grade

example : (∃ (LQ : LicensedQuotient (Option Bool)) (O : LQ.quotient → Bool),
              ∀ x h, toyBoundaryOperator.apply x h = O (LQ.proj x))
          ∧
          (∀ C' : LicensedQuotientFactorizationCertificate toyBoundaryOperator,
              ObservablesAgreePointwise toyBoundaryOperator
                (defaultLicensedQuotientFactorizationCertificate toyBoundaryOperator) C') :=
  LicensedQuotientFactorization_unconditional toyBoundaryOperator

example {X : Type} {Y : Type} (B : BoundaryOperator X Y) :
    ∀ C₁ C₂ : LicensedQuotientFactorizationCertificate B,
      ObservablesAgreePointwise B C₁ C₂ :=
  LicensedQuotientFactorization_uniqueness_unconditional B

example {X : Type} {Y : Type} (B : BoundaryOperator X Y) :
    (∃ (LQ : LicensedQuotient X) (O : LQ.quotient → Y),
        ∀ x h, B.apply x h = O (LQ.proj x))
    ∧
    (∀ C₁ C₂ : LicensedQuotientFactorizationCertificate B,
        ObservablesAgreePointwise B C₁ C₂) :=
  LicensedQuotientFactorization_universal_unconditional B

example : (∃ (LQ : LicensedQuotient (Option Bool)) (O : LQ.quotient → Bool),
              ∀ x h, toyBoundaryOperator.apply x h = O (LQ.proj x))
          ∧
          (∀ C₁ C₂ : LicensedQuotientFactorizationCertificate toyBoundaryOperator,
              ObservablesAgreePointwise toyBoundaryOperator C₁ C₂) :=
  toyBoundaryOperator_LicensedQuotientFactorization_universal_unconditional

end BoundaryOperatorLicensedQuotientFactorizationReach
