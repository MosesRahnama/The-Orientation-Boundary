import OperatorKO7.Meta.BoundaryOperator.LicensedQuotient

namespace BoundaryOperatorLicensedQuotientReach

open OperatorKO7.Meta.BoundaryOperator

#check boundaryOperator_codomain_nonempty
#check LicensedQuotient
#check LicensedQuotientFactorizationCertificate
#check LicensedQuotientFactorization
#check defaultLicensedQuotient
#check defaultLicensedQuotientFactorizationCertificate
#check LicensedQuotientFactorization_exists_unconditional
#check toyLicensedQuotient
#check toyBoundaryOperator_factorization
#check toyBoundaryOperator_has_licensed_quotient_factorization

example : LicensedQuotientFactorizationCertificate toyBoundaryOperator :=
  toyBoundaryOperator_factorization

example : ∃ (LQ : LicensedQuotient (Option Bool)) (O : LQ.quotient → Bool),
    ∀ x h, toyBoundaryOperator.apply x h = O (LQ.proj x) :=
  toyBoundaryOperator_has_licensed_quotient_factorization

example : ∃ (LQ : LicensedQuotient (Option Bool)) (O : LQ.quotient → Bool),
    ∀ x h, toyBoundaryOperator.apply x h = O (LQ.proj x) :=
  LicensedQuotientFactorization_exists_unconditional toyBoundaryOperator

end BoundaryOperatorLicensedQuotientReach
