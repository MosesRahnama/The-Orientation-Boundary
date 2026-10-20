import OperatorKO7.Meta.BoundaryOperator.LicensedQuotient

/-!
# Boundary Operator Licensed Quotient Factorization

## Formal Scope

The formal surface is pointwise equality of observable boundary outputs plus a factorization package through separately supplied projections. Quotient-carrier isomorphism and a common projection are outside the declarations.
-/

namespace OperatorKO7.Meta.BoundaryOperator

universe u v

/-- Pointwise agreement of two observation maps on the image of the
boundary-operator action. Each certificate identifies its observation with
the same `B.apply` value; no map between quotient carriers is constructed. -/
def ObservablesAgreePointwise
    {X : Type u} {Y : Type v}
    (B : BoundaryOperator X Y)
    (C₁ C₂ : LicensedQuotientFactorizationCertificate B) : Prop :=
    ∀ x : X, ∀ _h : B.domain x,
    C₁.observe (C₁.quotient.proj x) = C₂.observe (C₂.quotient.proj x)

/-- The pointwise-uniqueness theorem. Two licensed-quotient
factorizations of the same boundary operator produce observation
maps that agree on every B-image; the proof is direct because both
sides are equal to `B.apply x h` by the certificate factorization
property. -/
theorem LicensedQuotientFactorization_uniqueness_pointwise
    {X : Type u} {Y : Type v}
    (B : BoundaryOperator X Y)
    (C₁ C₂ : LicensedQuotientFactorizationCertificate B) :
    ObservablesAgreePointwise B C₁ C₂ := by
  intro x h
  have h1 : C₁.observe (C₁.quotient.proj x) = B.apply x h := (C₁.factors x h).symm
  have h2 : C₂.observe (C₂.quotient.proj x) = B.apply x h := (C₂.factors x h).symm
  exact h1.trans h2.symm

/-- Bundle of factorization existence and pointwise observable agreement. -/
theorem LicensedQuotientFactorization_engine_grade
    {X : Type u} {Y : Type v}
    (B : BoundaryOperator X Y)
    (C : LicensedQuotientFactorizationCertificate B) :
    (∃ (LQ : LicensedQuotient X) (O : LQ.quotient → Y),
        ∀ x h, B.apply x h = O (LQ.proj x))
    ∧
    (∀ C' : LicensedQuotientFactorizationCertificate B,
        ObservablesAgreePointwise B C C') :=
  ⟨LicensedQuotientFactorization B C,
   fun C' => LicensedQuotientFactorization_uniqueness_pointwise B C C'⟩

theorem LicensedQuotientFactorization_unconditional
    {X : Type u} {Y : Type v}
    (B : BoundaryOperator X Y) :
    (∃ (LQ : LicensedQuotient X) (O : LQ.quotient → Y),
        ∀ x h, B.apply x h = O (LQ.proj x))
    ∧
    (∀ C' : LicensedQuotientFactorizationCertificate B,
        ObservablesAgreePointwise B
          (defaultLicensedQuotientFactorizationCertificate B) C') :=
  LicensedQuotientFactorization_engine_grade B
    (defaultLicensedQuotientFactorizationCertificate B)

/-- Pointwise-agreement companion. The underlying theorem
theorem already universally quantifies over `(C₁, C₂)` certificate pairs;
this restatement surfaces that property as an explicit unconditional theorem
on `B` alone, with no ambient certificate fixed. Strictly stronger than
`LicensedQuotientFactorization_unconditional`'s second conjunct (which fixes
the default certificate as one side). -/
theorem LicensedQuotientFactorization_uniqueness_unconditional
    {X : Type u} {Y : Type v}
    (B : BoundaryOperator X Y) :
    ∀ C₁ C₂ : LicensedQuotientFactorizationCertificate B,
      ObservablesAgreePointwise B C₁ C₂ :=
  LicensedQuotientFactorization_uniqueness_pointwise B

/-- Combined factorization and observable-agreement package. It joins the
existence theorem with the universally-quantified pointwise-uniqueness
theorem. Quotient-carrier isomorphism remains outside this type. -/
theorem LicensedQuotientFactorization_universal_unconditional
    {X : Type u} {Y : Type v}
    (B : BoundaryOperator X Y) :
    (∃ (LQ : LicensedQuotient X) (O : LQ.quotient → Y),
        ∀ x h, B.apply x h = O (LQ.proj x))
    ∧
    (∀ C₁ C₂ : LicensedQuotientFactorizationCertificate B,
        ObservablesAgreePointwise B C₁ C₂) :=
  ⟨LicensedQuotientFactorization_exists_unconditional B,
   LicensedQuotientFactorization_uniqueness_unconditional B⟩

/-- Discharge of both companion theorems on the toy boundary operator. -/
theorem toyBoundaryOperator_LicensedQuotientFactorization_engine_grade :
    (∃ (LQ : LicensedQuotient (Option Bool)) (O : LQ.quotient → Bool),
        ∀ x h, toyBoundaryOperator.apply x h = O (LQ.proj x))
    ∧
    (∀ C' : LicensedQuotientFactorizationCertificate toyBoundaryOperator,
        ObservablesAgreePointwise toyBoundaryOperator
          toyBoundaryOperator_factorization C') :=
  LicensedQuotientFactorization_engine_grade
    toyBoundaryOperator toyBoundaryOperator_factorization

/-- Specialization of the combined package to the toy boundary operator. -/
theorem toyBoundaryOperator_LicensedQuotientFactorization_universal_unconditional :
    (∃ (LQ : LicensedQuotient (Option Bool)) (O : LQ.quotient → Bool),
        ∀ x h, toyBoundaryOperator.apply x h = O (LQ.proj x))
    ∧
    (∀ C₁ C₂ : LicensedQuotientFactorizationCertificate toyBoundaryOperator,
        ObservablesAgreePointwise toyBoundaryOperator C₁ C₂) :=
  LicensedQuotientFactorization_universal_unconditional toyBoundaryOperator

end OperatorKO7.Meta.BoundaryOperator
