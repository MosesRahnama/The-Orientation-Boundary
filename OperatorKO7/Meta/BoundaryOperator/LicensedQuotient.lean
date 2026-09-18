import OperatorKO7.Meta.BoundaryOperator

/-!
# Boundary Operator Licensed Quotient

This module defines a licensed-quotient factorization certificate and two
concrete instances. The unconditional construction is a default graph encoding:
it uses the identity gauge action, an `Option` codomain, and a license predicate
equal to `True`. The finite example factors the toy boundary operator from the
core module through its stated quotient data.
-/

namespace OperatorKO7.Meta.BoundaryOperator

universe u v

/-- Licensed quotient data for a boundary-operator input space. -/
structure LicensedQuotient (X : Type u) where
  G : Type u
  group_struct : Group G
  action : G → X → X
  quotient : Type u
  proj : X → quotient
  proj_quotients : ∀ g x, proj (action g x) = proj x
  license : LawvereYanofskyNegativeSeparation
  observable : quotient → Observable

attribute [instance] LicensedQuotient.group_struct

/-- Certificate that a boundary operator factors through a licensed quotient. -/
structure LicensedQuotientFactorizationCertificate
    {X : Type u} {Y : Type v}
    (B : BoundaryOperator X Y) where
  quotient : LicensedQuotient X
  observe : quotient.quotient → Y
  factors : ∀ x : X, ∀ h : B.domain x, B.apply x h = observe (quotient.proj x)

/-- Project the quotient, observation map, and factorization equality stored in
a supplied certificate. -/
theorem LicensedQuotientFactorization
    {X : Type u} {Y : Type v}
    (B : BoundaryOperator X Y)
    (C : LicensedQuotientFactorizationCertificate B) :
    ∃ (LQ : LicensedQuotient X) (O : LQ.quotient → Y),
      ∀ x h, B.apply x h = O (LQ.proj x) := by
  exact ⟨C.quotient, C.observe, C.factors⟩

theorem boundaryOperator_codomain_nonempty
    {X : Type u} {Y : Type v}
    (B : BoundaryOperator X Y) :
    Nonempty Y := by
  classical
  by_cases hY : Nonempty Y
  · exact hY
  · exfalso
    have hRecover :
        ∃ recover : Y → B.Payload,
          ∀ xh : DomainPoint B,
            recover (B.apply xh.1 xh.2) = B.payload_extract xh.1 := by
      refine ⟨fun y => False.elim (hY ⟨y⟩), ?_⟩
      intro xh
      exact False.elim (hY ⟨B.apply xh.1 xh.2⟩)
    exact B.payloadDiscarding hRecover

noncomputable def defaultLicensedQuotientObserve
    {X : Type u} {Y : Type v}
    (B : BoundaryOperator X Y) :
    Option (DomainPoint B) → Y
  | some xh => B.apply xh.1 xh.2
  | none => Classical.choice (boundaryOperator_codomain_nonempty B)

noncomputable def defaultLicensedQuotient
    {X : Type u} {Y : Type v}
    (B : BoundaryOperator X Y) :
    LicensedQuotient X where
  G := PUnit
  group_struct := inferInstance
  action := fun _ x => x
  quotient := Option (DomainPoint B)
  proj := fun x => by
    classical
    exact if h : B.domain x then some ⟨x, h⟩ else none
  proj_quotients := by
    intro g x
    cases g
    rfl
  license := {
    obstruction := True
    holds := trivial
  }
  observable
    | some _ => ⟨"boundary-licensed-quotient-live"⟩
    | none => ⟨"boundary-licensed-quotient-outside-domain"⟩

noncomputable def defaultLicensedQuotientFactorizationCertificate
    {X : Type u} {Y : Type v}
    (B : BoundaryOperator X Y) :
    LicensedQuotientFactorizationCertificate B where
  quotient := defaultLicensedQuotient B
  observe := defaultLicensedQuotientObserve B
  factors := by
    intro x h
    classical
    simp [defaultLicensedQuotient, defaultLicensedQuotientObserve, h]

theorem LicensedQuotientFactorization_exists_unconditional
    {X : Type u} {Y : Type v}
    (B : BoundaryOperator X Y) :
    ∃ (LQ : LicensedQuotient X) (O : LQ.quotient → Y),
      ∀ x h, B.apply x h = O (LQ.proj x) :=
  LicensedQuotientFactorization B
    (defaultLicensedQuotientFactorizationCertificate B)

/-- Licensed quotient data for the finite toy boundary example. -/
def toyLicensedQuotient : LicensedQuotient (Option Bool) where
  G := Z2
  group_struct := inferInstance
  action := Z2.actOptionBool
  quotient := Unit
  proj := fun _ => ()
  proj_quotients := by
    intro g x
    rfl
  license := {
    obstruction := True
    holds := trivial
  }
  observable := fun _ => ⟨"toy-boundary-observable"⟩

/-- The toy boundary operator factors through the displayed finite quotient. -/
def toyBoundaryOperator_factorization :
    LicensedQuotientFactorizationCertificate toyBoundaryOperator where
  quotient := toyLicensedQuotient
  observe := fun _ => false
  factors := by
    intro x h
    rfl

theorem toyBoundaryOperator_has_licensed_quotient_factorization :
    ∃ (LQ : LicensedQuotient (Option Bool)) (O : LQ.quotient → Bool),
      ∀ x h, toyBoundaryOperator.apply x h = O (LQ.proj x) :=
  LicensedQuotientFactorization toyBoundaryOperator toyBoundaryOperator_factorization

end OperatorKO7.Meta.BoundaryOperator
