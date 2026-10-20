/-!
This module defines an abstract one-step relation interface, a descent lens, and a local
contradiction theorem. The result is parametric and follows from the supplied
orientation-to-lens implication plus an exhibited lens violation.




































-/

set_option autoImplicit false

namespace OperatorKO7.RDRSDescentLens

/-- Data record whose requirements are the fields displayed below.







-/
structure RDRSStep (B S N T : Type) where
  /-- Field requirements are given by the displayed type. -/
  lhs : B → S → N → T
  /-- Field requirements are given by the displayed type. -/
  rhs : B → S → N → T

variable {B S N T A : Type}

/-- Definition with formal content given by the displayed type and body.











-/
def Orients (R : RDRSStep B S N T) (μ : T → A) (ltA : A → A → Prop) : Prop :=
  ∀ b s n, ltA (μ (R.rhs b s n)) (μ (R.lhs b s n))

/-- Data record whose requirements are the fields displayed below.











-/
structure DescentLens
    (R : RDRSStep B S N T) (μ : T → A) (ltA : A → A → Prop) where
  /-- Field requirements are given by the displayed type.
-/
  Bq : Type
  /-- Field requirements are given by the displayed type.
-/
  leB : Bq → Bq → Prop
  /-- Field requirements are given by the displayed type. -/
  q : T → Bq
  /-- Field requirements are given by the displayed type.

-/
  nonincrease_of_lt :
    ∀ b s n,
      ltA (μ (R.rhs b s n)) (μ (R.lhs b s n)) →
        leB (q (R.rhs b s n)) (q (R.lhs b s n))

/-- Definition with formal content given by the displayed type and body.










-/
def HasPumpViolation
    {R : RDRSStep B S N T} {μ : T → A} {ltA : A → A → Prop}
    (L : DescentLens R μ ltA) : Prop :=
  ∃ b s n, ¬ L.leB (L.q (R.rhs b s n)) (L.q (R.lhs b s n))

/-- The displayed proposition follows from the stated hypotheses.















-/
theorem no_orients_of_lens_violation
    {R : RDRSStep B S N T} {μ : T → A} {ltA : A → A → Prop}
    (L : DescentLens R μ ltA)
    (hBad : HasPumpViolation L) :
    ¬ Orients R μ ltA := by
  intro hOrients
  obtain ⟨b, s, n, hViolate⟩ := hBad
  exact hViolate (L.nonincrease_of_lt b s n (hOrients b s n))

/-- Definition with formal content given by the displayed type and body.









-/
def rdrs_descent_lens_local_contradiction_anchor : String :=
  "OperatorKO7.RDRSDescentLens.no_orients_of_lens_violation"

end OperatorKO7.RDRSDescentLens
