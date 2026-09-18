import OperatorKO7.Meta.PumpedBarrierClasses_Schema

/-!
# Escape Trichotomy: Schema Layer

Schema-level half of the escape-trichotomy development.

This file isolates the generic `StepDuplicatingSchema` block from
`Meta/EscapeTrichotomy.lean`:

- wrapper-subterm sensitivity,
- base-level successor transparency,
- representability by the Nat-valued direct barrier universe declared below,
- and the resulting schema-generic escape trichotomy theorem.

KO7-specific extensions are declared in `Meta/EscapeTrichotomy.lean`.
-/

namespace OperatorKO7.StepDuplicating

namespace StepDuplicatingSchema

/-- Wrapper-subterm sensitivity for a Nat-valued direct orienter:
both wrapper arguments must be strictly below the wrapped result. -/
def WrapSubtermSensitive (S : StepDuplicatingSchema) (μ : S.T → Nat) : Prop :=
  ∀ x y, μ x < μ (S.wrap x y) ∧ μ y < μ (S.wrap x y)

/-- Base-level successor transparency for a Nat-valued direct orienter. -/
def TransparentAtBase (S : StepDuplicatingSchema) (μ : S.T → Nat) : Prop :=
  μ (S.succ S.base) = μ S.base

/-- The Nat-valued direct families represented by this inductive predicate. -/
inductive NatDirectBarrierRepresentable (S : StepDuplicatingSchema) (μ : S.T → Nat) : Prop
  | additive (M : AdditiveMeasure S) (heval : M.eval = μ)
  | compositionalTransparent (CM : CompositionalMeasure S)
      (htransparent : CM.c_succ CM.c_base = CM.c_base) (heval : CM.eval = μ)
  | affineWithPump (M : AffineMeasureWithPump S) (heval : M.eval = μ)
  | quadraticWithPump (M : QuadraticCounterMeasureWithPump S) (heval : M.eval = μ)
  | crossQuadraticWithPump (M : CrossTermQuadraticMeasureWithPump S) (heval : M.eval = μ)
  | multilinearWithPump (M : MultilinearMeasureWithPump S) (heval : M.eval = μ)
  | polynomialWithPump (M : PolynomialMeasureWithPump S) (heval : M.eval = μ)
  | maxWithPump (M : MaxMeasureWithPump S) (heval : M.eval = μ)

/-- For the represented family type, global orientation implies failure of wrapper sensitivity,
base-level transparency, or membership in `NatDirectBarrierRepresentable`. -/
theorem nat_direct_escape_trichotomy
    {Sys : StepDuplicatingSystem} {μ : Sys.T → Nat}
    (horient : GlobalOrients Sys μ (· < ·)) :
    ¬ WrapSubtermSensitive Sys.toStepDuplicatingSchema μ ∨
      ¬ TransparentAtBase Sys.toStepDuplicatingSchema μ ∨
      ¬ NatDirectBarrierRepresentable Sys.toStepDuplicatingSchema μ := by
  classical
  by_cases hsub : WrapSubtermSensitive Sys.toStepDuplicatingSchema μ
  · by_cases htrans : TransparentAtBase Sys.toStepDuplicatingSchema μ
    · right
      right
      intro hrepr
      cases hrepr with
      | additive M heval =>
          subst heval
          exact (no_global_orients_additive (Sys := Sys) M) horient
      | compositionalTransparent CM htransparent heval =>
          subst heval
          exact (no_global_orients_compositional_transparent_succ
            (Sys := Sys) CM htransparent) horient
      | affineWithPump M heval =>
          subst heval
          exact (no_global_orients_affine_with_pump (Sys := Sys) M) horient
      | quadraticWithPump M heval =>
          subst heval
          exact (no_global_orients_quadratic_with_pump (Sys := Sys) M) horient
      | crossQuadraticWithPump M heval =>
          subst heval
          exact (no_global_orients_cross_quadratic_with_pump (Sys := Sys) M) horient
      | multilinearWithPump M heval =>
          subst heval
          exact (no_global_orients_multilinear_with_pump (Sys := Sys) M) horient
      | polynomialWithPump M heval =>
          subst heval
          exact (no_global_orients_polynomial_with_pump (Sys := Sys) M) horient
      | maxWithPump M heval =>
          subst heval
          exact (no_global_orients_max_with_pump (Sys := Sys) M) horient
    · right
      left
      exact htrans
  · left
    exact hsub

end StepDuplicatingSchema

end OperatorKO7.StepDuplicating
