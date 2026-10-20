import OperatorKO7.Meta.BoundaryGeneral.HomomorphicInexpressibility
import OperatorKO7.Meta.SafeStep.HomomorphicGuardBarrier
import OperatorKO7.Meta.Recursor.DPConfessionLicenseUnconditional

/-!
# Homomorphic projection barrier for the recursor fold

This module places the existing seven-constructor `RecursorTerm.fold` inside
the same proof-carrying `AlgebraHom` interface used by the guard theorem. For a
target recursor algebra whose `recR` operation ignores its third input, the fold
identifies the existing closed witness pair. The explicit syntactic counter
projection separates that pair and therefore cannot factor through the fold.

This is a signature-relative factorization obstruction. It is not a dependency
pair soundness theorem, a termination theorem, or an assertion that every
orientation method has this factorization shape.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.Recursor.HomomorphicProjectionBarrier

open OperatorKO7.Meta.BoundaryGeneral.HomomorphicInexpressibility
open OperatorKO7.Meta.SafeStep.HomomorphicGuardBarrier
open OperatorKO7.Meta.Recursor.DPConfessionLicense
open OperatorKO7.Meta.Recursor.RecursorFreeAlgebra
open OperatorKO7.Meta.Recursor.DPConfessionLicenseUnconditional

universe u

/-! ## Recursor algebras in the generic finitary interface -/

/-- The free seven-constructor algebra carried by closed `RecursorTerm` values. -/
def recursorTermAlgebra : FinitaryAlgebra ko7Signature where
  Carrier := RecursorTerm
  interp
    | .void, _ => RecursorTerm.void
    | .delta, args => RecursorTerm.delta (args 0)
    | .integrate, args => RecursorTerm.integrate (args 0)
    | .merge, args => RecursorTerm.merge (args 0) (args 1)
    | .app, args => RecursorTerm.app (args 0) (args 1)
    | .recDelta, args => RecursorTerm.recR (args 0) (args 1) (args 2)
    | .eqW, args => RecursorTerm.eqWit (args 0) (args 1)

/-- Convert the existing mixed-arity recursor algebra into the generic
finitary-algebra interface over the same seven operation symbols. -/
def algebraOfRecursorSigma {alpha : Type u} (S : SigmaAlgebra alpha) :
    FinitaryAlgebra ko7Signature where
  Carrier := alpha
  interp
    | .void, _ => S.void
    | .delta, args => S.delta (args 0)
    | .integrate, args => S.integrate (args 0)
    | .merge, args => S.merge (args 0) (args 1)
    | .app, args => S.app (args 0) (args 1)
    | .recDelta, args => S.recR (args 0) (args 1) (args 2)
    | .eqW, args => S.eqWit (args 0) (args 1)

/-- Package the existing seven preservation equations as a genuine generic
algebra homomorphism. -/
def algebraHomOfSigmaHomomorphism
    {alpha : Type u} (S : SigmaAlgebra alpha)
    (P : RecursorTerm -> alpha) (hP : IsSigmaHomomorphism P S) :
    AlgebraHom recursorTermAlgebra (algebraOfRecursorSigma S) where
  toFun := P
  map_op := by
    intro operation args
    cases operation with
    | void => exact hP.pres_void
    | delta => exact hP.pres_delta (args 0)
    | integrate => exact hP.pres_integrate (args 0)
    | merge => exact hP.pres_merge (args 0) (args 1)
    | app => exact hP.pres_app (args 0) (args 1)
    | recDelta => exact hP.pres_recR (args 0) (args 1) (args 2)
    | eqW => exact hP.pres_eqWit (args 0) (args 1)

/-- The existing recursor fold is a proof-carrying homomorphism for the exact
seven-constructor signature. -/
def foldHom {alpha : Type u} (S : SigmaAlgebra alpha) :
    AlgebraHom recursorTermAlgebra (algebraOfRecursorSigma S) :=
  algebraHomOfSigmaHomomorphism S (RecursorTerm.fold S)
    (RecursorTerm.fold_isSigmaHomomorphism S)

/-- The generic homomorphism's underlying function is the existing fold. -/
theorem foldHom_toFun {alpha : Type u} (S : SigmaAlgebra alpha)
    (t : RecursorTerm) :
    (foldHom S).toFun t = RecursorTerm.fold S t :=
  rfl

/-! ## Explicit projection and factorization obstruction -/

/-- Syntactic outer-counter projection on the existing witness family. It
detects a `delta` in the third argument of an outermost `recR`. -/
def recursorCounterProjection : RecursorTerm -> Nat
  | RecursorTerm.recR _ _ (RecursorTerm.delta _) => 1
  | _ => 0

/-- The existing closed recursor witnesses are genuinely distinct. -/
theorem recursor_witnesses_distinct : witnessLeft ≠ witnessRight :=
  witnessLeft_ne_witnessRight

/-- The explicit projection separates the existing closed witness pair. -/
theorem recursorCounterProjection_separates_witnesses :
    recursorCounterProjection witnessLeft ≠
      recursorCounterProjection witnessRight := by
  show (0 : Nat) ≠ 1
  intro h
  cases h

/-- Any packaged recursor homomorphism into an algebra whose `recR` operation
ignores its third input identifies the existing witness pair. -/
theorem sigmaHom_identifies_witnesses_of_recRConstantInThird
    {alpha : Type u} (S : SigmaAlgebra alpha)
    (P : RecursorTerm -> alpha) (hP : IsSigmaHomomorphism P S)
    (hRecR : RecRConstantInThird S) :
    (algebraHomOfSigmaHomomorphism S P hP).toFun witnessLeft =
      (algebraHomOfSigmaHomomorphism S P hP).toFun witnessRight :=
  dp_projection_not_in_recursor_signature_unconditional S P hP hRecR

/-- The explicit counter projection cannot factor through any such genuine
seven-constructor homomorphism. -/
theorem recursorCounterProjection_not_factorsThrough_sigmaHom
    {alpha : Type u} (S : SigmaAlgebra alpha)
    (P : RecursorTerm -> alpha) (hP : IsSigmaHomomorphism P S)
    (hRecR : RecRConstantInThird S) :
    Not (ProjectionFactorsThrough
      (algebraHomOfSigmaHomomorphism S P hP)
      recursorCounterProjection) := by
  exact projection_not_factorsThrough_of_hom_collapse
    (h := algebraHomOfSigmaHomomorphism S P hP)
    (projection := recursorCounterProjection)
    (a := witnessLeft) (b := witnessRight)
    (sigmaHom_identifies_witnesses_of_recRConstantInThird
      S P hP hRecR)
    recursorCounterProjection_separates_witnesses

/-- In particular, when the target algebra's recursor operation ignores its
third input, the counter projection cannot factor through the actual recursive
fold. -/
theorem recursorCounterProjection_not_factorsThrough_fold
    {alpha : Type u} (S : SigmaAlgebra alpha)
    (hRecR : RecRConstantInThird S) :
    Not (ProjectionFactorsThrough (foldHom S) recursorCounterProjection) :=
  recursorCounterProjection_not_factorsThrough_sigmaHom
    S (RecursorTerm.fold S)
      (RecursorTerm.fold_isSigmaHomomorphism S) hRecR

end OperatorKO7.Meta.Recursor.HomomorphicProjectionBarrier
