import OperatorKO7.Meta.BoundaryGeneral.HomomorphicInexpressibility
import OperatorKO7.Meta.SafeStep.SyntacticNonDerivability

/-!
# Homomorphic guard barrier for the exact KO7 signature

This module instantiates the generic finitary-algebra obstruction on the seven
KO7 constructors. The two input variables are separate from those seven
operations. A substitution endomorphism sends both distinguished variables to
`void`, preserves every KO7 operation, and fixes the selected closed positive
truth token `delta void`.

The new theorem concerns term definition by equality with that exact truth
token. The historical theorem using the broader output test `result != void`
is retained separately and is not claimed to follow from the narrower
truth-token theorem.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.SafeStep.HomomorphicGuardBarrier

open OperatorKO7.Meta.BoundaryGeneral.HomomorphicInexpressibility
open OperatorKO7.Meta.SafeStep.SigmaFreeAlgebra
open OperatorKO7.Meta.SafeStep.SyntacticNonDerivability

/-! ## Exact seven-constructor signature and algebra -/

/-- The seven KO7 operation symbols, excluding the two variable slots. -/
inductive KO7Op where
  | void
  | delta
  | integrate
  | merge
  | app
  | recDelta
  | eqW
  deriving DecidableEq, Fintype, Repr

/-- Exact arities of the seven KO7 constructors. -/
abbrev ko7Signature : FinitarySignature where
  Op := KO7Op
  arity
    | .void => 0
    | .delta => 1
    | .integrate => 1
    | .merge => 2
    | .app => 2
    | .recDelta => 3
    | .eqW => 2

/-- The exact seven-constructor algebra on `SigmaTerm`. The distinguished
`varA` and `varB` values belong to the carrier but are not operation symbols. -/
def ko7SigmaAlgebra : FinitaryAlgebra ko7Signature where
  Carrier := SigmaTerm
  interp
    | .void, _ => SigmaTerm.void
    | .delta, args => SigmaTerm.delta (args 0)
    | .integrate, args => SigmaTerm.integrate (args 0)
    | .merge, args => SigmaTerm.merge (args 0) (args 1)
    | .app, args => SigmaTerm.app (args 0) (args 1)
    | .recDelta, args => SigmaTerm.recDelta (args 0) (args 1) (args 2)
    | .eqW, args => SigmaTerm.eqW (args 0) (args 1)

/-- Embed the generic two-variable carrier into the existing Sigma syntax. -/
def binaryVarSigma : BinaryVar -> SigmaTerm
  | .left => SigmaTerm.varA
  | .right => SigmaTerm.varB

/-- Compile a generic term over the exact seven-constructor signature into the
existing `SigmaTerm` representation. -/
def compileKO7Term (t : FreeTerm ko7Signature BinaryVar) : SigmaTerm :=
  FreeTerm.eval ko7SigmaAlgebra binaryVarSigma t

/-! ## Genuine substitution homomorphisms -/

/-- Existing Sigma substitution, packaged with preservation proofs for all
seven operations. -/
def ko7SubstitutionHom (a b : SigmaTerm) :
    AlgebraHom ko7SigmaAlgebra ko7SigmaAlgebra where
  toFun := evalSigma a b
  map_op := by
    intro operation args
    cases operation with
    | void => rfl
    | delta => rfl
    | integrate => rfl
    | merge => rfl
    | app => rfl
    | recDelta => rfl
    | eqW => rfl

/-- Evaluating a generic KO7 term agrees with evaluating its compiled
`SigmaTerm` through the existing `evalSigma` evaluator. -/
theorem evalKO7Term_eq_evalSigma_compile
    (t : FreeTerm ko7Signature BinaryVar) (a b : SigmaTerm) :
    FreeTerm.eval ko7SigmaAlgebra (binaryVal a b) t =
      evalSigma a b (compileKO7Term t) := by
  have hnatural :=
    FreeTerm.eval_natural (ko7SubstitutionHom a b) t binaryVarSigma
  change
    evalSigma a b (compileKO7Term t) =
      FreeTerm.eval ko7SigmaAlgebra
        (fun x => evalSigma a b (binaryVarSigma x)) t at hnatural
  have hvaluation :
      (fun x => evalSigma a b (binaryVarSigma x)) =
        binaryVal a b := by
    funext x
    cases x <;> rfl
  rw [hvaluation] at hnatural
  exact hnatural.symm

/-- The endomorphism that identifies both distinguished variables with
`void`. -/
def ko7VariableCollapseHom :
    AlgebraHom ko7SigmaAlgebra ko7SigmaAlgebra :=
  ko7SubstitutionHom SigmaTerm.void SigmaTerm.void

/-- Closed positive truth token for the term-definition theorem. -/
def ko7PositiveTruth : SigmaTerm :=
  SigmaTerm.delta SigmaTerm.void

/-- The variable-collapse endomorphism fixes the closed truth token. -/
theorem ko7VariableCollapseHom_fixes_positiveTruth :
    ko7VariableCollapseHom.toFun ko7PositiveTruth = ko7PositiveTruth := by
  rfl

/-- The two distinguished Sigma variables are genuinely distinct. -/
theorem sigma_varA_ne_varB : SigmaTerm.varA ≠ SigmaTerm.varB := by
  intro h
  cases h

/-- The genuine homomorphism identifies the two distinguished variables. -/
theorem ko7VariableCollapseHom_identifies_variables :
    ko7VariableCollapseHom.toFun SigmaTerm.varA =
      ko7VariableCollapseHom.toFun SigmaTerm.varB := by
  rfl

/-- Non-vacuous proof-carrying obstruction for the exact KO7 signature. -/
def ko7GuardObstruction :
    HomomorphicPredicateObstruction ko7SigmaAlgebra ko7PositiveTruth
      (fun x y : SigmaTerm => x ≠ y) where
  hom := ko7VariableCollapseHom
  truth_fixed := ko7VariableCollapseHom_fixes_positiveTruth
  a := SigmaTerm.varA
  b := SigmaTerm.varB
  distinct := sigma_varA_ne_varB
  collapse := ko7VariableCollapseHom_identifies_variables
  target_at_pair := sigma_varA_ne_varB
  target_fails_after_map := by
    intro hne
    exact hne rfl

/-! ## Seven-constructor guard obstruction -/

/-- No term over the exact seven KO7 constructors returns the fixed positive
truth token exactly on disequal `SigmaTerm` inputs. This is interface-relative
term inexpressibility, not inexpressibility in arbitrary rewriting languages. -/
theorem ko7_sevenConstructor_disequality_not_termDefinable :
    Not (exists t : FreeTerm ko7Signature BinaryVar,
      forall a b : SigmaTerm,
        FreeTerm.eval ko7SigmaAlgebra (binaryVal a b) t =
          ko7PositiveTruth ↔ a ≠ b) := by
  change Not (TermDefinesBinaryPredicate ko7SigmaAlgebra ko7PositiveTruth
    (fun x y : SigmaTerm => x ≠ y))
  exact ko7GuardObstruction.not_termDefinable

/-- The historical, stronger-in-output-test theorem remains available with
its exact original seven-constructor evaluator and statement. It is retained
as a separate theorem, not presented as a corollary of the fixed-token result. -/
theorem legacy_voidTest_disequality_not_sigma_expressible :
    Not (exists t : SigmaTerm,
      forall a b : SigmaTerm,
        (a ≠ b) ↔ (evalSigma a b t ≠ SigmaTerm.void)) :=
  disequality_not_sigma_expressible_unconditional

end OperatorKO7.Meta.SafeStep.HomomorphicGuardBarrier
