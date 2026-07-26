import OperatorKO7.Kernel

/-!
# Sigma term algebra over the KO7 signature

`SigmaTerm` mirrors the seven `Trace` constructors and adds the two
distinguished leaves `varA` and `varB`. `evalSigma a b` replaces those leaves
with the supplied terms and recursively preserves every constructor head.
Because `a` and `b` are themselves `SigmaTerm` values, the result may still
contain distinguished leaves.

## Signature

The KO7 kernel `Trace` carries seven term constructors:
`void`, `delta`, `integrate`, `merge`, `app`, `recDelta`, `eqW`.
The two distinguished leaves provide the input positions used by the
two-argument Sigma expressions in `SyntacticNonDerivability.lean`.

## Substitution and the head-leaf classification

The evaluator `evalSigma t a b` substitutes `a` for every `varA`
and `b` for every `varB` in `t`. The head-leaf classification
distinguishes three cases of `t`:

  * `t = void`: `evalSigma t a b = void` for all `a, b`. The
    result is constantly the void leaf.
  * `t = varA`: `evalSigma t a b = a`.
  * `t = varB`: `evalSigma t a b = b`.
  * `t = delta s` / `integrate s` / `merge s1 s2` / `app s1 s2` /
    `recDelta s1 s2 s3` / `eqW s1 s2`: `evalSigma t a b` is wrapped
    in the same head constructor; in particular `evalSigma t a b`
    is never equal to `void` because constructors are disjoint.

`evalSigma_non_leaf_never_void` classifies terms by their outer constructor.
`substitution_invariance` is the ordinary structural induction principle for
`SigmaTerm`; despite its historical name, it does not mention `evalSigma` in
its theorem statement.
-/

namespace OperatorKO7.Meta.SafeStep.SigmaFreeAlgebra

/-- Terms over the KO7 signature with two distinguished leaves, `varA` and
`varB`. -/
inductive SigmaTerm : Type
  | void      : SigmaTerm
  | varA      : SigmaTerm
  | varB      : SigmaTerm
  | delta     : SigmaTerm → SigmaTerm
  | integrate : SigmaTerm → SigmaTerm
  | merge     : SigmaTerm → SigmaTerm → SigmaTerm
  | app       : SigmaTerm → SigmaTerm → SigmaTerm
  | recDelta  : SigmaTerm → SigmaTerm → SigmaTerm → SigmaTerm
  | eqW       : SigmaTerm → SigmaTerm → SigmaTerm
  deriving DecidableEq, Repr

/-- Replace every `varA` with `a` and every `varB` with `b`, preserving all
constructor heads. The supplied terms may themselves contain `varA` or
`varB`. -/
def evalSigma (a b : SigmaTerm) : SigmaTerm → SigmaTerm
  | SigmaTerm.void                 => SigmaTerm.void
  | SigmaTerm.varA                 => a
  | SigmaTerm.varB                 => b
  | SigmaTerm.delta s              =>
      SigmaTerm.delta (evalSigma a b s)
  | SigmaTerm.integrate s          =>
      SigmaTerm.integrate (evalSigma a b s)
  | SigmaTerm.merge s1 s2          =>
      SigmaTerm.merge (evalSigma a b s1) (evalSigma a b s2)
  | SigmaTerm.app s1 s2            =>
      SigmaTerm.app (evalSigma a b s1) (evalSigma a b s2)
  | SigmaTerm.recDelta s1 s2 s3    =>
      SigmaTerm.recDelta (evalSigma a b s1) (evalSigma a b s2)
        (evalSigma a b s3)
  | SigmaTerm.eqW s1 s2            =>
      SigmaTerm.eqW (evalSigma a b s1) (evalSigma a b s2)

/-- A SigmaTerm is a "leaf form" iff its outermost constructor is
`void`, `varA`, or `varB`. The non-leaf forms are exactly the six
constructor wrappers that produce a non-void head under evaluation. -/
def isLeafForm : SigmaTerm → Prop
  | SigmaTerm.void => True
  | SigmaTerm.varA => True
  | SigmaTerm.varB => True
  | _              => False

/-- Decision procedure for `isLeafForm`. -/
instance : DecidablePred isLeafForm := by
  intro t
  cases t <;> simp [isLeafForm] <;> infer_instance

/-- Substitution-invariance for non-leaf-form SigmaTerms: if the
outermost constructor of `t` is one of the six non-leaf
constructors (delta, integrate, merge, app, recDelta, eqW), then
the evaluator's result has the same outermost constructor and is
therefore distinct from `void` by the disjointness of constructor
heads in the inductive type. -/
theorem evalSigma_non_leaf_never_void
    (t : SigmaTerm) (h : ¬ isLeafForm t) (a b : SigmaTerm) :
    evalSigma a b t ≠ SigmaTerm.void := by
  cases t with
  | void      => exact False.elim (h trivial)
  | varA      => exact False.elim (h trivial)
  | varB      => exact False.elim (h trivial)
  | delta s         =>
      intro contra; cases contra
  | integrate s     =>
      intro contra; cases contra
  | merge s1 s2     =>
      intro contra; cases contra
  | app s1 s2       =>
      intro contra; cases contra
  | recDelta s1 s2 s3 =>
      intro contra; cases contra
  | eqW s1 s2       =>
      intro contra; cases contra

/-- Substitution-invariance for the void leaf: the void term
evaluates to void at every substitution. -/
theorem evalSigma_void (a b : SigmaTerm) :
    evalSigma a b SigmaTerm.void = SigmaTerm.void := rfl

/-- Substitution-invariance for the varA leaf: the varA term
evaluates to its first argument. -/
theorem evalSigma_varA (a b : SigmaTerm) :
    evalSigma a b SigmaTerm.varA = a := rfl

/-- Substitution-invariance for the varB leaf: the varB term
evaluates to its second argument. -/
theorem evalSigma_varB (a b : SigmaTerm) :
    evalSigma a b SigmaTerm.varB = b := rfl

/-- Structural induction for `SigmaTerm`, packaged as a theorem. -/
theorem substitution_invariance
    (P : SigmaTerm → Prop)
    (h_void : P SigmaTerm.void)
    (h_varA : P SigmaTerm.varA)
    (h_varB : P SigmaTerm.varB)
    (h_delta : ∀ s, P s → P (SigmaTerm.delta s))
    (h_integrate : ∀ s, P s → P (SigmaTerm.integrate s))
    (h_merge : ∀ s1 s2, P s1 → P s2 → P (SigmaTerm.merge s1 s2))
    (h_app : ∀ s1 s2, P s1 → P s2 → P (SigmaTerm.app s1 s2))
    (h_recDelta : ∀ s1 s2 s3, P s1 → P s2 → P s3
                              → P (SigmaTerm.recDelta s1 s2 s3))
    (h_eqW : ∀ s1 s2, P s1 → P s2 → P (SigmaTerm.eqW s1 s2)) :
    ∀ t, P t := by
  intro t
  induction t with
  | void              => exact h_void
  | varA              => exact h_varA
  | varB              => exact h_varB
  | delta s ih        => exact h_delta s ih
  | integrate s ih    => exact h_integrate s ih
  | merge s1 s2 ih1 ih2 => exact h_merge s1 s2 ih1 ih2
  | app s1 s2 ih1 ih2   => exact h_app s1 s2 ih1 ih2
  | recDelta s1 s2 s3 ih1 ih2 ih3 =>
      exact h_recDelta s1 s2 s3 ih1 ih2 ih3
  | eqW s1 s2 ih1 ih2   => exact h_eqW s1 s2 ih1 ih2

/-- The two distinct closed-leaf SigmaTerms `void` and
`delta void`. Used by `SyntacticNonDerivability.lean` as the
canonical disequality witness pair: the leaf-form analysis at
`(void, void)` and the wrapped-constructor analysis at
`(void, delta void)` together close the unconditional theorem
by case analysis on the candidate term's outermost constructor. -/
abbrev witness_pair_distinct :
    SigmaTerm.void ≠ SigmaTerm.delta SigmaTerm.void := by
  intro h; cases h

end OperatorKO7.Meta.SafeStep.SigmaFreeAlgebra
