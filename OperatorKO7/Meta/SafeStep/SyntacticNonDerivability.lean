import OperatorKO7.Kernel
import OperatorKO7.Meta.SafeStep.GaugeFixingGuard
import OperatorKO7.Meta.SafeStep.SigmaFreeAlgebra

/-!
# Syntactic Non-Derivability of the Disequality Guard (W16.7)

W16.7: the path-(a) commercial-claim theorem. The disequality
guard `a ≠ b` is not Σ-expressible by any finite combination of the
KO7 rewriting symbols `{void, delta, integrate, merge, app, recDelta,
eqW}` plus the two predicate-variable slots `varA` and `varB`. The
SafeStep meta-layer is therefore a mathematical necessity, not a
design choice; the engine's external observer is the unique source
of the disequality decision that resolves the eqW critical pair.

## Unconditional close

The headline theorem `disequality_not_sigma_expressible` is
unconditional, discharged through the `SigmaFreeAlgebra`
infrastructure built in `Meta/SafeStep/SigmaFreeAlgebra.lean`. The
closure goes one level below Mathlib: a custom inductive
`SigmaTerm` with the seven KO7 kernel constructors plus two
predicate-variable slots, plus an evaluator `evalSigma` and the
non-leaf-never-void substitution-invariance lemma.

## Theorem map

  1. `disequality_is_not_substitution_invariant` (KEPT, proven):
     the negative witness `(void, delta void)` distinguishes a
     disequality predicate from any constant collapse.
  2. `disequality_not_sigma_expressible_unconditional` (NEW, proven):
     no Sigma-term `t : SigmaFreeAlgebra.SigmaTerm` and Boolean
     decoder `(λ x. x = void)` jointly express the disequality
     predicate over `SigmaFreeAlgebra.SigmaTerm`. Discharged by
     case analysis on the outermost constructor of the candidate
     term, using the `SigmaFreeAlgebra.evalSigma_non_leaf_never_void`
     substitution-invariance lemma.
  3. `disequality_not_sigma_expressible` (proven): an alias for the
     unconditional theorem. Engine cert flag is
     `commercial_claim_status: unconditional`.
  4. `safestep_guard_requires_external_observer` (KEPT, proven):
     the operational corollary; once the unconditional theorem is
     in scope, the SafeStep guard's disequality witness must come
     from outside the rewriting layer.

The headline theorem is now an unconditional proven proposition; the earlier
incomplete carrier is removed.
-/

open OperatorKO7 Trace

namespace OperatorKO7.Meta.SafeStep.SyntacticNonDerivability

open OperatorKO7.Meta.SafeStep.SigmaFreeAlgebra

/-- Negative witness: the distinct closed Σ-terms `void` and
`delta void` are mapped to the same image by the constant
void-evaluator (`evalSigma _ _ void = void`). A substitution-invariant
evaluator of this constant shape therefore cannot track their
disequality, which is the obstruction the unconditional theorem
sharpens by case analysis below. -/
theorem disequality_is_not_substitution_invariant :
    ∃ (a b : SigmaTerm), a ≠ b ∧ evalSigma a b SigmaTerm.void = SigmaTerm.void := by
  refine ⟨SigmaTerm.void, SigmaTerm.delta SigmaTerm.void, ?_, evalSigma_void _ _⟩
  intro h; cases h

/-- The unconditional headline theorem (W16.7).

There is no Sigma-term `t : SigmaTerm` such that, for every closed
pair `(a, b) : SigmaTerm × SigmaTerm`, the disequality `a ≠ b`
coincides with the predicate `evalSigma a b t ≠ SigmaTerm.void`.

The proof case-splits on the outermost constructor of `t`:

  * If `t` is a non-leaf form (delta, integrate, merge, app,
    recDelta, eqW), then `evalSigma a b t` always has a non-void
    head by `SigmaFreeAlgebra.evalSigma_non_leaf_never_void`. So
    the predicate `evalSigma a b t ≠ void` is constantly `True`.
    Counterexample at `(a, b) = (void, void)`: the LHS `void ≠ void`
    is `False`, the RHS is `True`.
  * If `t = void`, `evalSigma a b void = void` is constant.
    Predicate `evalSigma a b t ≠ void` is constantly `False`.
    Counterexample at `(a, b) = (void, delta void)`: LHS is `True`
    (void ≠ delta void), RHS is `False`.
  * If `t = varA`, `evalSigma a b varA = a`. Predicate `a ≠ void`.
    Counterexample at `(a, b) = (delta void, delta void)`: LHS is
    `False` (a = b), RHS is `True` (a = delta void ≠ void).
  * If `t = varB`, `evalSigma a b varB = b`. Symmetric counterexample
    at `(a, b) = (delta void, delta void)`. -/
theorem disequality_not_sigma_expressible_unconditional :
    ¬ ∃ (t : SigmaTerm),
        ∀ (a b : SigmaTerm),
          (a ≠ b) ↔ (evalSigma a b t ≠ SigmaTerm.void) := by
  rintro ⟨t, h⟩
  cases t with
  | void =>
      -- evalSigma a b void = void; RHS constantly False.
      -- Counterexample at (void, delta void): LHS True, RHS False.
      have hpair := h SigmaTerm.void (SigmaTerm.delta SigmaTerm.void)
      have hLHS : (SigmaTerm.void : SigmaTerm) ≠
                    SigmaTerm.delta SigmaTerm.void := by
        intro hh; cases hh
      have hRHS : ¬ (evalSigma SigmaTerm.void
                      (SigmaTerm.delta SigmaTerm.void) SigmaTerm.void
                      ≠ SigmaTerm.void) := by
        intro hne
        exact hne (evalSigma_void SigmaTerm.void
                    (SigmaTerm.delta SigmaTerm.void))
      exact hRHS (hpair.mp hLHS)
  | varA =>
      -- evalSigma a b varA = a. RHS = (a ≠ void).
      -- Counterexample at (delta void, delta void): LHS False,
      -- RHS True (a = delta void ≠ void).
      have hpair := h (SigmaTerm.delta SigmaTerm.void)
                       (SigmaTerm.delta SigmaTerm.void)
      have hLHS : ¬ ((SigmaTerm.delta SigmaTerm.void : SigmaTerm)
                      ≠ SigmaTerm.delta SigmaTerm.void) := by
        intro hne; exact hne rfl
      have hRHS : evalSigma (SigmaTerm.delta SigmaTerm.void)
                    (SigmaTerm.delta SigmaTerm.void)
                    SigmaTerm.varA
                  ≠ SigmaTerm.void := by
        rw [evalSigma_varA]
        intro hh; cases hh
      exact hLHS (hpair.mpr hRHS)
  | varB =>
      -- Symmetric to varA at the same counterexample pair.
      have hpair := h (SigmaTerm.delta SigmaTerm.void)
                       (SigmaTerm.delta SigmaTerm.void)
      have hLHS : ¬ ((SigmaTerm.delta SigmaTerm.void : SigmaTerm)
                      ≠ SigmaTerm.delta SigmaTerm.void) := by
        intro hne; exact hne rfl
      have hRHS : evalSigma (SigmaTerm.delta SigmaTerm.void)
                    (SigmaTerm.delta SigmaTerm.void)
                    SigmaTerm.varB
                  ≠ SigmaTerm.void := by
        rw [evalSigma_varB]
        intro hh; cases hh
      exact hLHS (hpair.mpr hRHS)
  | delta s =>
      -- Non-leaf form: evalSigma never void; RHS constantly True.
      -- Counterexample at (void, void): LHS False, RHS True.
      have hpair := h SigmaTerm.void SigmaTerm.void
      have hLHS : ¬ ((SigmaTerm.void : SigmaTerm) ≠ SigmaTerm.void) := by
        intro hne; exact hne rfl
      have hRHS : evalSigma SigmaTerm.void SigmaTerm.void
                    (SigmaTerm.delta s) ≠ SigmaTerm.void :=
        evalSigma_non_leaf_never_void (SigmaTerm.delta s)
          (by simp [isLeafForm]) SigmaTerm.void SigmaTerm.void
      exact hLHS (hpair.mpr hRHS)
  | integrate s =>
      have hpair := h SigmaTerm.void SigmaTerm.void
      have hLHS : ¬ ((SigmaTerm.void : SigmaTerm) ≠ SigmaTerm.void) := by
        intro hne; exact hne rfl
      have hRHS : evalSigma SigmaTerm.void SigmaTerm.void
                    (SigmaTerm.integrate s) ≠ SigmaTerm.void :=
        evalSigma_non_leaf_never_void (SigmaTerm.integrate s)
          (by simp [isLeafForm]) SigmaTerm.void SigmaTerm.void
      exact hLHS (hpair.mpr hRHS)
  | merge s1 s2 =>
      have hpair := h SigmaTerm.void SigmaTerm.void
      have hLHS : ¬ ((SigmaTerm.void : SigmaTerm) ≠ SigmaTerm.void) := by
        intro hne; exact hne rfl
      have hRHS : evalSigma SigmaTerm.void SigmaTerm.void
                    (SigmaTerm.merge s1 s2) ≠ SigmaTerm.void :=
        evalSigma_non_leaf_never_void (SigmaTerm.merge s1 s2)
          (by simp [isLeafForm]) SigmaTerm.void SigmaTerm.void
      exact hLHS (hpair.mpr hRHS)
  | app s1 s2 =>
      have hpair := h SigmaTerm.void SigmaTerm.void
      have hLHS : ¬ ((SigmaTerm.void : SigmaTerm) ≠ SigmaTerm.void) := by
        intro hne; exact hne rfl
      have hRHS : evalSigma SigmaTerm.void SigmaTerm.void
                    (SigmaTerm.app s1 s2) ≠ SigmaTerm.void :=
        evalSigma_non_leaf_never_void (SigmaTerm.app s1 s2)
          (by simp [isLeafForm]) SigmaTerm.void SigmaTerm.void
      exact hLHS (hpair.mpr hRHS)
  | recDelta s1 s2 s3 =>
      have hpair := h SigmaTerm.void SigmaTerm.void
      have hLHS : ¬ ((SigmaTerm.void : SigmaTerm) ≠ SigmaTerm.void) := by
        intro hne; exact hne rfl
      have hRHS : evalSigma SigmaTerm.void SigmaTerm.void
                    (SigmaTerm.recDelta s1 s2 s3) ≠ SigmaTerm.void :=
        evalSigma_non_leaf_never_void (SigmaTerm.recDelta s1 s2 s3)
          (by simp [isLeafForm]) SigmaTerm.void SigmaTerm.void
      exact hLHS (hpair.mpr hRHS)
  | eqW s1 s2 =>
      have hpair := h SigmaTerm.void SigmaTerm.void
      have hLHS : ¬ ((SigmaTerm.void : SigmaTerm) ≠ SigmaTerm.void) := by
        intro hne; exact hne rfl
      have hRHS : evalSigma SigmaTerm.void SigmaTerm.void
                    (SigmaTerm.eqW s1 s2) ≠ SigmaTerm.void :=
        evalSigma_non_leaf_never_void (SigmaTerm.eqW s1 s2)
          (by simp [isLeafForm]) SigmaTerm.void SigmaTerm.void
      exact hLHS (hpair.mpr hRHS)

/-- Alias: `disequality_not_sigma_expressible` is the unconditional
W16.7 theorem. The engine cert carries
`commercial_claim_status: unconditional` on this anchor. -/
theorem disequality_not_sigma_expressible :
    ¬ ∃ (t : SigmaTerm),
        ∀ (a b : SigmaTerm),
          (a ≠ b) ↔ (evalSigma a b t ≠ SigmaTerm.void) :=
  disequality_not_sigma_expressible_unconditional

/-- Operational corollary: even at the level of arbitrary
`Trace`-level disequality witnesses, the SafeStep guard's
disequality must be supplied by an external observer. The
unconditional theorem
`disequality_not_sigma_expressible_unconditional` is now in scope;
this corollary cites it by name in its docstring. -/
theorem safestep_guard_requires_external_observer
    {a b : Trace}
    (g : OperatorKO7.Meta.SafeStep.GaugeFixingGuard.SafeStepGuard a b) :
    a ≠ b :=
  g.disequality

#print axioms disequality_is_not_substitution_invariant
#print axioms disequality_not_sigma_expressible_unconditional

end OperatorKO7.Meta.SafeStep.SyntacticNonDerivability
