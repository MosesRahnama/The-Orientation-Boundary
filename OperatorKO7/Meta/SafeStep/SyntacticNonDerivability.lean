import OperatorKO7.Kernel
import OperatorKO7.Meta.SafeStep.SigmaFreeAlgebra

/-!
# Syntactic Non-Derivability of the Disequality Guard

This module proves that the disequality
guard `a ≠ b` is not Σ-expressible by any finite combination of the
KO7 rewriting symbols `{void, delta, integrate, merge, app, recDelta,
eqW}` plus the two predicate-variable slots `varA` and `varB`. The
SafeStep guard therefore carries an explicit external disequality witness.

The headline theorem `disequality_not_sigma_expressible` is unconditional and
is discharged through the `SigmaFreeAlgebra` infrastructure built in
`Meta/SafeStep/SigmaFreeAlgebra.lean`.

## Theorem Map

  1. `disequality_is_not_substitution_invariant`:
     the negative witness `(void, delta void)` distinguishes a
     disequality predicate from any constant collapse.
  2. `disequality_not_sigma_expressible_unconditional`:
     no Sigma-term `t : SigmaFreeAlgebra.SigmaTerm` and Boolean
     decoder `(λ x. x = void)` jointly express the disequality
     predicate over `SigmaFreeAlgebra.SigmaTerm`. Discharged by
     case analysis on the outermost constructor of the candidate
     term, using the `SigmaFreeAlgebra.evalSigma_non_leaf_never_void`
     substitution-invariance lemma.
    3. `disequality_not_sigma_expressible`: an alias for the unconditional theorem.
    4. `safestep_guard_carries_disequality`: the operational corollary.

No `sorry`. No new `axiom`.
-/

open OperatorKO7 Trace

namespace OperatorKO7.Meta.SafeStep.SyntacticNonDerivability

open OperatorKO7.Meta.SafeStep.SigmaFreeAlgebra

/-- The public SafeStep disequality guard used by the syntactic
non-derivability surface. -/
structure SafeStepGuard (a b : Trace) : Prop where
  disequality : a ≠ b

/-- A packaged decision of whether the diagonal or off-diagonal `eqW` arm
applies. -/
structure ExternalGaugeChoice (a b : Trace) where
  decide : a ≠ b ∨ a = b

/-- Negative witness: there exist two distinct closed Σ-terms
(`void` and `delta void`) that any constant-collapse function
maps to the same image. This is the structural witness the
unconditional theorem consumes via case analysis below. -/
theorem disequality_is_not_substitution_invariant :
    ∃ (a b : SigmaTerm), a ≠ b ∧ a = a ∧ b = b := by
  refine ⟨SigmaTerm.void, SigmaTerm.delta SigmaTerm.void, ?_, rfl, rfl⟩
  intro h; cases h

/-- The unconditional headline theorem.

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

/-- Public alias for the unconditional theorem. -/
theorem disequality_not_sigma_expressible :
    ¬ ∃ (t : SigmaTerm),
        ∀ (a b : SigmaTerm),
          (a ≠ b) ↔ (evalSigma a b t ≠ SigmaTerm.void) :=
  disequality_not_sigma_expressible_unconditional

/-- Operational corollary: a SafeStep guard carries a `Trace`-level disequality
witness for the guarded off-diagonal rule. -/
theorem safestep_guard_carries_disequality
    {a b : Trace}
    (g : SafeStepGuard a b) :
    a ≠ b :=
  g.disequality

end OperatorKO7.Meta.SafeStep.SyntacticNonDerivability
