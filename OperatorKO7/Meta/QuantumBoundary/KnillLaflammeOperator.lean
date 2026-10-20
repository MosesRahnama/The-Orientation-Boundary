import Mathlib

/-!
# Knill-Laflamme condition at the operator level (Blueprint §9)

The abstract correctable-vs-syndrome split is already mechanized
(`Meta/ReverseBridge/CorrectableNoiseSyndrome.lean`). This module promotes it to the **operator
level**: the genuine Knill-Laflamme condition `P Eₐᵀ E_b P = c_{ab} P` on concrete matrices, with both
regimes realized:

* a rank-one code with error set `{I, lowering}` satisfies KL with `c = I`, so the errors are
  correctable (no information leaks out of the code);
* on the full two-dimensional code, the projector error `F = |0⟩⟨0|` makes `P Fᵀ F P` non-scalar, so
  KL fails: an uncorrectable **syndrome**.

Worked over `ℝ` (where the conjugate transpose is the transpose); the structure is identical over `ℂ`.

## Audit slots
- Relation: concrete finite operator algebra (not a rewriting relation).
- Closure: `propext`, `Classical.choice`, `Quot.sound`.
- Trust: no `sorry`/`axiom`/`native_decide`; concrete matrix identities.
- Scope: the KL *condition* and its two regimes; NOT the full KL recovery-channel existence theorem.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.QuantumBoundary.KnillLaflamme

open Matrix

/-- 2x2 real matrices (the smallest setting carrying both a correctable code and a syndrome). -/
abbrev M := Matrix (Fin 2) (Fin 2) ℝ

/-- The rank-one code projector onto `|0⟩`. -/
def P : M := !![1, 0; 0, 0]

/-- The correctable error set: no-error `I` and the lowering operator `|0⟩⟨1|`. -/
def E : Fin 2 → M := ![1, !![0, 0; 1, 0]]

@[simp] theorem E_apply_zero : E 0 = 1 := rfl
@[simp] theorem E_apply_one : E 1 = !![0, 0; 1, 0] := rfl

/-- The Knill-Laflamme condition for a code projector `Pc`, error set `Es`, and scalar matrix `c`:
`Pc Esₐᵀ Es_b Pc = c_{ab} Pc` for all `a, b`. -/
def KLCorrectable (Pc : M) (Es : Fin 2 → M) (c : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  ∀ a b, Pc * (Es a)ᵀ * Es b * Pc = c a b • Pc

/-- `P` is a projector. -/
theorem P_idempotent : P * P = P := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [P, Matrix.mul_apply, Fin.sum_univ_two]

/-- The lowering operator's transpose, as an explicit literal (so it can be rewritten away before any
entrywise computation). -/
theorem lowering_transpose : (!![0, 0; 1, 0] : M)ᵀ = !![0, 1; 0, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

/-- **Correctable regime:** the error set `{I, lowering}` satisfies Knill-Laflamme on the rank-one
code with `c = I`. The errors are correctable; no information about the code leaks. -/
theorem kl_holds : KLCorrectable P E (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  intro a b
  fin_cases a <;> fin_cases b <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp only [E, P, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.one_apply, Matrix.smul_apply] <;>
    norm_num

/-- **Syndrome regime:** on the full two-dimensional code (`P = I`), the projector error
`F = |0⟩⟨0|` gives `I Fᵀ F I = |0⟩⟨0|`, which is not a scalar multiple of `I`. Knill-Laflamme fails:
the error is an uncorrectable syndrome. -/
theorem kl_fails_syndrome :
    ¬ ∃ c : ℝ,
      (1 : M) * (!![1, 0; 0, 0] : M)ᵀ * (!![1, 0; 0, 0] : M) * (1 : M) = c • (1 : M) := by
  rintro ⟨c, hc⟩
  have h00 := congrFun (congrFun hc 0) 0
  have h11 := congrFun (congrFun hc 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, Matrix.smul_apply,
    Matrix.transpose_apply] at h00 h11
  -- h00 forces c = 1, h11 forces c = 0
  linarith

/-! ## Non-vacuity (both regimes are realized above) -/

/-- The two operator regimes coexist: the rank-one code is KL-correctable, while the full-space
projector error is a syndrome. -/
theorem kl_dichotomy_realized :
    KLCorrectable P E (1 : Matrix (Fin 2) (Fin 2) ℝ) ∧
      ¬ ∃ c : ℝ,
        (1 : M) * (!![1, 0; 0, 0] : M)ᵀ * (!![1, 0; 0, 0] : M) * (1 : M) = c • (1 : M) :=
  ⟨kl_holds, kl_fails_syndrome⟩

#print axioms P_idempotent
#print axioms kl_holds
#print axioms kl_fails_syndrome
#print axioms kl_dichotomy_realized

end OperatorKO7.Meta.QuantumBoundary.KnillLaflamme
