import OperatorKO7.Meta.ReverseMath.RCA0
import OperatorKO7.Meta.ReverseMath.ArtsGieslPi02
import OperatorKO7.Meta.ReverseMath.DeductionH
import OperatorKO7.Meta.ReverseMath.ArtsGieslProduct
import Mathlib.Tactic.FinCases

/-!
# Syntactic derivation of the predecessor-descent sentence

This module constructs `DerivableFO rca0BasicAxioms ArtsGieslSctSoundnessFormula` in the
`DeductionFO` and `DeductionH` calculi. Despite the historical identifier, the formula is the
elementary predecessor-descent sentence

`∀x∃y, ¬IsSet x → (¬IsSet y ∧ (y < x ∨ x = 0))`,

not an encoding of Arts-Giesl dependency-pair soundness or size-change termination soundness.

## The derivation

After `all_intro` (generalize `x`), the level-1 goal `∃y, sctMatrix` is proved by case analysis on
`IsSet x` (excluded middle):

* `IsSet x` (`lemmaA`): witness `y := x`; the guard `¬IsSet x` contradicts `IsSet x`, so the matrix
  holds by ex falso.
* `¬IsSet x`: specialize `axZeroOrSucc` at `x` to get `x = 0 ∨ ∃z(¬IsSet z ∧ x = S z ∧ z < x)`, then:
  * `x = 0` (`lemmaB`): witness `y := x`; the descent disjunct `x = 0` holds.
  * `∃z …` (`lemmaC`): `ex_mono` maps the predecessor witness `z` to `y`; `z < x` gives the descent
    disjunct directly (this is why `axZeroOrSucc` packages `z < x`, avoiding `eq_leibniz`).

`instTop_self_sctMatrix` is the witness-instantiation conversion `sctMatrix[y := x]` used by the two
branches that select `x` as the existential witness.
-/

set_option autoImplicit false

namespace OperatorKO7.ReverseMath

open FirstOrder Language OperatorKO7.ReverseMath.DeductionFO OperatorKO7.ReverseMath.DeductionH

/-! ### Witness-instantiation conversion (`sctMatrix[y := x]`) -/

/-- Pushing `substAll` through the quantifier-free connectives of `sctMatrix` is definitional;
only the atom-level term substitutions remain. -/
private theorem substAll_sctMatrix (σ : Fin 2 → L2.Term (Empty ⊕ Fin 1)) :
    Substitution.substAll σ sctMatrix =
      (∼ (Substitution.substAll σ (isSetBd (&0)))) ⟹
        ((∼ (Substitution.substAll σ (isSetBd (&1)))) ⊓
          ((Substitution.substAll σ (ltBd (&1) (&0))) ⊔
            (Substitution.substAll σ (Term.bdEqual (&0) zeroTerm)))) :=
  rfl

/-- The instantiation substitution `σ₀ = [&0, &0]` used to set `y := x` in `sctMatrix`. -/
private def σ₀ : Fin 2 → L2.Term (Empty ⊕ Fin 1) :=
  Fin.snoc (fun i : Fin 1 => Term.var (Sum.inr i)) (&0)

private theorem σ₀_eval (j : Fin 2) : σ₀ j = Term.var (Sum.inr 0) := by
  fin_cases j <;> simp [σ₀, Fin.snoc]

/-- Instantiating the inner (`∃`) variable `y = &1` of `sctMatrix` with the outer variable `x = &0`
yields the explicit self-witness matrix. -/
theorem instTop_self_sctMatrix :
    Substitution.instantiateTop (&0 : L2.Term (Empty ⊕ Fin 1)) sctMatrix =
      ((∼ (isSetBd (&0))) ⟹ ((∼ (isSetBd (&0))) ⊓
        (ltBd (&0) (&0) ⊔ Term.bdEqual (&0) zeroTerm))) := by
  have a0 : Substitution.substAll σ₀ (isSetBd (&0)) = isSetBd (&0) := by
    simp only [isSetBd, Substitution.substAll, Relations.boundedFormula₁, Relations.boundedFormula]
    congr 1
    funext i
    fin_cases i
    simp [Term.subst, σ₀_eval]
  have a1 : Substitution.substAll σ₀ (isSetBd (&1)) = isSetBd (&0) := by
    simp only [isSetBd, Substitution.substAll, Relations.boundedFormula₁, Relations.boundedFormula]
    congr 1
    funext i
    fin_cases i
    simp [Term.subst, σ₀_eval]
  have a2 : Substitution.substAll σ₀ (ltBd (&1) (&0)) = ltBd (&0) (&0) := by
    simp only [ltBd, Substitution.substAll, Relations.boundedFormula₂, Relations.boundedFormula]
    congr 1
    funext i
    fin_cases i <;> simp [Term.subst, σ₀_eval]
  have t1 : Term.subst (&0 : L2.Term (Empty ⊕ Fin 2)) (Sum.elim (fun e : Empty => e.elim) σ₀)
      = (&0 : L2.Term (Empty ⊕ Fin 1)) := by
    simp [Term.subst, σ₀_eval]
  have t2 : Term.subst (zeroTerm : L2.Term (Empty ⊕ Fin 2)) (Sum.elim (fun e : Empty => e.elim) σ₀)
      = (zeroTerm : L2.Term (Empty ⊕ Fin 1)) := by
    simp [zeroTerm, Constants.term, Term.subst, Matrix.empty_eq]
  have a3 : Substitution.substAll σ₀ (Term.bdEqual (&0) zeroTerm) = Term.bdEqual (&0) zeroTerm := by
    simp only [Term.bdEqual, Substitution.substAll, t1, t2]
  rw [Substitution.instantiateTop]
  show Substitution.substAll σ₀ sctMatrix = _
  rw [substAll_sctMatrix, a0, a1, a2, a3]

/-! ### Branch fragments of `axZeroOrSucc` -/

/-- The predecessor-existential body of `axZeroOrSucc` (level 2, `x = &0`, `z = &1`):
`¬IsSet z ∧ (x = S z ∧ z < x)`. -/
private def zosSucc : L2.BoundedFormula Empty 2 :=
  (∼ (isSetBd (&1))) ⊓ ((Term.bdEqual (&0) (succTerm (&1))) ⊓ (ltBd (&1) (&0)))

/-- The body of `axZeroOrSucc` after the leading `∀` (level 1, `x = &0`):
`¬IsSet x → (x = 0 ∨ ∃z, ¬IsSet z ∧ x = S z ∧ z < x)`. -/
private def zosBody : L2.BoundedFormula Empty 1 :=
  (∼ (isSetBd (&0))) ⟹ ((Term.bdEqual (&0) zeroTerm) ⊔ ∃' zosSucc)

/-! ### The three branch lemmas (closed implications into `∃y, sctMatrix`) -/

/-- Ex falso from a hypothesis and its negation (under a context). -/
private theorem contra {n : ℕ} {Γ : List (L2.BoundedFormula Empty n)}
    {A C : L2.BoundedFormula Empty n} (hA : DerivableH rca0BasicAxioms Γ A)
    (hnA : DerivableH rca0BasicAxioms Γ A.not) : DerivableH rca0BasicAxioms Γ C := by
  have h : DerivableH rca0BasicAxioms Γ (A.imp ⊥) := hnA
  exact falsum_elim_H (mp_H h hA)

/-- **`IsSet x` branch.** With witness `y := x`, the guard `¬IsSet x` contradicts `IsSet x`, so the
matrix holds by ex falso. -/
private theorem lemmaA :
    DerivableFO rca0BasicAxioms ((isSetBd (&0)) ⟹ (∃' sctMatrix)) := by
  show DerivableH rca0BasicAxioms [] ((isSetBd (&0)) ⟹ (∃' sctMatrix))
  apply deduction
  apply ex_intro_H (&0 : L2.Term (Empty ⊕ Fin 1))
  rw [instTop_self_sctMatrix]
  apply deduction
  exact contra (weaken (assume_last [] (isSetBd (&0))))
    (assume_last [isSetBd (&0)] ((isSetBd (&0)).not))

/-- **`x = 0` branch.** With witness `y := x`, the descent disjunct `x = 0` holds. -/
private theorem lemmaB :
    DerivableFO rca0BasicAxioms ((Term.bdEqual (&0) zeroTerm) ⟹ (∃' sctMatrix)) := by
  show DerivableH rca0BasicAxioms [] ((Term.bdEqual (&0) zeroTerm) ⟹ (∃' sctMatrix))
  apply deduction
  apply ex_intro_H (&0 : L2.Term (Empty ⊕ Fin 1))
  rw [instTop_self_sctMatrix]
  apply deduction
  refine and_intro_H ?_ ?_
  · exact assume_last [Term.bdEqual (&0) zeroTerm] ((isSetBd (&0)).not)
  · apply or_inr_H
    exact weaken (assume_last [] (Term.bdEqual (&0) zeroTerm))

/-- **`∃z` branch.** `ex_mono` maps the predecessor witness `z` to the existential witness `y`; the
packaged `z < x` gives the descent disjunct directly. -/
private theorem lemmaC :
    DerivableFO rca0BasicAxioms ((∃' zosSucc) ⟹ (∃' sctMatrix)) := by
  apply DerivableFO.ex_mono
  apply DerivableFO.all_intro
  show DerivableH rca0BasicAxioms [] (zosSucc.imp sctMatrix)
  apply deduction
  apply deduction
  have hP : DerivableH rca0BasicAxioms [zosSucc, (isSetBd (&0)).not] zosSucc :=
    weaken (assume_last [] zosSucc)
  exact and_intro_H (and_left_H hP) (or_inl_H (and_right_H (and_right_H hP)))

/-! ### The object derivation -/

/-- `rca0BasicAxioms` syntactically derives the predecessor-descent sentence in the `DeductionFO`
calculus. -/
theorem artsGiesl_syntactic_upper :
    DerivableFO rca0BasicAxioms ArtsGieslSctSoundnessFormula := by
  apply DerivableFO.all_intro
  show DerivableH rca0BasicAxioms [] (∃' sctMatrix)
  refine or_elim_H (em_H (isSetBd (&0))) ?_ ?_
  · exact mp_H (ofClosed lemmaA) (assume_last [] (isSetBd (&0)))
  · have hZOSbody : DerivableFO rca0BasicAxioms zosBody :=
      DerivableFO.all_elim (φ := zosBody)
        (DerivableFO.hyp (show axZeroOrSucc ∈ rca0BasicAxioms by simp [rca0BasicAxioms]))
    have hdisj : DerivableH rca0BasicAxioms [(isSetBd (&0)).not]
        ((Term.bdEqual (&0) zeroTerm) ⊔ ∃' zosSucc) :=
      mp_H (ofClosed hZOSbody) (assume_last [] ((isSetBd (&0)).not))
    refine or_elim_H hdisj ?_ ?_
    · exact mp_H (ofClosed lemmaB)
        (assume_last [(isSetBd (&0)).not] (Term.bdEqual (&0) zeroTerm))
    · exact mp_H (ofClosed lemmaC)
        (assume_last [(isSetBd (&0)).not] (∃' zosSucc))

/-- Specialization of `ArtsGieslOmega3ProductTheorem` at `rca0BasicAxioms`, using the syntactic
predecessor-descent derivation for its `upper` field. The product record does not establish an SCT
reversal or identify the predecessor sentence with dependency-pair soundness. -/
theorem artsGieslOmega3Product_rca0 :
    ArtsGieslOmega3ProductTheorem rca0BasicAxioms :=
  artsGieslOmega3Product_of_upper rca0BasicAxioms artsGiesl_syntactic_upper

#print axioms artsGiesl_syntactic_upper
#print axioms artsGieslOmega3Product_rca0

end OperatorKO7.ReverseMath
