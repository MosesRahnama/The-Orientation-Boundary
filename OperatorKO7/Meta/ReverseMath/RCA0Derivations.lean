import OperatorKO7.Meta.ReverseMath.ArtsGieslUpperSyntactic

/-!
# U7.7: finite predecessor arithmetic and its exact induction strength

This module defines a finite number-relativized arithmetic base, bounded induction instances, and
theory translation.  It proves that one bounded zero-or-successor induction instance derives the
zero-or-successor axiom and hence the predecessor-descent sentence in every containing theory.
Sharp countermodels for stronger false extensions live in `RCA0DerivationSharpness`.
-/

set_option autoImplicit false

namespace OperatorKO7.ReverseMath

open FirstOrder Language
open OperatorKO7.ReverseMath.DeductionFO
open OperatorKO7.ReverseMath.DeductionH

/-! ### 7.7a Simpson's basic axioms, number-relativized -/

/-- `S` is injective on numbers: `∀x y, ¬IsSet x → ¬IsSet y → S x = S y → x = y`. -/
def axSuccInj : L2.Sentence :=
  ∀' ∀' ((∼ (isSetBd (&1))) ⟹ ((∼ (isSetBd (&0))) ⟹
    ((Term.bdEqual (succTerm (&1)) (succTerm (&0))) ⟹ (Term.bdEqual (&1) (&0)))))

/-- `∀x y, ¬IsSet x → ¬IsSet y → x + S y = S (x + y)`. -/
def axAddSucc : L2.Sentence :=
  ∀' ∀' ((∼ (isSetBd (&1))) ⟹ ((∼ (isSetBd (&0))) ⟹
    (Term.bdEqual (addTerm (&1) (succTerm (&0))) (succTerm (addTerm (&1) (&0))))))

/-- `∀x, ¬IsSet x → x · 0 = 0`. -/
def axMulZero : L2.Sentence :=
  ∀' ((∼ (isSetBd (&0))) ⟹ (Term.bdEqual (mulTerm (&0) zeroTerm) zeroTerm))

/-- `∀x y, ¬IsSet x → ¬IsSet y → x · S y = x · y + x`. -/
def axMulSucc : L2.Sentence :=
  ∀' ∀' ((∼ (isSetBd (&1))) ⟹ ((∼ (isSetBd (&0))) ⟹
    (Term.bdEqual (mulTerm (&1) (succTerm (&0))) (addTerm (mulTerm (&1) (&0)) (&1)))))

/-- `∀x, ¬IsSet x → ¬(x < 0)`. -/
def axNotLtZero : L2.Sentence :=
  ∀' ((∼ (isSetBd (&0))) ⟹ (∼ (ltBd (&0) zeroTerm)))

/-- `∀x y, ¬IsSet x → ¬IsSet y → (x < S y ↔ x < y ∨ x = y)`, written as the conjunction of the
two implications. -/
def axLtSuccIff : L2.Sentence :=
  ∀' ∀' ((∼ (isSetBd (&1))) ⟹ ((∼ (isSetBd (&0))) ⟹
    ((ltBd (&1) (succTerm (&0)) ⟹ (ltBd (&1) (&0) ⊔ Term.bdEqual (&1) (&0))) ⊓
      ((ltBd (&1) (&0) ⊔ Term.bdEqual (&1) (&0)) ⟹ ltBd (&1) (succTerm (&0))))))

/-- Simpson's basic arithmetic axioms of second-order arithmetic, number-relativized. -/
def rca0SimpsonBasic : L2.Theory :=
  {axSuccNeZero, axSuccInj, axAddZero, axAddSucc, axMulZero, axMulSucc, axNotLtZero, axLtSuccIff}

/-- Canonical name for the number-relativized fragment used below.  This finite theory is not
the full second-order system `RCA₀`: it contains neither comprehension nor an induction scheme. -/
def numberRelativizedSimpsonArithmetic : L2.Theory := rca0SimpsonBasic

/-! ### 7.7b Induction instances and bounded-quantifier formulas -/

/-- The induction instance for a formula with one free number variable:
`φ(0) ∧ (∀k, ¬IsSet k → φ(k) → φ(S k)) → ∀n, ¬IsSet n → φ(n)`.
The base and step premises are closed before the conclusion variable is introduced. -/
def IND (φ : L2.BoundedFormula Empty 1) : L2.Sentence :=
  ((Substitution.substAll (fun _ : Fin 1 => (zeroTerm : L2.Term (Empty ⊕ Fin 0))) φ) ⊓
    (∀' ((∼ (isSetBd (&0))) ⟹
      ((Substitution.substAll (fun _ : Fin 1 => (&0 : L2.Term (Empty ⊕ Fin 1))) φ) ⟹
        (Substitution.substAll
          (fun _ : Fin 1 => succTerm (&0 : L2.Term (Empty ⊕ Fin 1))) φ))))) ⟹
  (∀' ((∼ (isSetBd (&0))) ⟹
    (Substitution.substAll (fun _ : Fin 1 => (&0 : L2.Term (Empty ⊕ Fin 1))) φ)))

/-- Bounded-quantifier (Δ₀) formulas: atoms, implications, and number quantifiers whose bound is
an explicit `z < t` side condition. -/
inductive IsBoundedQ : {n : ℕ} → L2.BoundedFormula Empty n → Prop
  | falsum {n : ℕ} : IsBoundedQ (⊥ : L2.BoundedFormula Empty n)
  | equal {n : ℕ} (t₁ t₂ : L2.Term (Empty ⊕ Fin n)) : IsBoundedQ (Term.bdEqual t₁ t₂)
  | rel {n l : ℕ} (R : L2.Relations l) (ts : Fin l → L2.Term (Empty ⊕ Fin n)) :
      IsBoundedQ (BoundedFormula.rel R ts)
  | imp {n : ℕ} {A B : L2.BoundedFormula Empty n} :
      IsBoundedQ A → IsBoundedQ B → IsBoundedQ (A.imp B)
  | ex_bounded {n : ℕ} {A : L2.BoundedFormula Empty (n + 1)} {t : L2.Term (Empty ⊕ Fin n)}
      (h : IsBoundedQ A) :
      IsBoundedQ (∃' ((ltBd (Term.var (Sum.inr (Fin.last n))) (t.liftAt 1 n)) ⊓ A))

namespace IsBoundedQ

theorem not {n : ℕ} {A : L2.BoundedFormula Empty n} (h : IsBoundedQ A) : IsBoundedQ (∼A) :=
  h.imp .falsum

theorem inf {n : ℕ} {A B : L2.BoundedFormula Empty n} (hA : IsBoundedQ A) (hB : IsBoundedQ B) :
    IsBoundedQ (A ⊓ B) :=
  (hA.imp hB.not).not

theorem sup {n : ℕ} {A B : L2.BoundedFormula Empty n} (hA : IsBoundedQ A) (hB : IsBoundedQ B) :
    IsBoundedQ (A ⊔ B) :=
  (hA.not).imp hB

theorem iff {n : ℕ} {A B : L2.BoundedFormula Empty n} (hA : IsBoundedQ A) (hB : IsBoundedQ B) :
    IsBoundedQ (A ⇔ B) :=
  (hA.imp hB).inf (hB.imp hA)

end IsBoundedQ

/-- The bounded predecessor certificate used by zero-or-successor induction.  At level two, `&0`
is the outer number and `&1` is the existentially bound predecessor. -/
def boundedZeroOrSuccPredecessorBody : L2.BoundedFormula Empty 2 :=
  (ltBd (&1) (&0)) ⊓ ((∼ (isSetBd (&1))) ⊓
    ((Term.bdEqual (&0) (succTerm (&1))) ⊓ (ltBd (&1) (&0))))

/-- The induction formula for the zero-or-successor dichotomy, in the bounded-existential shape. -/
def indFormulaZeroOrSucc : L2.BoundedFormula Empty 1 :=
  (Term.bdEqual (&0) zeroTerm) ⊔ ∃' boundedZeroOrSuccPredecessorBody

/-- The induction formula for irreflexivity of `<`. -/
def indFormulaLtIrrefl : L2.BoundedFormula Empty 1 :=
  ∼ (ltBd (&0) (&0))

theorem isBoundedQ_indFormulaZeroOrSucc : IsBoundedQ indFormulaZeroOrSucc := by
  unfold indFormulaZeroOrSucc
  refine IsBoundedQ.sup (IsBoundedQ.equal _ _) ?_
  refine IsBoundedQ.ex_bounded (t := (&0 : L2.Term (Empty ⊕ Fin 1))) ?_
  exact (((IsBoundedQ.rel Rel.isSet ![&1]).not).inf
    (((IsBoundedQ.equal (&0) (succTerm (&1))).inf (IsBoundedQ.rel Rel.lt ![&1, &0]))))

theorem isBoundedQ_indFormulaLtIrrefl : IsBoundedQ indFormulaLtIrrefl := by
  unfold indFormulaLtIrrefl
  exact (IsBoundedQ.rel Rel.lt ![&0, &0]).not

/-! ### The successor-order consequence of the base theory -/

private def axLtSuccIffMatrix : L2.BoundedFormula Empty 2 :=
  ((∼ (isSetBd (&1))) ⟹ ((∼ (isSetBd (&0))) ⟹
    ((ltBd (&1) (succTerm (&0)) ⟹ (ltBd (&1) (&0) ⊔ Term.bdEqual (&1) (&0))) ⊓
      ((ltBd (&1) (&0) ⊔ Term.bdEqual (&1) (&0)) ⟹ ltBd (&1) (succTerm (&0))))))

private theorem axLtSuccIff_eq : axLtSuccIff = ∀' ∀' axLtSuccIffMatrix := rfl

private def selfLtSuccPair : L2.BoundedFormula Empty 1 :=
  ((ltBd (&0) (succTerm (&0)) ⟹ (ltBd (&0) (&0) ⊔ Term.bdEqual (&0) (&0))) ⊓
    ((ltBd (&0) (&0) ⊔ Term.bdEqual (&0) (&0)) ⟹ ltBd (&0) (succTerm (&0))))

private def selfIffSubst : Fin 2 → L2.Term (Empty ⊕ Fin 1) :=
  Fin.snoc (fun i : Fin 1 => Term.var (Sum.inr i)) (&0)

private theorem selfIffSubst_eval (j : Fin 2) :
    selfIffSubst j = (&0 : L2.Term (Empty ⊕ Fin 1)) := by
  fin_cases j <;> simp [selfIffSubst, Fin.snoc]

private theorem substAll_axLtSuccIffMatrix
    (σ : Fin 2 → L2.Term (Empty ⊕ Fin 1)) :
    Substitution.substAll σ axLtSuccIffMatrix =
      ((∼ (Substitution.substAll σ (isSetBd (&1)))) ⟹
        ((∼ (Substitution.substAll σ (isSetBd (&0)))) ⟹
          ((Substitution.substAll σ (ltBd (&1) (succTerm (&0))) ⟹
              (Substitution.substAll σ (ltBd (&1) (&0)) ⊔
                Substitution.substAll σ (Term.bdEqual (&1) (&0)))) ⊓
            ((Substitution.substAll σ (ltBd (&1) (&0)) ⊔
                Substitution.substAll σ (Term.bdEqual (&1) (&0))) ⟹
              Substitution.substAll σ (ltBd (&1) (succTerm (&0))))))) := rfl

private theorem instantiateTop_self_axLtSuccIffMatrix :
    Substitution.instantiateTop (&0 : L2.Term (Empty ⊕ Fin 1)) axLtSuccIffMatrix =
      ((∼ (isSetBd (&0))) ⟹ ((∼ (isSetBd (&0))) ⟹ selfLtSuccPair)) := by
  have hSet0 : Substitution.substAll selfIffSubst (isSetBd (&0)) = isSetBd (&0) := by
    simp only [isSetBd, Substitution.substAll, Relations.boundedFormula₁,
      Relations.boundedFormula]
    congr 1
    funext i
    fin_cases i
    simp [Term.subst, selfIffSubst_eval]
  have hSet1 : Substitution.substAll selfIffSubst (isSetBd (&1)) = isSetBd (&0) := by
    simp only [isSetBd, Substitution.substAll, Relations.boundedFormula₁,
      Relations.boundedFormula]
    congr 1
    funext i
    fin_cases i
    simp [Term.subst, selfIffSubst_eval]
  have hSuccTerm :
      (succTerm (&0 : L2.Term (Empty ⊕ Fin 2))).subst
          (Sum.elim (fun e : Empty => e.elim) selfIffSubst) =
        succTerm (&0 : L2.Term (Empty ⊕ Fin 1)) := by
    simp only [succTerm, Functions.apply₁, Term.subst]
    congr 1
    funext i
    fin_cases i
    simp [selfIffSubst_eval]
  have hLtSucc :
      Substitution.substAll selfIffSubst (ltBd (&1) (succTerm (&0))) =
        ltBd (&0) (succTerm (&0)) := by
    simp only [ltBd, Substitution.substAll, Relations.boundedFormula₂,
      Relations.boundedFormula]
    congr 1
    funext i
    fin_cases i
    · simp [Term.subst, selfIffSubst_eval]
    · exact hSuccTerm
  have hLt : Substitution.substAll selfIffSubst (ltBd (&1) (&0)) = ltBd (&0) (&0) := by
    simp only [ltBd, Substitution.substAll, Relations.boundedFormula₂,
      Relations.boundedFormula]
    congr 1
    funext i
    fin_cases i <;> simp [Term.subst, selfIffSubst_eval]
  have hEq : Substitution.substAll selfIffSubst (Term.bdEqual (&1) (&0)) =
      Term.bdEqual (&0) (&0) := by
    simp only [Term.bdEqual, Substitution.substAll]
    congr 1
  rw [Substitution.instantiateTop]
  change Substitution.substAll selfIffSubst axLtSuccIffMatrix = _
  rw [substAll_axLtSuccIffMatrix, hSet1, hSet0, hLtSucc, hLt, hEq]
  rfl

/-- The number-relativized Simpson arithmetic base derives `x < S x` without induction. -/
theorem simpsonArithmetic_derives_axLtSucc : DerivableFO rca0SimpsonBasic axLtSucc := by
  rw [axLtSucc]
  apply DerivableFO.all_intro
  show OperatorKO7.ReverseMath.DeductionH.DerivableH rca0SimpsonBasic []
    ((∼ (isSetBd (&0))) ⟹ ltBd (&0) (succTerm (&0)))
  apply OperatorKO7.ReverseMath.DeductionH.deduction
  have hAx : DerivableFO rca0SimpsonBasic (∀' ∀' axLtSuccIffMatrix) := by
    rw [← axLtSuccIff_eq]
    exact DerivableFO.hyp
      (show axLtSuccIff ∈ rca0SimpsonBasic by simp [rca0SimpsonBasic])
  have hOpen : DerivableFO rca0SimpsonBasic (∀' axLtSuccIffMatrix) :=
    DerivableFO.all_elim hAx
  have hSelf := DerivableFO.spec (&0 : L2.Term (Empty ⊕ Fin 1)) hOpen
  rw [instantiateTop_self_axLtSuccIffMatrix] at hSelf
  have hPair : OperatorKO7.ReverseMath.DeductionH.DerivableH rca0SimpsonBasic
      [(isSetBd (&0)).not]
      selfLtSuccPair := by
    exact OperatorKO7.ReverseMath.DeductionH.mp_H
      (OperatorKO7.ReverseMath.DeductionH.mp_H
        (OperatorKO7.ReverseMath.DeductionH.ofClosed hSelf)
        (OperatorKO7.ReverseMath.DeductionH.assume_last [] ((isSetBd (&0)).not)))
      (OperatorKO7.ReverseMath.DeductionH.assume_last [] ((isSetBd (&0)).not))
  apply OperatorKO7.ReverseMath.DeductionH.mp_H
    (OperatorKO7.ReverseMath.DeductionH.and_right_H hPair)
  apply OperatorKO7.ReverseMath.DeductionH.or_inr_H
  exact OperatorKO7.ReverseMath.DeductionH.ofClosed
    (DerivableFO.eq_refl (&0 : L2.Term (Empty ⊕ Fin 1)))

/-! ### 7.7d The cut lemma -/

/-- **Theory-translation cut.** If every axiom of `T₁` is derivable in `T₂`, every sentence
derivable in `T₁` is derivable in `T₂`. -/
theorem derivableFO_of_subtheory {T₁ T₂ : L2.Theory}
    (h : ∀ φ ∈ T₁, DerivableFO T₂ φ) :
    ∀ {n : ℕ} {φ : L2.BoundedFormula Empty n}, DerivableFO T₁ φ → DerivableFO T₂ φ := by
  intro n φ hd
  induction hd with
  | hyp hmem => exact h _ hmem
  | mp _ _ ih₁ ih₂ => exact .mp ih₁ ih₂
  | ax_k φ ψ => exact .ax_k φ ψ
  | ax_s φ ψ χ => exact .ax_s φ ψ χ
  | ax_dne φ => exact .ax_dne φ
  | all_intro _ ih => exact .all_intro ih
  | all_elim _ ih => exact .all_elim ih
  | freeVarWeakening _ ih => exact .freeVarWeakening ih
  | spec t _ ih => exact .spec t ih
  | ex_intro t _ ih => exact .ex_intro t ih
  | eq_refl t => exact .eq_refl t
  | eq_leibniz ψ s t => exact .eq_leibniz ψ s t
  | or_inl A B => exact .or_inl A B
  | or_inr A B => exact .or_inr A B
  | or_elim A B C => exact .or_elim A B C
  | and_intro A B => exact .and_intro A B
  | and_left A B => exact .and_left A B
  | and_right A B => exact .and_right A B
  | falsum_elim A => exact .falsum_elim A
  | em A => exact .em A
  | ex_elim h₁ h₂ ih₁ ih₂ => exact .ex_elim ih₁ ih₂
  | ax_ex_intro t => exact .ax_ex_intro t
  | ax_ex_elim P C => exact .ax_ex_elim P C
  | ex_mono _ ih => exact .ex_mono ih

/-! ### One bounded induction instance suffices -/

/-- Simpson arithmetic plus the single bounded zero-or-successor induction instance. -/
def zeroOrSuccInductionFragment : L2.Theory :=
  rca0SimpsonBasic ∪ {IND indFormulaZeroOrSucc}

/-- The base arithmetic consequences persist in the one-instance extension. -/
theorem zeroOrSuccInductionFragment_derives_axLtSucc :
    DerivableFO zeroOrSuccInductionFragment axLtSucc := by
  exact derivableFO_of_subtheory
    (fun φ hφ => DerivableFO.hyp (by simp [zeroOrSuccInductionFragment, hφ]))
    simpsonArithmetic_derives_axLtSucc

private theorem subst_zeroTerm {n m : ℕ} (σ : Fin n → L2.Term (Empty ⊕ Fin m)) :
    (zeroTerm : L2.Term (Empty ⊕ Fin n)).subst
        (Sum.elim (fun e : Empty => e.elim) σ) = zeroTerm := by
  simp only [zeroTerm, Constants.term, Term.subst]
  congr 1
  funext i
  exact Fin.elim0 i

private theorem subst_succ_var {n m : ℕ} (σ : Fin n → L2.Term (Empty ⊕ Fin m))
    (j : Fin n) :
    (succTerm (&j : L2.Term (Empty ⊕ Fin n))).subst
        (Sum.elim (fun e : Empty => e.elim) σ) = succTerm (σ j) := by
  simp only [succTerm, Functions.apply₁, Term.subst]
  congr 1
  funext i
  fin_cases i
  rfl

private theorem subst_succTerm {α β : Type} (t : L2.Term α) (σ : α → L2.Term β) :
    (succTerm t).subst σ = succTerm (t.subst σ) := by
  unfold succTerm Functions.apply₁
  simp only [Term.subst]
  congr 1
  funext i
  fin_cases i
  rfl

private theorem succ_function_eta {n : ℕ} (t : L2.Term (Empty ⊕ Fin n)) :
    Term.func succSym (fun _ : Fin 1 => t) = succTerm t := by
  unfold succTerm Functions.apply₁
  congr 1
  funext i
  fin_cases i
  rfl

private theorem lift_zeroTerm_to_one :
    (zeroTerm : L2.Term (Empty ⊕ Fin 0)).liftAt 1 0 =
      (zeroTerm : L2.Term (Empty ⊕ Fin 1)) := by
  simp only [zeroTerm, Constants.term, Term.liftAt, Term.relabel]
  congr 1
  funext i
  exact Fin.elim0 i

private theorem substAll_not {n m : ℕ} (σ : Fin n → L2.Term (Empty ⊕ Fin m))
    (A : L2.BoundedFormula Empty n) :
    Substitution.substAll σ (∼A) = ∼(Substitution.substAll σ A) := rfl

private theorem substAll_inf {n m : ℕ} (σ : Fin n → L2.Term (Empty ⊕ Fin m))
    (A B : L2.BoundedFormula Empty n) :
    Substitution.substAll σ (A ⊓ B) =
      (Substitution.substAll σ A ⊓ Substitution.substAll σ B) := rfl

private theorem substAll_isSet_term {n m : ℕ} (σ : Fin n → L2.Term (Empty ⊕ Fin m))
    (t : L2.Term (Empty ⊕ Fin n)) :
    Substitution.substAll σ (isSetBd t) =
      isSetBd (t.subst (Sum.elim (fun e : Empty => e.elim) σ)) := by
  simp only [isSetBd, Substitution.substAll, Relations.boundedFormula₁,
    Relations.boundedFormula]
  congr 1
  funext i
  fin_cases i
  rfl

private theorem substAll_lt_terms {n m : ℕ} (σ : Fin n → L2.Term (Empty ⊕ Fin m))
    (s t : L2.Term (Empty ⊕ Fin n)) :
    Substitution.substAll σ (ltBd s t) =
      ltBd (s.subst (Sum.elim (fun e : Empty => e.elim) σ))
        (t.subst (Sum.elim (fun e : Empty => e.elim) σ)) := by
  simp only [ltBd, Substitution.substAll, Relations.boundedFormula₂,
    Relations.boundedFormula]
  congr 1
  funext i
  fin_cases i <;> rfl

private theorem substAll_eq_terms {n m : ℕ} (σ : Fin n → L2.Term (Empty ⊕ Fin m))
    (s t : L2.Term (Empty ⊕ Fin n)) :
    Substitution.substAll σ (Term.bdEqual s t) =
      Term.bdEqual (s.subst (Sum.elim (fun e : Empty => e.elim) σ))
        (t.subst (Sum.elim (fun e : Empty => e.elim) σ)) := rfl

private theorem substAll_isSet_var {n m : ℕ} (σ : Fin n → L2.Term (Empty ⊕ Fin m))
    (j : Fin n) :
    Substitution.substAll σ (isSetBd (&j)) = isSetBd (σ j) := by
  simp only [isSetBd, Substitution.substAll, Relations.boundedFormula₁,
    Relations.boundedFormula]
  congr 1
  funext i
  fin_cases i
  rfl

private theorem substAll_lt_var_var {n m : ℕ} (σ : Fin n → L2.Term (Empty ⊕ Fin m))
    (i j : Fin n) :
    Substitution.substAll σ (ltBd (&i) (&j)) = ltBd (σ i) (σ j) := by
  simp only [ltBd, Substitution.substAll, Relations.boundedFormula₂,
    Relations.boundedFormula]
  congr 1
  funext k
  fin_cases k <;> rfl

private theorem substAll_eq_var_zero {n m : ℕ} (σ : Fin n → L2.Term (Empty ⊕ Fin m))
    (i : Fin n) :
    Substitution.substAll σ (Term.bdEqual (&i) zeroTerm) =
      Term.bdEqual (σ i) zeroTerm := by
  simp only [Term.bdEqual, Substitution.substAll]
  rw [subst_zeroTerm]
  simp [Term.subst]

private theorem substAll_eq_var_succ_var {n m : ℕ}
    (σ : Fin n → L2.Term (Empty ⊕ Fin m)) (i j : Fin n) :
    Substitution.substAll σ (Term.bdEqual (&i) (succTerm (&j))) =
      Term.bdEqual (σ i) (succTerm (σ j)) := by
  simp only [Term.bdEqual, Substitution.substAll]
  rw [subst_succ_var]
  simp [Term.subst]

private theorem substAll_boundedZeroOrSuccPredecessorBody {m : ℕ}
    (σ : Fin 2 → L2.Term (Empty ⊕ Fin m)) :
    Substitution.substAll σ boundedZeroOrSuccPredecessorBody =
      ((Substitution.substAll σ (ltBd (&1) (&0))) ⊓
        ((∼ (Substitution.substAll σ (isSetBd (&1)))) ⊓
          ((Substitution.substAll σ (Term.bdEqual (&0) (succTerm (&1)))) ⊓
            Substitution.substAll σ (ltBd (&1) (&0))))) := rfl

private theorem substAll_indFormulaZeroOrSucc {m : ℕ}
    (σ : Fin 1 → L2.Term (Empty ⊕ Fin m)) :
    Substitution.substAll σ indFormulaZeroOrSucc =
      (Substitution.substAll σ (Term.bdEqual (&0) zeroTerm) ⊔
        ∃' (Substitution.substAll (Substitution.liftSubst σ)
          boundedZeroOrSuccPredecessorBody)) := rfl

private def zeroOrSuccInductionBaseFormula : L2.Sentence :=
  (Term.bdEqual (zeroTerm : L2.Term (Empty ⊕ Fin 0)) zeroTerm) ⊔
    ∃' ((ltBd (&0) zeroTerm) ⊓ ((∼ (isSetBd (&0))) ⊓
      ((Term.bdEqual zeroTerm (succTerm (&0))) ⊓ (ltBd (&0) zeroTerm))))

private theorem zeroOrSuccInductionBaseFormula_eq :
    Substitution.substAll
        (fun _ : Fin 1 => (zeroTerm : L2.Term (Empty ⊕ Fin 0)))
        indFormulaZeroOrSucc = zeroOrSuccInductionBaseFormula := by
  rw [substAll_indFormulaZeroOrSucc, substAll_eq_var_zero,
    substAll_boundedZeroOrSuccPredecessorBody, substAll_lt_var_var,
    substAll_isSet_var, substAll_eq_var_succ_var]
  unfold zeroOrSuccInductionBaseFormula
  have h0 : Substitution.liftSubst
      (fun _ : Fin 1 => (zeroTerm : L2.Term (Empty ⊕ Fin 0))) (0 : Fin 2) =
      (zeroTerm : L2.Term (Empty ⊕ Fin 1)) := by
    simp [Substitution.liftSubst, Fin.snoc, lift_zeroTerm_to_one]
  have h1 : Substitution.liftSubst
      (fun _ : Fin 1 => (zeroTerm : L2.Term (Empty ⊕ Fin 0))) (1 : Fin 2) =
      (&0 : L2.Term (Empty ⊕ Fin 1)) := by
    simp [Substitution.liftSubst, Fin.snoc]
  rw [h0, h1]

private def zeroOrSuccSuccessorWitnessFormula : L2.BoundedFormula Empty 1 :=
  (ltBd (&0) (succTerm (&0))) ⊓
    ((∼ (isSetBd (&0))) ⊓
      ((Term.bdEqual (succTerm (&0)) (succTerm (&0))) ⊓
        ltBd (&0) (succTerm (&0))))

private theorem zeroOrSuccSuccessorWitnessFormula_eq :
    Substitution.instantiateTop (&0 : L2.Term (Empty ⊕ Fin 1))
      (Substitution.substAll
        (Substitution.liftSubst
          (fun _ : Fin 1 => succTerm (&0 : L2.Term (Empty ⊕ Fin 1))))
        boundedZeroOrSuccPredecessorBody) = zeroOrSuccSuccessorWitnessFormula := by
  rw [substAll_boundedZeroOrSuccPredecessorBody, substAll_lt_var_var,
    substAll_isSet_var, substAll_eq_var_succ_var]
  have h0 : Substitution.liftSubst
      (fun _ : Fin 1 => succTerm (&0 : L2.Term (Empty ⊕ Fin 1))) (0 : Fin 2) =
      succTerm (&0 : L2.Term (Empty ⊕ Fin 2)) := by
    simp [Substitution.liftSubst, Fin.snoc, Term.liftAt, Term.relabel, succTerm,
      Functions.apply₁, succ_function_eta]
  have h1 : Substitution.liftSubst
      (fun _ : Fin 1 => succTerm (&0 : L2.Term (Empty ⊕ Fin 1))) (1 : Fin 2) =
      (&1 : L2.Term (Empty ⊕ Fin 2)) := by
    simp [Substitution.liftSubst, Fin.snoc]
  rw [h0, h1, Substitution.instantiateTop]
  simp only [substAll_inf, substAll_not, substAll_lt_terms, substAll_isSet_term,
    substAll_eq_terms]
  unfold zeroOrSuccSuccessorWitnessFormula
  simp [ltBd, isSetBd, subst_succTerm, Term.subst, Fin.snoc]

private theorem zeroOrSuccIdentitySubst :
    Substitution.substAll
      (fun _ : Fin 1 => (&0 : L2.Term (Empty ⊕ Fin 1)))
      indFormulaZeroOrSucc = indFormulaZeroOrSucc := by
  rw [substAll_indFormulaZeroOrSucc, substAll_eq_var_zero,
    substAll_boundedZeroOrSuccPredecessorBody, substAll_lt_var_var,
    substAll_isSet_var, substAll_eq_var_succ_var]
  unfold indFormulaZeroOrSucc boundedZeroOrSuccPredecessorBody
  have h0 : Substitution.liftSubst
      (fun _ : Fin 1 => (&0 : L2.Term (Empty ⊕ Fin 1))) (0 : Fin 2) =
      (&0 : L2.Term (Empty ⊕ Fin 2)) := by
    simp [Substitution.liftSubst, Fin.snoc, Term.liftAt, Term.relabel]
  have h1 : Substitution.liftSubst
      (fun _ : Fin 1 => (&0 : L2.Term (Empty ⊕ Fin 1))) (1 : Fin 2) =
      (&1 : L2.Term (Empty ⊕ Fin 2)) := by
    simp [Substitution.liftSubst, Fin.snoc]
  rw [h0, h1]

private theorem zeroOrSucc_induction_base {T : L2.Theory} :
    DerivableFO T
      (Substitution.substAll
        (fun _ : Fin 1 => (zeroTerm : L2.Term (Empty ⊕ Fin 0)))
        indFormulaZeroOrSucc) := by
  rw [zeroOrSuccInductionBaseFormula_eq]
  unfold zeroOrSuccInductionBaseFormula
  exact DerivableFO.mp (DerivableFO.or_inl _ _)
    (DerivableFO.eq_refl (zeroTerm : L2.Term (Empty ⊕ Fin 0)))

private theorem zeroOrSucc_induction_step {T : L2.Theory}
    (hLtSucc : DerivableFO T axLtSucc) :
    DerivableFO T
      (∀' ((∼ (isSetBd (&0))) ⟹
        ((Substitution.substAll
          (fun _ : Fin 1 => (&0 : L2.Term (Empty ⊕ Fin 1)))
          indFormulaZeroOrSucc) ⟹
        (Substitution.substAll
          (fun _ : Fin 1 => succTerm (&0 : L2.Term (Empty ⊕ Fin 1)))
          indFormulaZeroOrSucc)))) := by
  apply DerivableFO.all_intro
  show DerivableH T []
    ((∼ (isSetBd (&0))) ⟹
      ((Substitution.substAll
        (fun _ : Fin 1 => (&0 : L2.Term (Empty ⊕ Fin 1)))
        indFormulaZeroOrSucc) ⟹
      (Substitution.substAll
        (fun _ : Fin 1 => succTerm (&0 : L2.Term (Empty ⊕ Fin 1)))
        indFormulaZeroOrSucc)))
  apply deduction
  apply deduction
  apply or_inr_H
  apply ex_intro_H (&0 : L2.Term (Empty ⊕ Fin 1))
  rw [zeroOrSuccSuccessorWitnessFormula_eq]
  change DerivableH T
    [(isSetBd (&0)).not,
      Substitution.substAll (fun _ : Fin 1 => (&0 : L2.Term (Empty ⊕ Fin 1)))
        indFormulaZeroOrSucc]
    zeroOrSuccSuccessorWitnessFormula
  have hNumber : DerivableH T
      [(isSetBd (&0)).not,
        Substitution.substAll (fun _ : Fin 1 => (&0 : L2.Term (Empty ⊕ Fin 1)))
          indFormulaZeroOrSucc]
      ((isSetBd (&0)).not) :=
    weaken (assume_last [] ((isSetBd (&0)).not))
  have hLt : DerivableH T
      [(isSetBd (&0)).not,
        Substitution.substAll (fun _ : Fin 1 => (&0 : L2.Term (Empty ⊕ Fin 1)))
          indFormulaZeroOrSucc]
      (ltBd (&0) (succTerm (&0))) :=
    mp_H (ofClosed (DerivableFO.all_elim (by simpa [axLtSucc] using hLtSucc))) hNumber
  unfold zeroOrSuccSuccessorWitnessFormula
  exact and_intro_H hLt
    (and_intro_H hNumber
      (and_intro_H
        (ofClosed (DerivableFO.eq_refl (succTerm (&0 : L2.Term (Empty ⊕ Fin 1))))) hLt))

private def ordinaryPredecessorBody : L2.BoundedFormula Empty 2 :=
  (∼ (isSetBd (&1))) ⊓
    ((Term.bdEqual (&0) (succTerm (&1))) ⊓ (ltBd (&1) (&0)))

private theorem boundedPredecessor_implies_ordinary {T : L2.Theory} :
    DerivableFO T
      (∀' (boundedZeroOrSuccPredecessorBody ⟹ ordinaryPredecessorBody)) := by
  apply DerivableFO.all_intro
  show DerivableH T []
    (boundedZeroOrSuccPredecessorBody ⟹ ordinaryPredecessorBody)
  apply deduction
  have hStrong : DerivableH T
      [boundedZeroOrSuccPredecessorBody]
      boundedZeroOrSuccPredecessorBody := assume_last [] _
  unfold boundedZeroOrSuccPredecessorBody at hStrong
  unfold ordinaryPredecessorBody
  exact and_intro_H (and_left_H (and_right_H hStrong))
    (and_right_H (and_right_H hStrong))

private theorem boundedZeroOrSucc_implies_ordinary {T : L2.Theory} :
    DerivableFO T
      (indFormulaZeroOrSucc ⟹
        ((Term.bdEqual (&0) zeroTerm) ⊔ ∃' ordinaryPredecessorBody)) := by
  show DerivableH T []
    (indFormulaZeroOrSucc ⟹
      ((Term.bdEqual (&0) zeroTerm) ⊔ ∃' ordinaryPredecessorBody))
  apply deduction
  have hSource : DerivableH T [indFormulaZeroOrSucc] indFormulaZeroOrSucc :=
    assume_last [] indFormulaZeroOrSucc
  unfold indFormulaZeroOrSucc at hSource
  refine or_elim_H hSource ?_ ?_
  · apply or_inl_H
    exact assume_last [indFormulaZeroOrSucc] (Term.bdEqual (&0) zeroTerm)
  · apply or_inr_H
    exact mp_H (ofClosed (DerivableFO.ex_mono boundedPredecessor_implies_ordinary))
      (assume_last [indFormulaZeroOrSucc] (∃' boundedZeroOrSuccPredecessorBody))

/-- One bounded induction instance proves the number zero-or-successor axiom. -/
theorem zeroOrSuccInductionFragment_derives_axZeroOrSucc :
    DerivableFO zeroOrSuccInductionFragment axZeroOrSucc := by
  have hInd : DerivableFO zeroOrSuccInductionFragment (IND indFormulaZeroOrSucc) :=
    DerivableFO.hyp (by simp [zeroOrSuccInductionFragment])
  have hBase := zeroOrSucc_induction_base (T := zeroOrSuccInductionFragment)
  have hStep := zeroOrSucc_induction_step
    zeroOrSuccInductionFragment_derives_axLtSucc
  have hStrong : DerivableFO zeroOrSuccInductionFragment
      ((∼ (isSetBd (&0))) ⟹ indFormulaZeroOrSucc) := by
    have hPremise := DerivableFO.mp
      (DerivableFO.mp (DerivableFO.and_intro _ _) hBase) hStep
    have hConclusionAll := DerivableFO.mp hInd hPremise
    have hConclusion := DerivableFO.all_elim hConclusionAll
    rw [zeroOrSuccIdentitySubst] at hConclusion
    exact hConclusion
  rw [axZeroOrSucc]
  apply DerivableFO.all_intro
  show DerivableH zeroOrSuccInductionFragment []
    ((∼ (isSetBd (&0))) ⟹
      ((Term.bdEqual (&0) zeroTerm) ⊔ ∃' ordinaryPredecessorBody))
  apply deduction
  exact mp_H (ofClosed boundedZeroOrSucc_implies_ordinary)
    (mp_H (ofClosed hStrong) (assume_last [] ((isSetBd (&0)).not)))

/-! ### Arbitrary-theory closure -/

/-- Every theory containing the finite arithmetic base and the one required induction instance
derives zero-or-successor. -/
theorem axZeroOrSucc_derivable_of_contains {T : L2.Theory}
    (hbase : rca0SimpsonBasic ⊆ T)
    (hind : IND indFormulaZeroOrSucc ∈ T) :
    DerivableFO T axZeroOrSucc := by
  apply derivableFO_of_subtheory (T₁ := zeroOrSuccInductionFragment)
    (T₂ := T) (φ := axZeroOrSucc) ?_ zeroOrSuccInductionFragment_derives_axZeroOrSucc
  intro φ hφ
  rcases hφ with hφ | hφ
  · exact DerivableFO.hyp (hbase hφ)
  · have heq : φ = IND indFormulaZeroOrSucc := by
      simpa only [Set.mem_singleton_iff] using hφ
    subst φ
    exact DerivableFO.hyp hind

/-- The one-instance fragment derives the elementary predecessor-descent sentence. -/
theorem zeroOrSuccInductionFragment_derives_numberPredecessorDescent :
    DerivableFO zeroOrSuccInductionFragment numberPredecessorDescentSentence :=
  numberPredecessorDescent_derivable_of_axZeroOrSucc
    zeroOrSuccInductionFragment_derives_axZeroOrSucc

/-- Universal containment theorem: every theory containing the finite arithmetic base and the
single bounded zero-or-successor induction instance derives predecessor descent. -/
theorem numberPredecessorDescent_derivable_of_contains {T : L2.Theory}
    (hbase : rca0SimpsonBasic ⊆ T)
    (hind : IND indFormulaZeroOrSucc ∈ T) :
    DerivableFO T numberPredecessorDescentSentence :=
  numberPredecessorDescent_derivable_of_axZeroOrSucc
    (axZeroOrSucc_derivable_of_contains hbase hind)

/-- The finite base extended by every bounded induction instance.  This is not a presentation of
full second-order `RCA₀`: no comprehension scheme is included. -/
def numberRelativizedBoundedInductionTheory : L2.Theory :=
  rca0SimpsonBasic ∪ {ψ | ∃ φ : L2.BoundedFormula Empty 1, IsBoundedQ φ ∧ ψ = IND φ}

/-- The one-instance fragment is contained in the bounded-induction theory. -/
theorem zeroOrSuccInductionFragment_subset_boundedInductionTheory :
    zeroOrSuccInductionFragment ⊆ numberRelativizedBoundedInductionTheory := by
  intro ψ hψ
  rcases hψ with hbase | hind
  · exact Or.inl hbase
  · right
    have heq : ψ = IND indFormulaZeroOrSucc := by
      simpa only [Set.mem_singleton_iff] using hind
    exact ⟨indFormulaZeroOrSucc, isBoundedQ_indFormulaZeroOrSucc, heq⟩

/-- The full bounded-induction extension derives predecessor descent. -/
theorem boundedInductionTheory_derives_numberPredecessorDescent :
    DerivableFO numberRelativizedBoundedInductionTheory numberPredecessorDescentSentence := by
  exact derivableFO_of_subtheory
    (fun φ hφ => DerivableFO.hyp
      (zeroOrSuccInductionFragment_subset_boundedInductionTheory hφ))
    zeroOrSuccInductionFragment_derives_numberPredecessorDescent

end OperatorKO7.ReverseMath
