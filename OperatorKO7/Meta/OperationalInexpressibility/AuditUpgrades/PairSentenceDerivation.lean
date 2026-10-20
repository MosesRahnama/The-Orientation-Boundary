import OperatorKO7.Meta.ReverseMath.RCA0DerivationSharpness
import OperatorKO7.Meta.ReverseMath.SizeChangeSoundness

/-!
# The bounded sentence of the projected pair in the sound first-order calculus

`DupDPBoundedSNSentence` is the number-relativized sentence `∀c ∃n (c < n)`. Its standard-model
satisfaction is equivalent to bounded strong normalization of the recursor's projected pair
(`dupDP_boundedSN_iff_stdModel_formula`). This module places that sentence in the calculus of
`DeductionFO` over the eight basic axioms `rca0SimpsonBasic`.

* `successorClosedArithmetic_derives_dupDPBoundedSNSentence`: the eight axioms and the closure
  axiom `axSuccNumber` (the successor of a number is a number) derive the sentence; the bound of
  a counter `c` is `S c`.
* `dupDPBoundedSNSentence_derivable_of_contains`: the same derivation in every theory that
  contains the eight axioms and the closure axiom.
* `SuccessorEscapeCountermodel`: two elements; zero is the only number and its successor is a set
  object. The structure satisfies the eight axioms and the induction sentence of every formula in
  one free variable, and it falsifies the pair sentence.
* `not_derives_dupDPBoundedSNSentence_of_subset`: no subtheory of the eight axioms with all
  induction sentences derives the pair sentence.
* `inductionArithmetic_separates_descent_from_pair`: that theory derives predecessor descent and
  leaves the pair sentence underivable; `inductionArithmetic_not_derives_axSuccNumber` follows.

Trust: kernel-only. No `sorry`, no `admit`, no new `axiom`.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.OperationalInexpressibility.AuditUpgrades.PairSentenceDerivation

open FirstOrder Language
open OperatorKO7.ReverseMath
open OperatorKO7.ReverseMath.DeductionFO
open OperatorKO7.ReverseMath.DeductionH
open OperatorKO7.ReverseMath.SizeChangeSoundness

/-! ### The closure axiom and the two theories -/

/-- `∀x, ¬IsSet x → ¬IsSet (S x)`: the successor of a number is a number. -/
def axSuccNumber : L2.Sentence :=
  ∀' ((∼ (isSetBd (&0))) ⟹ (∼ (isSetBd (succTerm (&0)))))

/-- The eight basic axioms with successor closure of the numbers. -/
def successorClosedArithmetic : L2.Theory :=
  rca0SimpsonBasic ∪ {axSuccNumber}

/-- The eight basic axioms with the induction sentence of every formula in one free variable. -/
def inductionArithmetic : L2.Theory :=
  rca0SimpsonBasic ∪ Set.range IND

/-! ### The derivation -/

/-- The hypothesis that the counter is a number. -/
private abbrev numberHyp : L2.BoundedFormula Empty 1 :=
  (isSetBd (&0 : L2.Term (Empty ⊕ Fin 1))).not

/-- The matrix of the pair sentence at the bound `S c`. -/
private def pairWitnessFormula : L2.BoundedFormula Empty 1 :=
  (∼ (isSetBd (&0))) ⟹
    ((∼ (isSetBd (succTerm (&0)))) ⊓ ltBd (&0) (succTerm (&0)))

private def pairSubst : Fin 2 → L2.Term (Empty ⊕ Fin 1) :=
  Fin.snoc (fun i : Fin 1 => Term.var (Sum.inr i)) (succTerm (&0))

private theorem pairSubst_zero : pairSubst 0 = (&0 : L2.Term (Empty ⊕ Fin 1)) := by
  simp [pairSubst, Fin.snoc]

private theorem pairSubst_one : pairSubst 1 = succTerm (&0 : L2.Term (Empty ⊕ Fin 1)) := by
  simp [pairSubst, Fin.snoc]

private theorem pairWitness_eq :
    Substitution.instantiateTop (succTerm (&0 : L2.Term (Empty ⊕ Fin 1))) dupDPBoundMatrix =
      pairWitnessFormula := by
  have hSet0 : Substitution.substAll pairSubst (isSetBd (&0)) = isSetBd (&0) := by
    simp only [isSetBd, Substitution.substAll, Relations.boundedFormula₁,
      Relations.boundedFormula]
    congr 1
    funext i
    fin_cases i
    simp [Term.subst, pairSubst_zero]
  have hSet1 : Substitution.substAll pairSubst (isSetBd (&1)) = isSetBd (succTerm (&0)) := by
    simp only [isSetBd, Substitution.substAll, Relations.boundedFormula₁,
      Relations.boundedFormula]
    congr 1
    funext i
    fin_cases i
    simp [Term.subst, pairSubst_one]
  have hLt : Substitution.substAll pairSubst (ltBd (&0) (&1)) =
      ltBd (&0) (succTerm (&0)) := by
    simp only [ltBd, Substitution.substAll, Relations.boundedFormula₂,
      Relations.boundedFormula]
    congr 1
    funext i
    fin_cases i
    · simp [Term.subst, pairSubst_zero]
    · simp [Term.subst, pairSubst_one]
  rw [Substitution.instantiateTop]
  change Substitution.substAll pairSubst dupDPBoundMatrix = _
  change ((∼ (Substitution.substAll pairSubst (isSetBd (&0)))) ⟹
      ((∼ (Substitution.substAll pairSubst (isSetBd (&1)))) ⊓
        Substitution.substAll pairSubst (ltBd (&0) (&1)))) = pairWitnessFormula
  rw [hSet0, hSet1, hLt]
  rfl

/-- The eight basic axioms with successor closure derive the bounded sentence of the projected
pair. For a number `c` the bound is `S c`: closure makes it a number, and the base derivation of
`x < S x` orders it above `c`. -/
theorem successorClosedArithmetic_derives_dupDPBoundedSNSentence :
    DerivableFO successorClosedArithmetic DupDPBoundedSNSentence := by
  have hLtSucc : DerivableFO successorClosedArithmetic axLtSucc :=
    derivableFO_of_subtheory (fun φ hφ => DerivableFO.hyp (Or.inl hφ))
      simpsonArithmetic_derives_axLtSucc
  have hClosure : DerivableFO successorClosedArithmetic axSuccNumber :=
    DerivableFO.hyp (Or.inr (Set.mem_singleton axSuccNumber))
  have hLtOpen : DerivableFO successorClosedArithmetic
      ((∼ (isSetBd (&0))) ⟹ ltBd (&0) (succTerm (&0))) :=
    DerivableFO.all_elim (show DerivableFO successorClosedArithmetic
      (∀' ((∼ (isSetBd (&0))) ⟹ ltBd (&0) (succTerm (&0)))) from hLtSucc)
  have hClosureOpen : DerivableFO successorClosedArithmetic
      ((∼ (isSetBd (&0))) ⟹ (∼ (isSetBd (succTerm (&0))))) :=
    DerivableFO.all_elim (show DerivableFO successorClosedArithmetic
      (∀' ((∼ (isSetBd (&0))) ⟹ (∼ (isSetBd (succTerm (&0)))))) from hClosure)
  rw [DupDPBoundedSNSentence]
  apply DerivableFO.all_intro
  apply DerivableFO.ex_intro (succTerm (&0 : L2.Term (Empty ⊕ Fin 1)))
  rw [pairWitness_eq]
  show DerivableH successorClosedArithmetic [] pairWitnessFormula
  apply deduction
  have hNumber : DerivableH successorClosedArithmetic [numberHyp] numberHyp :=
    assume_last ([] : List (L2.BoundedFormula Empty 1)) numberHyp
  have hSucc : DerivableH successorClosedArithmetic [numberHyp]
      ((isSetBd (succTerm (&0 : L2.Term (Empty ⊕ Fin 1)))).not) :=
    mp_H (ofClosed hClosureOpen) hNumber
  have hLt : DerivableH successorClosedArithmetic [numberHyp]
      (ltBd (&0 : L2.Term (Empty ⊕ Fin 1)) (succTerm (&0))) :=
    mp_H (ofClosed hLtOpen) hNumber
  exact and_intro_H hSucc hLt

/-- Every theory containing the eight basic axioms and successor closure derives the bounded
sentence of the projected pair. -/
theorem dupDPBoundedSNSentence_derivable_of_contains {T : L2.Theory}
    (hbase : rca0SimpsonBasic ⊆ T) (hclosure : axSuccNumber ∈ T) :
    DerivableFO T DupDPBoundedSNSentence := by
  apply derivableFO_of_subtheory (T₁ := successorClosedArithmetic) (T₂ := T)
    (φ := DupDPBoundedSNSentence) ?_
    successorClosedArithmetic_derives_dupDPBoundedSNSentence
  intro φ hφ
  rcases hφ with hφ | hφ
  · exact DerivableFO.hyp (hbase hφ)
  · have heq : φ = axSuccNumber := by
      simpa only [Set.mem_singleton_iff] using hφ
    subst φ
    exact DerivableFO.hyp hclosure

/-! ### The countermodel -/

namespace SuccessorEscapeCountermodel

/-- Two elements: `false` is zero and the only number, `true` is a set object. -/
abbrev Carrier : Type := Bool

/-- Zero denotes the number, successor sends every element to the set object, addition returns
its second input, and multiplication returns zero. -/
def funMap : {k : ℕ} → Func k → (Fin k → Carrier) → Carrier
  | _, Func.zero, _ => false
  | _, Func.succ, _ => true
  | _, Func.add, v => v 1
  | _, Func.mul, _ => false

/-- `<` holds only from the number to the set object, membership is empty, and `IsSet` selects
`true`. -/
def relMap : {k : ℕ} → Rel k → (Fin k → Carrier) → Prop
  | _, Rel.lt, v => v 0 = false ∧ v 1 = true
  | _, Rel.mem, _ => False
  | _, Rel.isSet, v => v 0 = true

instance successorEscapeStructure : L2.Structure Carrier where
  funMap := funMap
  RelMap := relMap

instance nonemptyCarrier : Nonempty Carrier := ⟨false⟩

@[simp] private theorem snoc_empty_apply (a : Carrier) :
    ((Fin.snoc (default : Fin 0 → Carrier) a : Fin 1 → Carrier) 0) = a := by
  rw [Fin.snoc_zero]

@[simp] private theorem snoc_two_zero (a b : Carrier) :
    ((Fin.snoc (Fin.snoc (default : Fin 0 → Carrier) a : Fin 1 → Carrier) b :
      Fin 2 → Carrier) 0) = a := by
  rw [show (0 : Fin 2) = Fin.castSucc (0 : Fin 1) from rfl, Fin.snoc_castSucc,
    snoc_empty_apply]

@[simp] private theorem snoc_two_one (a b : Carrier) :
    ((Fin.snoc (Fin.snoc (default : Fin 0 → Carrier) a : Fin 1 → Carrier) b :
      Fin 2 → Carrier) 1) = b := by
  rw [show (1 : Fin 2) = Fin.last 1 from rfl, Fin.snoc_last]

@[simp] private theorem zero_symbol_value : (zeroSym : Carrier) = false := rfl

private theorem models_axSuccNeZero : Carrier ⊨ axSuccNeZero := by
  simp only [axSuccNeZero, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_imp, BoundedFormula.realize_not, BoundedFormula.realize_bdEqual,
    BoundedFormula.realize_rel₁, isSetBd]
  intro _ _
  simp [succTerm, zeroTerm, succSym, zeroSym,
    Term.realize_functions_apply₁, Term.realize_constants, successorEscapeStructure, funMap]

private theorem models_axSuccInj : Carrier ⊨ axSuccInj := by
  simp only [axSuccInj, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_imp, BoundedFormula.realize_not, BoundedFormula.realize_bdEqual,
    BoundedFormula.realize_rel₁, isSetBd]
  intro a b ha hb _
  have hb' : b = false := by
    simpa [successorEscapeStructure, relMap, Fin.snoc] using ha
  have ha' : a = false := by
    simpa [successorEscapeStructure, relMap, Fin.snoc] using hb
  simpa [Term.realize_var, Fin.snoc] using hb'.trans ha'.symm

private theorem models_axAddZero : Carrier ⊨ axAddZero := by
  simp only [axAddZero, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_imp, BoundedFormula.realize_not, BoundedFormula.realize_bdEqual,
    BoundedFormula.realize_rel₁, isSetBd]
  intro a hnum
  have ha : a = false := by
    simpa [successorEscapeStructure, relMap, Fin.snoc] using hnum
  subst a
  simp [addTerm, zeroTerm, addSym, zeroSym, Term.realize_var,
    Term.realize_functions_apply₂, Term.realize_constants, successorEscapeStructure, funMap,
    Fin.snoc]

private theorem models_axAddSucc : Carrier ⊨ axAddSucc := by
  simp only [axAddSucc, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_imp, BoundedFormula.realize_not, BoundedFormula.realize_bdEqual,
    BoundedFormula.realize_rel₁, isSetBd]
  intro _ _ _ _
  simp [addTerm, succTerm, addSym, succSym, Term.realize_var,
    Term.realize_functions_apply₁, Term.realize_functions_apply₂,
    successorEscapeStructure, funMap]

private theorem models_axMulZero : Carrier ⊨ axMulZero := by
  simp only [axMulZero, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_imp, BoundedFormula.realize_not, BoundedFormula.realize_bdEqual,
    BoundedFormula.realize_rel₁, isSetBd]
  intro _ _
  simp [mulTerm, zeroTerm, mulSym, zeroSym,
    Term.realize_functions_apply₂, Term.realize_constants, successorEscapeStructure, funMap]

private theorem models_axMulSucc : Carrier ⊨ axMulSucc := by
  simp only [axMulSucc, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_imp, BoundedFormula.realize_not, BoundedFormula.realize_bdEqual,
    BoundedFormula.realize_rel₁, isSetBd]
  intro a b ha hb
  have hb' : b = false := by
    simpa [successorEscapeStructure, relMap, Fin.snoc] using ha
  have ha' : a = false := by
    simpa [successorEscapeStructure, relMap, Fin.snoc] using hb
  subst a
  subst b
  simp [mulTerm, addTerm, succTerm, mulSym, addSym, succSym, Term.realize_var,
    Term.realize_functions_apply₂, successorEscapeStructure, funMap, Fin.snoc]

private theorem models_axNotLtZero : Carrier ⊨ axNotLtZero := by
  simp only [axNotLtZero, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_imp, BoundedFormula.realize_not, BoundedFormula.realize_rel₁,
    BoundedFormula.realize_rel₂, isSetBd, ltBd]
  intro _ _
  simp [zeroTerm, ltSym, zeroSym, Term.realize_var, Term.realize_constants,
    successorEscapeStructure, relMap]

private theorem models_axLtSuccIff : Carrier ⊨ axLtSuccIff := by
  simp only [axLtSuccIff, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_imp, BoundedFormula.realize_not, BoundedFormula.realize_inf,
    BoundedFormula.realize_sup, BoundedFormula.realize_bdEqual, BoundedFormula.realize_rel₁,
    BoundedFormula.realize_rel₂, isSetBd, ltBd]
  intro a b ha hb
  have hb' : b = false := by
    simpa [successorEscapeStructure, relMap, Fin.snoc] using ha
  have ha' : a = false := by
    simpa [successorEscapeStructure, relMap, Fin.snoc] using hb
  subst a
  subst b
  simp [succTerm, ltSym, succSym, Term.realize_var, Term.realize_functions_apply₁,
    successorEscapeStructure, funMap, relMap, Fin.snoc]

/-- The two-element structure satisfies every axiom of the eight-axiom base. -/
theorem models_simpsonArithmetic : Carrier ⊨ rca0SimpsonBasic :=
  ⟨fun φ hφ => by
    simp only [rca0SimpsonBasic, Set.mem_insert_iff, Set.mem_singleton_iff] at hφ
    rcases hφ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact models_axSuccNeZero
    · exact models_axSuccInj
    · exact models_axAddZero
    · exact models_axAddSucc
    · exact models_axMulZero
    · exact models_axMulSucc
    · exact models_axNotLtZero
    · exact models_axLtSuccIff⟩

/-- Every induction sentence holds: zero is the only number, so the conclusion of an induction
sentence is its base premise. -/
theorem models_IND (φ : L2.BoundedFormula Empty 1) : Carrier ⊨ IND φ := by
  simp only [IND, Sentence.Realize, Formula.Realize, BoundedFormula.realize_imp,
    BoundedFormula.realize_inf, BoundedFormula.realize_all, BoundedFormula.realize_not,
    BoundedFormula.realize_rel₁, isSetBd, Substitution.realize_substAll]
  rintro ⟨hbase, _⟩ a hnum
  have ha : a = false := by
    simpa [successorEscapeStructure, relMap, Fin.snoc] using hnum
  subst a
  simpa [zeroTerm, zeroSym, Term.realize_constants, Term.realize_var,
    successorEscapeStructure, funMap] using hbase

/-- The structure models the eight axioms with every induction sentence. -/
theorem models_inductionArithmetic : Carrier ⊨ inductionArithmetic := by
  refine ⟨fun ψ hψ => ?_⟩
  rcases hψ with hbase | ⟨φ, rfl⟩
  · letI : Carrier ⊨ rca0SimpsonBasic := models_simpsonArithmetic
    exact Theory.realize_sentence_of_mem rca0SimpsonBasic hbase
  · exact models_IND φ

/-- The sole number has no number above it, so the pair sentence fails. -/
theorem not_models_dupDPBoundedSNSentence : ¬ Carrier ⊨ DupDPBoundedSNSentence := by
  intro h
  simp only [DupDPBoundedSNSentence, dupDPBoundMatrix, Sentence.Realize, Formula.Realize,
    BoundedFormula.realize_all, BoundedFormula.realize_ex, BoundedFormula.realize_imp,
    BoundedFormula.realize_inf, BoundedFormula.realize_not, BoundedFormula.realize_rel₁,
    BoundedFormula.realize_rel₂, isSetBd, ltBd] at h
  obtain ⟨b, hb⟩ := h false
  cases b <;>
    simp [successorEscapeStructure, relMap, ltSym, isSetSym, Term.realize_var, Fin.snoc] at hb

end SuccessorEscapeCountermodel

/-! ### Underivability and the separation -/

/-- No subtheory of the eight axioms with all induction sentences derives the pair sentence. -/
theorem not_derives_dupDPBoundedSNSentence_of_subset {T : L2.Theory}
    (hT : T ⊆ inductionArithmetic) : ¬ DerivableFO T DupDPBoundedSNSentence := by
  intro h
  exact SuccessorEscapeCountermodel.not_models_dupDPBoundedSNSentence
    (derivableFO_sound_sentence
      (SuccessorEscapeCountermodel.models_inductionArithmetic.mono hT) h)

/-- The eight basic axioms alone do not derive the pair sentence. -/
theorem simpsonArithmetic_not_derives_dupDPBoundedSNSentence :
    ¬ DerivableFO rca0SimpsonBasic DupDPBoundedSNSentence :=
  not_derives_dupDPBoundedSNSentence_of_subset (fun _ h => Or.inl h)

/-- The bounded-induction theory of the calibration does not derive the pair sentence. -/
theorem boundedInductionTheory_not_derives_dupDPBoundedSNSentence :
    ¬ DerivableFO numberRelativizedBoundedInductionTheory DupDPBoundedSNSentence := by
  apply not_derives_dupDPBoundedSNSentence_of_subset
  intro ψ hψ
  rcases hψ with hbase | ⟨φ, _, rfl⟩
  · exact Or.inl hbase
  · exact Or.inr ⟨φ, rfl⟩

/-- The eight axioms with every induction sentence derive predecessor descent and do not derive
the pair sentence. -/
theorem inductionArithmetic_separates_descent_from_pair :
    DerivableFO inductionArithmetic numberPredecessorDescentSentence ∧
      ¬ DerivableFO inductionArithmetic DupDPBoundedSNSentence :=
  ⟨numberPredecessorDescent_derivable_of_contains (fun _ h => Or.inl h)
      (Or.inr ⟨indFormulaZeroOrSucc, rfl⟩),
    not_derives_dupDPBoundedSNSentence_of_subset (fun _ h => h)⟩

/-- The closure axiom is not derivable from the eight axioms with every induction sentence: with
it, that theory would derive the pair sentence. -/
theorem inductionArithmetic_not_derives_axSuccNumber :
    ¬ DerivableFO inductionArithmetic axSuccNumber := by
  intro hClosure
  apply not_derives_dupDPBoundedSNSentence_of_subset (T := inductionArithmetic) (fun _ h => h)
  apply derivableFO_of_subtheory (T₁ := successorClosedArithmetic) (T₂ := inductionArithmetic)
    (φ := DupDPBoundedSNSentence) ?_
    successorClosedArithmetic_derives_dupDPBoundedSNSentence
  intro φ hφ
  rcases hφ with hφ | hφ
  · exact DerivableFO.hyp (Or.inl hφ)
  · have heq : φ = axSuccNumber := by
      simpa only [Set.mem_singleton_iff] using hφ
    subst φ
    exact hClosure

/-- Calibration of the pair sentence: successor closure over the eight axioms derives it, no
subtheory of the eight axioms with all induction sentences derives it, and its standard-model
satisfaction is bounded strong normalization of the projected pair relation. -/
theorem pairSentence_calibration :
    DerivableFO successorClosedArithmetic DupDPBoundedSNSentence ∧
      (∀ T : L2.Theory, T ⊆ inductionArithmetic → ¬ DerivableFO T DupDPBoundedSNSentence) ∧
      (BoundedSN DupDPStep ↔ StdCarrier ⊨ DupDPBoundedSNSentence) :=
  ⟨successorClosedArithmetic_derives_dupDPBoundedSNSentence,
    fun _ hT => not_derives_dupDPBoundedSNSentence_of_subset hT,
    dupDP_boundedSN_iff_stdModel_formula⟩

end OperatorKO7.Meta.OperationalInexpressibility.AuditUpgrades.PairSentenceDerivation
