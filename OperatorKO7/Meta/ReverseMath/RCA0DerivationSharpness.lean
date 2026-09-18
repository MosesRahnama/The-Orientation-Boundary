import OperatorKO7.Meta.ReverseMath.RCA0Derivations

/-!
# Sharpness models for the finite predecessor-arithmetic fragments

The two finite structures in this file separate the actual consequences of the
number-relativized axioms from two false strengthenings.  They are semantic countermodels,
not assumptions in the positive derivations.
-/

set_option autoImplicit false

namespace OperatorKO7.ReverseMath

open FirstOrder Language
open OperatorKO7.ReverseMath.DeductionFO

/-- The base arithmetic theory plus the two individual induction instances originally proposed
for the predecessor-descent derivation. -/
def twoInductionFragment : L2.Theory :=
  rca0SimpsonBasic ∪ {IND indFormulaZeroOrSucc, IND indFormulaLtIrrefl}

namespace TwoInductionCountermodel

/-- A two-element single-sorted carrier. `false` is its only number and `true` its only set. -/
abbrev Carrier : Type := Bool

/-- Totalized arithmetic for the two-element countermodel.  The object-language zero denotes
the set element, successor is the identity, addition selects its first input, and multiplication
selects its second input. -/
def funMap : {n : ℕ} → Func n → (Fin n → Carrier) → Carrier
  | _, Func.zero, _ => true
  | _, Func.succ, v => v 0
  | _, Func.add, v => v 0
  | _, Func.mul, v => v 1

/-- In the two-element countermodel, `<` is equality, membership is empty, and `IsSet` selects
`true`. -/
def relMap : {n : ℕ} → Rel n → (Fin n → Carrier) → Prop
  | _, Rel.lt, v => v 0 = v 1
  | _, Rel.mem, _ => False
  | _, Rel.isSet, v => v 0 = true

instance twoInductionStructure : L2.Structure Carrier where
  funMap := funMap
  RelMap := relMap

instance nonemptyCarrier : Nonempty Carrier := ⟨false⟩

theorem false_is_number : ¬ twoInductionStructure.RelMap Rel.isSet ![false] := by
  simp [twoInductionStructure, relMap]

theorem true_is_set : twoInductionStructure.RelMap Rel.isSet ![true] := by
  rfl

theorem zero_is_set : twoInductionStructure.funMap Func.zero ![] = true := rfl

theorem lt_is_equality (a b : Carrier) :
    twoInductionStructure.RelMap Rel.lt ![a, b] ↔ a = b := by
  rfl

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

@[simp] private theorem zero_symbol_value : (zeroSym : Carrier) = true := rfl

private theorem models_axSuccNeZero : Carrier ⊨ axSuccNeZero := by
  simp only [axSuccNeZero, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_imp, BoundedFormula.realize_not, BoundedFormula.realize_bdEqual,
    BoundedFormula.realize_rel₁, isSetBd]
  intro a hnum
  simpa [succTerm, zeroTerm, isSetSym, succSym, zeroSym, Term.realize_var,
    Term.realize_functions_apply₁, Term.realize_constants, twoInductionStructure, funMap,
    relMap] using hnum

private theorem models_axSuccInj : Carrier ⊨ axSuccInj := by
  simp only [axSuccInj, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_imp, BoundedFormula.realize_not, BoundedFormula.realize_bdEqual,
    BoundedFormula.realize_rel₁, isSetBd]
  intro a b _ _ hab
  simpa [succTerm, isSetSym, succSym, Term.realize_var, Term.realize_functions_apply₁,
    twoInductionStructure, funMap, relMap, Fin.snoc_last, Fin.snoc_castSucc] using hab

private theorem models_axAddZero : Carrier ⊨ axAddZero := by
  simp only [axAddZero, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_imp, BoundedFormula.realize_not, BoundedFormula.realize_bdEqual,
    BoundedFormula.realize_rel₁, isSetBd]
  intro a _
  simp [addTerm, zeroTerm, addSym, zeroSym, Term.realize_var,
    Term.realize_functions_apply₂, Term.realize_constants, twoInductionStructure, funMap]

private theorem models_axAddSucc : Carrier ⊨ axAddSucc := by
  simp only [axAddSucc, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_imp, BoundedFormula.realize_not, BoundedFormula.realize_bdEqual,
    BoundedFormula.realize_rel₁, isSetBd]
  intro a b _ _
  simp [addTerm, succTerm, addSym, succSym, Term.realize_var,
    Term.realize_functions_apply₁, Term.realize_functions_apply₂, twoInductionStructure, funMap]

private theorem models_axMulZero : Carrier ⊨ axMulZero := by
  simp only [axMulZero, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_imp, BoundedFormula.realize_not, BoundedFormula.realize_bdEqual,
    BoundedFormula.realize_rel₁, isSetBd]
  intro _ _
  simp [mulTerm, zeroTerm, mulSym, zeroSym, Term.realize_var,
    Term.realize_functions_apply₂, Term.realize_constants, twoInductionStructure, funMap]

private theorem models_axMulSucc : Carrier ⊨ axMulSucc := by
  simp only [axMulSucc, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_imp, BoundedFormula.realize_not, BoundedFormula.realize_bdEqual,
    BoundedFormula.realize_rel₁, isSetBd]
  intro _ b _ _
  simp [mulTerm, addTerm, succTerm, mulSym, addSym, succSym, Term.realize_var,
    Term.realize_functions_apply₁, Term.realize_functions_apply₂, twoInductionStructure, funMap]

private theorem models_axNotLtZero : Carrier ⊨ axNotLtZero := by
  simp only [axNotLtZero, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_imp, BoundedFormula.realize_not, BoundedFormula.realize_rel₁,
    BoundedFormula.realize_rel₂, isSetBd, ltBd]
  intro a hnum
  simpa [zeroTerm, isSetSym, ltSym, zeroSym, Term.realize_var, Term.realize_constants,
    twoInductionStructure, funMap, relMap] using hnum

private theorem models_axLtSuccIff : Carrier ⊨ axLtSuccIff := by
  simp only [axLtSuccIff, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_imp, BoundedFormula.realize_not, BoundedFormula.realize_inf,
    BoundedFormula.realize_sup, BoundedFormula.realize_bdEqual, BoundedFormula.realize_rel₁,
    BoundedFormula.realize_rel₂, isSetBd, ltBd]
  intro a b _ _
  simp [succTerm, ltSym, succSym, Term.realize_var,
    Term.realize_functions_apply₁, twoInductionStructure, funMap, relMap]

/-- The two-element countermodel satisfies every number-relativized Simpson arithmetic axiom. -/
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

private theorem zeroOrSucc_formula_holds (a : Carrier) :
    indFormulaZeroOrSucc.Realize default ![a] := by
  cases a with
  | false =>
      simp [indFormulaZeroOrSucc, boundedZeroOrSuccPredecessorBody, isSetBd, ltBd,
        succTerm, zeroTerm, isSetSym, ltSym, succSym, zeroSym, Term.realize_var,
        Term.realize_functions_apply₁, Term.realize_constants, twoInductionStructure,
        funMap, relMap]
      exact Or.inl (snoc_two_one false false)
  | true =>
      simp [indFormulaZeroOrSucc, boundedZeroOrSuccPredecessorBody, isSetBd, ltBd,
        succTerm, zeroTerm, isSetSym, ltSym, succSym, zeroSym, Term.realize_var,
        Term.realize_functions_apply₁, Term.realize_constants, twoInductionStructure,
        funMap, relMap]

private theorem ltIrrefl_formula_fails (a : Carrier) :
    ¬ indFormulaLtIrrefl.Realize default ![a] := by
  cases a <;>
    simp [indFormulaLtIrrefl, ltBd, ltSym, Term.realize_var, twoInductionStructure, relMap]

/-- The zero-or-successor induction instance holds because its matrix holds at both carrier
elements, independently of the induction premise. -/
theorem models_indFormulaZeroOrSucc : Carrier ⊨ IND indFormulaZeroOrSucc := by
  simp only [IND, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_imp, BoundedFormula.realize_inf, BoundedFormula.realize_not,
    BoundedFormula.realize_rel₁, isSetBd, Substitution.realize_substAll]
  intro _ a _
  simpa only [Matrix.cons_val_zero] using zeroOrSucc_formula_holds a

/-- The irreflexivity induction instance holds vacuously: its base formula is false because the
object-language zero denotes the set element and `<` is equality. -/
theorem models_indFormulaLtIrrefl : Carrier ⊨ IND indFormulaLtIrrefl := by
  simp only [IND, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_imp, BoundedFormula.realize_inf, BoundedFormula.realize_not,
    BoundedFormula.realize_rel₁, isSetBd, Substitution.realize_substAll]
  intro hind
  exfalso
  apply ltIrrefl_formula_fails true
  simpa [zeroTerm, zeroSym, Term.realize_constants, twoInductionStructure, funMap] using hind.1

/-- The two-element structure models the base theory and both named induction instances. -/
theorem models_twoInductionFragment : Carrier ⊨ twoInductionFragment := by
  refine ⟨fun φ hφ => ?_⟩
  rcases hφ with hbase | hind
  · letI : Carrier ⊨ rca0SimpsonBasic := models_simpsonArithmetic
    exact Theory.realize_sentence_of_mem rca0SimpsonBasic hbase
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hind
    rcases hind with rfl | rfl
    · exact models_indFormulaZeroOrSucc
    · exact models_indFormulaLtIrrefl

/-- The same structure refutes the number-relativized irreflexivity sentence at its sole number. -/
theorem not_models_axLtIrrefl : ¬ Carrier ⊨ axLtIrrefl := by
  intro h
  simp only [axLtIrrefl, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_imp, BoundedFormula.realize_not, BoundedFormula.realize_rel₁,
    BoundedFormula.realize_rel₂, isSetBd, ltBd] at h
  have hirr := h false false_is_number
  apply hirr
  simp [ltSym, Term.realize_var, twoInductionStructure, relMap]

end TwoInductionCountermodel

/-- Semantic refutation of the false two-induction strengthening. -/
theorem twoInductionFragment_not_entails_axLtIrrefl :
    ¬ twoInductionFragment ⊨ᵇ axLtIrrefl := by
  intro h
  letI : TwoInductionCountermodel.Carrier ⊨ twoInductionFragment :=
    TwoInductionCountermodel.models_twoInductionFragment
  exact TwoInductionCountermodel.not_models_axLtIrrefl
    (Theory.models_sentence_iff.mp h
      (Theory.ModelType.of twoInductionFragment TwoInductionCountermodel.Carrier))

/-- By soundness, the false irreflexivity target is not derivable from the two-instance theory. -/
theorem twoInductionFragment_not_derives_axLtIrrefl :
    ¬ DerivableFO twoInductionFragment axLtIrrefl := by
  intro h
  exact TwoInductionCountermodel.not_models_axLtIrrefl
    (derivableFO_sound_sentence TwoInductionCountermodel.models_twoInductionFragment h)

namespace BaseInsufficiencyCountermodel

/-- Three elements: the zero object `z`, the sole number `n`, and a set object `s`. -/
abbrev Carrier : Type := Fin 3

def z : Carrier := ⟨0, by omega⟩
def n : Carrier := ⟨1, by omega⟩
def s : Carrier := ⟨2, by omega⟩

def succValue (x : Carrier) : Carrier := if x = n then s else x

def addValue (x y : Carrier) : Carrier :=
  if x = n then if y = s then s else n else x

def mulValue (x y : Carrier) : Carrier :=
  if x = n then if y = z then z else n else x

def funMap : {k : ℕ} → Func k → (Fin k → Carrier) → Carrier
  | _, Func.zero, _ => z
  | _, Func.succ, v => succValue (v 0)
  | _, Func.add, v => addValue (v 0) (v 1)
  | _, Func.mul, v => mulValue (v 0) (v 1)

def relMap : {k : ℕ} → Rel k → (Fin k → Carrier) → Prop
  | _, Rel.lt, v => v 0 = n ∧ v 1 = s
  | _, Rel.mem, _ => False
  | _, Rel.isSet, v => v 0 ≠ n

instance baseInsufficiencyStructure : L2.Structure Carrier where
  funMap := funMap
  RelMap := relMap

instance nonemptyCarrier : Nonempty Carrier := ⟨n⟩

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

@[simp] private theorem zero_symbol_value : (zeroSym : Carrier) = z := rfl

private theorem number_eq_n {a : Carrier}
    (h : ¬ baseInsufficiencyStructure.RelMap Rel.isSet ![a]) : a = n := by
  simpa [baseInsufficiencyStructure, relMap] using h

private theorem models_axSuccNeZero : Carrier ⊨ axSuccNeZero := by
  simp only [axSuccNeZero, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_imp, BoundedFormula.realize_not, BoundedFormula.realize_bdEqual,
    BoundedFormula.realize_rel₁, isSetBd]
  intro a hnum
  have ha : a = n := by
    simpa [baseInsufficiencyStructure, relMap, Fin.snoc] using hnum
  subst a
  simp [succTerm, zeroTerm, succSym, zeroSym, Term.realize_var,
    Term.realize_functions_apply₁, Term.realize_constants, baseInsufficiencyStructure, funMap,
    succValue, z, n, s, Fin.snoc]

private theorem models_axSuccInj : Carrier ⊨ axSuccInj := by
  simp only [axSuccInj, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_imp, BoundedFormula.realize_not, BoundedFormula.realize_bdEqual,
    BoundedFormula.realize_rel₁, isSetBd]
  intro a b ha hb _
  have hb' : b = n := by
    simpa [baseInsufficiencyStructure, relMap, Fin.snoc] using ha
  have ha' : a = n := by
    simpa [baseInsufficiencyStructure, relMap, Fin.snoc] using hb
  simpa [Term.realize_var, Fin.snoc] using hb'.trans ha'.symm

private theorem models_axAddZero : Carrier ⊨ axAddZero := by
  simp only [axAddZero, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_imp, BoundedFormula.realize_not, BoundedFormula.realize_bdEqual,
    BoundedFormula.realize_rel₁, isSetBd]
  intro a hnum
  have ha : a = n := by
    simpa [baseInsufficiencyStructure, relMap, Fin.snoc] using hnum
  subst a
  simp [addTerm, zeroTerm, addSym, zeroSym, Term.realize_var,
    Term.realize_functions_apply₂, Term.realize_constants, baseInsufficiencyStructure, funMap,
    addValue, z, n, s, Fin.snoc]

private theorem models_axAddSucc : Carrier ⊨ axAddSucc := by
  simp only [axAddSucc, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_imp, BoundedFormula.realize_not, BoundedFormula.realize_bdEqual,
    BoundedFormula.realize_rel₁, isSetBd]
  intro a b ha hb
  have hb' : b = n := by
    simpa [baseInsufficiencyStructure, relMap, Fin.snoc] using ha
  have ha' : a = n := by
    simpa [baseInsufficiencyStructure, relMap, Fin.snoc] using hb
  subst a
  subst b
  simp [addTerm, succTerm, addSym, succSym, Term.realize_var,
    Term.realize_functions_apply₁, Term.realize_functions_apply₂,
    baseInsufficiencyStructure, funMap, addValue, succValue, n, s, Fin.snoc]

private theorem models_axMulZero : Carrier ⊨ axMulZero := by
  simp only [axMulZero, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_imp, BoundedFormula.realize_not, BoundedFormula.realize_bdEqual,
    BoundedFormula.realize_rel₁, isSetBd]
  intro a hnum
  have ha : a = n := by
    simpa [baseInsufficiencyStructure, relMap, Fin.snoc] using hnum
  subst a
  simp [mulTerm, zeroTerm, mulSym, zeroSym, Term.realize_var,
    Term.realize_functions_apply₂, Term.realize_constants, baseInsufficiencyStructure, funMap,
    mulValue, z, n, Fin.snoc]

private theorem models_axMulSucc : Carrier ⊨ axMulSucc := by
  simp only [axMulSucc, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_imp, BoundedFormula.realize_not, BoundedFormula.realize_bdEqual,
    BoundedFormula.realize_rel₁, isSetBd]
  intro a b ha hb
  have hb' : b = n := by
    simpa [baseInsufficiencyStructure, relMap, Fin.snoc] using ha
  have ha' : a = n := by
    simpa [baseInsufficiencyStructure, relMap, Fin.snoc] using hb
  subst a
  subst b
  simp [mulTerm, addTerm, succTerm, mulSym, addSym, succSym, Term.realize_var,
    Term.realize_functions_apply₁, Term.realize_functions_apply₂,
    baseInsufficiencyStructure, funMap, mulValue, addValue, succValue, z, n, s, Fin.snoc]

private theorem models_axNotLtZero : Carrier ⊨ axNotLtZero := by
  simp only [axNotLtZero, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_imp, BoundedFormula.realize_not, BoundedFormula.realize_rel₁,
    BoundedFormula.realize_rel₂, isSetBd, ltBd]
  intro a hnum
  have ha : a = n := by
    simpa [baseInsufficiencyStructure, relMap, Fin.snoc] using hnum
  subst a
  simp [zeroTerm, ltSym, zeroSym, Term.realize_var, Term.realize_constants,
    baseInsufficiencyStructure, relMap, z, n, s, Fin.snoc]

private theorem models_axLtSuccIff : Carrier ⊨ axLtSuccIff := by
  simp only [axLtSuccIff, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_imp, BoundedFormula.realize_not, BoundedFormula.realize_inf,
    BoundedFormula.realize_sup, BoundedFormula.realize_bdEqual, BoundedFormula.realize_rel₁,
    BoundedFormula.realize_rel₂, isSetBd, ltBd]
  intro a b ha hb
  have hb' : b = n := by
    simpa [baseInsufficiencyStructure, relMap, Fin.snoc] using ha
  have ha' : a = n := by
    simpa [baseInsufficiencyStructure, relMap, Fin.snoc] using hb
  subst a
  subst b
  simp [succTerm, ltSym, succSym, Term.realize_var, Term.realize_functions_apply₁,
    baseInsufficiencyStructure, funMap, relMap, succValue, n, s, Fin.snoc]

/-- The three-element structure satisfies every axiom of the Simpson arithmetic base. -/
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

/-- The sole number is neither the interpreted zero nor the successor of a number, so the base
theory does not force the zero-or-successor sentence. -/
theorem not_models_axZeroOrSucc : ¬ Carrier ⊨ axZeroOrSucc := by
  intro h
  simp only [axZeroOrSucc, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_imp, BoundedFormula.realize_not, BoundedFormula.realize_sup,
    BoundedFormula.realize_ex, BoundedFormula.realize_inf, BoundedFormula.realize_bdEqual,
    BoundedFormula.realize_rel₁, BoundedFormula.realize_rel₂, isSetBd, ltBd] at h
  have hn := h n
  have hnNumber : ¬ baseInsufficiencyStructure.RelMap Rel.isSet ![n] := by
    simp [baseInsufficiencyStructure, relMap]
  rcases hn hnNumber with hz | ⟨a, haNumber, hsucc, _⟩
  · simp [zeroTerm, zeroSym, Term.realize_constants, baseInsufficiencyStructure, z, n,
      Fin.snoc] at hz
  · have ha : a = n := by
      simpa [baseInsufficiencyStructure, relMap, Fin.snoc] using haNumber
    subst a
    simp [succTerm, succSym, Term.realize_var, Term.realize_functions_apply₁,
      baseInsufficiencyStructure, funMap, succValue, n, s, Fin.snoc]
      at hsucc

end BaseInsufficiencyCountermodel

/-- The number-relativized Simpson base does not semantically entail zero-or-successor. -/
theorem simpsonArithmetic_not_entails_zeroOrSucc :
    ¬ rca0SimpsonBasic ⊨ᵇ axZeroOrSucc := by
  intro h
  letI : BaseInsufficiencyCountermodel.Carrier ⊨ rca0SimpsonBasic :=
    BaseInsufficiencyCountermodel.models_simpsonArithmetic
  exact BaseInsufficiencyCountermodel.not_models_axZeroOrSucc
    (Theory.models_sentence_iff.mp h
      (Theory.ModelType.of rca0SimpsonBasic BaseInsufficiencyCountermodel.Carrier))

/-- By soundness, the number-relativized Simpson base cannot derive zero-or-successor. -/
theorem simpsonArithmetic_not_derives_zeroOrSucc :
    ¬ DerivableFO rca0SimpsonBasic axZeroOrSucc := by
  intro h
  exact BaseInsufficiencyCountermodel.not_models_axZeroOrSucc
    (derivableFO_sound_sentence BaseInsufficiencyCountermodel.models_simpsonArithmetic h)

end OperatorKO7.ReverseMath
