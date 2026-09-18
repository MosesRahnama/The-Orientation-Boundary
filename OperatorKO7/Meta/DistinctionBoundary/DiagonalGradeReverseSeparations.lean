import OperatorKO7.Meta.DistinctionBoundary.IndexedDiagonalGrade

set_option autoImplicit false

/-!
# Semantic reverse-separation fixtures for diagonal grades

The numeric `IndexedDiagonalGrade` tower is an interface ledger. This module
supplies four carrier-and-interface witnesses for the semantic non-implications
that the ledger alone cannot establish.

Relation: not applicable.
Closure: capability interfaces stated below.
Strategy: not applicable.
External trust: none.
-/

namespace OperatorKO7.Meta.DistinctionBoundary.DiagonalGradeReverseSeparations

/-- A quotation surface is faithful when quotation is injective. -/
def FaithfulQuote {A Code : Type} (quote : A → Code) : Prop :=
  ∀ ⦃x y⦄, quote x = quote y → x = y

/-- The diagonal law of a self-evaluation interface. -/
def SelfEvaluationLaw {A Code : Type}
    (quote : A → Code) (eval : Code → A → A) (diag : Code → A) : Prop :=
  ∀ x, diag (quote x) = eval (quote x) x

/-- An evaluator is universal for the named represented class. -/
def UniversalEvaluation {Code Arg Val : Type}
    (Represented : (Arg → Val) → Prop) (eval : Code → Arg → Val) : Prop :=
  ∀ f, Represented f → ∃ code, ∀ x, eval code x = f x

/-- A unary represented class is closed under composition. -/
def RepresentationClosed {A : Type} (Represented : (A → A) → Prop) : Prop :=
  ∀ f g, Represented f → Represented g → Represented (fun x => f (g x))

/-- A Bool-valued comparator is sound and complete for equality. -/
def BooleanEqualityComparator {A : Type} (test : A → A → Bool) : Prop :=
  (∀ a b, test a b = true → a = b) ∧ (∀ a, test a a = true)

/-! ## Self-evaluation does not force faithful diagonal syntax -/

def lossyQuote : Bool → Unit := fun _ => ()

def lossyEval : Unit → Bool → Bool := fun _ _ => false

def lossyDiag : Unit → Bool := fun _ => false

theorem lossy_selfEvaluationLaw :
    SelfEvaluationLaw lossyQuote lossyEval lossyDiag := by
  intro x
  rfl

theorem lossyQuote_not_faithful : ¬ FaithfulQuote lossyQuote := by
  intro h
  have htf : (true : Bool) = false := h rfl
  cases htf

/-- First missing reverse certificate: a self-evaluation diagonal law can hold
while the quotation surface identifies distinct carrier elements. -/
theorem selfEvaluation_without_faithfulDiagonalSyntax :
    SelfEvaluationLaw lossyQuote lossyEval lossyDiag ∧
      ¬ FaithfulQuote lossyQuote :=
  ⟨lossy_selfEvaluationLaw, lossyQuote_not_faithful⟩

/-! ## Universal evaluation does not force a shared self-evaluation carrier -/

def separatedUniversalEval : Bool → Unit → Bool := fun code _ => code

def AllUnitBool (_f : Unit → Bool) : Prop := True

/-- Shared-carrier self-evaluation needs, at minimum, an identification of the
code and argument carriers. -/
def CodeArgumentIdentification (Code Arg : Type) : Prop :=
  ∃ toArg : Code → Arg, ∃ toCode : Arg → Code,
    (∀ code, toCode (toArg code) = code) ∧
      (∀ arg, toArg (toCode arg) = arg)

theorem separatedUniversalEval_universal :
    UniversalEvaluation AllUnitBool separatedUniversalEval := by
  intro f _
  refine ⟨f (), ?_⟩
  intro x
  cases x
  rfl

theorem bool_unit_no_codeArgumentIdentification :
    ¬ CodeArgumentIdentification Bool Unit := by
  rintro ⟨toArg, toCode, hleft, _hright⟩
  have harg : toArg true = toArg false := Subsingleton.elim _ _
  have htf : (true : Bool) = false := by
    calc
      true = toCode (toArg true) := (hleft true).symm
      _ = toCode (toArg false) := congrArg toCode harg
      _ = false := hleft false
  cases htf

/-- Second missing reverse certificate: universal evaluation exists on a
separate code/value interface while code and argument carriers have no
two-sided identification needed for shared-carrier self-evaluation. -/
theorem universalEvaluation_without_selfEvaluationCarrier :
    UniversalEvaluation AllUnitBool separatedUniversalEval ∧
      ¬ CodeArgumentIdentification Bool Unit :=
  ⟨separatedUniversalEval_universal, bool_unit_no_codeArgumentIdentification⟩

/-! ## Representation closure does not force universal evaluation -/

def AllBoolEndomaps (_f : Bool → Bool) : Prop := True

theorem allBoolEndomaps_closed : RepresentationClosed AllBoolEndomaps := by
  intro f g _ _
  trivial

/-- A one-code evaluator cannot represent every Bool endomap. -/
theorem no_unitCode_universal_boolEndomaps :
    ¬ ∃ eval : Unit → Bool → Bool, UniversalEvaluation AllBoolEndomaps eval := by
  rintro ⟨eval, hU⟩
  obtain ⟨cId, hId⟩ := hU (fun b : Bool => b) trivial
  obtain ⟨cNeg, hNeg⟩ := hU (fun b : Bool => !b) trivial
  have hc : cId = cNeg := Subsingleton.elim _ _
  have h0 := hId false
  have h1 := hNeg false
  rw [hc] at h0
  simp at h1
  rw [h0] at h1
  cases h1

/-- Third missing reverse certificate: the full Bool endomap class is closed
under composition, while a fixed one-code evaluator is incapable of universal
coverage of that class. -/
theorem representationClosure_without_universalEvaluation :
    RepresentationClosed AllBoolEndomaps ∧
      ¬ ∃ eval : Unit → Bool → Bool, UniversalEvaluation AllBoolEndomaps eval :=
  ⟨allBoolEndomaps_closed, no_unitCode_universal_boolEndomaps⟩

/-! ## Boolean comparison does not force representation closure -/

def boolEqualityTest (a b : Bool) : Bool := decide (a = b)

theorem boolEqualityTest_correct : BooleanEqualityComparator boolEqualityTest := by
  constructor
  · intro a b h
    exact of_decide_eq_true h
  · intro a
    exact decide_eq_true rfl

def NegationOnly (f : Bool → Bool) : Prop :=
  f = fun b => !b

theorem negationOnly_not_closed : ¬ RepresentationClosed NegationOnly := by
  intro hClosed
  have h := hClosed (fun b : Bool => !b) (fun b : Bool => !b) rfl rfl
  have h0 := congrFun h false
  simp at h0

/-- Fourth missing reverse certificate: a correct equality comparator exists on
Bool while the named represented class containing only negation fails closure
under composition. -/
theorem booleanComparison_without_representationClosure :
    BooleanEqualityComparator boolEqualityTest ∧
      ¬ RepresentationClosed NegationOnly :=
  ⟨boolEqualityTest_correct, negationOnly_not_closed⟩

#check @FaithfulQuote
#check @SelfEvaluationLaw
#check @UniversalEvaluation
#check @RepresentationClosed
#check @BooleanEqualityComparator
#check @lossyQuote
#check @lossyEval
#check @lossyDiag
#check @lossy_selfEvaluationLaw
#check @lossyQuote_not_faithful
#check @selfEvaluation_without_faithfulDiagonalSyntax
#check @separatedUniversalEval
#check @AllUnitBool
#check @CodeArgumentIdentification
#check @separatedUniversalEval_universal
#check @bool_unit_no_codeArgumentIdentification
#check @universalEvaluation_without_selfEvaluationCarrier
#check @AllBoolEndomaps
#check @allBoolEndomaps_closed
#check @no_unitCode_universal_boolEndomaps
#check @representationClosure_without_universalEvaluation
#check @boolEqualityTest
#check @boolEqualityTest_correct
#check @NegationOnly
#check @negationOnly_not_closed
#check @booleanComparison_without_representationClosure

#print axioms FaithfulQuote
#print axioms SelfEvaluationLaw
#print axioms UniversalEvaluation
#print axioms RepresentationClosed
#print axioms BooleanEqualityComparator
#print axioms lossyQuote
#print axioms lossyEval
#print axioms lossyDiag
#print axioms lossy_selfEvaluationLaw
#print axioms lossyQuote_not_faithful
#print axioms selfEvaluation_without_faithfulDiagonalSyntax
#print axioms separatedUniversalEval
#print axioms AllUnitBool
#print axioms CodeArgumentIdentification
#print axioms separatedUniversalEval_universal
#print axioms bool_unit_no_codeArgumentIdentification
#print axioms universalEvaluation_without_selfEvaluationCarrier
#print axioms AllBoolEndomaps
#print axioms allBoolEndomaps_closed
#print axioms no_unitCode_universal_boolEndomaps
#print axioms representationClosure_without_universalEvaluation
#print axioms boolEqualityTest
#print axioms boolEqualityTest_correct
#print axioms NegationOnly
#print axioms negationOnly_not_closed
#print axioms booleanComparison_without_representationClosure

end OperatorKO7.Meta.DistinctionBoundary.DiagonalGradeReverseSeparations
