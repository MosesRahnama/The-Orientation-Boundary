import OperatorKO7.Meta.ReverseMath.ArtsGieslProduct
import OperatorKO7.Meta.ReverseMath.ArtsGieslUpperSemantic

/-!
This module packages five imported facts about the predecessor-descent sentence, a canonical
omega-cubed order, and a KO7 rank implication. The conjunction record preserves the scope of
those component theorems.



-/

set_option autoImplicit false

namespace OperatorKO7.ReverseMath

open FirstOrder Language

/-- Data record whose requirements are the fields displayed below.
-/
structure ArtsGieslOmega3ProductSemantic : Prop where
  /-- Field requirements are given by the displayed type. -/
  pi02 : Complexity.IsPi02 ArtsGieslSctSoundnessFormula
  /-- Field requirements are given by the displayed type. -/
  upperSemantic : rca0BasicAxioms ⊨ᵇ ArtsGieslSctSoundnessFormula
  /-- Field requirements are given by the displayed type. -/
  omega3Descriptor : OperatorKO7.ReverseMathOmega3.WOOmega3Backing
  /-- Field requirements are given by the displayed type. -/
  soundnessFaithful :
    (StdCarrier ⊨ ArtsGieslSctSoundnessFormula) ↔ ActualArtsGieslSctSoundness
  /-- Field requirements are given by the displayed type. -/
  ko7Bridge :
    SctDescentSoundness.{0} → WellFounded OperatorKO7.MetaDependencyPairs.DPPairRev

/-- The displayed proposition follows from the stated hypotheses. -/
theorem artsGieslOmega3ProductSemantic_holds : ArtsGieslOmega3ProductSemantic where
  pi02 := artsGieslSctSoundness_isPi02
  upperSemantic := rca0_modelsBoundedFormula_sct
  omega3Descriptor := OperatorKO7.ReverseMathOmega3.wo_omega3_backing
  soundnessFaithful := artsGieslSctSoundness_faithful
  ko7Bridge := actualSctSoundness_certifies_ko7_recursor

#check ArtsGieslOmega3ProductSemantic
#check artsGieslOmega3ProductSemantic_holds
#print axioms artsGieslOmega3ProductSemantic_holds

end OperatorKO7.ReverseMath
