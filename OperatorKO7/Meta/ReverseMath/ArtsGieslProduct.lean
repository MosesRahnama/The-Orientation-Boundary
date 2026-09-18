import OperatorKO7.Meta.ReverseMath.ArtsGieslFaithful
import OperatorKO7.Meta.ReverseMath.ArtsGieslKO7Bridge
import OperatorKO7.Meta.ReverseMath.DeductionFO

/-!
# Product record for predecessor descent, an `ω³` order, and KO7 rank descent

The record in this module groups five independently typed facts: the `Π⁰₂` shape and derivability of
the predecessor-descent sentence, a canonical well-order of type `ω³`, standard-model faithfulness
for the predecessor sentence, and a KO7 dependency-pair well-foundedness implication from a generic
natural-number measure principle. The record does not prove that the predecessor sentence expresses
Arts-Giesl dependency-pair soundness, and it does not prove an SCT reverse-mathematics equivalence.
-/

set_option autoImplicit false

namespace OperatorKO7.ReverseMath

open FirstOrder Language

/-- A conjunction-style record parameterized by the theory `T`. Its fields concern the historically
named predecessor sentence, a canonical `ω³` order, and the KO7 rank-descent implication. No field
identifies these components as an SCT equivalence. -/
structure ArtsGieslOmega3ProductTheorem (T : L2.Theory) : Prop where
  /-- The predecessor-descent sentence is structurally `Π⁰₂`. -/
  pi02 : Complexity.IsPi02 ArtsGieslSctSoundnessFormula
  /-- `T` derives the predecessor-descent sentence in the first-order calculus. -/
  upper : DeductionFO.DerivableFO T ArtsGieslSctSoundnessFormula
  /-- Well-foundedness and order-type equality for the canonical `ω³` carrier. -/
  omega3Descriptor : OperatorKO7.ReverseMathOmega3.WOOmega3Backing
  /-- Standard-model satisfaction is equivalent to the elementary natural-number property. -/
  soundnessFaithful :
    (StdCarrier ⊨ ArtsGieslSctSoundnessFormula) ↔ ActualArtsGieslSctSoundness
  /-- A generic natural-number measure-descent principle implies well-foundedness of `DPPairRev`. -/
  ko7Bridge :
    SctDescentSoundness.{0} → WellFounded OperatorKO7.MetaDependencyPairs.DPPairRev

/-- Assemble the record from a supplied derivation of the predecessor sentence and the four imported
component theorems. -/
theorem artsGieslOmega3Product_of_upper (T : L2.Theory)
    (upper : DeductionFO.DerivableFO T ArtsGieslSctSoundnessFormula) :
    ArtsGieslOmega3ProductTheorem T where
  pi02 := artsGieslSctSoundness_isPi02
  upper := upper
  omega3Descriptor := OperatorKO7.ReverseMathOmega3.wo_omega3_backing
  soundnessFaithful := artsGieslSctSoundness_faithful
  ko7Bridge := actualSctSoundness_certifies_ko7_recursor

#check ArtsGieslOmega3ProductTheorem
#check artsGieslOmega3Product_of_upper
#print axioms artsGieslOmega3Product_of_upper

end OperatorKO7.ReverseMath
