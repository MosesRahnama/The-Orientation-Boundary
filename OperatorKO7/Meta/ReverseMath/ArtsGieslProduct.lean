import OperatorKO7.Meta.ReverseMath.ArtsGieslFaithful
import OperatorKO7.Meta.ReverseMath.ArtsGieslKO7Bridge
import OperatorKO7.Meta.ReverseMath.DeductionFO

/-!
# The Arts–Giesl `ω³` product theorem (assembly)

This module assembles the `ArtsGieslOmega3ProductTheorem` of the roadmap from the genuinely-proven
component theorems. The product is the order-*descriptor* calibration (NOT a fake reversal): it
bundles the structural `Π⁰₂` classification, the upper derivability, the genuine `WO(ω³)` order
descriptor, the standard-model faithfulness bridge, and the KO7-recursor relevance bridge (R2).

## What is proven unconditionally here

Four of the five fields are discharged by real, kernel-checked, baseline-axiom-only theorems built in
this directory:

* `pi02` ← `artsGieslSctSoundness_isPi02` (structural recursion on the formula, not a metadata tag);
* `omega3Descriptor` ← `ReverseMathOmega3.wo_omega3_backing` (genuine `WellFounded` + order-type `ω³`);
* `soundnessFaithful` ← `artsGieslSctSoundness_faithful` (standard-model satisfaction ↔ the actual
  arithmetical property);
* `ko7Bridge` ← `actualSctSoundness_certifies_ko7_recursor` (the SCT principle certifies the actual
  KO7 duplicating recursor `DPPairRev`, non-vacuously).

## The upper field

`upper : DerivableFO T ArtsGieslSctSoundnessFormula` is the object-derivation upper bound (roadmap R1,
route (a)): a literal Hilbert-style proof in the sound first-order calculus `DeductionFO` (which, via
its `all_intro`/`spec`/`ex_intro` rules, can derive the quantified `∀∃` sentence — the propositional
`Deduction.Derivable` cannot). It is parameterized over the theory `T` here, so the product is proven
for **any** theory given its upper derivation; `ArtsGieslUpperSyntactic.lean` discharges it for
`T := rca0BasicAxioms` with the genuine object derivation `artsGiesl_syntactic_upper`, yielding the
fully syntactic product `artsGieslOmega3Product_rca0`.

No `sorry`, `axiom`, or `native_decide`.
-/

set_option autoImplicit false

namespace OperatorKO7.ReverseMath

open FirstOrder Language

/-- The Arts–Giesl `ω³` product theorem, parameterized over the object theory `T`. The order
*descriptor* calibration: structural `Π⁰₂` classification, upper derivability of the SCT/AG soundness
sentence from `T`, the genuine `WO(ω³)` order descriptor, the standard-model faithfulness bridge, and
the KO7-recursor relevance bridge. -/
structure ArtsGieslOmega3ProductTheorem (T : L2.Theory) : Prop where
  /-- The SCT/AG soundness sentence is `Π⁰₂` (genuine structural classification). -/
  pi02 : Complexity.IsPi02 ArtsGieslSctSoundnessFormula
  /-- `T` derives the SCT/AG soundness sentence (object-level upper bound, first-order calculus). -/
  upper : DeductionFO.DerivableFO T ArtsGieslSctSoundnessFormula
  /-- The `WO(ω³)` order descriptor: a genuine well-ordering of order type exactly `ω³`. -/
  omega3Descriptor : OperatorKO7.ReverseMathOmega3.WOOmega3Backing
  /-- Faithfulness: standard-model satisfaction of the sentence is exactly the actual property. -/
  soundnessFaithful :
    (StdCarrier ⊨ ArtsGieslSctSoundnessFormula) ↔ ActualArtsGieslSctSoundness
  /-- KO7 relevance (R2): the SCT soundness principle certifies the actual KO7 recursor. -/
  ko7Bridge :
    SctDescentSoundness.{0} → WellFounded OperatorKO7.MetaDependencyPairs.DPPairRev

/-- **Product assembly.** For any object theory `T` that derives the SCT/AG soundness sentence, the
full `ArtsGieslOmega3ProductTheorem T` holds: the other four fields are discharged unconditionally by
the component theorems of this directory. Specialize `T := RCA0` once the upper derivation lands. -/
theorem artsGieslOmega3Product_of_upper (T : L2.Theory)
    (upper : DeductionFO.DerivableFO T ArtsGieslSctSoundnessFormula) :
    ArtsGieslOmega3ProductTheorem T where
  pi02 := artsGieslSctSoundness_isPi02
  upper := upper
  omega3Descriptor := OperatorKO7.ReverseMathOmega3.wo_omega3_backing
  soundnessFaithful := artsGieslSctSoundness_faithful
  ko7Bridge := actualSctSoundness_certifies_ko7_recursor

end OperatorKO7.ReverseMath
