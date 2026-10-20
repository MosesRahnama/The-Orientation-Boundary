import OperatorKO7.Meta.ReverseMath.Language
import OperatorKO7.Meta.ReverseMath.Complexity

/-!
This module defines the elementary predecessor-descent sentence and proves its structural Pi02
and prenex forms. The canonical identifiers are `numberPredecessorDescentMatrix` and
`numberPredecessorDescentSentence`; the historical identifiers `sctMatrix` and
`ArtsGieslSctSoundnessFormula` are compatibility aliases and do not formalize dependency-pair
soundness or size-change termination soundness.
-/

set_option autoImplicit false

namespace OperatorKO7.ReverseMath

open FirstOrder Language

/-- The matrix of the predecessor-descent sentence: `¬IsSet x → (¬IsSet y ∧ (y < x ∨ x = 0))`.
This is the canonical name. The historical identifier `sctMatrix` is a compatibility alias; it does
not formalize dependency-pair soundness or size-change termination soundness. -/
def numberPredecessorDescentMatrix : L2.BoundedFormula Empty 2 :=
  (∼ (isSetBd (&0))) ⟹ ((∼ (isSetBd (&1))) ⊓ (ltBd (&1) (&0) ⊔ Term.bdEqual (&0) zeroTerm))

/-- Compatibility alias for `numberPredecessorDescentMatrix`: a naming artefact of the earlier
size-change-termination reading, not a formalization of dependency-pair soundness. -/
def sctMatrix : L2.BoundedFormula Empty 2 := numberPredecessorDescentMatrix

/-- The canonical name for the elementary predecessor-descent sentence
`∀x ∃y, ¬IsSet x → (¬IsSet y ∧ (y < x ∨ x = 0))`. It is not the Arts-Giesl dependency-pair
soundness theorem and not an SCT soundness principle. -/
def numberPredecessorDescentSentence : L2.Sentence := ∀' ∃' numberPredecessorDescentMatrix

/-- Compatibility alias for `numberPredecessorDescentSentence`: a naming artefact of the earlier
size-change-termination reading, not a formalization of dependency-pair soundness. -/
def ArtsGieslSctSoundnessFormula : L2.Sentence := numberPredecessorDescentSentence

/-- The predecessor-descent matrix is quantifier-free. -/
theorem numberPredecessorDescentMatrix_isQF : numberPredecessorDescentMatrix.IsQF := by
  unfold numberPredecessorDescentMatrix
  exact (Relations.isQF _ _).not.imp
    ((Relations.isQF _ _).not.inf ((ltBd_isQF _ _).sup (BoundedFormula.IsAtomic.equal _ _).isQF))

/-- Compatibility alias of `numberPredecessorDescentMatrix_isQF`. -/
theorem sctMatrix_isQF : sctMatrix.IsQF := numberPredecessorDescentMatrix_isQF

/-- The predecessor-descent sentence is `Π⁰₂` (a `∀∃` over a quantifier-free matrix). -/
theorem numberPredecessorDescentSentence_isPi02 :
    Complexity.IsPi02 numberPredecessorDescentSentence :=
  Complexity.IsQF.all_ex_isPi02 numberPredecessorDescentMatrix_isQF

/-- Compatibility alias of `numberPredecessorDescentSentence_isPi02`. -/
theorem artsGieslSctSoundness_isPi02 :
    Complexity.IsPi02 ArtsGieslSctSoundnessFormula :=
  numberPredecessorDescentSentence_isPi02

/-- The predecessor-descent sentence is in prenex normal form. -/
theorem numberPredecessorDescentSentence_isPrenex :
    numberPredecessorDescentSentence.IsPrenex :=
  Complexity.IsPi02.isPrenex numberPredecessorDescentSentence_isPi02

/-- Compatibility alias of `numberPredecessorDescentSentence_isPrenex`. -/
theorem artsGieslSctSoundness_isPrenex :
    ArtsGieslSctSoundnessFormula.IsPrenex :=
  numberPredecessorDescentSentence_isPrenex

end OperatorKO7.ReverseMath
