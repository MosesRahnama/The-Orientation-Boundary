import OperatorKO7.Meta.ReverseMath.Language
import OperatorKO7.Meta.ReverseMath.Complexity

/-!
This module defines an elementary predecessor-descent sentence and proves its structural Pi02
and prenex forms. The historical identifier is retained for compatibility; the formal sentence
concerns predecessor descent.







-/

set_option autoImplicit false

namespace OperatorKO7.ReverseMath

open FirstOrder Language

/-- Definition with formal content given by the displayed type and body.

-/
def sctMatrix : L2.BoundedFormula Empty 2 :=
  (∼ (isSetBd (&0))) ⟹ ((∼ (isSetBd (&1))) ⊓ (ltBd (&1) (&0) ⊔ Term.bdEqual (&0) zeroTerm))

/-- The displayed proposition follows from the stated hypotheses. -/
theorem sctMatrix_isQF : sctMatrix.IsQF := by
  unfold sctMatrix
  exact (Relations.isQF _ _).not.imp
    ((Relations.isQF _ _).not.inf ((ltBd_isQF _ _).sup (BoundedFormula.IsAtomic.equal _ _).isQF))

/-- Definition with formal content given by the displayed type and body.

-/
def ArtsGieslSctSoundnessFormula : L2.Sentence := ∀' ∃' sctMatrix

/-- The displayed proposition follows from the stated hypotheses.
-/
theorem artsGieslSctSoundness_isPi02 :
    Complexity.IsPi02 ArtsGieslSctSoundnessFormula :=
  Complexity.IsQF.all_ex_isPi02 sctMatrix_isQF

/-- The displayed proposition follows from the stated hypotheses. -/
theorem artsGieslSctSoundness_isPrenex :
    ArtsGieslSctSoundnessFormula.IsPrenex :=
  Complexity.IsPi02.isPrenex artsGieslSctSoundness_isPi02

end OperatorKO7.ReverseMath
