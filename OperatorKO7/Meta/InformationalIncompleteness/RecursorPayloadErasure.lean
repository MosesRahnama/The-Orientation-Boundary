import OperatorKO7.Meta.RDRSSemanticArbitraryClassifier

/-!
This module studies a single counter-first relation on pairs of natural numbers. Theorems
construct a counter-only ranking for that relation and show payload-insensitive decrease for the
constructed measure. General method-independence requires a separate quantified transport
theorem.
























-/

set_option autoImplicit false

namespace OperatorKO7.Meta.InformationalIncompleteness.RecursorPayloadErasure

open OperatorKO7.RDRSDescentLens
open OperatorKO7.RDRSSemanticDirectMeasure
open OperatorKO7.RDRSSemanticPayloadSensitivity
open OperatorKO7.RDRSSemanticNormalizedRawSyntax
open OperatorKO7.RDRSSemanticArbitraryClassifier

/-- Abbreviation for the displayed type.


-/
abbrev iiRecursor : RDRSStep Unit Nat Nat (Nat × Nat) := counterFirstLexRaw_R

/-- Definition with formal content given by the displayed type and body.








-/
def iiRecursorPayloadErasure : PayloadErasure iiRecursor :=
  counterFirstLexPayloadErasure

/-- The displayed proposition follows from the stated hypotheses.











-/
theorem iiRecursor_orienting_measure_counter_dominated
    (M : SemanticMeasureData (Nat × Nat))
    (hOrient : Orients iiRecursor M.μ M.ltA) :
    CounterDominated iiRecursor M :=
  counterFirstLex_arbitrary_orienting_measure_counter_dominated M hOrient

/-- The displayed proposition follows from the stated hypotheses.










-/
theorem iiRecursor_no_decisive_payload_sensitive
    (M : SemanticMeasureData (Nat × Nat)) :
    ¬ PayloadSensitiveDecisive iiRecursor M :=
  counterFirstLex_no_arbitrary_decisive_payload_sensitive M

/-- Definition with formal content given by the displayed type and body. -/
def recursor_payload_erasure_anchor : String :=
  "OperatorKO7.Meta.InformationalIncompleteness.RecursorPayloadErasure.iiRecursor_orienting_measure_counter_dominated"

end OperatorKO7.Meta.InformationalIncompleteness.RecursorPayloadErasure
