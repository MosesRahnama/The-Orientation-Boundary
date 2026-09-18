import OperatorKO7.Meta.Methods.OrientationClosure.AttainedPairs
import OperatorKO7.Meta.RDRSSemanticArbitraryClassifier
import OperatorKO7.Meta.RDRSSemanticCertificate

set_option autoImplicit false

/-!
# Orientation Boundary publication capstone

This module packages three paper-facing consequences of theorem families that
are already present in the Orientation Boundary development.  It introduces no
new measure language, rewrite relation, semantic carrier, or decision problem.
-/

namespace OperatorKO7.Methods.OrientationClosure.OrientationBoundaryPublicationCapstone

open OperatorKO7.Methods.OrientationClosure.SchemaCore
open OperatorKO7.Methods.OrientationClosure.AttainedPairs
open OperatorKO7.Meta.BoundaryGeneral.DirectMeasureGrammarClosure
open OperatorKO7.RDRSDescentLens
open OperatorKO7.RDRSSemanticArbitraryClassifier
open OperatorKO7.RDRSSemanticCertificate

/--
Proves: for every expression in the reflected scalar measure grammar, uniform
orientation of every actual free-recursor successor root instance is equivalent
to payload blindness together with strict counter response.
Does not prove: contextual termination, confluence, or orientation by measures
outside the reflected scalar grammar.
Relation: free-recursor successor instances represented by `FreeTerm` and the
successor constructor of `RootStep`.
Closure: root single-step.
Strategy: not applicable.
Trust: Lean kernel with the foundational axioms inherited from the two imported
characterization theorems.
Scope: every `MeasureExpr` in `DirectMeasureGrammarClosure`.
-/
theorem free_successor_orientation_iff_payloadBlind_and_counterStrict
    (e : MeasureExpr) :
    (∀ {ν : Type} (b s n : FreeTerm ν),
      profileMeasure e.eval (.wrap s (.recur b s n)) <
        profileMeasure e.eval (.recur b s (.succ n))) ↔
      PayloadBlind e.eval ∧ CounterStrict e.eval := by
  constructor
  · intro h
    exact (orients_iff_payloadBlind_and_counterStrict e).1
      ((profile_orients_successors_iff e.eval).1 h)
  · intro h
    exact (profile_orients_successors_iff e.eval).2
      ((orients_iff_payloadBlind_and_counterStrict e).2 h)

/--
Proves: on the counter-admissible subclass of the reflected scalar grammar,
uniform orientation of every actual free-recursor successor root instance is
equivalent to payload blindness.
Does not prove: that counter admissibility follows from payload blindness.
Relation: free-recursor successor instances represented by `FreeTerm` and the
successor constructor of `RootStep`.
Closure: root single-step.
Strategy: not applicable.
Trust: Lean kernel with the foundational axioms inherited from the two imported
biconditionals.
Scope: every `MeasureExpr e` with `CounterAdmissible e`.
-/
theorem free_successor_counterAdmissible_orients_iff_payloadBlind
    (e : MeasureExpr) (hadmissible : CounterAdmissible e) :
    (∀ {ν : Type} (b s n : FreeTerm ν),
      profileMeasure e.eval (.wrap s (.recur b s n)) <
        profileMeasure e.eval (.recur b s (.succ n))) ↔
      PayloadBlind e.eval := by
  constructor
  · intro h
    exact (counterAdmissible_orients_iff_payloadBlind e hadmissible).1
      ((profile_orients_successors_iff e.eval).1 h)
  · intro h
    exact (profile_orients_successors_iff e.eval).2
      ((counterAdmissible_orients_iff_payloadBlind e hadmissible).2 h)

/--
Proves: a payload-erasing RDRS step admits no decisive payload-sensitive
orientation certificate of the declared certificate type.
Does not prove: source-system termination or a syntactic classification of raw
Lean functions.
Relation: an abstract `RDRSStep B S N T` equipped with `PayloadErasure R`.
Closure: root single-step.
Strategy: not applicable.
Trust: kernel-only; the two imported semantic declarations used here have no
axioms in their current Lean proof closure.
Scope: every supplied payload erasure and every
`DecisivePayloadSensitiveCertificate R`.
-/
theorem no_decisive_certificate_of_payload_erasure
    {B S N T : Type} {R : RDRSStep B S N T}
    (E : PayloadErasure R) :
    DecisivePayloadSensitiveCertificate R → False := by
  intro C
  exact
    (no_decisive_payload_sensitive_of_payload_erasure E
      C.toSemanticOrientationCertificate.measure.data) C.toDecisive

end OperatorKO7.Methods.OrientationClosure.OrientationBoundaryPublicationCapstone
