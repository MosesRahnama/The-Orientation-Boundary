import OperatorKO7.Meta.Methods.OrientationClosure.AttainedPairs
import OperatorKO7.Meta.RDRSSemanticArbitraryClassifier
import OperatorKO7.Meta.RDRSSemanticCertificate

set_option autoImplicit false

/-!
# Orientation Boundary publication capstone

This module packages three paper-facing consequences of theorem families that
are already present in the Orientation Boundary development.  It introduces no
new measure language, rewrite relation, semantic carrier, or decision problem.
The two boundary biconditionals hold at each variable type of the free
recursor separately; the form quantified over every variable type at once is a
corollary.
-/

namespace OperatorKO7.Methods.OrientationClosure.OrientationBoundaryPublicationCapstone

open OperatorKO7.Methods.OrientationClosure.SchemaCore
open OperatorKO7.Methods.OrientationClosure.AttainedPairs
open OperatorKO7.Meta.BoundaryGeneral.DirectMeasureGrammarClosure
open OperatorKO7.RDRSDescentLens
open OperatorKO7.RDRSSemanticArbitraryClassifier
open OperatorKO7.RDRSSemanticCertificate

/--
Proves: at every variable type `ν`, for every expression in the reflected scalar
measure grammar, orientation of every actual successor root instance of
`FreeTerm ν` by the profile measure is equivalent to payload blindness together
with strict counter response.
Does not prove: contextual termination, confluence, or orientation by measures
outside the reflected scalar grammar.
Relation: free-recursor successor instances on `FreeTerm ν`, the pair shape of
the successor constructor of `RootStep`.
Closure: root single-step.
Strategy: not applicable.
Trust: Lean kernel with the foundational axioms inherited from the two imported
characterization theorems.
Scope: every `ν : Type` and every `MeasureExpr` in `DirectMeasureGrammarClosure`.
-/
theorem free_successor_orientation_iff_payloadBlind_and_counterStrict
    {ν : Type} (e : MeasureExpr) :
    (∀ b s n : FreeTerm ν,
      profileMeasure e.eval (.wrap s (.recur b s n)) <
        profileMeasure e.eval (.recur b s (.succ n))) ↔
      PayloadBlind e.eval ∧ CounterStrict e.eval :=
  (profile_orients_successors_iff e.eval).trans
    (orients_iff_payloadBlind_and_counterStrict e)

/--
Proves: for every expression in the reflected scalar measure grammar,
orientation of every actual successor root instance of `FreeTerm ν` at every
variable type `ν` at once is equivalent to payload blindness together with
strict counter response.
Does not prove: anything beyond the per-carrier biconditional
`free_successor_orientation_iff_payloadBlind_and_counterStrict`, from which it
follows.
Relation: free-recursor successor instances on `FreeTerm ν`, every `ν`.
Closure: root single-step.
Strategy: not applicable.
Trust: Lean kernel with the axioms of the per-carrier biconditional.
Scope: every `MeasureExpr` in `DirectMeasureGrammarClosure`.
-/
theorem free_successor_orientation_allCarriers_iff_payloadBlind_and_counterStrict
    (e : MeasureExpr) :
    (∀ {ν : Type} (b s n : FreeTerm ν),
      profileMeasure e.eval (.wrap s (.recur b s n)) <
        profileMeasure e.eval (.recur b s (.succ n))) ↔
      PayloadBlind e.eval ∧ CounterStrict e.eval := by
  constructor
  · intro h
    exact (free_successor_orientation_iff_payloadBlind_and_counterStrict (ν := Empty) e).1
      (fun b s n => h b s n)
  · intro h ν b s n
    exact (free_successor_orientation_iff_payloadBlind_and_counterStrict (ν := ν) e).2 h b s n

/--
Proves: at every variable type `ν`, on the counter-admissible subclass of the
reflected scalar grammar, orientation of every actual successor root instance of
`FreeTerm ν` is equivalent to payload blindness.
Does not prove: that counter admissibility follows from payload blindness.
Relation: free-recursor successor instances on `FreeTerm ν`, the pair shape of
the successor constructor of `RootStep`.
Closure: root single-step.
Strategy: not applicable.
Trust: Lean kernel with the foundational axioms inherited from the two imported
biconditionals.
Scope: every `ν : Type` and every `MeasureExpr e` with `CounterAdmissible e`.
-/
theorem free_successor_counterAdmissible_orients_iff_payloadBlind
    {ν : Type} (e : MeasureExpr) (hadmissible : CounterAdmissible e) :
    (∀ b s n : FreeTerm ν,
      profileMeasure e.eval (.wrap s (.recur b s n)) <
        profileMeasure e.eval (.recur b s (.succ n))) ↔
      PayloadBlind e.eval :=
  (profile_orients_successors_iff e.eval).trans
    (counterAdmissible_orients_iff_payloadBlind e hadmissible)

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
