import OperatorKO7.Meta.RDRSDescentLens
import OperatorKO7.Meta.RDRSSemanticDirectMeasure
import OperatorKO7.Meta.RDRSSemanticPayloadSensitivity
import OperatorKO7.Meta.RDRSSemanticCertificate

/-!
# RDRS Semantic Lens-Pump Counterexample

## Formal Scope

SemanticLensPumpWitness is an existential counterexample to Orients. The no-orientation theorem consumes that counterexample; payload preservation does not derive it in this module.
-/

set_option autoImplicit false

namespace OperatorKO7.RDRSSemanticLensPump

open OperatorKO7.RDRSDescentLens
open OperatorKO7.RDRSSemanticDirectMeasure
open OperatorKO7.RDRSSemanticPayloadSensitivity
open OperatorKO7.RDRSSemanticCertificate

/--
Proves: a semantic lens-pump witness for `M` on `R` is a triple
  `(b, s, n)` at which the strict relation `M.ltA` does NOT hold on
  `(M.μ (R.rhs b s n), M.μ (R.lhs b s n))`. The witness is the
  semantic analogue of the U1 `HasPumpViolation` lens witness, here
  taken on the trivial `M.μ` "identity lens".
Does not prove: that every measure admits a witness; the witness
  is a structural failure mode for the measure.
Relation: abstract `RDRSStep B S N T`; not a concrete rewriting
  relation.
Closure: root single-step on the abstract step pair.
Strategy: not applicable.
Trust: kernel-only.
Scope: per concrete `(R, M)` pair.
-/
def SemanticLensPumpWitness {B S N T : Type} (R : RDRSStep B S N T)
    (M : SemanticMeasureData T) : Prop :=
  ∃ b s n, ¬ M.ltA (M.μ (R.rhs b s n)) (M.μ (R.lhs b s n))

/--
Proves: an orientation-counterexample lemma. A
  `SemanticLensPumpWitness` is already a concrete failure of one required
  `Orients` instance, so it contradicts universal orientation.
Does not prove: that `M` has a witness; the existence of a witness
  is a separate caller obligation.
Relation: abstract `RDRSStep B S N T`; not a concrete rewriting
  relation.
Closure: root single-step.
Strategy: not applicable.
Trust: kernel-only.
Scope: parametric over `B`, `S`, `N`, `T`, `R`, and `M`.
-/
theorem semantic_lens_pump_no_orients
    {B S N T : Type} (R : RDRSStep B S N T)
    (M : SemanticMeasureData T)
    (hWitness : SemanticLensPumpWitness R M) :
    ¬ Orients R M.μ M.ltA := by
  intro hOrient
  obtain ⟨b, s, n, hViolate⟩ := hWitness
  exact hViolate (hOrient b s n)

/--
Proves: a packaged semantic payload-sensitive lens-pump descent:
  a decisive payload-sensitive certificate plus the separately proved
  lens-pump witness for the same measure data.
Does not prove: that the witness is automatically extractable from the
  certificate. This structure names the specified additional proof obligation
  rather than hiding it behind the word "decisive".
Relation: abstract `RDRSStep B S N T`.
Closure: root single-step.
Strategy: not applicable.
Trust: kernel-only.
Scope: per concrete `R`.
-/
structure SemanticPayloadSensitiveLensPumpDescent {B S N T : Type}
    (R : RDRSStep B S N T) where
  /-- Decisive payload-sensitive orientation certificate. -/
  certificate : DecisivePayloadSensitiveCertificate R
  /-- Lens-pump witness for the certificate's semantic measure data. -/
  witness :
    SemanticLensPumpWitness R
      certificate.toSemanticOrientationCertificate.measure.data

/--
Proves: a packaged semantic payload-sensitive lens-pump descent exposes
  the lens violation needed by the barrier theorem.
Does not prove: the witness from decisiveness alone; it is a stored field.
Relation: abstract `RDRSStep B S N T`.
Closure: root single-step.
Strategy: not applicable.
Trust: kernel-only.
Scope: every packaged semantic payload-sensitive lens-pump descent.
-/
theorem semantic_payload_sensitive_descent_has_lens_violation
    {B S N T : Type} {R : RDRSStep B S N T}
    (D : SemanticPayloadSensitiveLensPumpDescent R) :
    SemanticLensPumpWitness R
      D.certificate.toSemanticOrientationCertificate.measure.data :=
  D.witness

/--
Proves: projection of the stored lens-pump counterexample into a
  no-orientation result for the package's measure data.
Does not prove: that decisiveness alone forces a lens-pump witness.
Relation: abstract `RDRSStep B S N T`.
Closure: root single-step.
Strategy: not applicable.
Trust: kernel-only.
Scope: parametric over `B`, `S`, `N`, `T`, `R`, and `D`.
-/
theorem no_orients_of_semantic_payload_sensitive_decisive_descent
    {B S N T : Type} {R : RDRSStep B S N T}
    (D : SemanticPayloadSensitiveLensPumpDescent R) :
    ¬ Orients R
        D.certificate.toSemanticOrientationCertificate.measure.μ
        D.certificate.toSemanticOrientationCertificate.measure.ltA :=
  semantic_lens_pump_no_orients R
    D.certificate.toSemanticOrientationCertificate.measure.data
    D.witness

/-- Audit anchor for the S3 universal semantic lens-pump barrier. -/
def rdrs_semantic_lens_pump_anchor : String :=
  "OperatorKO7.RDRSSemanticLensPump.semantic_lens_pump_no_orients"

end OperatorKO7.RDRSSemanticLensPump
