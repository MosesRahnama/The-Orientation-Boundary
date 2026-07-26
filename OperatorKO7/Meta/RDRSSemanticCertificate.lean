import OperatorKO7.Meta.RDRSDescentLens
import OperatorKO7.Meta.RDRSSemanticDirectMeasure
import OperatorKO7.Meta.RDRSSemanticPayloadSensitivity

/-!
# RDRS semantic certificates

Packages semantic direct measures with orientation and payload-
sensitivity certificates. Three certificate strata:

* `SemanticOrientationCertificate R` = a semantic direct measure
  plus a proof that it orients `R`.
* `RawSensitiveOrientationCertificate R` = the orientation
  certificate plus a `PayloadSensitiveRaw` witness.
* `DecisivePayloadSensitiveCertificate R` = the orientation
  certificate plus `PayloadSensitiveRaw` and a `¬ CounterDominated`
  witness (the structural content of decisive payload sensitivity).

`RDRSSemanticLensPump.lean` consumes these certificate structures. Existence
of a certificate remains an explicit input for a chosen abstract `RDRSStep`.
-/

set_option autoImplicit false

namespace OperatorKO7.RDRSSemanticCertificate

open OperatorKO7.RDRSDescentLens
open OperatorKO7.RDRSSemanticDirectMeasure
open OperatorKO7.RDRSSemanticPayloadSensitivity

/-- A semantic direct measure together with a proof that it orients the supplied abstract
`RDRSStep` at the root-step relation. -/
structure SemanticOrientationCertificate {B S N T : Type}
    (R : RDRSStep B S N T) where
  measure : SemanticDirectMeasure T
  orients : Orients R measure.μ measure.ltA

/-- Extends an orientation certificate with the supplied `PayloadSensitiveRaw` witness. -/
structure RawSensitiveOrientationCertificate {B S N T : Type}
    (R : RDRSStep B S N T) extends SemanticOrientationCertificate R where
  raw_sensitive :
    PayloadSensitiveRaw R toSemanticOrientationCertificate.measure.data

/-- Extends an orientation certificate with supplied `PayloadSensitiveRaw` and
`not CounterDominated` witnesses for the same abstract step relation. -/
structure DecisivePayloadSensitiveCertificate {B S N T : Type}
    (R : RDRSStep B S N T) extends SemanticOrientationCertificate R where
  raw_sensitive :
    PayloadSensitiveRaw R toSemanticOrientationCertificate.measure.data
  not_counter_dominated :
    ¬ CounterDominated R toSemanticOrientationCertificate.measure.data

/-- Repackages the three stored certificate fields as `PayloadSensitiveDecisive`. -/
theorem DecisivePayloadSensitiveCertificate.toDecisive
    {B S N T : Type} {R : RDRSStep B S N T}
    (C : DecisivePayloadSensitiveCertificate R) :
    PayloadSensitiveDecisive R C.toSemanticOrientationCertificate.measure.data :=
  ⟨C.toSemanticOrientationCertificate.orients,
    C.raw_sensitive, C.not_counter_dominated⟩

/-- String identifier for the decisive-certificate declaration. -/
def rdrs_semantic_certificate_anchor : String :=
  "OperatorKO7.RDRSSemanticCertificate.DecisivePayloadSensitiveCertificate"

end OperatorKO7.RDRSSemanticCertificate
