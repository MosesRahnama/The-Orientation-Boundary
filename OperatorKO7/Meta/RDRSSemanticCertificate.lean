import OperatorKO7.Meta.RDRSDescentLens
import OperatorKO7.Meta.RDRSSemanticDirectMeasure
import OperatorKO7.Meta.RDRSSemanticPayloadSensitivity

/-!
# RDRS Semantic Certificate (Milestone S2/S3 bridge)

Roadmap source:
`OperatorKO7/Expansion/Universal_Payload_Sensitive_Direct_Measures_Roadmap.md`

Packages semantic direct measures with orientation and payload-
sensitivity certificates. Three certificate strata:

* `SemanticOrientationCertificate R` = a semantic direct measure
  plus a proof that it orients `R`.
* `RawSensitiveOrientationCertificate R` = the orientation
  certificate plus a `PayloadSensitiveRaw` witness.
* `DecisivePayloadSensitiveCertificate R` = the orientation
  certificate plus `PayloadSensitiveRaw` and a `¬ CounterDominated`
  witness (the structural content of decisive payload sensitivity).

The certificate types are the input types for the S3 universal
lens-pump barrier (`RDRSSemanticLensPump.lean`).

## Bible compliance

- W2: `set_option autoImplicit false`.
- W8: every `def`/`theorem`/`structure` carries the structured
  docstring template.
- W5/R1: no forbidden trust-surface tokens from the Lean audit bible.
- Relation Gate: every certificate / theorem `Relation:` line is
  explicit.
-/

set_option autoImplicit false

namespace OperatorKO7.RDRSSemanticCertificate

open OperatorKO7.RDRSDescentLens
open OperatorKO7.RDRSSemanticDirectMeasure
open OperatorKO7.RDRSSemanticPayloadSensitivity

/--
Proves: a semantic orientation certificate for an RDRS step pair `R`:
  a semantic direct measure together with a proof that the measure
  orients `R`.
Does not prove: payload sensitivity or decisiveness; those are
  added by the certificates below.
Relation: abstract `RDRSStep B S N T`; not a concrete rewriting
  relation.
Closure: root single-step orientation.
Strategy: not applicable.
Trust: kernel-only.
Scope: every `R` for which a `SemanticDirectMeasure` orients.
-/
structure SemanticOrientationCertificate {B S N T : Type}
    (R : RDRSStep B S N T) where
  measure : SemanticDirectMeasure T
  orients : Orients R measure.μ measure.ltA

/--
Proves: an orientation certificate that is additionally raw payload-
  sensitive on `R`.
Does not prove: decisive payload sensitivity; the
  `PayloadSensitiveRaw` witness only requires payload-distinguishing
  values somewhere on the LHS.
Relation: abstract `RDRSStep B S N T`.
Closure: root single-step.
Strategy: not applicable.
Trust: kernel-only.
Scope: per concrete `R`.
-/
structure RawSensitiveOrientationCertificate {B S N T : Type}
    (R : RDRSStep B S N T) extends SemanticOrientationCertificate R where
  raw_sensitive :
    PayloadSensitiveRaw R toSemanticOrientationCertificate.measure.data

/--
Proves: an orientation certificate that is decisively payload-
  sensitive on `R`: the orientation conjunct comes from the parent
  certificate, and the certificate carries the
  `PayloadSensitiveRaw` and `¬ CounterDominated` witnesses needed
  for the `PayloadSensitiveDecisive` shape.
Does not prove: that decisively-payload-sensitive certificates
  exist for every `R`; the S3 barrier proves they fail to orient
  under additional structural conditions.
Relation: abstract `RDRSStep B S N T`.
Closure: root single-step.
Strategy: not applicable.
Trust: kernel-only.
Scope: per concrete `R`.
-/
structure DecisivePayloadSensitiveCertificate {B S N T : Type}
    (R : RDRSStep B S N T) extends SemanticOrientationCertificate R where
  raw_sensitive :
    PayloadSensitiveRaw R toSemanticOrientationCertificate.measure.data
  not_counter_dominated :
    ¬ CounterDominated R toSemanticOrientationCertificate.measure.data

/--
Proves: every decisive payload-sensitive certificate projects a
  `PayloadSensitiveDecisive` witness.
Does not prove: existence of decisive certificates; only the
  structural projection.
Relation: abstract `RDRSStep B S N T`.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: every decisive certificate.
-/
theorem DecisivePayloadSensitiveCertificate.toDecisive
    {B S N T : Type} {R : RDRSStep B S N T}
    (C : DecisivePayloadSensitiveCertificate R) :
    PayloadSensitiveDecisive R C.toSemanticOrientationCertificate.measure.data :=
  ⟨C.toSemanticOrientationCertificate.orients,
    C.raw_sensitive, C.not_counter_dominated⟩

/-- Audit anchor for the semantic-certificate surface. -/
def rdrs_semantic_certificate_anchor : String :=
  "OperatorKO7.RDRSSemanticCertificate.DecisivePayloadSensitiveCertificate"

end OperatorKO7.RDRSSemanticCertificate
