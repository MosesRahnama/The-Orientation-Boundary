/-!
# Typed-output carrier

The five tagged output forms and their syntactic discipline check. Extracted on 2026-08-10 from
`Meta/MetaHalt_Predicate.lean` so that consumers needing only the output vocabulary do not inherit
the meta-halt outer-loop machinery. Declarations are verbatim and keep the namespace
`OperatorKO7.MetaHalt.Predicate`, so every downstream `open` and qualified reference is unchanged.

This module depends on nothing but core Lean.

Relation: not applicable (a tagged output datatype).
Property: definition plus a syntactic well-formedness check.
Trust: kernel-only.
-/

set_option autoImplicit false

namespace OperatorKO7.MetaHalt.Predicate

/-- Five tagged output forms whose payloads are Strings or lists of Strings. -/
inductive TypedOutput
  /-- T1: operational completion. A derivation in the base language. -/
  | T1_complete (derivationTag : String)
  /-- T2: construction via operational extension. -/
  | T2_construction (constructionObject : String) (verifierLog : String)
  /-- T3: confession with import. -/
  | T3_confession
      (externalTheorem : String)
      (externalFramework : String)
      (droppedDimension : String)
      (residualDerivationTag : String)
  /-- T4: typed abstention. -/
  | T4_abstention
      (operationallyIncompleteDimension : String)
      (frameworksConsidered : List String)
      (frameworksRejected : List String)
  /-- T5: external impossibility certificate. -/
  | T5_impossibilityCert
      (metaTheoremReference : String)
      (checkableCertificateTag : String)
  deriving DecidableEq, Repr

/-- Boolean syntactic check for empty payload fields and caller-supplied license
flags. It does not validate the referenced derivation, log, theorem, or
certificate. -/
def isTypedOutputDisciplineViolation
    (out : TypedOutput)
    (isLicensedT1 isLicensedT2 isLicensedT3 isLicensedT4 isLicensedT5 : Bool) : Bool :=
  match out with
  | .T1_complete tag =>
      (!isLicensedT1) || decide (tag = "")
  | .T2_construction obj log =>
      (!isLicensedT2) || decide (obj = "") || decide (log = "")
  | .T3_confession thm fw dim res =>
      (!isLicensedT3) || decide (thm = "") || decide (fw = "") ||
        decide (dim = "") || decide (res = "")
  | .T4_abstention dim cons rej =>
      (!isLicensedT4) || decide (dim = "") || decide (cons = []) || decide (rej = [])
  | .T5_impossibilityCert thm cert =>
      (!isLicensedT5) || decide (thm = "") || decide (cert = "")

/-- A T4 abstention with a non-empty dimension record and non-empty
    considered/rejected lists, emitted in a licensed context, is not a
    discipline violation. -/
theorem t4_abstention_well_formed_not_violation
    (dim : String) (cons rej : List String)
    (hdim : dim ≠ "") (hcons : cons ≠ []) (hrej : rej ≠ [])
    (l1 l2 l3 l4 l5 : Bool) (h4 : l4 = true) :
    isTypedOutputDisciplineViolation
      (TypedOutput.T4_abstention dim cons rej) l1 l2 l3 l4 l5 = false := by
  simp [isTypedOutputDisciplineViolation, h4, hdim, hcons, hrej]

/-- An untyped refusal packaged as `T4_abstention` with an empty dimension
    record is a discipline violation regardless of context. -/
theorem untyped_t4_refusal_is_violation
    (l1 l2 l3 l4 l5 : Bool) :
    isTypedOutputDisciplineViolation
      (TypedOutput.T4_abstention "" [] []) l1 l2 l3 l4 l5 = true := by
  simp [isTypedOutputDisciplineViolation]

#print axioms t4_abstention_well_formed_not_violation
#print axioms untyped_t4_refusal_is_violation

end OperatorKO7.MetaHalt.Predicate
