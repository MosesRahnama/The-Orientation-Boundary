import OperatorKO7.Meta.MetaHalt_Signatures
import OperatorKO7.Meta.WitnessOrder
import OperatorKO7.Meta.OperationalIncompleteness
import OperatorKO7.Meta.ConfessionMethod_Family

/-!
# META-HALT Predicate and Typed-Output Discipline

## Formal Scope

The declarations implement Boolean and record-field classifiers over supplied flags and Strings. They do not validate proof objects, logs, certificates, or execution semantics.
-/

namespace OperatorKO7.MetaHalt.Predicate

open OperatorKO7
open OperatorKO7.WitnessOrder
open OperatorKO7.MetaHalt.Signatures

/-- The four firing clauses of Definition 5.3. -/
inductive MetaHaltClause
  | structuralBlock
  | certifiedCycle
  | budgetExhausted
  | catalogExhausted
  deriving DecidableEq, Repr

/-- The binary META-HALT predicate of Definition 5.3, returned as an option
    carrying the firing clause. -/
def metaHalt
    (O : ObligationSignature)
    (L : LanguageSignature)
    (T : SearchTraceSignature)
    (admiss : AdmissibilityTable)
    (loops : LoopPatternTable)
    (budget : Nat)
    (catalogRemaining : Nat) : Option MetaHaltClause :=
  if admiss.admits O L = false then
    some MetaHaltClause.structuralBlock
  else if loops.anyFires T = true then
    some MetaHaltClause.certifiedCycle
  else if budget ≤ T.stepsConsumed then
    some MetaHaltClause.budgetExhausted
  else if catalogRemaining = 0 then
    some MetaHaltClause.catalogExhausted
  else
    none

instance (O : ObligationSignature) (L : LanguageSignature)
    (T : SearchTraceSignature) (admiss : AdmissibilityTable)
    (loops : LoopPatternTable) (budget catalogRemaining : Nat) :
    Decidable (metaHalt O L T admiss loops budget catalogRemaining = none) :=
  inferInstance

/-- Every supplied input tuple has an output equal to the value computed by
`metaHalt`. The proposition does not characterize proof-object exclusion or
finiteness beyond the input types. -/
theorem metaHalt_consumes_signatures_not_proofs :
    ∀ (O : ObligationSignature) (L : LanguageSignature)
      (T : SearchTraceSignature) (admiss : AdmissibilityTable)
      (loops : LoopPatternTable) (budget catalogRemaining : Nat),
      ∃ c : Option MetaHaltClause,
        c = metaHalt O L T admiss loops budget catalogRemaining := by
  intro O L T admiss loops budget catalogRemaining
  exact ⟨metaHalt O L T admiss loops budget catalogRemaining, rfl⟩

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

/-- Boolean classifier over verdict-shaped tags and two caller-supplied flags;
no execution trace is inspected. -/
def isFalseSupervisoryTermination
    (out : TypedOutput)
    (reachedThresholdWitness producedTerminalHaltCert : Bool) : Bool :=
  let isVerdictShaped :=
    match out with
    | .T1_complete _ => true
    | .T2_construction _ _ => true
    | .T5_impossibilityCert _ _ => true
    | _ => false
  isVerdictShaped && (!reachedThresholdWitness) && (!producedTerminalHaltCert)

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

end OperatorKO7.MetaHalt.Predicate
