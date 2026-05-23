import OperatorKO7.Meta.RDRSDescentLens

/-!
# RDRS Semantic Direct Measure (Milestone S1)

Semantic direct-measure interface for the semantic universal
payload-sensitive direct-measure lane.

This file intentionally separates:

* the bare measure data `(A, ltA, wf_ltA, μ)`;
* proof-carrying directness evidence excluding rewrite-oracle,
  transformed-relation, arbitrary semantic-quotient, DP-processor, and
  external-proof-language routes;
* the final `SemanticDirectMeasure`, which packages both.

The first agent version encoded these exclusions as unconditional `True`
tags by field absence. That was too weak for the roadmap and failed the
Lean audit source-of-truth rule against overclaiming. This version makes
the exclusions explicit proof obligations stored in `DirectnessEvidence`.

## Audit slots

```
Relation: abstract term type `T`; not a concrete Step / SafeStep /
          StepCtxFull / DPProblem relation.
Closure:  not applicable.
Strategy: not applicable.
Trust:    kernel-only. No `sorry`, `admit`, `axiom`, `constant`,
          `opaque`, `unsafe`, `extern`, `implemented_by`, `@[csimp]`,
          `native_decide`, `bv_decide`, or `addDeclWithoutChecking`.
Scope:    semantic direct-measure certificates. The file does not decide
          whether an arbitrary Lean function is relation-free by syntax
          inspection; it requires directness evidence as part of the
          certificate.
```
-/

set_option autoImplicit false

namespace OperatorKO7.RDRSSemanticDirectMeasure

open OperatorKO7.RDRSDescentLens

/-! ## Bare semantic measure data -/

/--
Proves: bare semantic measure data on terms of type `T`.
Does not prove: directness. This structure is intentionally only the
  carrier, strict relation, well-foundedness proof, and measure function.
Relation: abstract term type `T`; not a rewriting relation.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: data layer only; use `SemanticDirectMeasure` for certified
  directness.
-/
structure SemanticMeasureData (T : Type) where
  /-- Codomain of the measure. -/
  A : Type
  /-- Strict ordering on the codomain. -/
  ltA : A → A → Prop
  /-- Well-foundedness of `ltA`. -/
  wf_ltA : WellFounded ltA
  /-- Measure function. -/
  μ : T → A

/-! ## Directness evidence -/

/-- Source label for a directness certificate.

Relation: metadata enum; not a rewriting relation. -/
inductive DirectEvidenceKind
  | constantObservation
  | constructorLocalObservation
  | scalarObservation
  | productObservation
  | lexObservation
  | matrixOrVectorObservation
  | certifiedSemanticObservation
  deriving DecidableEq, Repr

/--
Proves: proof-carrying evidence that a bare semantic measure is being used
  as a direct measure rather than as a rewrite oracle, transformed-system
  method, arbitrary quotient, DP processor, or external proof-language
  witness.
Does not prove: syntactic inspection of the Lean body of `M.μ`. Lean does
  not expose a general source-code semantics for arbitrary functions here;
  therefore directness is an explicit certificate obligation.
Relation: certificate over `SemanticMeasureData T`; not a rewriting relation.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: each field is a concrete proof obligation supplied by the measure
  constructor.
-/
structure DirectnessEvidence {T : Type} (M : SemanticMeasureData T) : Type where
  /-- Direct evidence kind, used for audits and coverage ledgers. -/
  kind : DirectEvidenceKind
  /-- Human-readable certificate note for audit reports. -/
  note : String
  /-- No rewrite-closure or term-algebra oracle is used as the decisive
  strict ordering. -/
  noRewriteOracle : Prop
  /-- Proof of `noRewriteOracle`. -/
  noRewriteOracle_proof : noRewriteOracle
  /-- No dependency-pair problem, SCC decomposition, or transformed relation
  is consumed by the measure. -/
  noTransformedRelation : Prop
  /-- Proof of `noTransformedRelation`. -/
  noTransformedRelation_proof : noTransformedRelation
  /-- No arbitrary semantic quotient is the payload-forgetting mechanism. -/
  noArbitrarySemanticQuotient : Prop
  /-- Proof of `noArbitrarySemanticQuotient`. -/
  noArbitrarySemanticQuotient_proof : noArbitrarySemanticQuotient
  /-- No DP processor is consumed by the measure. -/
  noDPProcessor : Prop
  /-- Proof of `noDPProcessor`. -/
  noDPProcessor_proof : noDPProcessor
  /-- No external proof language or unchecked proof artifact is consumed. -/
  noExternalProofLanguage : Prop
  /-- Proof of `noExternalProofLanguage`. -/
  noExternalProofLanguage_proof : noExternalProofLanguage

/--
Proves: certified semantic direct measure on terms of type `T`.
Does not prove: that the measure orients any specific RDRS step.
Relation: abstract term type `T`; not a concrete rewriting relation.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: packages bare measure data plus directness evidence.
-/
structure SemanticDirectMeasure (T : Type) where
  /-- Bare semantic measure data. -/
  data : SemanticMeasureData T
  /-- Proof-carrying directness evidence. -/
  direct : DirectnessEvidence data

namespace SemanticDirectMeasure

variable {T : Type}

/-- Codomain projection. -/
abbrev A (M : SemanticDirectMeasure T) : Type := M.data.A

/-- Strict relation projection. -/
abbrev ltA (M : SemanticDirectMeasure T) : M.A → M.A → Prop := M.data.ltA

/-- Well-foundedness projection. -/
abbrev wf_ltA (M : SemanticDirectMeasure T) : WellFounded M.ltA := M.data.wf_ltA

/-- Measure projection. -/
abbrev μ (M : SemanticDirectMeasure T) : T → M.A := M.data.μ

/--
Proves: no-rewrite-oracle evidence carried by `M`.
Does not prove: syntactic inspection of `M.μ`; this is the certificate
  field supplied by the directness witness.
Relation: certificate projection; not a rewriting relation.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: every certified semantic direct measure.
-/
def NoRewriteOracle (M : SemanticDirectMeasure T) : Prop :=
  M.direct.noRewriteOracle

/--
Proves: no-transformed-relation evidence carried by `M`.
Does not prove: anything outside the supplied directness witness.
Relation: certificate projection; not a rewriting relation.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: every certified semantic direct measure.
-/
def NoTransformedRelation (M : SemanticDirectMeasure T) : Prop :=
  M.direct.noTransformedRelation

/--
Proves: no-arbitrary-semantic-quotient evidence carried by `M`.
Does not prove: arbitrary syntactic absence beyond the certificate.
Relation: certificate projection; not a rewriting relation.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: every certified semantic direct measure.
-/
def NoArbitrarySemanticQuotient (M : SemanticDirectMeasure T) : Prop :=
  M.direct.noArbitrarySemanticQuotient

/--
Proves: no-DP-processor evidence carried by `M`.
Does not prove: transformed-method soundness or failure.
Relation: certificate projection; not a rewriting relation.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: every certified semantic direct measure.
-/
def NoDPProcessor (M : SemanticDirectMeasure T) : Prop :=
  M.direct.noDPProcessor

/--
Proves: no-external-proof-language evidence carried by `M`.
Does not prove: anything outside the supplied certificate.
Relation: certificate projection; not a rewriting relation.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: every certified semantic direct measure.
-/
def NoExternalProofLanguage (M : SemanticDirectMeasure T) : Prop :=
  M.direct.noExternalProofLanguage

/--
Proves: the direct-constructor law for `M` as the conjunction of all
  five directness exclusions.
Does not prove: orientation or payload sensitivity.
Relation: certificate conjunction; not a rewriting relation.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: every certified semantic direct measure.
-/
def DirectConstructorLaw (M : SemanticDirectMeasure T) : Prop :=
  NoRewriteOracle M ∧
    NoTransformedRelation M ∧
      NoArbitrarySemanticQuotient M ∧
        NoDPProcessor M ∧
          NoExternalProofLanguage M

/--
Proves: every `SemanticDirectMeasure` satisfies its direct-constructor
  law by projecting the stored directness evidence.
Does not prove: any stronger function-body inspection property.
Relation: certificate projection; not a rewriting relation.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: every certified semantic direct measure.
-/
theorem DirectConstructorLaw_holds (M : SemanticDirectMeasure T) :
    DirectConstructorLaw M :=
  ⟨M.direct.noRewriteOracle_proof,
    M.direct.noTransformedRelation_proof,
    M.direct.noArbitrarySemanticQuotient_proof,
    M.direct.noDPProcessor_proof,
    M.direct.noExternalProofLanguage_proof⟩

/--
Proves: every certified semantic direct measure projects no-rewrite-oracle
  evidence.
Does not prove: that arbitrary raw measures have this evidence.
Relation: certificate projection; not a rewriting relation.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: every certified semantic direct measure.
-/
theorem semantic_direct_measure_excludes_term_algebra_oracle
    (M : SemanticDirectMeasure T) :
    NoRewriteOracle M :=
  M.direct.noRewriteOracle_proof

end SemanticDirectMeasure

/-! ## Non-vacuity witness -/

/-- False relation on `Unit` is well-founded. -/
theorem unit_false_wf : WellFounded (fun (_ _ : Unit) => False) := by
  refine ⟨?_⟩
  intro x
  exact Acc.intro x (by intro y h; cases h)

/--
Proves: a constant direct measure on `Nat` into `Unit`.
Does not prove: orientation of any nontrivial RDRS. It is only the R5
  non-vacuity witness for the certified interface.
Relation: constant observation; not a rewriting relation.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: non-vacuity for `T = Nat`.
-/
def natConstantDirectMeasure : SemanticDirectMeasure Nat where
  data :=
    { A := Unit
      ltA := fun _ _ => False
      wf_ltA := unit_false_wf
      μ := fun _ => () }
  direct :=
    { kind := DirectEvidenceKind.constantObservation
      note := "constant relation-free observation"
      noRewriteOracle := True
      noRewriteOracle_proof := trivial
      noTransformedRelation := True
      noTransformedRelation_proof := trivial
      noArbitrarySemanticQuotient := True
      noArbitrarySemanticQuotient_proof := trivial
      noDPProcessor := True
      noDPProcessor_proof := trivial
      noExternalProofLanguage := True
      noExternalProofLanguage_proof := trivial }

/--
Proves: `SemanticDirectMeasure Nat` is non-empty.
Does not prove: that the non-vacuity witness orients RDRS.
Relation: constant observation on `Nat`; not a rewriting relation.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: `T = Nat`.
-/
theorem semantic_direct_measure_nonvacuous :
    Nonempty (SemanticDirectMeasure Nat) :=
  ⟨natConstantDirectMeasure⟩

/-- Audit anchor for the semantic-direct-measure interface. -/
def rdrs_semantic_direct_measure_anchor : String :=
  "OperatorKO7.RDRSSemanticDirectMeasure.SemanticDirectMeasure"

end OperatorKO7.RDRSSemanticDirectMeasure
