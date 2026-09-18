import OperatorKO7.Meta.RDRSDescentLens
import OperatorKO7.Meta.RDRSProjectionTransaction
import OperatorKO7.Meta.RDRSRawDirectMeasure
import OperatorKO7.Meta.RDRSMethodCertificate
import OperatorKO7.Meta.RDRSRetainedCoordinate

/-!
# RDRS Normalized-Certificate Classifier

Deterministic priority classifier over the U2 normalized-certificate
syntax plus U1.5 projection-transaction evidence.

Bible compliance:
- W2: `set_option autoImplicit false` set below.
- W8: every theorem and `def` carries the structured Proves / Does not
  prove / Relation / Closure / Strategy / Trust / Scope template.
- W5: no `native_decide` / `bv_decide`.
- R1: no `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `extern`,
  `implemented_by`, `@[csimp]`, `native_decide`, `bv_decide`, or
  `addDeclWithoutChecking`.
- Relation Gate: classifier operates over normalized-certificate
  syntax plus abstract `ProjectionTransactionEscape R` evidence; not
  a concrete rewriting relation.

Priority order:

1. `ProjectionTransactionEscape` if projection-transaction evidence is supplied.
2. `ConstructionEscape` if the normalized route is construction-style.
3. `TransformEscape` if the normalized route is transform-style.
4. `PayloadSensitiveBlocked` if the remaining direct certificate is strict and payload-sensitive.
5. `NotDirect` otherwise.

The construction / transform flags have priority over the blocked
branch because classification is over normalized method certificates,
not raw measures. A non-direct route may mention payload syntactically
without being a direct payload-sensitive descent certificate.
-/

set_option autoImplicit false

namespace OperatorKO7.RDRSMethodCertificateClassifier

open OperatorKO7.RDRSDescentLens
open OperatorKO7.RDRSProjectionTransaction
open OperatorKO7.RDRSRawDirectMeasure
open OperatorKO7.RDRSMethodCertificate
open OperatorKO7.RDRSRetainedCoordinate

/-- Classifier output. `TEMPORARY_UNCLASSIFIED` is retained only so the
zero-residual theorem can rule it out.

Relation: classifier output enum; not a concrete rewriting relation. -/
inductive CertificateClass
  | PayloadSensitiveBlocked
  | ProjectionTransactionEscape
  | ConstructionEscape
  | TransformEscape
  | NotDirect
  | TEMPORARY_UNCLASSIFIED
  deriving DecidableEq, Repr

/-- Deterministic classifier input.

Relation: abstract `RDRSStep B S N T`; not a concrete rewriting
relation. -/
structure ClassifierInput {B S N T : Type} (R : RDRSStep B S N T) where
  cert           : NormalizedDescentCertificate
  projectionTx   : Option (ProjectionTransactionEscape R)
  isConstruction : Bool
  isTransform    : Bool

/--
Proves: the deterministic-priority classifier output for the given
  `ClassifierInput R`, returning one of the six labels in
  `CertificateClass`.
Does not prove: anything about the input's semantic content (the
  classifier is a routing function, not a barrier theorem).
Relation: abstract `RDRSStep B S N T`; not a concrete rewriting
  relation.
Closure: not applicable (this is a pure function on classifier inputs).
Strategy: not applicable.
Trust: kernel-only.
Scope: parametric over `B`, `S`, `N`, `T`, and `R`.
-/
def classify {B S N T : Type} {R : RDRSStep B S N T}
    (input : ClassifierInput R) : CertificateClass :=
  match input.projectionTx with
  | some _ => CertificateClass.ProjectionTransactionEscape
  | none =>
    if input.isConstruction then
      CertificateClass.ConstructionEscape
    else if input.isTransform then
      CertificateClass.TransformEscape
    else
      match input.cert with
      | .abstain => CertificateClass.NotDirect
      | .strictDescent m _ =>
        if m.containsPayloadOccur then
          CertificateClass.PayloadSensitiveBlocked
        else
          CertificateClass.NotDirect

variable {B S N T : Type} {R : RDRSStep B S N T}

/--
Proves: if the classifier routes an input to
  `ProjectionTransactionEscape`, then projection-transaction evidence
  was supplied on the input (`∃ P, input.projectionTx = some P`).
Does not prove: that the projection-transaction evidence is correct,
  or that orientation is transported.
Relation: classifier surface; not a concrete rewriting relation.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: parametric over `R` and the input.
-/
theorem classify_projection_transaction_escape_sound
    (input : ClassifierInput R)
    (h : classify input = CertificateClass.ProjectionTransactionEscape) :
    ∃ P : ProjectionTransactionEscape R, input.projectionTx = some P := by
  cases input with
  | mk cert projectionTx isConstruction isTransform =>
    cases projectionTx with
    | none =>
      cases isConstruction <;> cases isTransform <;> cases cert with
      | abstain =>
        simp [classify] at h
      | strictDescent m o =>
        cases hp : m.containsPayloadOccur <;> simp [classify, hp] at h
    | some P =>
      exact ⟨P, rfl⟩

/--
Proves: if the classifier routes to `PayloadSensitiveBlocked`, then
  no projection-transaction evidence was supplied, both route flags
  are false, the certificate is a strict-descent claim, and the
  measure is syntactically payload-sensitive.
Does not prove: that the payload-sensitive measure fails to orient
  the source RDRS step (that is the universal-barrier theorem;
  classifier soundness is structural only).
Relation: classifier surface; not a concrete rewriting relation.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: parametric over `R` and the input.
-/
theorem classify_payload_sensitive_blocked_sound_guarded
    (input : ClassifierInput R)
    (h : classify input = CertificateClass.PayloadSensitiveBlocked) :
    input.projectionTx = none ∧
    input.isConstruction = false ∧
    input.isTransform = false ∧
    ∃ m o,
      input.cert = NormalizedDescentCertificate.strictDescent m o ∧
      m.containsPayloadOccur = true := by
  cases input with
  | mk cert projectionTx isConstruction isTransform =>
    cases projectionTx with
    | some P =>
      simp [classify] at h
    | none =>
      cases isConstruction <;> cases isTransform <;> cases cert with
      | abstain =>
        simp [classify] at h
      | strictDescent m o =>
        cases hp : m.containsPayloadOccur <;> simp [classify, hp] at h ⊢

/--
Proves: weaker form of `classify_payload_sensitive_blocked_sound_guarded`
  that drops the explicit `isConstruction = false ∧ isTransform = false`
  guards from the conclusion.
Does not prove: more than the guarded form. The guard fields can still
  be recovered via the guarded theorem.
Relation: classifier surface; not a concrete rewriting relation.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only (delegates to the guarded form).
Scope: parametric over `R` and the input.
-/
theorem classify_payload_sensitive_blocked_sound
    (input : ClassifierInput R)
    (h : classify input = CertificateClass.PayloadSensitiveBlocked) :
    input.projectionTx = none ∧
    ∃ m o,
      input.cert = NormalizedDescentCertificate.strictDescent m o ∧
      m.containsPayloadOccur = true := by
  have hg := classify_payload_sensitive_blocked_sound_guarded input h
  exact ⟨hg.1, hg.2.2.2⟩

/--
Proves: if the classifier routes to `ConstructionEscape`, then no
  projection-transaction evidence was supplied and the construction
  flag was set on the input.
Does not prove: that the construction route actually orients the
  source RDRS step. The construction route flag is opaque at this
  layer.
Relation: classifier surface; not a concrete rewriting relation.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: parametric over `R` and the input.
-/
theorem classify_construction_escape_sound
    (input : ClassifierInput R)
    (h : classify input = CertificateClass.ConstructionEscape) :
    input.projectionTx = none ∧ input.isConstruction = true := by
  cases input with
  | mk cert projectionTx isConstruction isTransform =>
    cases projectionTx with
    | some P =>
      simp [classify] at h
    | none =>
      cases isConstruction <;> cases isTransform <;> cases cert with
      | abstain =>
        simp [classify] at h ⊢
      | strictDescent m o =>
        cases hp : m.containsPayloadOccur <;> simp [classify, hp] at h ⊢

/--
Proves: if the classifier routes to `TransformEscape`, then no
  projection-transaction evidence was supplied, the construction
  flag was not set, and the transform flag was set on the input.
Does not prove: that the transform route actually orients the source
  RDRS step. The transform route flag is opaque at this layer.
Relation: classifier surface; not a concrete rewriting relation.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: parametric over `R` and the input.
-/
theorem classify_transform_escape_sound
    (input : ClassifierInput R)
    (h : classify input = CertificateClass.TransformEscape) :
    input.projectionTx = none ∧
    input.isConstruction = false ∧
    input.isTransform = true := by
  cases input with
  | mk cert projectionTx isConstruction isTransform =>
    cases projectionTx with
    | some P =>
      simp [classify] at h
    | none =>
      cases isConstruction <;> cases isTransform <;> cases cert with
      | abstain =>
        simp [classify] at h ⊢
      | strictDescent m o =>
        cases hp : m.containsPayloadOccur <;> simp [classify, hp] at h ⊢

/--
Proves: if the classifier routes to `NotDirect`, then no
  projection-transaction evidence was supplied, both route flags are
  false, and the certificate either abstains or is a strict-descent
  claim whose measure is not payload-sensitive.
Does not prove: that the input is unrelated to direct payload-sensitive
  descent in any deeper semantic sense; the conclusion is the explicit
  syntactic disjunction.
Relation: classifier surface; not a concrete rewriting relation.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: parametric over `R` and the input.
-/
theorem classify_not_direct_sound
    (input : ClassifierInput R)
    (h : classify input = CertificateClass.NotDirect) :
    input.projectionTx = none ∧
    input.isConstruction = false ∧
    input.isTransform = false ∧
    (input.cert = NormalizedDescentCertificate.abstain ∨
     (∃ m o,
        input.cert = NormalizedDescentCertificate.strictDescent m o ∧
        m.containsPayloadOccur = false)) := by
  cases input with
  | mk cert projectionTx isConstruction isTransform =>
    cases projectionTx with
    | some P =>
      simp [classify] at h
    | none =>
      cases isConstruction <;> cases isTransform <;> cases cert with
      | abstain =>
        simp [classify] at h ⊢
      | strictDescent m o =>
        cases hp : m.containsPayloadOccur <;> simp [classify, hp] at h ⊢

/--
Proves: the classifier never returns `TEMPORARY_UNCLASSIFIED` on any
  closed-grammar input plus optional projection-transaction evidence.
Does not prove: anything about inputs outside the closed grammar; the
  closed grammar is `NormalizedDescentCertificate` + optional
  `ProjectionTransactionEscape` + two Bool flags.
Relation: classifier surface; not a concrete rewriting relation.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: universal over all closed-grammar inputs.
-/
theorem temporary_unclassified_count_is_zero
    (input : ClassifierInput R) :
    classify input ≠ CertificateClass.TEMPORARY_UNCLASSIFIED := by
  cases input with
  | mk cert projectionTx isConstruction isTransform =>
    cases projectionTx <;> cases isConstruction <;> cases isTransform <;>
      cases cert with
      | abstain =>
        simp [classify]
      | strictDescent m o =>
        cases hp : m.containsPayloadOccur <;> simp [classify, hp]

/--
Proves: every classifier input lands in one of the five formal classes
  (`PayloadSensitiveBlocked`, `ProjectionTransactionEscape`,
  `ConstructionEscape`, `TransformEscape`, `NotDirect`); the
  `TEMPORARY_UNCLASSIFIED` branch is structurally excluded.
Does not prove: anything about distribution across the buckets.
Relation: classifier surface; not a concrete rewriting relation.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only (uses `temporary_unclassified_count_is_zero`
  internally).
Scope: universal over all closed-grammar inputs.
-/
theorem classify_total (input : ClassifierInput R) :
    classify input = CertificateClass.PayloadSensitiveBlocked ∨
    classify input = CertificateClass.ProjectionTransactionEscape ∨
    classify input = CertificateClass.ConstructionEscape ∨
    classify input = CertificateClass.TransformEscape ∨
    classify input = CertificateClass.NotDirect := by
  have hne := temporary_unclassified_count_is_zero (R := R) input
  generalize hcls : classify input = c
  cases c
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
  · rw [hcls] at hne
    exact absurd rfl hne

/--
Proves: when the classifier routes to `ProjectionTransactionEscape`,
  the supplied projection-transaction lifts a projected orientation
  back to the source RDRS step (via `lifted_orients` of
  `ProjectionTransactionEscape`).
Does not prove: that the projected orientation is correct semantics
  on the source TRS; only the structural transport equation is
  asserted.
Relation: abstract `RDRSStep B S N T`; not a concrete rewriting
  relation.
Closure: one-step on the abstract step pair.
Strategy: not applicable.
Trust: kernel-only.
Scope: parametric over `R` and the input.
-/
theorem classify_projection_transaction_escape_lifts_orientation
    (input : ClassifierInput R)
    (h : classify input = CertificateClass.ProjectionTransactionEscape) :
    ∃ P : ProjectionTransactionEscape R,
      input.projectionTx = some P ∧
      Orients R P.liftedMeasure P.transaction.ltA' := by
  obtain ⟨P, hP⟩ := classify_projection_transaction_escape_sound input h
  exact ⟨P, hP, P.lifted_orients⟩

/--
Proves: the U3 retained-coordinate counter factorisation theorem
  conclusion holds ONLY when the caller supplies an explicit factor
  hypothesis `∃ factor : Nat → P.CounterIndex, ∀ t, ...`.
Does not prove: the unconditional form of the U3 theorem. There is
  no unconditional version anywhere in this stack.
Relation: abstract `RDRSStep B S N T`; not a concrete rewriting
  relation.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only (delegates to the U3 theorem).
Scope: parametric over the projection transaction `P` and the static
  hypothesis package `SH`; the factor hypothesis must be supplied by
  the caller.
-/
theorem retainedCoordinate_factorsThrough_counter_conditional
    (P : ProjectionTransaction R)
    (SH : StaticRetainedHypotheses R)
    (factor_hypothesis :
      ∃ factor : Nat → P.CounterIndex,
        ∀ t, P.retainedCoordinate (P.pi t) = factor (SH.counter t)) :
    ∃ factorFromCounter : Nat → P.A',
      ∀ t, P.mu' (P.pi t) = factorFromCounter (SH.counter t) :=
  retainedCoordinate_factorsThrough_counter P SH factor_hypothesis

/--
Proves: the implication form "(factor hypothesis) → (counter
  factorisation conclusion)" of the U3 retained-coordinate theorem.
Does not prove: the conclusion without the factor hypothesis.
Relation: abstract `RDRSStep B S N T`; not a concrete rewriting
  relation.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only (delegates to the U3 theorem).
Scope: parametric over `P`, `SH`.
-/
theorem retainedCoordinate_factorsThrough_counter_is_conditional
    (P : ProjectionTransaction R)
    (SH : StaticRetainedHypotheses R) :
    (∃ factor : Nat → P.CounterIndex,
        ∀ t, P.retainedCoordinate (P.pi t) = factor (SH.counter t)) →
    (∃ factorFromCounter : Nat → P.A',
        ∀ t, P.mu' (P.pi t) = factorFromCounter (SH.counter t)) :=
  retainedCoordinate_factorsThrough_counter P SH

/--
Proves: audit anchor String for the U4 classifier `classify` def.
Does not prove: anything about the classifier itself.
Relation: not applicable.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: downstream registries cite this constant.
-/
def rdrs_method_certificate_classifier_anchor : String :=
  "OperatorKO7.RDRSMethodCertificateClassifier.classify"

/--
Proves: audit anchor String for the zero-residual closure theorem.
Does not prove: anything about the theorem itself.
Relation: not applicable.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: downstream registries cite this constant.
-/
def rdrs_method_certificate_classifier_zero_residual_anchor : String :=
  "OperatorKO7.RDRSMethodCertificateClassifier.temporary_unclassified_count_is_zero"

end OperatorKO7.RDRSMethodCertificateClassifier
