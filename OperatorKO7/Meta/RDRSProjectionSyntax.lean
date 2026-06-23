import OperatorKO7.Meta.RDRSDescentLens

/-!
# RDRS Projection Syntax (Milestone U1, Sprint U1)

Syntactic payload-forgetting projection / erasure interface for the
universal payload-sensitive direct-measure project, and the positive
projection-escape certificate.

Roadmap source: `OperatorKO7/Expansion/Universal_Payload_Sensitive_Direct_Measures_Roadmap.md`
Milestone U1, Sprint U1, file `Meta/RDRSProjectionSyntax.lean`.

Bible compliance:
- W2: `set_option autoImplicit false` set below.
- W8: every theorem and `def` exposing a Prop-valued surface carries
  the structured Proves / Does not prove / Relation / Closure /
  Strategy / Trust / Scope template.
- W5: no `native_decide` or `bv_decide`.
- R1: no `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `extern`,
  `implemented_by`, `@[csimp]`, `native_decide`, `bv_decide`, or
  `addDeclWithoutChecking`.
- Relation Gate: every theorem is parametric over an abstract
  `RDRSStep` carrier; the Relation field records "abstract RDRSStep
  step-pair; not a concrete Step / SafeStep / StepCtxFull".

The roadmap's non-negotiable shape for the projection branch is that
"`ProjectionEscape` must carry positive success evidence, not only
erasure syntax." This file enforces that requirement structurally:

- `PayloadForgetErasure` packages the erasure syntax (a map
  `erase : T → T'` and a projected RDRS step that commutes with
  erasure on LHS and RHS).
- `ProjectionEscape` extends that with a projected measure, a strict
  projected relation, and a proof field `projected_orientation` that
  the projected measure strictly orients the projected rule. Without
  the `projected_orientation` proof, no `ProjectionEscape` inhabits
  the type.

The lifted measure on the original term type factors the projected
measure through the erasure, and `lifted_orients` shows that the
projected descent is the decisive descent certificate for the
original rule.

Scope discipline:
- Arbitrary semantic quotients do not inhabit this syntactic branch: only
  syntactic erasures with a positive projected-orientation proof
  inhabit `ProjectionEscape`. Semantic-envelope cases belong to a
  separate non-direct theorem layer downstream.
-/

set_option autoImplicit false

namespace OperatorKO7.RDRSProjectionSyntax

open OperatorKO7.RDRSDescentLens

/-- Syntactic payload-forgetting erasure.

A map `erase : T → T'` together with a projected RDRS step `Rproj` on
the erased type, plus equations that erasure commutes with the LHS and
RHS of every step. On its own this is just erasure syntax; it carries
no orientation evidence and is rejected as a projection escape until a
positive `projected_orientation` is supplied (see `ProjectionEscape`
below).

Relation: abstract `RDRSStep B S N T`; not a concrete rewriting
relation. -/
structure PayloadForgetErasure
    {B S N T : Type} (R : RDRSStep B S N T) (T' : Type) where
  /-- The payload-forgetting erasure on terms. -/
  erase : T → T'
  /-- The projected RDRS rule on the erased term type. -/
  Rproj : RDRSStep B S N T'
  /-- Erasure commutes with the LHS for every step `(b, s, n)`. -/
  erase_commutes_lhs :
    ∀ b s n, erase (R.lhs b s n) = Rproj.lhs b s n
  /-- Erasure commutes with the RHS for every step `(b, s, n)`. -/
  erase_commutes_rhs :
    ∀ b s n, erase (R.rhs b s n) = Rproj.rhs b s n

/-- **Positive success certificate** for a projection escape.

A `ProjectionEscape R` packages four ingredients:

* a syntactic payload-forgetting erasure
  `E : PayloadForgetErasure R T'`,
* a projected measure `mu' : T' → A'`,
* a strict projected relation `ltA' : A' → A' → Prop`,
* a proof `projected_orientation : Orients E.Rproj mu' ltA'` that the
  projected measure strictly orients the projected rule.

The `projected_orientation` field is the positive success evidence the
roadmap requires. Bare erasure syntax is rejected by the type system:
a `ProjectionEscape` cannot be constructed without exhibiting a proof
that the projected descent actually orients the projected rule.
Arbitrary semantic quotients without that proof do not inhabit this
type.

Relation: abstract `RDRSStep B S N T`; not a concrete rewriting
relation. -/
structure ProjectionEscape
    {B S N T : Type} (R : RDRSStep B S N T) where
  /-- Projected term type after payload erasure. -/
  T' : Type
  /-- Projected measure codomain. -/
  A' : Type
  /-- Syntactic payload-forgetting erasure (erasure syntax). -/
  E : PayloadForgetErasure R T'
  /-- Projected measure on the erased term type. -/
  mu' : T' → A'
  /-- Strict projected relation on the measure codomain. -/
  ltA' : A' → A' → Prop
  /-- **Positive success evidence.** Proof that the projected measure
  strictly orients the projected rule. Without this field the structure
  is not inhabited. -/
  projected_orientation :
    Orients E.Rproj mu' ltA'

namespace ProjectionEscape

variable {B S N T : Type} {R : RDRSStep B S N T} (P : ProjectionEscape R)

/--
Proves: the lifted measure on the original term type is the
  composition `P.mu' ∘ P.E.erase`.
Does not prove: that the lifted measure orients the original RDRS
  rule (that is the content of `lifted_orients` below).
Relation: abstract `RDRSStep B S N T`; not a concrete rewriting
  relation.
Closure: not applicable (this is a function definition, not a
  rewriting theorem).
Strategy: not applicable.
Trust: kernel-only (a pure function definition).
Scope: parametric over `P : ProjectionEscape R`.
-/
def liftedMeasure : T → P.A' := fun t => P.mu' (P.E.erase t)

/--
Proves: the lifted measure `P.liftedMeasure` orients the original
  RDRS rule `R` in the projected strict relation `P.ltA'`, that is,
  `Orients R P.liftedMeasure P.ltA'`.
Does not prove: termination of any concrete rewriting system, or that
  `P.ltA'` is well-founded.
Relation: abstract `RDRSStep B S N T`; not a concrete rewriting
  relation.
Closure: one-step on the abstract step pair.
Strategy: not applicable.
Trust: kernel-only. The proof uses only the field equations
  `P.E.erase_commutes_lhs` and `P.E.erase_commutes_rhs` together with
  `P.projected_orientation`; no `decide`, `native_decide`, or external
  trust appears.
Scope: parametric over `P`.
-/
theorem lifted_orients :
    Orients R P.liftedMeasure P.ltA' := by
  intro b s n
  show P.ltA' (P.mu' (P.E.erase (R.rhs b s n)))
              (P.mu' (P.E.erase (R.lhs b s n)))
  rw [P.E.erase_commutes_lhs, P.E.erase_commutes_rhs]
  exact P.projected_orientation b s n

/--
Proves: every `ProjectionEscape R` exhibits a quintuple
  `(T', A', E, mu', ltA')` such that `Orients E.Rproj mu' ltA'`
  holds; that is, every inhabitant of `ProjectionEscape R` carries
  positive projected-orientation evidence.
Does not prove: that there exists a `ProjectionEscape R` for any
  specific `R` (this is an inhabitant-extracting statement, not an
  existence-of-inhabitant statement).
Relation: abstract `RDRSStep B S N T`; not a concrete rewriting
  relation.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only. The witness is `P.projected_orientation`; no
  decide / native_decide / external trust appears.
Scope: parametric over `P`.
-/
theorem requires_positive_evidence (P : ProjectionEscape R) :
    ∃ (T' A' : Type) (E : PayloadForgetErasure R T')
      (mu' : T' → A') (ltA' : A' → A' → Prop),
      Orients E.Rproj mu' ltA' :=
  ⟨P.T', P.A', P.E, P.mu', P.ltA', P.projected_orientation⟩

end ProjectionEscape

/--
Proves: the audit anchor String for
  `ProjectionEscape.requires_positive_evidence` is the fully-qualified
  Lean name as a `String` value.
Does not prove: anything about the underlying theorem.
Relation: not applicable.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: downstream registries cite this constant when wiring the
  projection branch into the eventual classifier.
-/
def rdrs_projection_escape_positive_evidence_anchor : String :=
  "OperatorKO7.RDRSProjectionSyntax.ProjectionEscape.requires_positive_evidence"

/--
Proves: a String constant recording that the plain `ProjectionEscape`
  surface is superseded by
  `OperatorKO7.RDRSProjectionTransaction.ProjectionTransactionEscape`,
  which adds the seed-collapse (phi), counter-factorisation, and
  projected well-foundedness obligations.
Does not prove: anything mathematical; this is a documentation marker.
Relation: not applicable.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: downstream classifiers should target the transaction surface;
  the plain form remains available as a lower-level building block via
  `OperatorKO7.RDRSProjectionTransaction.ofProjectionEscape`, once the
  caller also supplies projected well-foundedness.
-/
def rdrs_projection_syntax_superseded_marker : String :=
  "OperatorKO7.RDRSProjectionSyntax: lower-level; final classifier surface in OperatorKO7.RDRSProjectionTransaction"

end OperatorKO7.RDRSProjectionSyntax
