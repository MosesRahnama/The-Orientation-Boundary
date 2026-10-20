import OperatorKO7.Meta.RDRSRawDirectMeasure

/-!
# RDRS Method Certificate Syntax (U2 Route B, normalization + payloadSensitive?)

This module pairs the raw direct-measure syntax of
`Meta/RDRSRawDirectMeasure.lean` with a normalized descent-certificate
syntax, a deterministic total normalization function, and a decidable
syntactic `payloadSensitive?` predicate. The module ships the basic
soundness and completeness statements that are provable now without
importing U1 semantic substrate.

Scope explicitly carved out by the dispatch:

* No DP processors, full MSPO, arbitrary monotone algebras, arbitrary
  semantic quotients, or unrestricted semantic labeling appear as
  direct-measure constructors. The closed grammar lives in
  `Meta/RDRSRawDirectMeasure.lean`.
* No U1 modules are imported. The soundness and completeness facts are
  about the closed syntax of `RawDirectMeasure` / `RawDirectOrder`, not
  about semantic step relations or denotational interpretations.

Provided surfaces:

* `RawDirectCertificate` -- the raw certificate triple
  `(measure, order, strict_descent_claim)`.
* `NormalizedDescentCertificate` -- the closed-grammar normalized form,
  with two cases: `strictDescent` (a measure / order pair carrying a
  strict-descent claim) and `abstain` (the certificate does not claim
  strict descent and is rejected up front).
* `normalize : RawDirectCertificate -> NormalizedDescentCertificate` --
  deterministic total normalization. The function is structural: it
  preserves the measure / order syntax verbatim when the certificate
  carries a strict-descent claim, and routes to `abstain` otherwise.
* `payloadSensitive? : NormalizedDescentCertificate -> Bool` --
  decidable syntactic test: true iff the normalized certificate's
  strict-descent measure mentions a payload-role occurrence counter.
  An `abstain` certificate is never payload-sensitive (the test returns
  `false`).
* `payloadSensitive?_sound` -- if the normalized form is
  `payloadSensitive?`, then the underlying raw measure contains a
  payload-role occurrence counter (`containsPayloadOccur = true`).
* `payloadSensitive?_complete` -- if the raw measure contains a
  payload-role occurrence counter and the certificate carries a
  strict-descent claim, then the normalized form is payload-sensitive.
* `normalize_total` -- normalization is total (every raw direct
  certificate produces a normalized descent certificate).
* `payloadSensitive?_decidable` -- `payloadSensitive?` is decidable on
  every normalized descent certificate (immediate from Boolean
  equality).

No proof placeholder is used and no top-level postulate is declared.
-/

namespace OperatorKO7.RDRSMethodCertificate

open OperatorKO7.RDRSRawDirectMeasure

/-- A raw direct certificate is the orienter's submission: a raw measure,
a raw order, and a Boolean flag declaring that the orienter claims strict
descent on the rule's lhs / rhs pair. The flag is the only side hint the
raw form carries; normalization either preserves it as a strict-descent
case or routes the certificate to `abstain`. -/
structure RawDirectCertificate where
  measure        : RawDirectMeasure
  order          : RawDirectOrder
  strictDescent  : Bool
  deriving DecidableEq, Repr

/-- Normalized descent-certificate syntax.

The grammar has two cases. `strictDescent` carries a measure / order pair
on which the orienter has claimed strict descent; `abstain` is the
normalized form for certificates whose strict-descent flag was not set.
The `abstain` case is the syntactic refusal slot the universal theorem
will branch on. -/
inductive NormalizedDescentCertificate
  | strictDescent (m : RawDirectMeasure) (o : RawDirectOrder)
  | abstain
  deriving DecidableEq, Repr

/-- Deterministic total normalization. Preserves the measure / order
syntax verbatim when the certificate carries a strict-descent claim;
routes to `abstain` otherwise. This is a pure structural function over
the closed raw grammar -- no semantic interpretation occurs here. -/
def normalize (c : RawDirectCertificate) : NormalizedDescentCertificate :=
  match c.strictDescent with
  | true  => NormalizedDescentCertificate.strictDescent c.measure c.order
  | false => NormalizedDescentCertificate.abstain

/-- Decidable syntactic test for payload sensitivity on a normalized
certificate. Returns `true` iff the strict-descent branch's measure
mentions a payload-role occurrence counter. `abstain` is never
payload-sensitive. -/
def payloadSensitive? : NormalizedDescentCertificate → Bool
  | .strictDescent m _ => m.containsPayloadOccur
  | .abstain           => false

/-- Convenience: lift `payloadSensitive?` to the raw certificate level. -/
def rawPayloadSensitive? (c : RawDirectCertificate) : Bool :=
  payloadSensitive? (normalize c)

/-! ### Decidability

`payloadSensitive?` returns `Bool`, so the equality `payloadSensitive? c =
true` is decidable by `Bool` reflection. The instance below makes that
decidability available at use sites without re-deriving it on each call. -/

instance payloadSensitive?_decidable (c : NormalizedDescentCertificate) :
    Decidable (payloadSensitive? c = true) :=
  inferInstance

instance rawPayloadSensitive?_decidable (c : RawDirectCertificate) :
    Decidable (rawPayloadSensitive? c = true) :=
  inferInstance

/-! ### Soundness, completeness, totality -/

/-- Normalization is total: every raw direct certificate maps to a
normalized descent certificate. The statement is propositional non-
emptiness; the proof is by case analysis on the `strictDescent` flag. -/
theorem normalize_total (c : RawDirectCertificate) :
    ∃ n : NormalizedDescentCertificate, normalize c = n :=
  ⟨normalize c, rfl⟩

/-- Soundness of `payloadSensitive?` on the strict-descent branch: when
the normalized form is payload-sensitive, the underlying measure must
syntactically contain a payload-role occurrence counter. -/
theorem payloadSensitive?_sound
    {m : RawDirectMeasure} {o : RawDirectOrder} :
    payloadSensitive? (NormalizedDescentCertificate.strictDescent m o) = true →
      m.containsPayloadOccur = true := by
  intro h
  exact h

/-- Soundness of `payloadSensitive?` on `abstain`: an abstaining
certificate is never reported payload-sensitive. -/
theorem payloadSensitive?_abstain_false :
    payloadSensitive? NormalizedDescentCertificate.abstain = false := rfl

/-- Completeness of `payloadSensitive?` for the strict-descent branch:
when the underlying measure mentions a payload-role occurrence counter
and the certificate carries a strict-descent claim, the normalized form
is payload-sensitive. -/
theorem payloadSensitive?_complete
    (c : RawDirectCertificate)
    (hStrict : c.strictDescent = true)
    (hPayload : c.measure.containsPayloadOccur = true) :
    payloadSensitive? (normalize c) = true := by
  unfold normalize payloadSensitive?
  rw [hStrict]
  exact hPayload

/-- An abstaining raw certificate normalizes to `abstain`. -/
theorem normalize_abstain_of_not_strict
    (c : RawDirectCertificate) (hAbstain : c.strictDescent = false) :
    normalize c = NormalizedDescentCertificate.abstain := by
  unfold normalize
  rw [hAbstain]

/-- A raw certificate that does not claim strict descent is never
payload-sensitive after normalization. -/
theorem rawPayloadSensitive?_abstain
    (c : RawDirectCertificate) (hAbstain : c.strictDescent = false) :
    rawPayloadSensitive? c = false := by
  unfold rawPayloadSensitive?
  rw [normalize_abstain_of_not_strict c hAbstain]
  rfl

/-- A raw certificate whose strict-descent claim is on AND whose measure
syntactically mentions the payload role is reported payload-sensitive at
the raw level. This is the raw-level statement of the
soundness/completeness biconditional, restricted to the strict-descent
branch. -/
theorem rawPayloadSensitive?_iff_strict_and_contains
    (c : RawDirectCertificate) :
    rawPayloadSensitive? c = true ↔
      c.strictDescent = true ∧ c.measure.containsPayloadOccur = true := by
  unfold rawPayloadSensitive? normalize payloadSensitive?
  cases hStrict : c.strictDescent with
  | true =>
      simp
  | false =>
      simp

/-- Per-constructor smoke pin: the trivial payload-only measure
`occurCount PayloadRole.payload` (with any natLt order, strict-descent
claim true) is payload-sensitive. -/
theorem rawPayloadSensitive?_payload_natLt :
    rawPayloadSensitive?
        { measure := RawDirectMeasure.occurCount PayloadRole.payload
          order := RawDirectOrder.natLt
          strictDescent := true } = true := rfl

/-- Per-constructor smoke pin: the trivial counter-only measure is not
payload-sensitive (mentions only the counter role, not payload). -/
theorem rawPayloadSensitive?_counter_not :
    rawPayloadSensitive?
        { measure := RawDirectMeasure.occurCount PayloadRole.counter
          order := RawDirectOrder.natLt
          strictDescent := true } = false := rfl

end OperatorKO7.RDRSMethodCertificate
