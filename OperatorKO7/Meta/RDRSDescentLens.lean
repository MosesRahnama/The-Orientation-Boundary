/-!
# RDRS Descent Lens (Milestone U1, Sprint U1)

B-parametric descent-lens interface for the universal payload-sensitive
direct-measure project.

Roadmap source: `OperatorKO7/Expansion/Universal_Payload_Sensitive_Direct_Measures_Roadmap.md`
Milestone U1, Sprint U1, file `Meta/RDRSDescentLens.lean`.

Bible compliance:
- W2: `set_option autoImplicit false` set below.
- W8: every theorem and `def` exposing a Prop-valued surface carries the
  structured Proves / Does not prove / Relation / Closure / Strategy /
  Trust / Scope docstring template.
- W5: no `native_decide` or `bv_decide` in this file.
- R1: no `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `extern`,
  `implemented_by`, `@[csimp]`, `native_decide`, `bv_decide`, or
  `addDeclWithoutChecking` in this file.
- Relation Gate: this file is parametric over an abstract `RDRSStep`
  carrier and does not name a concrete rewriting relation. The
  "Relation:" field for each theorem records that explicitly
  ("abstract RDRSStep step-pair; not a concrete Step / SafeStep /
  StepCtxFull / DPProblem").

This module contributes the reusable local-contradiction lemma used by
the universal direct-barrier program. A `DescentLens` adds a side
observer `q : T → Bq` to a measure `μ : T → A` and an ambient strict
relation `ltA : A → A → Prop`; the lens carries the obligation that
ambient strict descent forces the lens relation to hold on every RDRS
step. A single "pump violation" of the lens relation then blocks
uniform RDRS orientation locally, without any well-foundedness
assumption on the lens codomain.

Scope discipline:
- This file owns only the lens interface and the local contradiction
  theorem. It does not define the raw direct-measure universe
  (Milestone U2), the certificate compiler (Milestone U3), the
  classifier (Milestone U4), the boundary-relative bottleneck
  (Milestone U5), or the universal barrier capstone (Milestone U7).
- No well-foundedness or order-class assumption on the lens codomain.
-/

set_option autoImplicit false

namespace OperatorKO7.RDRSDescentLens

/-- Minimum abstract RDRS step-pair interface: an LHS and an RHS, each
parameterised by a base type `B`, step-argument type `S`, counter type
`N`, and term carrier `T`.

Relation: abstract RDRSStep step-pair; not a concrete
`Step / SafeStep / StepCtxFull / DPProblem`. Concrete carriers
(for example `OperatorKO7.StepDuplicating.RightDuplicatingRecursorSchema`)
instantiate this interface; the interface stays minimal so the
lens-pump theorem is parametric. -/
structure RDRSStep (B S N T : Type) where
  /-- Left-hand side of the rule for parameters `b`, `s`, `n`. -/
  lhs : B → S → N → T
  /-- Right-hand side of the rule for parameters `b`, `s`, `n`. -/
  rhs : B → S → N → T

variable {B S N T A : Type}

/--
Proves: the measure `μ` strictly decreases in the ambient relation
  `ltA` on every RDRS step `(b, s, n)`.
Does not prove: well-foundedness of `ltA`, termination of any concrete
  rewriting relation, or anything about `Step / SafeStep / StepCtxFull`.
Relation: abstract `RDRSStep B S N T`; not a concrete rewriting relation.
Closure: one-step on the abstract step pair (no transitive or context
  closure is taken).
Strategy: not applicable; the abstract step pair carries no strategy.
Trust: kernel-only (pure `Prop`-valued definition).
Scope: parametric over arbitrary `B`, `S`, `N`, `T`, `A`, and
  arbitrary `ltA`.
-/
def Orients (R : RDRSStep B S N T) (μ : T → A) (ltA : A → A → Prop) : Prop :=
  ∀ b s n, ltA (μ (R.rhs b s n)) (μ (R.lhs b s n))

/-- B-parametric descent lens.

A side observer `q : T → Bq` paired with a relation `leB` on the lens
codomain. The defining obligation `nonincrease_of_lt` says: whenever
ambient strict descent under `μ / ltA` fires on a step, the lens
relation must also hold on that step.

The lens codomain `Bq` is at most an unrestricted `Type`; there is no
well-foundedness or order-class assumption on `leB`. The lens-pump
local contradiction theorem below uses only `nonincrease_of_lt`.

Relation: abstract `RDRSStep B S N T`; not a concrete rewriting
relation. -/
structure DescentLens
    (R : RDRSStep B S N T) (μ : T → A) (ltA : A → A → Prop) where
  /-- Lens codomain. No well-foundedness or order-class assumption is
  imposed on this type. -/
  Bq : Type
  /-- Lens relation on the codomain. Plain `Prop`-valued binary relation;
  no well-foundedness, transitivity, or asymmetry is required. -/
  leB : Bq → Bq → Prop
  /-- Side observer that the lens projects every RDRS term through. -/
  q : T → Bq
  /-- Ambient strict descent forces the lens relation: on every step
  `(b, s, n)`, if `μ` strictly decreases in `ltA`, then `q` non-increases
  in `leB`. This is the only obligation the lens carries. -/
  nonincrease_of_lt :
    ∀ b s n,
      ltA (μ (R.rhs b s n)) (μ (R.lhs b s n)) →
        leB (q (R.rhs b s n)) (q (R.lhs b s n))

/--
Proves: there exists a triple `(b, s, n)` at which the lens relation
  `leB (q rhs) (q lhs)` fails.
Does not prove: that the lens has any other defect, or that the
  ambient orientation predicate `Orients R μ ltA` fails on its own.
Relation: abstract `RDRSStep B S N T`; not a concrete rewriting
  relation.
Closure: one-step on the abstract step pair.
Strategy: not applicable.
Trust: kernel-only (pure existential `Prop`).
Scope: parametric over the supplied lens `L`.
-/
def HasPumpViolation
    {R : RDRSStep B S N T} {μ : T → A} {ltA : A → A → Prop}
    (L : DescentLens R μ ltA) : Prop :=
  ∃ b s n, ¬ L.leB (L.q (R.rhs b s n)) (L.q (R.lhs b s n))

/--
Proves: a single pump violation of a descent lens blocks uniform
  abstract RDRS orientation, that is, `¬ Orients R μ ltA`.
Does not prove: termination of any concrete rewriting system, lack of
  weak orientation, or any property of the lens codomain ordering.
Relation: abstract `RDRSStep B S N T`; not a concrete rewriting
  relation.
Closure: one-step on the abstract step pair (no transitive or context
  closure is invoked).
Strategy: not applicable.
Trust: kernel-only. The proof composes `L.nonincrease_of_lt`,
  `HasPumpViolation`, and the orientation predicate; no
  `decide`, `native_decide`, or external trust appears.
Scope: parametric over `B`, `S`, `N`, `T`, `A`, `R`, `μ`, `ltA`, and
  the lens `L`. No well-foundedness, transitivity, or asymmetry of
  `leB` is invoked.
-/
theorem no_orients_of_lens_violation
    {R : RDRSStep B S N T} {μ : T → A} {ltA : A → A → Prop}
    (L : DescentLens R μ ltA)
    (hBad : HasPumpViolation L) :
    ¬ Orients R μ ltA := by
  intro hOrients
  obtain ⟨b, s, n, hViolate⟩ := hBad
  exact hViolate (L.nonincrease_of_lt b s n (hOrients b s n))

/--
Proves: the audit anchor String for `no_orients_of_lens_violation`
  is the fully-qualified Lean name as a `String` value.
Does not prove: anything about the theorem itself.
Relation: not applicable (this is a String constant, not a theorem).
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only (a literal String).
Scope: downstream registries cite this constant when wiring the
  local-contradiction theorem into the universal-barrier program.
-/
def rdrs_descent_lens_local_contradiction_anchor : String :=
  "OperatorKO7.RDRSDescentLens.no_orients_of_lens_violation"

end OperatorKO7.RDRSDescentLens
