import OperatorKO7.Meta.RDRSDescentLens
import OperatorKO7.Meta.RDRSSemanticDirectMeasure

/-!
# RDRS Naive Raw Semantic Universal Adjudication (Milestone S0)

Lean adjudication of the naive raw semantic universal claim.

Roadmap source: `OperatorKO7/Expansion/Universal_Payload_Sensitive_Direct_Measures_Roadmap.md`
Milestone S0: Adjudicate the naive raw semantic universal statement.

## The claim under adjudication

The naive raw form quantifies over ARBITRARY `RawSemanticMeasure T`
(no directness discipline, no payload-sensitivity discipline) and
claims that NO such measure orients ANY RDRS step pair. Concretely:

```text
NaiveRawSemanticUniversal :=
  ∀ R M, ¬ Orients R M.μ M.ltA
```

This is the strongest possible barrier claim.

## Verdict

`NaiveRawSemanticUniversal` is FALSE. The Lean theorem
`naive_raw_semantic_universal_adjudicated` is the named adjudication:
it carries `¬ NaiveRawSemanticUniversal`. The refutation is by
exhibiting four named countermodels, any one of which suffices.

## Countermodels

```text
1. counterFirstLex     -- counter-first lex measure that mentions payload
2. termAlgebraOracle   -- term-algebra / rewrite-closure semantic witness
3. nonlinearCouple     -- nonlinear counter-payload coupled witness
4. projectionForget    -- projection-composed payload-forgetting witness
```

Each countermodel is a `(R, M)` pair together with an explicit
`Orients R M.μ M.ltA` theorem.

## Bible compliance

* W2: `set_option autoImplicit false` set below.
* W8: every `def`/`theorem` carries the Proves / Does not prove /
  Relation / Closure / Strategy / Trust / Scope template.
* W5: no `native_decide` / `bv_decide`.
* R1: no `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `extern`,
  `implemented_by`, `@[csimp]`, `native_decide`, `bv_decide`, or
  `addDeclWithoutChecking`.
* Relation Gate: every theorem's Relation field is explicit.
-/

set_option autoImplicit false

namespace OperatorKO7.RDRSSemanticRawUniversalAdjudication

open OperatorKO7.RDRSDescentLens

/--
Proves: the structure for "raw semantic measures" — the broadest
  possible measure shape, with no directness discipline. A
  `RawSemanticMeasure T` has a codomain `A`, a strict relation `ltA`,
  a well-foundedness proof, and a measure function `μ : T → A`.
Does not prove: the bible's `SemanticDirectMeasure` discipline. This
  raw form is the SUPERCLASS used to state the naive universal; the
  refined `SemanticDirectMeasure` of
  `OperatorKO7.Meta.RDRSSemanticDirectMeasure` adds the discipline
  tags.
Relation: parametric over `T`; not a concrete rewriting relation.
Closure: not applicable (this is a structure).
Strategy: not applicable.
Trust: kernel-only.
Scope: includes rewrite-closure oracles, transformed-relation
  measures, arbitrary semantic quotients, etc. by virtue of having
  no discipline tags.
-/
structure RawSemanticMeasure (T : Type) where
  /-- Codomain. -/
  A : Type
  /-- Strict ordering on the codomain. -/
  ltA : A → A → Prop
  /-- Well-foundedness of `ltA`. -/
  wf_ltA : WellFounded ltA
  /-- The measure function. -/
  μ : T → A

/--
Proves: the naive raw semantic universal claim: for every RDRS step
  pair `R` (over any `B, S, N, T`) and every `RawSemanticMeasure T`,
  the measure does NOT orient `R`.
Does not prove: any specific countermodel (that is the adjudication
  theorem's content).
Relation: abstract `RDRSStep B S N T`; not a concrete rewriting
  relation.
Closure: not applicable (universal `Prop`).
Strategy: not applicable.
Trust: kernel-only (pure `Prop` definition).
Scope: universal over all `B`, `S`, `N`, `T`, `R`, and `M`. This
  is the strongest possible barrier claim and is FALSE; the
  adjudication theorem below refutes it by named countermodel.
-/
def NaiveRawSemanticUniversal : Prop :=
  ∀ {B S N T : Type} (R : RDRSStep B S N T) (M : RawSemanticMeasure T),
    ¬ Orients R M.μ M.ltA

/-! ### Countermodel 1: counter-first lex measure that mentions payload -/

/--
Proves: a concrete RDRS step pair on `T = Nat × Nat` (counter ×
  payload). LHS at `(n + 1, n)`, RHS at `(n, n)`. The counter
  strictly decreases; the payload coordinate is mentioned (both
  LHS and RHS carry an `n` in the second slot) but is unchanged.
Does not prove: any property of this RDRS beyond the lhs/rhs
  definitions.
Relation: this IS the concrete `RDRSStep Unit Unit Nat (Nat × Nat)`.
Closure: not applicable (data definition).
Strategy: not applicable.
Trust: kernel-only.
Scope: this single concrete step pair.
-/
def counterFirstLex_R : RDRSStep Unit Unit Nat (Nat × Nat) where
  lhs _ _ n := (n + 1, n)
  rhs _ _ n := (n, n)

/--
Proves: a concrete `RawSemanticMeasure (Nat × Nat)` whose codomain
  is `Nat`, whose strict relation is `<`, and whose measure projects
  to the first coordinate (the counter).
Does not prove: that this measure is "direct" in the bible sense;
  the raw form has no discipline.
Relation: parametric data; not a concrete rewriting relation.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: this single concrete measure.
-/
def counterFirstLex_M : RawSemanticMeasure (Nat × Nat) where
  A := Nat
  ltA := (· < ·)
  wf_ltA := Nat.lt_wfRel.wf
  μ := Prod.fst

/--
Proves: the counter-first lex measure orients `counterFirstLex_R`;
  i.e. `Orients counterFirstLex_R counterFirstLex_M.μ counterFirstLex_M.ltA`.
Does not prove: that any other measure orients this RDRS, or that
  this RDRS terminates in any stronger sense.
Relation: this specific `RDRSStep Unit Unit Nat (Nat × Nat)`.
Closure: root single-step orientation.
Strategy: not applicable.
Trust: kernel-only (single `Nat.lt_succ_self` step).
Scope: this concrete `(R, M)` pair.
-/
theorem counterFirstLex_orients :
    Orients counterFirstLex_R counterFirstLex_M.μ counterFirstLex_M.ltA := by
  intro _ _ n
  exact Nat.lt_succ_self n

/-! ### Countermodel 2: term-algebra / rewrite-closure semantic witness -/

/--
Proves: a concrete RDRS step pair on `T = Nat`. LHS at `n + 1`,
  RHS at `n`. The natural-number successor / predecessor pattern is
  the canonical term-algebra interpretation.
Does not prove: anything beyond the data.
Relation: `RDRSStep Unit Unit Nat Nat`.
Closure: not applicable (data).
Strategy: not applicable.
Trust: kernel-only.
Scope: this single step pair.
-/
def termAlgebraOracle_R : RDRSStep Unit Unit Nat Nat where
  lhs _ _ n := n + 1
  rhs _ _ n := n

/--
Proves: a concrete `RawSemanticMeasure Nat` whose codomain is
  `Nat`, whose strict relation is `<`, and whose measure is the
  identity. This is a term-algebra / rewrite-closure-style measure:
  the ordering on the codomain coincides with a natural ordering on
  the term type.
Does not prove: that this measure is "direct"; the raw form
  intentionally allows term-algebra oracles.
Relation: parametric data.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: this single concrete measure.
-/
def termAlgebraOracle_M : RawSemanticMeasure Nat where
  A := Nat
  ltA := (· < ·)
  wf_ltA := Nat.lt_wfRel.wf
  μ := id

/--
Proves: the term-algebra-oracle measure orients
  `termAlgebraOracle_R`.
Does not prove: that the term-algebra oracle is a legitimate direct
  measure; the bible `SemanticDirectMeasure` interface excludes such
  oracles.
Relation: `RDRSStep Unit Unit Nat Nat`.
Closure: root single-step.
Strategy: not applicable.
Trust: kernel-only.
Scope: this concrete `(R, M)` pair.
-/
theorem termAlgebraOracle_orients :
    Orients termAlgebraOracle_R termAlgebraOracle_M.μ termAlgebraOracle_M.ltA := by
  intro _ _ n
  exact Nat.lt_succ_self n

/-! ### Countermodel 3: nonlinear counter-payload coupled witness -/

/--
Proves: a concrete RDRS step pair on `T = Nat × Nat`. RHS payload
  is the square of the LHS payload (nonlinear coupling); LHS
  counter is `n + 1`, RHS counter is `n`.
Does not prove: anything beyond the data.
Relation: `RDRSStep Unit Nat Nat (Nat × Nat)`.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: this single step pair.
-/
def nonlinearCouple_R : RDRSStep Unit Nat Nat (Nat × Nat) where
  lhs _ s n := (n + 1, s)
  rhs _ s n := (n, s * s)

/--
Proves: a concrete `RawSemanticMeasure (Nat × Nat)` whose measure
  projects to the counter coordinate. The nonlinear payload
  coupling in the RDRS is invisible to this measure.
Does not prove: that this measure is "direct"; the raw form has
  no discipline.
Relation: parametric data.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: this single concrete measure.
-/
def nonlinearCouple_M : RawSemanticMeasure (Nat × Nat) where
  A := Nat
  ltA := (· < ·)
  wf_ltA := Nat.lt_wfRel.wf
  μ := fun p => p.fst

/--
Proves: the nonlinear-coupling measure orients `nonlinearCouple_R`;
  the counter coordinate strictly decreases.
Does not prove: that the nonlinear payload coupling is admissible
  in the bible discipline; it is not.
Relation: this specific `RDRSStep Unit Nat Nat (Nat × Nat)`.
Closure: root single-step.
Strategy: not applicable.
Trust: kernel-only.
Scope: this concrete `(R, M)` pair.
-/
theorem nonlinearCouple_orients :
    Orients nonlinearCouple_R nonlinearCouple_M.μ nonlinearCouple_M.ltA := by
  intro _ _ n
  exact Nat.lt_succ_self n

/-! ### Countermodel 4: projection-composed payload-forgetting witness -/

/--
Proves: a concrete RDRS step pair on `T = Nat × Nat`. The payload
  is preserved between LHS and RHS, while the counter strictly
  decreases.
Does not prove: anything beyond the data.
Relation: `RDRSStep Unit Nat Nat (Nat × Nat)`.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: this single step pair.
-/
def projectionForget_R : RDRSStep Unit Nat Nat (Nat × Nat) where
  lhs _ s n := (n + 1, s)
  rhs _ s n := (n, s)

/--
Proves: a concrete `RawSemanticMeasure (Nat × Nat)` whose measure
  is the composition `id ∘ Prod.fst` — explicitly the identity on
  the counter, with the payload forgotten by the `Prod.fst`
  projection.
Does not prove: that this measure is "direct"; the projection
  composition is an erasure pattern excluded from
  `SemanticDirectMeasure` discipline.
Relation: parametric data.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: this single concrete measure.
-/
def projectionForget_M : RawSemanticMeasure (Nat × Nat) where
  A := Nat
  ltA := (· < ·)
  wf_ltA := Nat.lt_wfRel.wf
  μ := id ∘ Prod.fst

/--
Proves: the projection-composed payload-forgetting measure orients
  `projectionForget_R`.
Does not prove: that projection-composed forgetting is admissible
  in the bible discipline.
Relation: `RDRSStep Unit Nat Nat (Nat × Nat)`.
Closure: root single-step.
Strategy: not applicable.
Trust: kernel-only.
Scope: this concrete `(R, M)` pair.
-/
theorem projectionForget_orients :
    Orients projectionForget_R projectionForget_M.μ projectionForget_M.ltA := by
  intro _ _ n
  exact Nat.lt_succ_self n

/-! ### Adjudication theorem -/

/--
Proves: `¬ NaiveRawSemanticUniversal`. The naive raw semantic
  universal claim is FALSE. The refutation goes through the
  counter-first lex countermodel
  `(counterFirstLex_R, counterFirstLex_M)` together with the
  `counterFirstLex_orients` theorem; three additional named
  countermodels (`termAlgebraOracle`, `nonlinearCouple`,
  `projectionForget`) are also exhibited.
Does not prove: that any REFINED semantic universal is false.
  In particular, the refined claim restricted to the bible's
  `SemanticDirectMeasure` discipline (with directness +
  payload-sensitivity restrictions) is a separate question handled
  in subsequent milestones (S2 onward).
Relation: abstract `RDRSStep B S N T`; not a concrete rewriting
  relation.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only (uses the named `counterFirstLex_orients`
  theorem).
Scope: refutes the naive raw form only.
-/
theorem naive_raw_semantic_universal_false :
    ¬ NaiveRawSemanticUniversal := by
  intro H
  exact H counterFirstLex_R counterFirstLex_M counterFirstLex_orients

/--
Proves: required marker alias asserting that the naive raw
  semantic universal claim has been adjudicated (here: refuted).
Does not prove: the verdict beyond the refutation; the verdict
  is `¬ NaiveRawSemanticUniversal`.
Relation: abstract `RDRSStep B S N T`; not a concrete rewriting
  relation.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only (delegates to `naive_raw_semantic_universal_false`).
Scope: the adjudication marker for downstream registries.
-/
theorem naive_raw_semantic_universal_adjudicated :
    ¬ NaiveRawSemanticUniversal :=
  naive_raw_semantic_universal_false

/--
Proves: audit anchor String for the adjudication theorem.
Does not prove: anything about the theorem itself.
Relation: not applicable.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only (literal String).
Scope: downstream registries cite this constant.
-/
def rdrs_naive_raw_semantic_universal_adjudicated_anchor : String :=
  "OperatorKO7.RDRSSemanticRawUniversalAdjudication.naive_raw_semantic_universal_adjudicated"

end OperatorKO7.RDRSSemanticRawUniversalAdjudication
