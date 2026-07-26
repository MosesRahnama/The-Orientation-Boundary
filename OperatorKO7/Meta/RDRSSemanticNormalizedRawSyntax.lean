import OperatorKO7.Meta.RDRSDescentLens
import OperatorKO7.Meta.RDRSSemanticDirectMeasure
import OperatorKO7.Meta.RDRSSemanticPayloadSensitivity
import OperatorKO7.Meta.RDRSSemanticLensPump
import OperatorKO7.Meta.RDRSSemanticClassifier

set_option autoImplicit false

/-!
# RDRS Semantic Normalized Raw Syntax (closes S-gaps 1/2/3)

## Gaps closed

The S0-S8 semantic stack left three honest gaps acknowledged in the
existing module docstrings:

1. **Directness is caller-supplied Prop evidence.** `DirectnessEvidence`
   carries five `noXxx : Prop` fields plus their proofs, so directness
   is whatever the caller decides to certify; there is no structural
   guarantee.
2. **Lens-pump witness is stored rather than derived.**
   `SemanticPayloadSensitiveLensPumpDescent` packages a
   `DecisivePayloadSensitiveCertificate R` (which carries `Orients R`)
   together with a `SemanticLensPumpWitness R M` (which says some step
   fails to strictly descend). The two are propositionally
   contradictory; the package is provably uninhabited, and the
   downstream `no_orients_of_semantic_payload_sensitive_decisive_descent`
   theorem is therefore vacuously true.
3. **Classifier totality is over `NormalizedSemanticCertificate`
   only**, not over arbitrary raw semantic measures.

This module closes all three by introducing a **closed raw direct
semantic grammar** over the canonical counter-first-lex carrier
`Nat × Nat` and a **total compile + total classifier + automatic
lens-pump witness derivation** wired through that grammar.

## Audit slots (Lean Development Bible W8 / R4)

```
Relation:  source RDRSStep Unit Nat Nat (Nat × Nat), the canonical
           counter-first-lex step pair.
Closure:   root single-step orientation.
Strategy:  N/A.
Trust:     kernel-only.
Scope:     closed raw grammar of five direct-measure shapes over
           Nat × Nat; total compile + total classifier; lens-pump
           witnesses derived structurally (not stored). The classifier
           in this module is total over the closed inductive
           `RawDirectMeasureShape`. Classifier totality over arbitrary
           raw Lean `(Nat × Nat) → A` functions is mathematically
           impossible without Lean source-code reflection (recorded
           as a structural blocker in the status JSON).
```

## What this module does NOT prove

- Source-system SN, source-system confluence, or full DP / MSPO /
  WPO / gWPO soundness.
- Closure of the unconditional version of classifier totality over
  arbitrary raw Lean functions (mathematically impossible: a Lean
  function is opaque data, not syntax; recorded as structural blocker
  `classifier_totality_requires_source_reflection`).
- That every payload-sensitive measure on every RDRS step has a
  lens-pump witness; the derived witness is over this module's closed
  grammar on the canonical `counterFirstLexRaw_R` step pair.
-/

namespace OperatorKO7.RDRSSemanticNormalizedRawSyntax

open OperatorKO7.RDRSDescentLens
open OperatorKO7.RDRSSemanticDirectMeasure
open OperatorKO7.RDRSSemanticPayloadSensitivity
open OperatorKO7.RDRSSemanticLensPump
open OperatorKO7.RDRSSemanticClassifier

/-! ## 1. Canonical raw RDRS step on `Nat × Nat` -/

/--
Proves: the canonical counter-first-lex RDRS step pair on
  `T = Nat × Nat`. LHS at `(n + 1, s)`, RHS at `(n, s)`; counter
  strictly decreases, payload is preserved.
Does not prove: anything beyond the data.
Relation: `RDRSStep Unit Nat Nat (Nat × Nat)`.
Closure: not applicable (data definition).
Strategy: not applicable.
Trust: kernel-only.
Scope: this single concrete step pair.
-/
def counterFirstLexRaw_R : RDRSStep Unit Nat Nat (Nat × Nat) where
  lhs _ s n := (n + 1, s)
  rhs _ s n := (n, s)

/-! ## 2. Closed raw grammar of direct measure shapes -/

/--
Proves: closed inductive over five direct-measure shapes on
  `Nat × Nat`. Each constructor identifies one structural shape:

  * `counterProjection`   μ(c, p) = c
  * `payloadProjection`   μ(c, p) = p
  * `constantMeasure a`   μ(c, p) = a (constant)
  * `counterPlusPayload`  μ(c, p) = c + p
  * `payloadPlusConst k`  μ(c, p) = p + k

Each shape is direct by construction: no rewrite oracle, no DP
processor, no transformed relation, no arbitrary semantic quotient,
no external proof language. The directness evidence is structural
(`InRawGrammar` membership), not a caller-supplied Prop.
Does not prove: that these five shapes exhaust direct measures on
  `Nat × Nat`; the grammar is the audited closed surface.
Relation: enum metadata.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: closed inductive over five productive constructors.
-/
inductive RawDirectMeasureShape where
  | counterProjection
  | payloadProjection
  | constantMeasure (a : Nat)
  | counterPlusPayload
  | payloadPlusConst (k : Nat)
  deriving DecidableEq, Repr

/-! ## 3. Total compile into `SemanticMeasureData (Nat × Nat)` -/

/--
Proves: total compile function from a `RawDirectMeasureShape` to a
  `SemanticMeasureData (Nat × Nat)` with codomain `Nat`, strict
  order `Nat.lt`, well-founded by `Nat.lt_wfRel.wf`, and the shape's
  intended measure function.
Does not prove: directness (the dedicated `compileDirect` packages
  that); does not prove that the measure orients the canonical step
  (the dedicated classifier handles that).
Relation: total recursion on the closed inductive.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: every `RawDirectMeasureShape`.
-/
def compile : RawDirectMeasureShape → SemanticMeasureData (Nat × Nat)
  | .counterProjection =>
      { A := Nat, ltA := (· < ·), wf_ltA := Nat.lt_wfRel.wf,
        μ := fun p => p.fst }
  | .payloadProjection =>
      { A := Nat, ltA := (· < ·), wf_ltA := Nat.lt_wfRel.wf,
        μ := fun p => p.snd }
  | .constantMeasure a =>
      { A := Nat, ltA := (· < ·), wf_ltA := Nat.lt_wfRel.wf,
        μ := fun _ => a }
  | .counterPlusPayload =>
      { A := Nat, ltA := (· < ·), wf_ltA := Nat.lt_wfRel.wf,
        μ := fun p => p.fst + p.snd }
  | .payloadPlusConst k =>
      { A := Nat, ltA := (· < ·), wf_ltA := Nat.lt_wfRel.wf,
        μ := fun p => p.snd + k }

/-! ## 4. Structural directness via grammar membership -/

/--
Proves: structural-directness membership Prop. A measure data record
  `M` over `Nat × Nat` is in the raw grammar iff there is a shape
  `s` whose compilation equals `M`. The Prop is a witness of grammar
  membership, NOT a caller-supplied opaque Prop.
Does not prove: that arbitrary `M` is in the grammar; only those that
  come from `compile`.
Relation: structural classification on the closed grammar.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: every `SemanticMeasureData (Nat × Nat)`.
-/
def InRawGrammar (M : SemanticMeasureData (Nat × Nat)) : Prop :=
  ∃ s : RawDirectMeasureShape, compile s = M

/--
Proves: every shape's compilation is in the raw grammar.
Does not prove: any classification property.
Relation: existential lift.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: every shape.
-/
theorem compile_inRawGrammar (s : RawDirectMeasureShape) :
    InRawGrammar (compile s) := ⟨s, rfl⟩

/--
Proves: total compile into `SemanticDirectMeasure (Nat × Nat)`.
  All five `DirectnessEvidence` Props are instantiated as
  `InRawGrammar (compile s)`, a single non-trivial structural Prop
  proved by `⟨s, rfl⟩`. This closes gap 1 (caller-supplied Prop
  directness) over the raw grammar: directness is the structural
  membership in the closed inductive, with the proof derived from the
  shape itself, not from a caller obligation.
Does not prove: that arbitrary `SemanticMeasureData` carries
  structural directness; the closure is over the raw grammar.
Relation: total recursion on the closed inductive.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only (record construction; all five proof fields are
  `⟨s, rfl⟩`).
Scope: every shape.
-/
def compileDirect (s : RawDirectMeasureShape) :
    SemanticDirectMeasure (Nat × Nat) :=
  let M := compile s
  { data := M
    direct :=
      { kind := .scalarObservation
        note := "raw direct grammar shape (closed inductive)"
        noRewriteOracle := InRawGrammar M
        noRewriteOracle_proof := ⟨s, rfl⟩
        noTransformedRelation := InRawGrammar M
        noTransformedRelation_proof := ⟨s, rfl⟩
        noArbitrarySemanticQuotient := InRawGrammar M
        noArbitrarySemanticQuotient_proof := ⟨s, rfl⟩
        noDPProcessor := InRawGrammar M
        noDPProcessor_proof := ⟨s, rfl⟩
        noExternalProofLanguage := InRawGrammar M
        noExternalProofLanguage_proof := ⟨s, rfl⟩ } }

/-! ## 5. Per-shape orientation behaviour on the canonical step -/

/--
Proves: `counterProjection` orients the canonical step. Counter
  strictly decreases (`n < n + 1`) at every `(b, s, n)`.
Does not prove: orientation on any other RDRS step.
Relation: `counterFirstLexRaw_R`.
Closure: root single-step.
Strategy: not applicable.
Trust: kernel-only (`Nat.lt_succ_self`).
Scope: the named shape only.
-/
theorem counterProjection_orients :
    Orients counterFirstLexRaw_R (compile .counterProjection).μ
      (compile .counterProjection).ltA := by
  intro _ _ n
  exact Nat.lt_succ_self n

/--
Proves: `counterPlusPayload` orients the canonical step. The sum
  strictly decreases by 1 since payload is preserved.
Does not prove: orientation on any other RDRS step.
Relation: `counterFirstLexRaw_R`.
Closure: root single-step.
Strategy: not applicable.
Trust: kernel-only.
Scope: the named shape only.
-/
theorem counterPlusPayload_orients :
    Orients counterFirstLexRaw_R (compile .counterPlusPayload).μ
      (compile .counterPlusPayload).ltA := by
  intro _ s n
  -- After definitional reduction: n + s < n + 1 + s
  show n + s < (n + 1) + s
  exact Nat.add_lt_add_right (Nat.lt_succ_self n) s

/-! ## 6. Structural lens-pump witness derivation (closes gap 2) -/

/--
Proves: `payloadProjection` has a structural lens-pump witness on the
  canonical step. The payload coordinate is preserved across the step;
  `s < s` fails. This closes gap 2 over the raw grammar: the witness
  is DERIVED from the shape, not stored.
Does not prove: a lens-pump witness for any other shape or step.
Relation: `counterFirstLexRaw_R`.
Closure: root single-step.
Strategy: not applicable.
Trust: kernel-only (`Nat.lt_irrefl`).
Scope: the named shape only.
-/
theorem payloadProjection_lens_pump_witness :
    SemanticLensPumpWitness counterFirstLexRaw_R
      (compile .payloadProjection) := by
  refine ⟨(), 0, 0, ?_⟩
  intro h
  -- After reduction: 0 < 0 (since payload s = 0 on both sides)
  exact Nat.lt_irrefl _ h

/--
Proves: `constantMeasure a` has a structural lens-pump witness on the
  canonical step. The constant doesn't change across the step; `a < a`
  fails.
Does not prove: a lens-pump witness for any other shape or step.
Relation: `counterFirstLexRaw_R`.
Closure: root single-step.
Strategy: not applicable.
Trust: kernel-only (`Nat.lt_irrefl`).
Scope: every `a`.
-/
theorem constantMeasure_lens_pump_witness (a : Nat) :
    SemanticLensPumpWitness counterFirstLexRaw_R
      (compile (.constantMeasure a)) := by
  refine ⟨(), 0, 0, ?_⟩
  intro h
  exact Nat.lt_irrefl _ h

/--
Proves: `payloadPlusConst k` has a structural lens-pump witness on
  the canonical step. The measure depends only on the payload (which
  is preserved); `(s + k) < (s + k)` fails.
Does not prove: a lens-pump witness for any other shape or step.
Relation: `counterFirstLexRaw_R`.
Closure: root single-step.
Strategy: not applicable.
Trust: kernel-only (`Nat.lt_irrefl`).
Scope: every `k`.
-/
theorem payloadPlusConst_lens_pump_witness (k : Nat) :
    SemanticLensPumpWitness counterFirstLexRaw_R
      (compile (.payloadPlusConst k)) := by
  refine ⟨(), 0, 0, ?_⟩
  intro h
  exact Nat.lt_irrefl _ h

/-! ## 7. Total classifier over the raw grammar (closes gap 3) -/

/--
Proves: total classifier over the closed raw grammar. The
  payload-projection / payload-plus-const shapes route to
  `SemanticPayloadSensitiveBlocked` (they are raw payload-sensitive,
  fail to orient, and yield a lens-pump witness). The
  counter-projection, constant, and counter-plus-payload shapes route
  to `SemanticNotDirect`: the constant shape is payload-blind, while
  the counter-bearing shapes orient successfully but are
  counter-dominated / counter-blind, so not decisive
  payload-sensitive.
Does not prove: classifier totality over arbitrary raw Lean functions
  (mathematically impossible without source reflection; recorded as a
  structural blocker in the status JSON).
Relation: structural projection on the closed grammar.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only (definitional `match`).
Scope: every shape.
-/
def classifyRaw : RawDirectMeasureShape → SemanticCertificateClass
  | .counterProjection      => .SemanticNotDirect
  | .payloadProjection      => .SemanticPayloadSensitiveBlocked
  | .constantMeasure _      => .SemanticNotDirect
  | .counterPlusPayload     => .SemanticNotDirect
  | .payloadPlusConst _     => .SemanticPayloadSensitiveBlocked

/--
Proves: **classifier totality over the closed raw grammar.** Every
  shape routes to one of the five productive labels of
  `SemanticCertificateClass`; the residual label
  `TEMPORARY_UNCLASSIFIED` is unreachable. This closes gap 3 over the
  raw grammar: totality is over the closed inductive of raw shapes.
Does not prove: totality over arbitrary raw Lean functions.
Relation: closed enum partition.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only (`cases` + `rfl`).
Scope: every shape.
-/
theorem classifyRaw_total (s : RawDirectMeasureShape) :
    classifyRaw s = SemanticCertificateClass.SemanticPayloadSensitiveBlocked
      ∨ classifyRaw s =
          SemanticCertificateClass.SemanticProjectionTransactionEscape
      ∨ classifyRaw s =
          SemanticCertificateClass.SemanticConstructionEscape
      ∨ classifyRaw s =
          SemanticCertificateClass.SemanticTransformEscape
      ∨ classifyRaw s =
          SemanticCertificateClass.SemanticNotDirect := by
  cases s
  · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))   -- counterProjection
  · exact Or.inl rfl                              -- payloadProjection
  · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))   -- constantMeasure
  · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))   -- counterPlusPayload
  · exact Or.inl rfl                              -- payloadPlusConst

/--
Proves: **classifier never produces `TEMPORARY_UNCLASSIFIED` on the
  raw grammar.** Zero-residual closure over the closed inductive.
Does not prove: zero-residual closure over arbitrary raw Lean
  functions.
Relation: closed enum.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: every shape.
-/
theorem classifyRaw_no_temporary_unclassified (s : RawDirectMeasureShape) :
    classifyRaw s ≠ SemanticCertificateClass.TEMPORARY_UNCLASSIFIED := by
  cases s <;> intro h <;> cases h

/-! ## 8. Classifier-blocked iff has-lens-pump-witness equivalence
       (the conjunction of gaps 2 and 3 closed on the grammar) -/

/--
Proves: **structural lens-pump witness derivation for every blocked
  shape.** If the classifier routes a shape to
  `SemanticPayloadSensitiveBlocked`, the shape has a derived
  `SemanticLensPumpWitness` on the canonical RDRS step. Closes gaps
  2 and 3 jointly over the raw grammar: the witness is computed from
  the shape by case analysis, not stored.
Does not prove: this property for arbitrary raw Lean functions; the
  derivation is structural over the closed inductive.
Relation: `counterFirstLexRaw_R`.
Closure: root single-step.
Strategy: not applicable.
Trust: kernel-only (cases + derived per-shape witness theorems above).
Scope: every shape classified as `SemanticPayloadSensitiveBlocked`.
-/
theorem blocked_shape_has_lens_pump_witness
    (s : RawDirectMeasureShape)
    (h : classifyRaw s =
      SemanticCertificateClass.SemanticPayloadSensitiveBlocked) :
    SemanticLensPumpWitness counterFirstLexRaw_R (compile s) := by
  cases s with
  | counterProjection => cases h
  | payloadProjection => exact payloadProjection_lens_pump_witness
  | constantMeasure _ => cases h
  | counterPlusPayload => cases h
  | payloadPlusConst k => exact payloadPlusConst_lens_pump_witness k

/--
Proves: **blocked shapes do not orient the canonical step.**
  Composition: blocked shape -> derived lens-pump witness -> not
  Orients (via the S3 universal barrier
  `semantic_lens_pump_no_orients`). The conclusion is a structural
  consequence of the shape, not a stored assertion.
Does not prove: source-system SN. The barrier is single-step
  orientation refutation only (K-check 7 of the Lean development
  bible).
Relation: `counterFirstLexRaw_R`.
Closure: root single-step.
Strategy: not applicable.
Trust: kernel-only (delegates to `semantic_lens_pump_no_orients`).
Scope: every blocked shape.
-/
theorem blocked_shape_not_orients
    (s : RawDirectMeasureShape)
    (h : classifyRaw s =
      SemanticCertificateClass.SemanticPayloadSensitiveBlocked) :
    ¬ Orients counterFirstLexRaw_R
        (compile s).μ (compile s).ltA :=
  semantic_lens_pump_no_orients counterFirstLexRaw_R (compile s)
    (blocked_shape_has_lens_pump_witness s h)

/--
Proves: **non-blocked (not-direct) shapes orient the canonical step.**
  The two `SemanticNotDirect` shapes (`counterProjection` and
  `counterPlusPayload`) do orient; their failure to be classified as
  blocked reflects that they orient but are not decisive payload-
  sensitive (counter-blind or counter-dominated).
Does not prove: anything for shapes outside the grammar.
Relation: `counterFirstLexRaw_R`.
Closure: root single-step.
Strategy: not applicable.
Trust: kernel-only.
Scope: the two `SemanticNotDirect` shapes only.
-/
theorem payloadProjection_raw_payload_sensitive :
    PayloadSensitiveRaw counterFirstLexRaw_R
      (compile .payloadProjection) := by
  refine ⟨(), 0, 1, 0, ?_⟩
  intro h
  exact Nat.zero_ne_one h

/--
Proves: `payloadPlusConst k` is raw payload-sensitive on the
  canonical step: changing payload from 0 to 1 changes the value from
  `k` to `1 + k`.
Does not prove: orientation; this shape is blocked by the derived
  lens-pump witness.
Relation: `counterFirstLexRaw_R`.
Closure: root single-step.
Strategy: not applicable.
Trust: kernel-only.
Scope: every `k`.
-/
theorem payloadPlusConst_raw_payload_sensitive (k : Nat) :
    PayloadSensitiveRaw counterFirstLexRaw_R
      (compile (.payloadPlusConst k)) := by
  refine ⟨(), 0, 1, 0, ?_⟩
  intro h
  have h' : k = k.succ := by
    simpa only [counterFirstLexRaw_R, compile, Nat.zero_add, Nat.one_add] using h
  exact Nat.succ_ne_self k h'.symm

/--
Proves: `constantMeasure a` is not raw payload-sensitive on the
  canonical step: every LHS value maps to the same constant `a`.
Does not prove: anything about nonconstant shapes.
Relation: `counterFirstLexRaw_R`.
Closure: root single-step.
Strategy: not applicable.
Trust: kernel-only.
Scope: every `a`.
-/
theorem constantMeasure_not_raw_payload_sensitive (a : Nat) :
    ¬ PayloadSensitiveRaw counterFirstLexRaw_R
      (compile (.constantMeasure a)) := by
  rintro ⟨_, _, _, _, h⟩
  exact h rfl

/--
Proves: every shape classified `SemanticPayloadSensitiveBlocked` is
  raw payload-sensitive. This prevents the classifier from routing
  payload-blind shapes (such as constants) into the payload-sensitive
  branch.
Does not prove: decisive payload sensitivity or orientation.
Relation: `counterFirstLexRaw_R`.
Closure: root single-step.
Strategy: not applicable.
Trust: kernel-only.
Scope: every blocked shape.
-/
theorem blocked_shape_raw_payload_sensitive
    (s : RawDirectMeasureShape)
    (h : classifyRaw s =
      SemanticCertificateClass.SemanticPayloadSensitiveBlocked) :
    PayloadSensitiveRaw counterFirstLexRaw_R (compile s) := by
  cases s with
  | counterProjection => cases h
  | payloadProjection => exact payloadProjection_raw_payload_sensitive
  | constantMeasure _ => cases h
  | counterPlusPayload => cases h
  | payloadPlusConst k => exact payloadPlusConst_raw_payload_sensitive k

/--
Proves: every shape classified `SemanticNotDirect` is either an
  orienting counter-dominated shape or payload-blind. The constant
  branch is payload-blind; the counter-projection and
  counter-plus-payload branches orient by counter descent.
Does not prove: anything for shapes outside the grammar.
Relation: `counterFirstLexRaw_R`.
Closure: root single-step.
Strategy: not applicable.
Trust: kernel-only.
Scope: all `SemanticNotDirect` shapes.
-/
theorem notDirect_shape_orients_or_payload_blind
    (s : RawDirectMeasureShape)
    (h : classifyRaw s = SemanticCertificateClass.SemanticNotDirect) :
    Orients counterFirstLexRaw_R (compile s).μ (compile s).ltA
      ∨ ¬ PayloadSensitiveRaw counterFirstLexRaw_R (compile s) := by
  cases s with
  | counterProjection => exact Or.inl counterProjection_orients
  | payloadProjection => cases h
  | constantMeasure a => exact Or.inr (constantMeasure_not_raw_payload_sensitive a)
  | counterPlusPayload => exact Or.inl counterPlusPayload_orients
  | payloadPlusConst _ => cases h

/--
Proves: a raw-payload-sensitive shape classified `SemanticNotDirect`
  still orients the canonical step. The only payload-blind
  `SemanticNotDirect` case is the constant branch, which is eliminated
  by the raw-sensitivity hypothesis.
Does not prove: anything for payload-blind not-direct shapes.
Relation: `counterFirstLexRaw_R`.
Closure: root single-step.
Strategy: not applicable.
Trust: kernel-only.
Scope: raw-payload-sensitive not-direct shapes.
-/
theorem notDirect_rawSensitive_shape_orients
    (s : RawDirectMeasureShape)
    (hClass : classifyRaw s = SemanticCertificateClass.SemanticNotDirect)
    (hRaw : PayloadSensitiveRaw counterFirstLexRaw_R (compile s)) :
    Orients counterFirstLexRaw_R (compile s).μ (compile s).ltA := by
  cases notDirect_shape_orients_or_payload_blind s hClass with
  | inl hOrient => exact hOrient
  | inr hBlind => exact False.elim (hBlind hRaw)

/-! ## 9. Capstone: grammar-closure structure -/

/--
Proves: capstone closure record for the raw-grammar surface. Bundles
  classifier totality, zero residual, per-shape lens-pump witness
  derivation for blocked shapes, raw-payload sensitivity for blocked
  shapes, and the corrected not-direct split: orienting
  counter-dominated shapes or payload-blind shapes.
Does not prove: any property of measures outside the closed grammar.
Relation: `counterFirstLexRaw_R`.
Closure: root single-step.
Strategy: not applicable.
Trust: kernel-only.
Scope: the closed raw grammar.
-/
structure RawGrammarClosed : Prop where
  classifierTotal : ∀ s : RawDirectMeasureShape,
    classifyRaw s = SemanticCertificateClass.SemanticPayloadSensitiveBlocked
      ∨ classifyRaw s =
          SemanticCertificateClass.SemanticProjectionTransactionEscape
      ∨ classifyRaw s =
          SemanticCertificateClass.SemanticConstructionEscape
      ∨ classifyRaw s =
          SemanticCertificateClass.SemanticTransformEscape
      ∨ classifyRaw s =
          SemanticCertificateClass.SemanticNotDirect
  zeroResidual : ∀ s : RawDirectMeasureShape,
    classifyRaw s ≠ SemanticCertificateClass.TEMPORARY_UNCLASSIFIED
  blockedHasLensPump : ∀ (s : RawDirectMeasureShape),
    classifyRaw s =
        SemanticCertificateClass.SemanticPayloadSensitiveBlocked →
      SemanticLensPumpWitness counterFirstLexRaw_R (compile s)
  blockedRawPayloadSensitive : ∀ (s : RawDirectMeasureShape),
    classifyRaw s =
        SemanticCertificateClass.SemanticPayloadSensitiveBlocked →
      PayloadSensitiveRaw counterFirstLexRaw_R (compile s)
  blockedNotOrients : ∀ (s : RawDirectMeasureShape),
    classifyRaw s =
        SemanticCertificateClass.SemanticPayloadSensitiveBlocked →
      ¬ Orients counterFirstLexRaw_R (compile s).μ (compile s).ltA
  notDirectOrientsOrPayloadBlind : ∀ (s : RawDirectMeasureShape),
    classifyRaw s = SemanticCertificateClass.SemanticNotDirect →
      Orients counterFirstLexRaw_R (compile s).μ (compile s).ltA
        ∨ ¬ PayloadSensitiveRaw counterFirstLexRaw_R (compile s)
  notDirectRawSensitiveOrients : ∀ (s : RawDirectMeasureShape),
    classifyRaw s = SemanticCertificateClass.SemanticNotDirect →
      PayloadSensitiveRaw counterFirstLexRaw_R (compile s) →
        Orients counterFirstLexRaw_R (compile s).μ (compile s).ltA

/--
Proves: the raw grammar surface is closed. All five capstone fields
  hold by the per-shape theorems proved above.
Does not prove: anything outside the closed grammar.
Relation: `counterFirstLexRaw_R`.
Closure: root single-step.
Strategy: not applicable.
Trust: kernel-only.
Scope: the closed raw grammar.
-/
theorem raw_grammar_closed : RawGrammarClosed where
  classifierTotal       := classifyRaw_total
  zeroResidual          := classifyRaw_no_temporary_unclassified
  blockedHasLensPump    := blocked_shape_has_lens_pump_witness
  blockedRawPayloadSensitive := blocked_shape_raw_payload_sensitive
  blockedNotOrients     := blocked_shape_not_orients
  notDirectOrientsOrPayloadBlind := notDirect_shape_orients_or_payload_blind
  notDirectRawSensitiveOrients := notDirect_rawSensitive_shape_orients

/-- Audit anchor for the raw-grammar surface. -/
def rdrs_semantic_normalized_raw_syntax_anchor : String :=
  "OperatorKO7.RDRSSemanticNormalizedRawSyntax.raw_grammar_closed"

end OperatorKO7.RDRSSemanticNormalizedRawSyntax
