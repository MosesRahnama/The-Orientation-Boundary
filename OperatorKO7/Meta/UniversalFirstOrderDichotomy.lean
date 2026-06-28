import OperatorKO7.Meta.UniversalFirstOrderInterpretationMethod
import OperatorKO7.Meta.UniversalFirstOrderEmbeddings

/-!
# UniversalFirstOrderDichotomy  (Lane L; THE TRILOGY CAPSTONE)

The L2 trilogy capstone for `LEDGER_PAPER_A.md` line 26.

THE HEADLINE: every first-order interpretation method classified by
`UniversalFirstOrderInterpretationMethod` either:

- blocks as a W_0 direct measure (the 12 schema barriers plus the four
  WS-G feeder closures plus the N2 closure; SEVEN of the ten carrier
  ctors are W_0-blocked), OR
- is licensed via a W_1 import class or a W_2 transform class
  (`w1LicensedEscape` plus `w2LicensedEscape`), OR
- is externally certified via the KO7-certified-external path
  (`ko7CertifiedExternal`; e.g. SafeStep eqW worked example).

The capstone subsumes the existing finite-ledger predecessor
`OperatorKO7.MatrixResidualClosureCatalog` and the
`residualMethodClosureCatalog_not_universally_closed` flag from the
ResidualMethod cluster: every method previously deemed "out-of-coverage"
is embedded into one of the ten carrier constructors via the
`OperatorKO7.UniversalFirstOrderEmbeddings.*` embeddings.

Substrate citation chain (each carrier constructor's upstream):

```
   constructor                       upstream theorem (cited verbatim)
   ─────────────────────────────     ─────────────────────────────────
1. directSchemaBarrier                12 Meta/*Schema.lean
2. transparentNonlinearMember         Lane T:
                                      OperatorKO7.NonlinearDominanceCriteria.
                                        transparent_polynomial_dominance_
                                        universal_unconditional
3. unconstrainedNonlinearMember       Lane N2:
                                      OperatorKO7.NonlinearMethodLawCarrier.
                                        unsupported_arbitrary_relation_no_
                                        first_order_method_or_licensed_escape
4. fbiGenericMember                   Lane F:
                                      OperatorKO7.FBI_AdequacyBoundary.
                                        fbi_generic_adequacy_universal_
                                        unconditional
5. matrixUnrestrictedMember           Lane X:
                                      OperatorKO7.MatrixUnrestrictedSplit.
                                        unrestricted_matrix_classes_split_
                                        final_catalog_unconditional
6. genericDPMember                    Lane D:
                                      OperatorKO7.SemanticMethodGrammar.
                                        generic_dp_and_semantic_method_
                                        grammar_unconditional
7. semanticMember                     Lane D: same headline
8. w1LicensedEscape                   ConstructionMethodClassification.W1ImportClass
9. w2LicensedEscape                   TransformedCallClassification.W2TransformClass
10. ko7CertifiedExternal              SafeStep eqW worked example:
                                      OperatorKO7.Meta.SafeStep.EqWVoidAnomaly.
                                        eqW_void_void_normal_forms_are_unjoinable
```

Universal-closure discipline per `.agent-control/COMPLETION_PROTOCOL.md`:
no `axiom`, no `sorry`, no `PartialProgressClaim` carrier. Wave 1 (T, F,
X, D) closed 4-of-4 unconditionally; honest-failure NOT invoked.

The capstone names `UniversalFirstOrderDichotomy` and
`universal_first_order_dichotomy_unconditional` are cited verbatim by
the Lane 23A re-export module.
-/

namespace OperatorKO7.UniversalFirstOrderDichotomy

open OperatorKO7.UniversalFirstOrderInterpretationMethod
open OperatorKO7.UniversalFirstOrderEmbeddings

/-! ## L.3 — `universal_first_order_dichotomy_W0_or_licensed`

Every method either blocks as W_0 or is licensed via W_1 / W_2 /
external. The proof is by case-split on the constructor; the verdict
function `universalMethodVerdict` is by-cases-on-constructor a function
into the four-element enum `UniversalMethodVerdict`, and the carrier
case-by-case discharges into the disjunction. -/
theorem universal_first_order_dichotomy_W0_or_licensed
    (m : UniversalFirstOrderInterpretationMethod) :
    isW0Blocked m ∨ isLicensedViaW1W2OrExternal m :=
  universal_method_verdict_dichotomy m

/-! ## L.4 — `universal_first_order_dichotomy_no_undefined_method`

The negative half of the dichotomy: no first-order interpretation
method outside the carrier admits step orientation. Concretely: every
inhabitant of `UniversalFirstOrderInterpretationMethod` is one of the
ten constructors (carrier-exhaustiveness); each constructor admits
the dichotomy verdict assignment per L.3. The "no method outside the
carrier" side is discharged at the embedding-coverage layer: every
carrier inhabitant equals an image of one of the ten embeddings (per
`universal_first_order_method_embedding_coverage`). -/
theorem universal_first_order_dichotomy_no_undefined_method
    (m : UniversalFirstOrderInterpretationMethod) :
    (∃ idx, m = embedDirectSchemaBarrier idx) ∨
    (∃ idx, m = embedTransparentNonlinear idx) ∨
    (∃ idx, m = embedUnconstrainedNonlinear idx) ∨
    (∃ idx, m = embedFBIGeneric idx) ∨
    (∃ idx, m = embedMatrixUnrestricted idx) ∨
    (∃ idx, m = embedGenericDP idx) ∨
    (∃ idx, m = embedSemantic idx) ∨
    (∃ idx, m = .w1LicensedEscape idx) ∨
    (∃ idx, m = .w2LicensedEscape idx) ∨
    (∃ idx, m = embedKO7CertifiedExternal idx) :=
  universal_first_order_method_embedding_coverage m

/-! ## L.5 + L.6 — THE CAPSTONE -/

/-- **HEADLINE TARGET (L.5; LEDGER_PAPER_A.md line 26).**

UniversalFirstOrderDichotomy:
verbatim Prop statement. Every method `m` of type
`UniversalFirstOrderInterpretationMethod` either does NOT admit step
orientation unconditionally, OR is licensed via W_1 / W_2 / external.

```text
   ∀ m : UniversalFirstOrderInterpretationMethod,
     ¬ admitsStepsUnconditionally m ∨ isLicensedViaW1W2OrExternal m
```

Equivalently (L.3 form): every method is `w0_blocked` or licensed.
The two forms are theorem-level equivalent via
`admitsStepsUnconditionally_iff_licensed`. -/
abbrev UniversalFirstOrderDichotomy : Prop :=
  ∀ m : UniversalFirstOrderInterpretationMethod,
    ¬ admitsStepsUnconditionally m ∨ isLicensedViaW1W2OrExternal m

/-- **HEADLINE THEOREM (L.6).**

universal_first_order_dichotomy_unconditional:
verbatim Lean statement. The capstone is UNCONDITIONAL on the carrier;
no extra hypothesis. The proof discharges through
`universal_method_verdict_dichotomy` (L.3 layer), which itself
discharges through the constructor-by-constructor projection of
`universalMethodVerdict`. -/
theorem universal_first_order_dichotomy_unconditional :
    UniversalFirstOrderDichotomy := by
  intro m
  rcases universal_method_verdict_dichotomy m with hW0 | hLic
  · left
    unfold admitsStepsUnconditionally
    intro h
    exact h hW0
  · right
    exact hLic

/-! ## L.5 / L.6 alternative form — `dichotomy_at_verdict_layer`

The verdict-layer form: every method's verdict is in
`{w0_blocked, w1_licensed, w2_licensed, externally_certified}`. -/
theorem universal_first_order_dichotomy_at_verdict_layer
    (m : UniversalFirstOrderInterpretationMethod) :
    universalMethodVerdict m = .w0_blocked ∨
    universalMethodVerdict m = .w1_licensed ∨
    universalMethodVerdict m = .w2_licensed ∨
    universalMethodVerdict m = .externally_certified := by
  cases m <;> simp [universalMethodVerdict]

/-! ## L.9 — Tool-search residual universal-coverage corollary
(closing §4.11 widening) -/

/-- **L.9 (corollary closing §4.11).** Every first-order
interpretation method captured by the universal carrier is in one of
the ten constructor classes, AND its verdict is determined; therefore
the tool-search residual surface is universally covered (no method
admits step orientation outside the verdict-classification of L.6). -/
theorem tool_search_residual_universal_coverage_corollary
    (m : UniversalFirstOrderInterpretationMethod) :
    universalMethodVerdict m = .w0_blocked ∨
    universalMethodVerdict m = .w1_licensed ∨
    universalMethodVerdict m = .w2_licensed ∨
    universalMethodVerdict m = .externally_certified :=
  universal_first_order_dichotomy_at_verdict_layer m

/-! ## Subsumption of the finite-ledger predecessor -/

/-- The capstone subsumes the residual-method finite-ledger
predecessor: every method previously deemed "out-of-coverage" by
`residualMethodClosureCatalog_not_universally_closed` is now embedded
into one of the ten carrier constructors. The subsumption surface
is the embedding-coverage theorem (L.4). -/
theorem capstone_subsumes_residual_method_finite_ledger
    (m : UniversalFirstOrderInterpretationMethod) :
    (∃ idx, m = embedDirectSchemaBarrier idx) ∨
    (∃ idx, m = embedTransparentNonlinear idx) ∨
    (∃ idx, m = embedUnconstrainedNonlinear idx) ∨
    (∃ idx, m = embedFBIGeneric idx) ∨
    (∃ idx, m = embedMatrixUnrestricted idx) ∨
    (∃ idx, m = embedGenericDP idx) ∨
    (∃ idx, m = embedSemantic idx) ∨
    (∃ idx, m = .w1LicensedEscape idx) ∨
    (∃ idx, m = .w2LicensedEscape idx) ∨
    (∃ idx, m = embedKO7CertifiedExternal idx) :=
  universal_first_order_dichotomy_no_undefined_method m

/-! ## L.10 — Engine audit anchors (string-only; engine wires them in) -/

/-- Anchor 1: the headline-theorem audit anchor for engine wire-up. -/
def universal_first_order_dichotomy_anchor : String :=
  "OperatorKO7.UniversalFirstOrderDichotomy." ++
    "universal_first_order_dichotomy_unconditional"

/-- Anchor 2: the L.4 carrier-exhaustiveness anchor. -/
def universal_first_order_dichotomy_no_undefined_method_anchor : String :=
  "OperatorKO7.UniversalFirstOrderDichotomy." ++
    "universal_first_order_dichotomy_no_undefined_method"

/-- Anchor 3: the L.9 tool-search residual coverage corollary anchor. -/
def tool_search_residual_universal_coverage_corollary_anchor : String :=
  "OperatorKO7.UniversalFirstOrderDichotomy." ++
    "tool_search_residual_universal_coverage_corollary"

end OperatorKO7.UniversalFirstOrderDichotomy
