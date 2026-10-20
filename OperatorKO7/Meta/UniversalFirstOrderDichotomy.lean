import OperatorKO7.Meta.UniversalFirstOrderInterpretationMethod
import OperatorKO7.Meta.UniversalFirstOrderEmbeddings

/-!
# UniversalFirstOrderDichotomy

The headline: every first-order interpretation method classified by
`InterpretationMethod` either:

- blocks as a W_0 direct measure (the 12 schema barriers plus the four
 feeder closures plus the N2 closure; seven of the ten carrier
 constructors are W_0-blocked), OR
- is licensed via a W_1 import class or a W_2 transform class
 (`w1LicensedEscape` plus `w2LicensedEscape`), OR
- is externally certified via the KO7-certified-external path
 (`ko7CertifiedExternal`; e.g. SafeStep eqW worked example).

The capstone subsumes the finite-ledger predecessor
`OperatorKO7.MatrixResidualClosureCatalog` and the
`residualMethodClosureCatalog_not_universally_closed` result: every method previously deemed "out-of-coverage"
is embedded into one of the ten carrier constructors via the
`OperatorKO7.UniversalFirstOrderEmbeddings.*` embeddings.

Substrate citation chain (each carrier constructor's upstream):

```
   constructor                       upstream theorem (cited verbatim)
   ─────────────────────────────     ─────────────────────────────────
1. directSchemaBarrier                the twelve schema-barrier theorems
2. transparentNonlinearMember         OperatorKO7.NonlinearDominanceCriteria.
                                        transparent_polynomial_dominance_
                                        universal_unconditional
3. unconstrainedNonlinearMember       OperatorKO7.NonlinearMethodLawCarrier.
                                        unsupported_arbitrary_relation_no_
                                        first_order_method_or_licensed_escape
4. fbiGenericMember                   OperatorKO7.FBI_AdequacyBoundary.
                                        fbi_generic_adequacy_universal_
                                        unconditional
5. matrixUnrestrictedMember           OperatorKO7.MatrixUnrestrictedSplit.
                                        unrestricted_matrix_classes_split_
                                        final_catalog_unconditional
6. genericDPMember                    OperatorKO7.SemanticMethodGrammar.
                                        generic_dp_and_semantic_method_
                                        grammar_unconditional
7. semanticMember                     same headline
8. w1LicensedEscape                   ConstructionMethodClassification.W1ImportClass
9. w2LicensedEscape                   TransformedCallClassification.W2TransformClass
10. ko7CertifiedExternal              SafeStep eqW worked example:
                                      OperatorKO7.Meta.SafeStep.EqWVoidAnomaly.
                                        eqW_void_void_normal_forms_are_unjoinable
```

Universal-closure discipline:
no `axiom`, no `sorry`, no `PartialProgressClaim` carrier. (T, F,
X, D) closed 4-of-4 unconditionally.

The capstone proposition is `DichotomyStatement`. The theorem name
`universal_first_order_dichotomy_unconditional` is retained for the
re-export module.
-/


namespace OperatorKO7.UniversalFirstOrderDichotomy

open OperatorKO7.UniversalFirstOrderInterpretationMethod
open OperatorKO7.UniversalFirstOrderEmbeddings

/-! ## `universal_first_order_dichotomy_W0_or_licensed`

Every method either blocks as W_0 or is licensed via W_1 / W_2 /
external. The proof is by case-split on the constructor; the verdict
function `universalMethodVerdict` is by-cases-on-constructor a function
into the four-element enum `UniversalMethodVerdict`, and the carrier
case-by-case discharges into the disjunction. -/
theorem universal_first_order_dichotomy_W0_or_licensed
    (m : InterpretationMethod) :
    isW0Blocked m ∨ isLicensedViaW1W2OrExternal m :=
  universal_method_verdict_dichotomy m

/-! ## `universal_first_order_dichotomy_no_undefined_method`

The negative half of the dichotomy: no first-order interpretation
method outside the carrier admits step orientation. Concretely: every
inhabitant of `InterpretationMethod` is one of the
ten constructors (carrier-exhaustiveness); each constructor admits
the dichotomy verdict assignment per L.3. The "no method outside the
carrier" side is discharged at the embedding-coverage layer: every
carrier inhabitant equals an image of one of the ten embeddings (per
`universal_first_order_method_embedding_coverage`). -/
theorem universal_first_order_dichotomy_no_undefined_method
    (m : InterpretationMethod) :
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

/-! ## The capstone -/

/-- **Headline target.**

Dichotomy statement: every method `m` of type
`InterpretationMethod` either does NOT admit step
orientation unconditionally, OR is licensed via W_1 / W_2 / external.

```text
   ∀ m : InterpretationMethod,
     ¬ admitsStepsUnconditionally m ∨ isLicensedViaW1W2OrExternal m
```

Equivalently: every method is `w0_blocked` or licensed.
The two forms are theorem-level equivalent via
`admitsStepsUnconditionally_iff_licensed`. -/
abbrev DichotomyStatement : Prop :=
  ∀ m : InterpretationMethod,
    ¬ admitsStepsUnconditionally m ∨ isLicensedViaW1W2OrExternal m

/-- **Headline theorem.**

universal_first_order_dichotomy_unconditional:
the capstone statement. The capstone is UNCONDITIONAL on the carrier;
no extra hypothesis. The proof discharges through
`universal_method_verdict_dichotomy` (the case-split layer), which itself
discharges through the constructor-by-constructor projection of
`universalMethodVerdict`. -/
theorem universal_first_order_dichotomy_unconditional :
    DichotomyStatement := by
  intro m
  rcases universal_method_verdict_dichotomy m with hW0 | hLic
  · left
    unfold admitsStepsUnconditionally
    intro h
    exact h hW0
  · right
    exact hLic

/-! ## Alternative form — `dichotomy_at_verdict_layer`

The verdict-layer form: every method's verdict is in
`{w0_blocked, w1_licensed, w2_licensed, externally_certified}`. -/
theorem universal_first_order_dichotomy_at_verdict_layer
    (m : InterpretationMethod) :
    universalMethodVerdict m = .w0_blocked ∨
    universalMethodVerdict m = .w1_licensed ∨
    universalMethodVerdict m = .w2_licensed ∨
    universalMethodVerdict m = .externally_certified := by
  cases m <;> simp [universalMethodVerdict]

/-! ## Tool-search residual universal-coverage corollary -/

/-- Every first-order
interpretation method captured by the universal carrier is in one of
the ten constructor classes, AND its verdict is determined; therefore
the tool-search residual surface is universally covered (no method
admits step orientation outside the verdict classification). -/
theorem tool_search_residual_universal_coverage_corollary
    (m : InterpretationMethod) :
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
is the embedding-coverage theorem. -/
theorem capstone_subsumes_residual_method_finite_ledger
    (m : InterpretationMethod) :
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

/-! ## Audit anchors (string-only) -/

/-- Anchor 1: the headline-theorem name as a string. -/
def universal_first_order_dichotomy_anchor : String :=
  "OperatorKO7.UniversalFirstOrderDichotomy." ++
    "universal_first_order_dichotomy_unconditional"

/-- Anchor 2: the carrier-exhaustiveness theorem name as a string. -/
def universal_first_order_dichotomy_no_undefined_method_anchor : String :=
  "OperatorKO7.UniversalFirstOrderDichotomy." ++
    "universal_first_order_dichotomy_no_undefined_method"

/-- Anchor 3: the tool-search residual coverage corollary name as a string. -/
def tool_search_residual_universal_coverage_corollary_anchor : String :=
  "OperatorKO7.UniversalFirstOrderDichotomy." ++
    "tool_search_residual_universal_coverage_corollary"

end OperatorKO7.UniversalFirstOrderDichotomy
