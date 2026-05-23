import Mathlib.Logic.ExistsUnique
import Mathlib.Tactic.Cases

/-!
# UniversalFirstOrderInterpretationMethod  (Lane L; trilogy capstone carrier)

The carrier inductive type that aggregates every first-order interpretation
method category. Every method that orients duplicating-step rewrites
either:

1. blocks as a W_0 direct measure (the 12 direct schema barriers plus the
   four WS-G feeder closures plus the N2 closure), OR
2. is licensed via a W_1 import class or a W_2 transform class, OR
3. is externally certified (the KO7-certified-external path; e.g. the
   W16 SafeStep eqW worked example).

This file ships the 10-constructor carrier (L.1) plus the per-constructor
classification (L.2). The capstone dichotomy theorem (L.5 / L.6), the
embeddings (L.7), and the corollaries L.8 / L.9 live in sibling Lane L
modules.

Citation chain (each constructor's docstring cites the upstream theorem
by exact name; the embedding into the named type is in
`Meta/UniversalFirstOrderEmbeddings.lean`):

```
   constructor                      upstream substrate
   ─────────────────────────       ─────────────────────────────────────
1. directSchemaBarrier              12 direct schema barriers
                                    (Meta/*Schema.lean)
2. transparentNonlinearMember       Lane T:
                                    OperatorKO7.NonlinearDominanceCriteria.
                                      transparent_polynomial_dominance_
                                      universal_unconditional
3. unconstrainedNonlinearMember     Lane N2:
                                    OperatorKO7.NonlinearMethodLawCarrier.
                                      unsupported_arbitrary_relation_no_
                                      first_order_method_or_licensed_escape
4. fbiGenericMember                 Lane F:
                                    OperatorKO7.FBI_AdequacyBoundary.
                                      fbi_generic_adequacy_universal_
                                      unconditional
5. matrixUnrestrictedMember         Lane X:
                                    OperatorKO7.MatrixUnrestrictedSplit.
                                      unrestricted_matrix_classes_split_
                                      final_catalog_unconditional
6. genericDPMember                  Lane D:
                                    OperatorKO7.SemanticMethodGrammar.
                                      generic_dp_and_semantic_method_
                                      grammar_unconditional
                                    (DP half; cites GenericDPMethod's 6
                                      ctors per the unified bundle)
7. semanticMember                   Lane D:
                                    OperatorKO7.SemanticMethodGrammar.
                                      generic_dp_and_semantic_method_
                                      grammar_unconditional
                                    (semantic half; cites SemanticMethod's
                                      3 ctors)
8. w1LicensedEscape                 ConstructionMethodClassification:
                                    OperatorKO7.Meta.
                                      ConstructionMethodClassification.
                                        W1ImportClass
9. w2LicensedEscape                 TransformedCallClassification:
                                    OperatorKO7.Meta.
                                      TransformedCallClassification.
                                        W2TransformClass
10. ko7CertifiedExternal            SafeStep eqW worked example
                                    (W16; SafeStep/EqWVoidAnomaly plus
                                      SafeStep/SyntacticNonDerivability):
                                    eqW_void_void_normal_forms_are_
                                      unjoinable
```

This file is theorem-only; no `axiom`, no `sorry`. Universal-closure
discipline per `.agent-control/COMPLETION_PROTOCOL.md`.
-/

namespace OperatorKO7.UniversalFirstOrderInterpretationMethod

/-! ## L.1 — The carrier inductive type -/

/-- Direct-schema-barrier index: 12 closed schema-barrier classes per
LEDGER_PAPER_A.md §4.1 (KBO_Impossible / DepthBarrier / MatrixBarrier{2,
Arbitrary, ArcticTropical, D, Functional, Lex, LexD, LexPermD, Mix2} +
ArcticBarrier). The index is a 0-based natural number; the embedding
in `UniversalFirstOrderEmbeddings.lean` maps each index to a paper-
facing schema-barrier name. -/
abbrev DirectSchemaBarrierIndex : Type := Nat

/-- Tag-type for the four classification verdicts the dichotomy emits.

`w0_blocked`           the method's interpretation is W_0; rewriting
                        with this method terminates, so it does NOT
                        admit step-duplicating orientation
`w1_licensed`          method is licensed via a W_1 import class
`w2_licensed`          method is licensed via a W_2 transform class
`externally_certified` method is externally certified (e.g. KO7-
                        certified-external; SafeStep eqW worked example) -/
inductive UniversalMethodVerdict
  | w0_blocked
  | w1_licensed
  | w2_licensed
  | externally_certified
  deriving DecidableEq, Repr

/-- The universal first-order interpretation-method carrier. 10
constructors covering every named first-order method family closed
across the trilogy.

Each constructor's docstring cites its upstream theorem by exact name
(see the file-banner Citation chain above). The classification function
`universalMethodVerdict` (below) pins each constructor to a verdict
in `UniversalMethodVerdict`; the verdicts together form the universal
dichotomy.

Constructors carry a Nat index where the underlying family has more
than one member (e.g. the 12 schema barriers are indexed 0-11). The
embedding modules (`UniversalFirstOrderEmbeddings.lean`) provide the
concrete maps from each substrate type into this carrier. -/
inductive UniversalFirstOrderInterpretationMethod : Type
  /-- One of the 12 direct schema barriers (Meta/*Schema.lean). Index
  in [0, 12). -/
  | directSchemaBarrier (idx : DirectSchemaBarrierIndex)
  /-- A transparent-polynomial nonlinear method admitting the Lane T
  closure. Cites
  `OperatorKO7.NonlinearDominanceCriteria.transparent_polynomial_
  dominance_universal_unconditional`. -/
  | transparentNonlinearMember (idx : Nat)
  /-- An unconstrained-arbitrary nonlinear method falling under the
  Lane N2 dichotomy. Cites
  `OperatorKO7.NonlinearMethodLawCarrier.unsupported_arbitrary_relation_
  no_first_order_method_or_licensed_escape`. -/
  | unconstrainedNonlinearMember (idx : Nat)
  /-- An FBI generic method falling under the Lane F closure. Cites
  `OperatorKO7.FBI_AdequacyBoundary.fbi_generic_adequacy_universal_
  unconditional`. -/
  | fbiGenericMember (idx : Nat)
  /-- An unrestricted matrix relation falling under the Lane X closure.
  Cites
  `OperatorKO7.MatrixUnrestrictedSplit.unrestricted_matrix_classes_
  split_final_catalog_unconditional`; the kind taxonomy is
  `MatrixCertificateKind` (6 ctors). -/
  | matrixUnrestrictedMember (idx : Nat)
  /-- A generic DP method falling under the Lane D coverage. 6
  named DP method types (pairExtraction, scc, argumentFiltering,
  usableRules, externalOrdering, certificateEngine). Cites
  `OperatorKO7.SemanticMethodGrammar.generic_dp_and_semantic_method_
  grammar_unconditional`. -/
  | genericDPMember (idx : Nat)
  /-- A semantic method falling under the Lane D coverage. 3 named
  semantic method types (modelImport, logicalRelation,
  reducibilityCandidate). Cites the same headline as
  `genericDPMember`. -/
  | semanticMember (idx : Nat)
  /-- A W_1 licensed-escape method indexed by W1ImportClass. Cites
  `OperatorKO7.Meta.ConstructionMethodClassification.W1ImportClass` (4
  ctors: directWholeTerm, importedWholeLicensedEscape, polynomialClass,
  toolSearchClass). -/
  | w1LicensedEscape (idx : Nat)
  /-- A W_2 licensed-escape method indexed by W2TransformClass. Cites
  `OperatorKO7.Meta.TransformedCallClassification.W2TransformClass`
  (3 ctors). -/
  | w2LicensedEscape (idx : Nat)
  /-- An externally-certified method (KO7-certified-external path).
  E.g. the W16 SafeStep eqW worked example; cites
  `OperatorKO7.Meta.SafeStep.EqWVoidAnomaly.eqW_void_void_normal_
  forms_are_unjoinable`. -/
  | ko7CertifiedExternal (idx : Nat)
  deriving DecidableEq, Repr

/-! ## L.2 — Per-constructor classification -/

/-- Every constructor of `UniversalFirstOrderInterpretationMethod`
projects to a unique `UniversalMethodVerdict`.

Verdict assignment:

```
   constructor family                     verdict
   ─────────────────────────────         ──────────────────────
   directSchemaBarrier                    w0_blocked
   transparentNonlinearMember             w0_blocked  (Lane T closure)
   unconstrainedNonlinearMember           w0_blocked  (Lane N2 dichotomy)
   fbiGenericMember                       w0_blocked  (Lane F coverage)
   matrixUnrestrictedMember               w0_blocked  (Lane X catalog)
   genericDPMember                        w0_blocked  (Lane D coverage)
   semanticMember                         w0_blocked  (Lane D coverage)
   w1LicensedEscape                       w1_licensed
   w2LicensedEscape                       w2_licensed
   ko7CertifiedExternal                   externally_certified
```

The first seven (W_0-blocked) carry their lane upstream as the closure
substrate; the W_1 / W_2 / externally-certified routes carry their own
substrate. The dichotomy theorem L.5 says: for every method
m, `universalMethodVerdict m ∈ {w0_blocked, w1_licensed, w2_licensed,
externally_certified}` — which is universally true by construction
(all four enum values are exhausted). -/
def universalMethodVerdict :
    UniversalFirstOrderInterpretationMethod → UniversalMethodVerdict
  | .directSchemaBarrier _         => .w0_blocked
  | .transparentNonlinearMember _  => .w0_blocked
  | .unconstrainedNonlinearMember _ => .w0_blocked
  | .fbiGenericMember _            => .w0_blocked
  | .matrixUnrestrictedMember _    => .w0_blocked
  | .genericDPMember _             => .w0_blocked
  | .semanticMember _              => .w0_blocked
  | .w1LicensedEscape _            => .w1_licensed
  | .w2LicensedEscape _            => .w2_licensed
  | .ko7CertifiedExternal _        => .externally_certified

/-- The verdict-projection theorem (L.2 surface): every method projects
to a unique verdict. The proof is by case-analysis on the constructor;
the verdict is determined by the constructor head. -/
theorem universal_first_order_method_classification
    (m : UniversalFirstOrderInterpretationMethod) :
    ∃! verdict : UniversalMethodVerdict,
      universalMethodVerdict m = verdict := by
  refine ⟨universalMethodVerdict m, rfl, ?_⟩
  intros y hy
  exact hy.symm

/-! ## Auxiliary predicates the dichotomy theorem consumes -/

/-- The method's verdict is `w0_blocked`. -/
def isW0Blocked (m : UniversalFirstOrderInterpretationMethod) : Prop :=
  universalMethodVerdict m = .w0_blocked

/-- The method's verdict is one of `w1_licensed`, `w2_licensed`,
or `externally_certified`. The "licensed-via-something" disjunction
that the dichotomy theorem consumes. -/
def isLicensedViaW1W2OrExternal
    (m : UniversalFirstOrderInterpretationMethod) : Prop :=
  universalMethodVerdict m = .w1_licensed ∨
    universalMethodVerdict m = .w2_licensed ∨
    universalMethodVerdict m = .externally_certified

/-! ## Method admits step orientation predicate -/

/-- A method `m` "admits step orientation unconditionally" iff its
classification verdict is NOT `w0_blocked`. The dichotomy says: methods
that DO admit step orientation are exactly those licensed via W_1 / W_2
or externally certified. -/
def admitsStepsUnconditionally
    (m : UniversalFirstOrderInterpretationMethod) : Prop :=
  universalMethodVerdict m ≠ .w0_blocked

/-- The dichotomy at the verdict layer: every method either is
`w0_blocked` OR is licensed via W_1 / W_2 / external. -/
theorem universal_method_verdict_dichotomy
    (m : UniversalFirstOrderInterpretationMethod) :
    isW0Blocked m ∨ isLicensedViaW1W2OrExternal m := by
  unfold isW0Blocked isLicensedViaW1W2OrExternal
  cases m <;> simp [universalMethodVerdict]

/-- The verdicts `w0_blocked` and any of the licensed variants are
mutually exclusive (different enum constructors). -/
theorem isW0Blocked_iff_not_licensed
    (m : UniversalFirstOrderInterpretationMethod) :
    isW0Blocked m ↔ ¬ isLicensedViaW1W2OrExternal m := by
  unfold isW0Blocked isLicensedViaW1W2OrExternal
  cases m <;> simp [universalMethodVerdict]

theorem admitsStepsUnconditionally_iff_licensed
    (m : UniversalFirstOrderInterpretationMethod) :
    admitsStepsUnconditionally m ↔ isLicensedViaW1W2OrExternal m := by
  unfold admitsStepsUnconditionally isLicensedViaW1W2OrExternal
  cases m <;> simp [universalMethodVerdict]

end OperatorKO7.UniversalFirstOrderInterpretationMethod
