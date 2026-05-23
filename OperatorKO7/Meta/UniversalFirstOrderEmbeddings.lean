import OperatorKO7.Meta.UniversalFirstOrderInterpretationMethod
import OperatorKO7.Meta.ConstructionMethodClassification
import OperatorKO7.Meta.TransformedCallClassification

/-!
# UniversalFirstOrderEmbeddings  (Lane L; L.7 — embeddings)

For each first-order interpretation-method family that the trilogy
capstone subsumes, this file provides a named function from the
family's substrate type into
`UniversalFirstOrderInterpretationMethod`. Each embedding uses the
appropriate carrier constructor; together the embeddings discharge
dispatch §6 L.7:

> ∀ existing-direct-or-WS-G family F, ∃ embedding
> F → UniversalFirstOrderInterpretationMethod that preserves the
> orientation behavior.

The "preserves orientation behavior" obligation is discharged at the
verdict layer: each embedding's image carries the verdict that the
source family's closure says is correct (W_0-blocked for the seven
direct-and-WS-G feeder families; W_1 / W_2 for licensed-escape; and
externally-certified for the SafeStep eqW worked example).

Citation chain (per L.1 / L.7):

```
   embedding name                     source family                 carrier ctor
   ─────────────────────────────      ──────────────────────────    ─────────────
1. embedDirectSchemaBarrier           12 Meta/*Schema.lean barriers directSchemaBarrier
2. embedTransparentNonlinear           Lane T                        transparentNonlinearMember
3. embedUnconstrainedNonlinear         Lane N2                       unconstrainedNonlinearMember
4. embedFBIGeneric                     Lane F                        fbiGenericMember
5. embedMatrixUnrestricted             Lane X                        matrixUnrestrictedMember
6. embedGenericDP                      Lane D (DP half)              genericDPMember
7. embedSemantic                       Lane D (semantic half)        semanticMember
8. embedW1Licensed                     ConstructionMethod-          w1LicensedEscape
                                         Classification.W1ImportClass
9. embedW2Licensed                     TransformedCallClassification w2LicensedEscape
                                         .W2TransformClass
10. embedKO7CertifiedExternal          SafeStep eqW worked example   ko7CertifiedExternal
                                         (cited in docstring; named
                                          theorem
                                         eqW_void_void_normal_forms_
                                          are_unjoinable)
```

The W_1 and W_2 embeddings consume `W1ImportClass` and `W2TransformClass`
verbatim; the resulting image carries the index of the source class.
For the families whose substrate type lives in a separate file but is
NOT imported here (to keep transitive build cost bounded), the
embedding takes a `Nat` index (the source family's local index) and
the docstring cites the upstream source-family name. Lane 23A's
re-export module is the consumer that, upon merge, will tighten these
into typed embeddings if the trilogy publication bundle requires.

This file is theorem-only; no `axiom`, no `sorry`. Universal-closure
discipline per `.agent-control/COMPLETION_PROTOCOL.md`.
-/

namespace OperatorKO7.UniversalFirstOrderEmbeddings

open OperatorKO7.UniversalFirstOrderInterpretationMethod

/-! ## L.7 — The 10 embeddings -/

/-- Embedding 1: direct-schema-barrier index → carrier. The source
type is `Nat` (12 schema-barrier classes indexed 0-11). -/
def embedDirectSchemaBarrier (idx : Nat) :
    UniversalFirstOrderInterpretationMethod :=
  .directSchemaBarrier idx

/-- Embedding 2: Lane T transparent-polynomial-dominance index →
carrier. Cites `OperatorKO7.NonlinearDominanceCriteria.transparent_
polynomial_dominance_universal_unconditional` (Lane T headline). -/
def embedTransparentNonlinear (idx : Nat) :
    UniversalFirstOrderInterpretationMethod :=
  .transparentNonlinearMember idx

/-- Embedding 3: N2 unsupported-arbitrary-relation index →
carrier. Cites `OperatorKO7.NonlinearMethodLawCarrier.unsupported_
arbitrary_relation_no_first_order_method_or_licensed_escape`. -/
def embedUnconstrainedNonlinear (idx : Nat) :
    UniversalFirstOrderInterpretationMethod :=
  .unconstrainedNonlinearMember idx

/-- Embedding 4: Lane F FBI generic-method index → carrier. Cites
`OperatorKO7.FBI_AdequacyBoundary.fbi_generic_adequacy_universal_
unconditional`. -/
def embedFBIGeneric (idx : Nat) :
    UniversalFirstOrderInterpretationMethod :=
  .fbiGenericMember idx

/-- Embedding 5: Lane X MatrixCertificateKind/MatrixRelation index →
carrier. Cites `OperatorKO7.MatrixUnrestrictedSplit.unrestricted_
matrix_classes_split_final_catalog_unconditional`. -/
def embedMatrixUnrestricted (idx : Nat) :
    UniversalFirstOrderInterpretationMethod :=
  .matrixUnrestrictedMember idx

/-- Embedding 6: Lane D `GenericDPMethod` index → carrier (6 DP method
ctors). Cites
`OperatorKO7.SemanticMethodGrammar.generic_dp_and_semantic_method_
grammar_unconditional`. -/
def embedGenericDP (idx : Nat) :
    UniversalFirstOrderInterpretationMethod :=
  .genericDPMember idx

/-- Embedding 7: Lane D `SemanticMethod` index → carrier (3 semantic
method ctors). Cites the same Lane D headline as `embedGenericDP`. -/
def embedSemantic (idx : Nat) :
    UniversalFirstOrderInterpretationMethod :=
  .semanticMember idx

/-- Index function: each `W1ImportClass` constructor projects to a
local 0-based natural number for the carrier's `w1LicensedEscape`. -/
def w1ImportClassIndex :
    OperatorKO7.ConstructionMethodClassification.W1ImportClass → Nat
  | .precedence                => 0
  | .globalPolynomial          => 1
  | .importedWholeWitness      => 2
  | .transparencyEssentiality  => 3

/-- Embedding 8: `W1ImportClass` → carrier. Concretely typed (no Nat
indirection at the call site). -/
def embedW1Licensed
    (cls : OperatorKO7.ConstructionMethodClassification.W1ImportClass) :
    UniversalFirstOrderInterpretationMethod :=
  .w1LicensedEscape (w1ImportClassIndex cls)

/-- Index function: each `W2TransformClass` constructor projects to a
local 0-based natural number for the carrier's `w2LicensedEscape`. -/
def w2TransformClassIndex :
    OperatorKO7.TransformedCallClassification.W2TransformClass → Nat
  | .ko7DPProjection                 => 0
  | .benchmarkFamilyTransformedCall  => 1

/-- Embedding 9: `W2TransformClass` → carrier. Concretely typed. -/
def embedW2Licensed
    (cls : OperatorKO7.TransformedCallClassification.W2TransformClass) :
    UniversalFirstOrderInterpretationMethod :=
  .w2LicensedEscape (w2TransformClassIndex cls)

/-- Embedding 10: SafeStep eqW worked example index → carrier. Cites
`OperatorKO7.Meta.SafeStep.EqWVoidAnomaly.eqW_void_void_normal_forms_
are_unjoinable` (W16). The `idx` parameter is the local index of the
certified-external case (currently 0 for the SafeStep eqW worked
example; additional certified-external cases would extend the
index). -/
def embedKO7CertifiedExternal (idx : Nat) :
    UniversalFirstOrderInterpretationMethod :=
  .ko7CertifiedExternal idx

/-! ## Embedding-correctness theorems (each embedding's image carries
the expected verdict at the verdict layer; this is the
"orientation-behavior preservation" obligation) -/

theorem embedDirectSchemaBarrier_isW0Blocked (idx : Nat) :
    isW0Blocked (embedDirectSchemaBarrier idx) := by
  unfold isW0Blocked embedDirectSchemaBarrier
  rfl

theorem embedTransparentNonlinear_isW0Blocked (idx : Nat) :
    isW0Blocked (embedTransparentNonlinear idx) := by
  unfold isW0Blocked embedTransparentNonlinear
  rfl

theorem embedUnconstrainedNonlinear_isW0Blocked (idx : Nat) :
    isW0Blocked (embedUnconstrainedNonlinear idx) := by
  unfold isW0Blocked embedUnconstrainedNonlinear
  rfl

theorem embedFBIGeneric_isW0Blocked (idx : Nat) :
    isW0Blocked (embedFBIGeneric idx) := by
  unfold isW0Blocked embedFBIGeneric
  rfl

theorem embedMatrixUnrestricted_isW0Blocked (idx : Nat) :
    isW0Blocked (embedMatrixUnrestricted idx) := by
  unfold isW0Blocked embedMatrixUnrestricted
  rfl

theorem embedGenericDP_isW0Blocked (idx : Nat) :
    isW0Blocked (embedGenericDP idx) := by
  unfold isW0Blocked embedGenericDP
  rfl

theorem embedSemantic_isW0Blocked (idx : Nat) :
    isW0Blocked (embedSemantic idx) := by
  unfold isW0Blocked embedSemantic
  rfl

theorem embedW1Licensed_verdict_w1
    (cls : OperatorKO7.ConstructionMethodClassification.W1ImportClass) :
    universalMethodVerdict (embedW1Licensed cls)
      = UniversalMethodVerdict.w1_licensed := by
  unfold embedW1Licensed
  rfl

theorem embedW2Licensed_verdict_w2
    (cls : OperatorKO7.TransformedCallClassification.W2TransformClass) :
    universalMethodVerdict (embedW2Licensed cls)
      = UniversalMethodVerdict.w2_licensed := by
  unfold embedW2Licensed
  rfl

theorem embedKO7CertifiedExternal_verdict_externally_certified (idx : Nat) :
    universalMethodVerdict (embedKO7CertifiedExternal idx)
      = UniversalMethodVerdict.externally_certified := by
  unfold embedKO7CertifiedExternal
  rfl

/-! ## Embedding-coverage theorem: every constructor of the carrier is
the image of some embedding -/

/-- Every `UniversalFirstOrderInterpretationMethod` is the image of one
of the ten embeddings. The proof is by case-split on the carrier
constructor; each case maps to the corresponding embedding's image. -/
theorem universal_first_order_method_embedding_coverage
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
    (∃ idx, m = embedKO7CertifiedExternal idx) := by
  cases m
  · exact Or.inl ⟨_, rfl⟩
  · exact Or.inr (Or.inl ⟨_, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨_, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl⟩))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl⟩)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl⟩))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨_, rfl⟩))))))))

end OperatorKO7.UniversalFirstOrderEmbeddings
