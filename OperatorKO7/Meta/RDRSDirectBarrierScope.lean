import OperatorKO7.Meta.DirectBarrierScope

/-!
# RDRS Direct-Barrier Scope (theory-expansion module)

Roadmap source: `OperatorKO7/Expansion/RDRS_Termination_Methods_Roadmap.md`
(the direct-barrier-scope row of the RDRS termination-method universe atlas) and
`OperatorKO7/Paper/Rahnama_The_Orientation_Boundary.tex`
("Semantic universal payload-sensitive direct-measure program" + the
escape-trichotomy 14-family universe, `thm:escape-trichotomy`).

This module states and proves, **unconditionally**, the precise scope of the
formalized direct-barrier grammar within the RDRS termination-method universe:
which named RDRS direct-measure method families fall INSIDE the formalized
direct-barrier grammar (the escape-trichotomy 14-family universe) versus which
ESCAPE it, and by which named mechanism.

It is a finite, Lean-indexed *classification* theorem over a CLOSED method
universe, in the roadmap's stated sense ("classify each named method family by
the mechanism it uses against RDRS"). It is NOT a universal SN theorem and does
not re-prove each family's barrier:

* the family TAGS mirror the escape-trichotomy universe whose representability
  proofs live in `OperatorKO7.EscapeTrichotomy`
  (`ko7_nat_direct_escape_trichotomy`, `ko7_direct_escape_trichotomy_extended`);
* the scope-violation escapes are tied to the concrete `¬ InScope` sentinels of
  `OperatorKO7.StepDuplicating.DirectBarrierScope`;
* the transform/oracle escapes (DP processor, rewrite oracle, semantic labeling)
  are classified by their named non-direct mechanism, matching the directness
  exclusions of `OperatorKO7.RDRSSemanticDirectMeasure` (no transformed relation,
  no rewrite oracle, no DP processor).

## Audit slots (Lean Development Bible W8 / R4)

```
Relation:  closed metadata inductives over the named RDRS method universe.
           Not a Step / SafeStep / StepCtxFull / DPProblem rewriting relation.
Closure:   N/A (structural classification, not a rewriting closure).
Strategy:  not applicable.
Trust:     kernel-only. No sorry / admit / axiom / native_decide / @[csimp] /
           unsafe / partial / opaque. Public results return baseline-only under
           `#print axioms`.
Scope:     CLOSED grammar over a finite, explicitly enumerated method universe.
           Tag-level classification; not a per-family inhabited-measure claim.
```
-/

set_option autoImplicit false

namespace OperatorKO7.RDRSDirectBarrierScope

open OperatorKO7.StepDuplicating

/-! ### The formalized direct-barrier grammar: the escape-trichotomy 14-family universe -/

/--
Proves: closed enum of the fourteen direct-barrier families formalized by the
  escape trichotomy (Orientation Boundary §escape-trichotomy; the universe of
  `KO7NatDirectBarrierRepresentable` / `KO7DirectBarrierRepresentable`).
Does not prove: that any family is inhabited by an orienting measure here; the
  representability proofs live in `OperatorKO7.EscapeTrichotomy`.
Relation: enum metadata; not a rewriting relation.
Closure: not applicable.  Strategy: not applicable.  Trust: kernel-only.
Scope: closed inductive over fourteen family tags.
-/
inductive DirectBarrierFamily where
  | additiveCompositional
  | transparentCompositional
  | pumpedAffine
  | pumpedQuadratic
  | pumpedCrossQuadratic
  | pumpedMultilinear
  | pumpedPolynomial
  | pumpedMaxPlus
  | maxDepth
  | headPrecedence
  | matrixScalarProjection
  | trackedPrimaryComponentwise
  | trackedPrimaryLex
  | trackedPrimaryVectorLex
  deriving DecidableEq, Repr

/-- The closed list of all fourteen formalized direct-barrier grammar families. -/
def directBarrierGrammarFamilies : List DirectBarrierFamily :=
  [ .additiveCompositional, .transparentCompositional, .pumpedAffine,
    .pumpedQuadratic, .pumpedCrossQuadratic, .pumpedMultilinear,
    .pumpedPolynomial, .pumpedMaxPlus, .maxDepth, .headPrecedence,
    .matrixScalarProjection, .trackedPrimaryComponentwise,
    .trackedPrimaryLex, .trackedPrimaryVectorLex ]

/-! ### Named escape mechanisms -/

/--
Proves: closed enum of the named mechanisms by which an RDRS method escapes the
  direct-barrier grammar.
Does not prove: full method semantics; each tag names the mechanism only.
Relation: enum metadata.  Closure: N/A.  Strategy: N/A.  Trust: kernel-only.
Scope: closed inductive over seven escape mechanisms (four scope-violations tied
  to `DirectBarrierScope` sentinels, three non-direct transform/oracle routes).
-/
inductive DirectBarrierEscapeReason where
  | transformsRelation          -- DP processor / problem transform; not a direct measure
  | consumesRewriteOracle       -- term-algebra rewrite-oracle route
  | semanticLabelingTransform   -- semantic / predictive / root labeling
  | computabilityClosure        -- HORPO / CPO / sized types; violates syntacticDirect
  | equationalQuotient          -- AC / rewriting modulo; violates noEquationalQuotient
  | sharingAwareSemantics       -- graph reduction; violates treeSemantics
  | nonmonotoneCoOrder          -- co-WPO / co-rewrite pairs; violates monotoneObserver
  deriving DecidableEq, Repr

/-! ### The RDRS direct-method universe -/

/--
Proves: closed enum of the named RDRS direct-method families being classified:
  fourteen inside-grammar representatives (one per direct-barrier family) and
  seven escape methods.
Does not prove: exhaustiveness of all RDRS literature methods; this is the
  finite Lean-indexed atlas universe for the direct-barrier-scope row.
Relation: enum metadata.  Closure: N/A.  Strategy: N/A.  Trust: kernel-only.
Scope: closed inductive over twenty-one method tags.
-/
inductive RDRSDirectMethod where
  -- inside the formalized direct-barrier grammar (one representative per family)
  | additive
  | transparentCompositional
  | affinePump
  | quadraticPump
  | crossQuadraticPump
  | multilinearPump
  | polynomialPump
  | maxPlusPump
  | maxDepth
  | headPrecedence
  | matrixScalarProjection
  | trackedPrimaryComponentwise
  | trackedPrimaryLex
  | trackedPrimaryVectorLex
  -- escapes the formalized direct-barrier grammar
  | dependencyPairProcessor
  | rewriteOracle
  | semanticLabeling
  | computabilityClosure
  | equationalQuotient
  | sharingAwareSemantics
  | nonmonotoneCoOrder
  deriving DecidableEq, Repr

/-- The two-label scope classifier codomain. -/
inductive DirectBarrierScopeClass where
  | insideDirectBarrierGrammar
  | escapesDirectBarrierGrammar
  deriving DecidableEq, Repr

/-! ### Classifiers -/

/--
Proves: the direct-barrier grammar family of each inside method, or `none` for
  an escape method.
Does not prove: inhabitation of the family; this is a tag-level map.
Relation: structural projection.  Closure: N/A.  Strategy: N/A.  Trust: kernel-only.
Scope: total over the closed method universe.
-/
def barrierFamilyOf : RDRSDirectMethod → Option DirectBarrierFamily
  | .additive                   => some .additiveCompositional
  | .transparentCompositional   => some .transparentCompositional
  | .affinePump                 => some .pumpedAffine
  | .quadraticPump              => some .pumpedQuadratic
  | .crossQuadraticPump         => some .pumpedCrossQuadratic
  | .multilinearPump            => some .pumpedMultilinear
  | .polynomialPump             => some .pumpedPolynomial
  | .maxPlusPump                => some .pumpedMaxPlus
  | .maxDepth                   => some .maxDepth
  | .headPrecedence             => some .headPrecedence
  | .matrixScalarProjection     => some .matrixScalarProjection
  | .trackedPrimaryComponentwise => some .trackedPrimaryComponentwise
  | .trackedPrimaryLex          => some .trackedPrimaryLex
  | .trackedPrimaryVectorLex    => some .trackedPrimaryVectorLex
  | .dependencyPairProcessor    => none
  | .rewriteOracle              => none
  | .semanticLabeling           => none
  | .computabilityClosure       => none
  | .equationalQuotient         => none
  | .sharingAwareSemantics      => none
  | .nonmonotoneCoOrder         => none

/--
Proves: the named escape mechanism of each escape method, or `none` for an
  inside method.
Relation: structural projection.  Closure: N/A.  Strategy: N/A.  Trust: kernel-only.
Scope: total over the closed method universe.
-/
def escapeReasonOf : RDRSDirectMethod → Option DirectBarrierEscapeReason
  | .dependencyPairProcessor    => some .transformsRelation
  | .rewriteOracle              => some .consumesRewriteOracle
  | .semanticLabeling           => some .semanticLabelingTransform
  | .computabilityClosure       => some .computabilityClosure
  | .equationalQuotient         => some .equationalQuotient
  | .sharingAwareSemantics      => some .sharingAwareSemantics
  | .nonmonotoneCoOrder         => some .nonmonotoneCoOrder
  | _                           => none

/--
Proves: the two-label scope classification of each RDRS direct method.
Relation: structural projection.  Closure: N/A.  Strategy: N/A.  Trust: kernel-only.
Scope: total over the closed method universe.
-/
def directBarrierScope : RDRSDirectMethod → DirectBarrierScopeClass
  | .dependencyPairProcessor    => .escapesDirectBarrierGrammar
  | .rewriteOracle              => .escapesDirectBarrierGrammar
  | .semanticLabeling           => .escapesDirectBarrierGrammar
  | .computabilityClosure       => .escapesDirectBarrierGrammar
  | .equationalQuotient         => .escapesDirectBarrierGrammar
  | .sharingAwareSemantics      => .escapesDirectBarrierGrammar
  | .nonmonotoneCoOrder         => .escapesDirectBarrierGrammar
  | _                           => .insideDirectBarrierGrammar

/--
Proves: for the four scope-violation escapes, the concrete
  `DirectBarrierScope` sentinel witnessing the violation; `none` otherwise.
Does not prove: a sentinel for the transform/oracle escapes, which are not
  scope-field violations but named non-direct mechanisms.
Relation: structural projection.  Closure: N/A.  Strategy: N/A.  Trust: kernel-only.
Scope: the four scope-violation escape methods.
-/
def escapeScopeWitness? : RDRSDirectMethod → Option DirectBarrierScope
  | .computabilityClosure  => some computabilityScope
  | .equationalQuotient    => some acQuotientScope
  | .sharingAwareSemantics => some sharingScope
  | .nonmonotoneCoOrder    => some coOrderScope
  | _                      => none

/-! ### Grammar integrity -/

/--
Proves: the formalized direct-barrier grammar has exactly fourteen distinct
  families, matching the escape-trichotomy universe cardinality.
Relation: closed list.  Closure: N/A.  Strategy: N/A.  Trust: kernel-only.
Scope: `directBarrierGrammarFamilies`.
-/
theorem directBarrierGrammarFamilies_card :
    directBarrierGrammarFamilies.length = 14 ∧ directBarrierGrammarFamilies.Nodup := by
  refine ⟨rfl, ?_⟩
  decide

/-! ### The unconditional direct-barrier-scope theorem -/

/--
Proves: **the unconditional direct-barrier scope.** Over the closed RDRS
  direct-method universe:

  1. a method is classified `insideDirectBarrierGrammar` iff it carries a
     grammar family (`barrierFamilyOf` is `some`);
  2. a method is classified `escapesDirectBarrierGrammar` iff it carries a named
     escape mechanism (`escapeReasonOf` is `some`);
  3. inside and escape are mutually exclusive and jointly exhaustive: exactly one
     of `barrierFamilyOf`, `escapeReasonOf` is `some` for every method;
  4. every inside family tag is a member of the formalized fourteen-family
     direct-barrier grammar.

Does not prove: a universal SN theorem, nor that each family tag is inhabited by
  an orienting measure (that is `OperatorKO7.EscapeTrichotomy`), nor full method
  semantics for the escapes.
Relation: closed metadata inductives.  Closure: N/A.  Strategy: N/A.
Trust: kernel-only.  Scope: every `m : RDRSDirectMethod`.
-/
theorem rdrs_direct_barrier_scope_unconditional :
    (∀ m : RDRSDirectMethod,
        directBarrierScope m = DirectBarrierScopeClass.insideDirectBarrierGrammar
          ↔ (barrierFamilyOf m).isSome = true) ∧
    (∀ m : RDRSDirectMethod,
        directBarrierScope m = DirectBarrierScopeClass.escapesDirectBarrierGrammar
          ↔ (escapeReasonOf m).isSome = true) ∧
    (∀ m : RDRSDirectMethod,
        (barrierFamilyOf m).isSome = ! (escapeReasonOf m).isSome) ∧
    (∀ (m : RDRSDirectMethod) (fam : DirectBarrierFamily),
        barrierFamilyOf m = some fam → fam ∈ directBarrierGrammarFamilies) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro m; cases m <;> simp [directBarrierScope, barrierFamilyOf]
  · intro m; cases m <;> simp [directBarrierScope, escapeReasonOf]
  · intro m; cases m <;> rfl
  · intro m fam h
    cases m <;> simp [barrierFamilyOf] at h <;> subst h <;> decide

/--
Proves: **escape totality.** The classifier sends every escape method to a named
  mechanism, and no inside method to one.
Relation: closed enum partition.  Closure: N/A.  Strategy: N/A.  Trust: kernel-only.
Scope: every `m : RDRSDirectMethod`.
-/
theorem rdrs_direct_barrier_scope_escape_total (m : RDRSDirectMethod) :
    directBarrierScope m = DirectBarrierScopeClass.escapesDirectBarrierGrammar
      ↔ ∃ r : DirectBarrierEscapeReason, escapeReasonOf m = some r := by
  cases m <;> simp [directBarrierScope, escapeReasonOf]

/--
Proves: **scope-violation escapes are genuinely out of scope.** Each escape
  method that carries a `DirectBarrierScope` sentinel violates the direct
  barrier scope contract: `¬ InScope` of that sentinel.
Does not prove: a sentinel for the transform/oracle escapes (they are non-direct
  by mechanism, not scope-field violations).
Relation: structural projection on `DirectBarrierScope`.  Closure: N/A.
Strategy: N/A.  Trust: kernel-only.
Scope: the four scope-violation escape methods.
-/
theorem rdrs_scope_violation_escapes_not_in_scope
    (m : RDRSDirectMethod) (S : DirectBarrierScope)
    (h : escapeScopeWitness? m = some S) :
    ¬ InScope S := by
  cases m <;> simp [escapeScopeWitness?] at h <;> subst h
  · exact computabilityScope_not_InScope
  · exact acQuotientScope_not_InScope
  · exact sharingScope_not_InScope
  · exact coOrderScope_not_InScope

/-! ### Non-vacuity (R5) -/

/-- An inside-grammar method exists (R5 positive witness). -/
theorem rdrs_direct_barrier_scope_inside_nonvacuous :
    ∃ m : RDRSDirectMethod,
      directBarrierScope m = DirectBarrierScopeClass.insideDirectBarrierGrammar :=
  ⟨.additive, rfl⟩

/-- An escape method exists (R5 positive witness). -/
theorem rdrs_direct_barrier_scope_escape_nonvacuous :
    ∃ m : RDRSDirectMethod,
      directBarrierScope m = DirectBarrierScopeClass.escapesDirectBarrierGrammar :=
  ⟨.dependencyPairProcessor, rfl⟩

/-! ### Audit anchor -/

/-- Audit anchor for the theory-expansion direct-barrier-scope module. -/
def audit_theory_expansion_direct_barrier_scope_module_anchor : String :=
  "OperatorKO7.RDRSDirectBarrierScope.rdrs_direct_barrier_scope_unconditional"

end OperatorKO7.RDRSDirectBarrierScope
