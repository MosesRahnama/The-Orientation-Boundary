import OperatorKO7.Meta.RDRSCoverageLedger
import OperatorKO7.Meta.DPSubtermCriterionExact
import OperatorKO7.Meta.KBO_Impossible
import OperatorKO7.Meta.KBO_SubtermCoefficient
import OperatorKO7.Meta.Methods.UnarySignatureInapplicability
import OperatorKO7.Meta.Methods.ExactPromotionCarriers
import OperatorKO7.Meta.Methods.AlgebraicInterpretationRows
import OperatorKO7.Meta.Methods.NaturalMatrixInterpretationRows
import OperatorKO7.Meta.Methods.OrientationClosure.ResearchPackages

set_option autoImplicit false

/-!
# RDRS Coverage Evidence Ledger (WP-5)

Semantic companion to `Meta/RDRSCoverageLedger.lean`.

`Meta/RDRSCoverageLedger.lean` is a *status* ledger: it assigns each of the 76
`RDRSMethodFamily` rows a `U6Classification` tag and a String theorem
identifier. A status tag is data. It is not a proof, and a String is never
evidence. This module supplies the missing semantic layer and keeps the two
strictly apart.

```
status layer   (RDRSCoverageLedger)   u6ClassOf : family -> U6Classification     [data]
                                              |
legacy evidence layer                 RowClaim : family -> classification -> Prop
                                              |
                            +-----------------+------------------+
                            |                                    |
                   TheoremBackedEvidence                 CuratedDisposition
                   (16 constructor-closed adapters)      (60 indexed legacy gaps)
                                              |
                                              v
native ORIENTATION layer              NativeRowClaim : family -> Prop
                                      (76 exact method-native semantics)
```

## What `RowClaim` is, and what it deliberately is not

For a theorem-backed row, `RowClaim f (u6ClassOf f)` reduces to the *exact full
proposition* of that row's fully-qualified anchor theorem, with every
hypothesis and every relation/closure qualifier left in place. It is never
`u6ClassOf f = c`, never `True`, never a String or name comparison, and never
any other classifier-only surrogate.

For every other row `RowClaim f c` reduces to `False`. That remains the honest
reading of the **historical adapter interface**: no semantic claim is on offer
through that adapter. The consequence is proved, not asserted, in
`curated_row_has_no_semantic_claim`, and it keeps the old two dispositions
structurally disjoint. Dispatch ORIENTATION does not mutate this interface. The
new `Native.NativeRowClaim` layer closes the sixty adapter gaps by routing them
to the exact method-native row propositions in the reserved modules.

## The sixteen theorem-backed rows

| family | class | anchor whose exact proposition is the row claim |
|---|---|---|
| `standardKBO` | `payloadSensitiveBlocked` | `standardKBO_no_ko7_rec_succ` |
| `subtermCoefficientKBO` | `payloadSensitiveBlocked` | `subtermCoefficientKBO_no_ko7_rec_succ` |
| `cichonSlowGrowing` | `constructionEscape` | `cichonSlowGrowing_certifies` |
| `linearPolyQ` | `payloadSensitiveBlocked` | `linearPolyQ_row_anchor` |
| `linearPolyR` | `payloadSensitiveBlocked` | `linearPolyR_row_anchor` |
| `matrixNScalarProjection` | `payloadSensitiveBlocked` | `naturalMatrix_exact_row` |
| `triangularMatrix` | `payloadSensitiveBlocked` | `triangularMatrix_exact_row` |
| `dpSubtermCriterion` | `projectionTransactionEscape` | `ko7_dpSubtermCriterion_row_anchor` |
| `dpArgumentFiltering` | `projectionTransactionEscape` | `argumentFiltering_certifies` |
| `dpNeutralProcessors` | `notDirect` | `neutralDPProcessor_certifies` |
| `usableRulesMinimality` | `transformEscape` | `ko7_usableRules_rootClosure_minimality_anchor` |
| `sharingNonConservativity` | `transformEscape` | `sharing_certifies` |
| `equationalQuotientNonConservativity` | `transformEscape` | `equationalQuotient_certifies` |
| `cycleRewritingInapplicability` | `notDirect` | `cycleRewriting_inapplicable` |
| `stringRewritingInapplicability` | `notDirect` | `stringRewriting_inapplicable` |
| `sizeChangeTerminationEscape` | `projectionTransactionEscape` | `sizeChange_certifies` |

The remaining 60 rows are curated **in this legacy adapter interface**. Each
carries an indexed `CuratedReason` (`noTransportAdapter`, `externalNonLane`,
`substrateChange`, `importDependent`) and no `RowClaim` in this interface.

Dispatch ORIENTATION adds a separate native-semantic closure below. It binds
those same sixty rows to the exact method-native propositions in the reserved
`Methods/*Rows.lean` modules while preserving this 16/60 interface for backward
compatibility and audit history. Thus `curated` below means "no legacy adapter",
not "no method semantics exist in the worktree".

## NameGate record (Gate C of the audit bible)

Three anchor identifiers in the status ledger named declarations that do not
exist under the cited namespace. They are repaired in
`Meta/RDRSCoverageLedger.lean` and NameGated live (`#check @...`) in
`Test/RDRSCoverageEvidenceLedgerReach.lean`:

* KBO rows: `OperatorKO7.KBO_Impossible....` has no such namespace. The
  declaration lives in `OperatorKO7.KBOImpossible`.
* Semantic/structural rows: `OperatorKO7.RDRSSemanticStructuralAtlas....` is
  missing its `Meta` component. The declaration lives in
  `OperatorKO7.Meta.RDRSSemanticStructuralAtlas`.
* Arctic/tropical rows: `OperatorKO7.MatrixBarrierArcticTropical.arcticTropical_licensedEscape_payload`
  does not exist. That name lives in `OperatorKO7.MatrixUnrestrictedSplit`; the
  module-local barrier theorems are the per-family anchors.

## Scope discipline

* No `sorry`, `admit`, `axiom`, `constant`, `opaque`, `unsafe`, `partial`,
  `native_decide`, or `bv_decide`.
* `u6ClassOf`, `U6Classification`, and `RDRSMethodFamily` are used unchanged.
  This module adds no status value and revises no classification.
* `OperatorKO7.lean` is not edited here.
-/

namespace OperatorKO7.RDRSCoverageLedger.Evidence

open OperatorKO7.RDRSTerminationMethodUniverse
open OperatorKO7.RDRSCoverageLedger.Full
open OperatorKO7.SymbolicComparatorBarrier
open OperatorKO7.MetaDependencyPairs
open OperatorKO7.DPSubtermCriterionExactNS
open OperatorKO7.Methods.ExactPromotionCarriers
open OperatorKO7.Methods.AlgebraicInterpretationRows
open OperatorKO7.Methods.NaturalMatrixInterpretationRows
open OperatorKO7.StepDuplicating.StepDuplicatingSchema

/-! ## 1. The closed, exhaustive semantic row claim -/

/-! ### A finite standard KBO on the schema signature -/

/-- The four function symbols of the finite duplicating-rule schema. -/
inductive SchemaSymbol where
  | base | succ | wrap | recur
  deriving DecidableEq, Repr

/-- An admissible standard KBO model for the finite schema signature. A
numeric injective rank gives a strict total precedence; zero symbol weight is
allowed only for the unary symbol, which must then be precedence-maximal. -/
structure StandardKBO where
  variableWeight : Nat
  variableWeight_pos : 0 < variableWeight
  symbolWeight : SchemaSymbol → Nat
  constantWeight_ge_variable : variableWeight ≤ symbolWeight .base
  precedenceRank : SchemaSymbol → Nat
  precedenceRank_injective : Function.Injective precedenceRank
  zeroWeightOnlySucc : ∀ s, symbolWeight s = 0 → s = .succ
  zeroWeightSuccMaximal : symbolWeight .succ = 0 →
    ∀ s, s ≠ .succ → precedenceRank s < precedenceRank .succ

/-- Standard additive KBO weight on schema terms. -/
def schemaKBOWeight (K : StandardKBO) : STerm → Nat
  | .var _ => K.variableWeight
  | .base => K.symbolWeight .base
  | .succ t => K.symbolWeight .succ + schemaKBOWeight K t
  | .wrap x y => K.symbolWeight .wrap + schemaKBOWeight K x + schemaKBOWeight K y
  | .recur b s n =>
      K.symbolWeight .recur + schemaKBOWeight K b + schemaKBOWeight K s
        + schemaKBOWeight K n

/-- The standard variable condition on schema terms. -/
def SchemaVariableCondition (x y : STerm) : Prop :=
  ∀ v : SchemaVar, countVar v y ≤ countVar v x

/-- Root-symbol predicate used by the precedence arm. -/
def STerm.matches : STerm → SchemaSymbol → Prop
  | .base, .base => True
  | .succ _, .succ => True
  | .wrap _ _, .wrap => True
  | .recur _ _ _, .recur => True
  | _, _ => False

/-- Nonempty iteration of the unary schema symbol over a variable. This is the
standard zero-weight unary-variable arm of KBO. -/
inductive SuccIterationOfVar (v : SchemaVar) : STerm → Prop
  | once : SuccIterationOfVar v (.succ (.var v))
  | more {t : STerm} : SuccIterationOfVar v t → SuccIterationOfVar v (.succ t)

/-- Finite standard KBO for the schema signature: strict weight, strict root
precedence at equal weight, and lexicographic extension at equal root and
weight, plus the admissible zero-weight unary-variable arm. Every arm carries
the standard variable condition. -/
inductive SchemaKBOGt (K : StandardKBO) : STerm → STerm → Prop
  | weight {x y : STerm}
      (variableCondition : SchemaVariableCondition x y)
      (weightStrict : schemaKBOWeight K y < schemaKBOWeight K x) :
      SchemaKBOGt K x y
  | unaryVariable {v : SchemaVar} {x : STerm}
      (variableCondition : SchemaVariableCondition x (.var v))
      (iteration : SuccIterationOfVar v x)
      (zeroUnaryWeight : K.symbolWeight .succ = 0) :
      SchemaKBOGt K x (.var v)
  | precedence {x y : STerm} {sx sy : SchemaSymbol}
      (variableCondition : SchemaVariableCondition x y)
      (weightEqual : schemaKBOWeight K x = schemaKBOWeight K y)
      (rootX : STerm.matches x sx) (rootY : STerm.matches y sy)
      (precedenceStrict : K.precedenceRank sy < K.precedenceRank sx) :
      SchemaKBOGt K x y
  | succLex {x y : STerm}
      (variableCondition : SchemaVariableCondition (.succ x) (.succ y))
      (weightEqual : schemaKBOWeight K (.succ x) = schemaKBOWeight K (.succ y))
      (argumentStrict : SchemaKBOGt K x y) :
      SchemaKBOGt K (.succ x) (.succ y)
  | wrapLeftLex {x₁ x₂ y₁ y₂ : STerm}
      (variableCondition : SchemaVariableCondition (.wrap x₁ x₂) (.wrap y₁ y₂))
      (weightEqual : schemaKBOWeight K (.wrap x₁ x₂) =
        schemaKBOWeight K (.wrap y₁ y₂))
      (argumentStrict : SchemaKBOGt K x₁ y₁) :
      SchemaKBOGt K (.wrap x₁ x₂) (.wrap y₁ y₂)
  | wrapRightLex {x₁ x₂ y₂ : STerm}
      (variableCondition : SchemaVariableCondition (.wrap x₁ x₂) (.wrap x₁ y₂))
      (weightEqual : schemaKBOWeight K (.wrap x₁ x₂) =
        schemaKBOWeight K (.wrap x₁ y₂))
      (argumentStrict : SchemaKBOGt K x₂ y₂) :
      SchemaKBOGt K (.wrap x₁ x₂) (.wrap x₁ y₂)
  | recurFirstLex {b₁ s₁ n₁ b₂ s₂ n₂ : STerm}
      (variableCondition : SchemaVariableCondition (.recur b₁ s₁ n₁) (.recur b₂ s₂ n₂))
      (weightEqual : schemaKBOWeight K (.recur b₁ s₁ n₁) =
        schemaKBOWeight K (.recur b₂ s₂ n₂))
      (argumentStrict : SchemaKBOGt K b₁ b₂) :
      SchemaKBOGt K (.recur b₁ s₁ n₁) (.recur b₂ s₂ n₂)
  | recurSecondLex {b s₁ n₁ s₂ n₂ : STerm}
      (variableCondition : SchemaVariableCondition (.recur b s₁ n₁) (.recur b s₂ n₂))
      (weightEqual : schemaKBOWeight K (.recur b s₁ n₁) =
        schemaKBOWeight K (.recur b s₂ n₂))
      (argumentStrict : SchemaKBOGt K s₁ s₂) :
      SchemaKBOGt K (.recur b s₁ n₁) (.recur b s₂ n₂)
  | recurThirdLex {b s n₁ n₂ : STerm}
      (variableCondition : SchemaVariableCondition (.recur b s n₁) (.recur b s n₂))
      (weightEqual : schemaKBOWeight K (.recur b s n₁) =
        schemaKBOWeight K (.recur b s n₂))
      (argumentStrict : SchemaKBOGt K n₁ n₂) :
      SchemaKBOGt K (.recur b s n₁) (.recur b s n₂)

/-- Every standard-KBO comparison satisfies the variable condition. -/
theorem SchemaKBOGt.variableCondition {K : StandardKBO} {x y : STerm}
    (h : SchemaKBOGt K x y) : SchemaVariableCondition x y := by
  cases h <;> assumption

/-- Concrete positive-weight and strict-precedence model, an inhabited member
of the full admissible carrier family. -/
def finiteStandardKBO : StandardKBO where
  variableWeight := 1
  variableWeight_pos := by decide
  symbolWeight := fun _ => 1
  constantWeight_ge_variable := by decide
  precedenceRank
    | .base => 0
    | .succ => 1
    | .wrap => 2
    | .recur => 3
  precedenceRank_injective := by
    intro a b h
    cases a <;> cases b <;> simp_all
  zeroWeightOnlySucc := by
    intro s h
    simp at h
  zeroWeightSuccMaximal := by
    intro h
    simp at h

/-- The strict-weight arm is genuinely inhabited by a distinct pair. -/
theorem finiteStandardKBO_orients_strictWeight_witness :
    SchemaKBOGt finiteStandardKBO (.succ .base) .base := by
  apply SchemaKBOGt.weight
  · intro v
    cases v <;> decide
  · decide

/-- The equal-weight precedence arm is also genuinely inhabited. -/
theorem finiteStandardKBO_orients_precedence_witness :
    SchemaKBOGt finiteStandardKBO (.wrap .base .base) (.succ (.succ .base)) := by
  apply SchemaKBOGt.precedence (sx := .wrap) (sy := .succ)
  · intro v
    cases v <;> decide
  · decide
  · trivial
  · trivial
  · decide

/-- A carrier-specialized obstruction for the actual KO7 recursor-successor
root step. -/
structure StandardKBORecSuccObstruction (K : StandardKBO) : Prop where
  noSchemaOrientation : ¬ SchemaKBOGt K dupSrc dupTgt
  sourceInstantiation :
    instantiate Trace.void Trace.void Trace.void dupSrc =
      Trace.recΔ Trace.void Trace.void (Trace.delta Trace.void)
  targetInstantiation :
    instantiate Trace.void Trace.void Trace.void dupTgt =
      Trace.app Trace.void (Trace.recΔ Trace.void Trace.void Trace.void)
  actualRootStep :
    Step (Trace.recΔ Trace.void Trace.void (Trace.delta Trace.void))
      (Trace.app Trace.void (Trace.recΔ Trace.void Trace.void Trace.void))

/-- No finite standard KBO on this signature orients the KO7 duplicating
recursor-successor root rule. -/
theorem standardKBO_no_ko7_rec_succ (K : StandardKBO) :
    StandardKBORecSuccObstruction K where
  noSchemaOrientation := by
    intro h
    have hv : countVar SchemaVar.s dupTgt ≤ countVar SchemaVar.s dupSrc :=
      SchemaKBOGt.variableCondition h SchemaVar.s
    simp [dupSrc, dupTgt, countVar] at hv
  sourceInstantiation := instantiate_dupSrc _ _ _
  targetInstantiation := instantiate_dupTgt _ _ _
  actualRootStep := Step.R_rec_succ _ _ _

/-- Exact standard-KBO row proposition. -/
abbrev StandardKBORowClaim : Prop :=
  ∀ K : StandardKBO, StandardKBORecSuccObstruction K

/-- Concrete semantic proposition for the KO7 DP subterm-criterion row. It
names the canonical certificate, both index conventions, strict descent on the
actual dependency-pair relation, and well-foundedness of its reverse. -/
abbrev DPSubtermCriterionRowClaim : Prop :=
  ko7DPSubtermCriterionExact.projectionIndex = 2
    ∧ ko7DPSubtermCriterionExact.projectionIndex_paper = 3
    ∧ (∀ {a b : Trace}, DPPair a b →
        ko7DPSubtermCriterionExact.rank b < ko7DPSubtermCriterionExact.rank a)
    ∧ WellFounded DPPairRev

/-- Typed per-row anchor for the canonical exact KO7 DP certificate. -/
theorem ko7_dpSubtermCriterion_row_anchor : DPSubtermCriterionRowClaim :=
  ⟨rfl, rfl, ko7DPSubtermCriterionExact.pair_strict_descent,
    ko7DPSubtermCriterionExact.reverse_pair_well_founded⟩

/-! ### Finite usable-rule root closure for KO7 -/

/-- The eight root rules of `Step`, retained as a finite decidable universe. -/
inductive KO7RootRule where
  | intDelta
  | mergeVoidLeft
  | mergeVoidRight
  | mergeCancel
  | recZero
  | recSucc
  | eqRefl
  | eqDiff
  deriving DecidableEq, Repr

/-- Complete finite root-rule universe. -/
def allKO7RootRules : List KO7RootRule :=
  [.intDelta, .mergeVoidLeft, .mergeVoidRight, .mergeCancel,
    .recZero, .recSucc, .eqRefl, .eqDiff]

theorem allKO7RootRules_nodup : allKO7RootRules.Nodup := by decide

theorem allKO7RootRules_complete (r : KO7RootRule) : r ∈ allKO7RootRules := by
  cases r <;> decide

/-- Defined root symbols occurring on KO7 rule left-hand sides. -/
inductive KO7DefinedRoot where
  | integrate | merge | recursor | equality
  deriving DecidableEq, Repr

/-- Defined root of a finite KO7 root rule. -/
def ko7RuleRoot : KO7RootRule → KO7DefinedRoot
  | .intDelta => .integrate
  | .mergeVoidLeft | .mergeVoidRight | .mergeCancel => .merge
  | .recZero | .recSucc => .recursor
  | .eqRefl | .eqDiff => .equality

/-- Defined roots occurring in a concrete trace. `app` and `delta` are
constructors, not defined-rule heads. -/
def traceDefinedRoots : Trace → List KO7DefinedRoot
  | .void => []
  | .delta t => traceDefinedRoots t
  | .integrate t => .integrate :: traceDefinedRoots t
  | .merge x y => .merge :: (traceDefinedRoots x ++ traceDefinedRoots y)
  | .app x y => traceDefinedRoots x ++ traceDefinedRoots y
  | .recΔ b s n => .recursor ::
      (traceDefinedRoots b ++ traceDefinedRoots s ++ traceDefinedRoots n)
  | .eqW x y => .equality :: (traceDefinedRoots x ++ traceDefinedRoots y)

/-- Concrete left-hand-side template for each root rule. `void` instantiates
the rule parameters; these are actual `Step` instances, not name tags. -/
def ko7RuleLhsTemplate : KO7RootRule → Trace
  | .intDelta => .integrate (.delta .void)
  | .mergeVoidLeft => .merge .void .void
  | .mergeVoidRight => .merge .void .void
  | .mergeCancel => .merge .void .void
  | .recZero => .recΔ .void .void .void
  | .recSucc => .recΔ .void .void (.delta .void)
  | .eqRefl => .eqW .void .void
  | .eqDiff => .eqW .void .void

/-- Concrete right-hand-side template for each root rule. Parameters are
represented by `void`, so defined symbols underneath parameter positions are
not spuriously added to the usable closure. -/
def ko7RuleRhsTemplate : KO7RootRule → Trace
  | .intDelta => .void
  | .mergeVoidLeft => .void
  | .mergeVoidRight => .void
  | .mergeCancel => .void
  | .recZero => .void
  | .recSucc => .app .void (.recΔ .void .void .void)
  | .eqRefl => .void
  | .eqDiff => .integrate (.merge .void .void)

/-- Parameterized instance relation for the complete finite `Step` rule
universe. Unlike the templates, this retains every constructor parameter. -/
inductive KO7RuleInstance : KO7RootRule → Trace → Trace → Prop
  | intDelta (t : Trace) :
      KO7RuleInstance .intDelta (.integrate (.delta t)) .void
  | mergeVoidLeft (t : Trace) :
      KO7RuleInstance .mergeVoidLeft (.merge .void t) t
  | mergeVoidRight (t : Trace) :
      KO7RuleInstance .mergeVoidRight (.merge t .void) t
  | mergeCancel (t : Trace) :
      KO7RuleInstance .mergeCancel (.merge t t) t
  | recZero (b s : Trace) :
      KO7RuleInstance .recZero (.recΔ b s .void) b
  | recSucc (b s n : Trace) :
      KO7RuleInstance .recSucc (.recΔ b s (.delta n)) (.app s (.recΔ b s n))
  | eqRefl (a : Trace) :
      KO7RuleInstance .eqRefl (.eqW a a) .void
  | eqDiff (a b : Trace) :
      KO7RuleInstance .eqDiff (.eqW a b) (.integrate (.merge a b))

/-- The parameterized finite rule universe is extensionally complete for
`Step`: every and only `Step` edges are instances of an enumerated rule. -/
theorem step_iff_complete_KO7RuleInstance {x y : Trace} :
    Step x y ↔ ∃ r, r ∈ allKO7RootRules ∧ KO7RuleInstance r x y := by
  constructor
  · intro h
    cases h
    · exact ⟨.intDelta, allKO7RootRules_complete _, .intDelta _⟩
    · exact ⟨.mergeVoidLeft, allKO7RootRules_complete _, .mergeVoidLeft _⟩
    · exact ⟨.mergeVoidRight, allKO7RootRules_complete _, .mergeVoidRight _⟩
    · exact ⟨.mergeCancel, allKO7RootRules_complete _, .mergeCancel _⟩
    · exact ⟨.recZero, allKO7RootRules_complete _, .recZero _ _⟩
    · exact ⟨.recSucc, allKO7RootRules_complete _, .recSucc _ _ _⟩
    · exact ⟨.eqRefl, allKO7RootRules_complete _, .eqRefl _⟩
    · exact ⟨.eqDiff, allKO7RootRules_complete _, .eqDiff _ _⟩
  · rintro ⟨r, _, h⟩
    cases h
    · exact Step.R_int_delta _
    · exact Step.R_merge_void_left _
    · exact Step.R_merge_void_right _
    · exact Step.R_merge_cancel _
    · exact Step.R_rec_zero _ _
    · exact Step.R_rec_succ _ _ _
    · exact Step.R_eq_refl _
    · exact Step.R_eq_diff _ _

/-- Every symbolic closure template is an instance of the corresponding
parameterized rule. -/
theorem ko7RuleTemplate_is_ruleInstance (r : KO7RootRule) :
    KO7RuleInstance r (ko7RuleLhsTemplate r) (ko7RuleRhsTemplate r) := by
  cases r
  · exact .intDelta _
  · exact .mergeVoidLeft _
  · exact .mergeVoidRight _
  · exact .mergeCancel _
  · exact .recZero _ _
  · exact .recSucc _ _ _
  · exact .eqRefl _
  · exact .eqDiff _ _

/-- Every finite template is therefore an actual `Step` edge. -/
theorem ko7RuleTemplate_is_actual_step (r : KO7RootRule) :
    Step (ko7RuleLhsTemplate r) (ko7RuleRhsTemplate r) :=
  step_iff_complete_KO7RuleInstance.mpr
    ⟨r, allKO7RootRules_complete r, ko7RuleTemplate_is_ruleInstance r⟩

/-- Computable form of the direct-call test. -/
def ko7RootDirectCallB (r q : KO7RootRule) : Bool :=
  (traceDefinedRoots (ko7RuleRhsTemplate r)).contains (ko7RuleRoot q)

/-- A rule directly calls another rule when the latter's defined root occurs
in the former's concrete right-hand-side template. -/
def KO7RootDirectCall (r q : KO7RootRule) : Prop :=
  ko7RootDirectCallB r q = true

/-- Root-closure condition for a finite list of KO7 rules. -/
def KO7RootClosed (rules : List KO7RootRule) : Prop :=
  ∀ r, r ∈ rules → ∀ q, KO7RootDirectCall r q → q ∈ rules

/-- Canonical usable set generated by the dependency-pair seed `recSucc`.
The RHS recursive call has root `recΔ`, so both rules headed by `recΔ` are
retained. -/
def ko7CanonicalUsableRules : List KO7RootRule := [.recZero, .recSucc]

theorem ko7CanonicalUsableRules_nodup : ko7CanonicalUsableRules.Nodup := by
  decide

/-- The recursive RHS calls the zero-rule branch sharing its `recΔ` root. -/
theorem recSucc_directlyCalls_recZero :
    KO7RootDirectCall .recSucc .recZero := by
  simp [KO7RootDirectCall, ko7RootDirectCallB, ko7RuleRoot,
    ko7RuleRhsTemplate, traceDefinedRoots]

/-- The recursive RHS also calls the successor-rule branch sharing its
`recΔ` root. -/
theorem recSucc_directlyCalls_recSucc :
    KO7RootDirectCall .recSucc .recSucc := by
  simp [KO7RootDirectCall, ko7RootDirectCallB, ko7RuleRoot,
    ko7RuleRhsTemplate, traceDefinedRoots]

/-- The canonical usable set is root-closed. -/
theorem ko7CanonicalUsableRules_rootClosed :
    KO7RootClosed ko7CanonicalUsableRules := by
  intro r hr q hq
  have hr' : r = .recZero ∨ r = .recSucc := by
    simpa [ko7CanonicalUsableRules] using hr
  rcases hr' with rfl | rfl
  · simp [KO7RootDirectCall, ko7RootDirectCallB, ko7RuleRoot, ko7RuleRhsTemplate,
      traceDefinedRoots] at hq
  · cases q <;> simp [ko7CanonicalUsableRules, KO7RootDirectCall, ko7RootDirectCallB,
      ko7RuleRoot, ko7RuleRhsTemplate, traceDefinedRoots] at hq ⊢

/-- The duplicating recursor-successor rule is retained. -/
theorem ko7CanonicalUsableRules_retains_recSucc :
    KO7RootRule.recSucc ∈ ko7CanonicalUsableRules := by
  simp [ko7CanonicalUsableRules]

/-- The canonical set is the least root-closed set containing `recSucc`. -/
theorem ko7CanonicalUsableRules_least (rules : List KO7RootRule)
    (closed : KO7RootClosed rules) (seed : KO7RootRule.recSucc ∈ rules) :
    ∀ q, q ∈ ko7CanonicalUsableRules → q ∈ rules := by
  intro q hq
  have hq' : q = .recZero ∨ q = .recSucc := by
    simpa [ko7CanonicalUsableRules] using hq
  rcases hq' with rfl | rfl
  · exact closed .recSucc seed .recZero recSucc_directlyCalls_recZero
  · exact seed

/-- The retained duplicating rule denotes every actual `R_rec_succ` root
instance. -/
theorem ko7CanonicalUsableRules_retained_recSucc_step (b s n : Trace) :
    Step (Trace.recΔ b s (Trace.delta n)) (Trace.app s (Trace.recΔ b s n)) :=
  Step.R_rec_succ b s n

/-! ### DP-RHS extraction and generated usable-rule fixed point -/

/-- Symbolic RHS of the single KO7 dependency pair. -/
def ko7DPRhsSchema : STerm :=
  .recur (.var .b) (.var .s) (.var .n)

/-- Defined roots visible in a symbolic schema term; variables contribute no
roots because usable-rule extraction does not inspect their substitutions. -/
def schemaDefinedRoots : STerm → List KO7DefinedRoot
  | .var _ | .base => []
  | .succ t => schemaDefinedRoots t
  | .wrap x y => schemaDefinedRoots x ++ schemaDefinedRoots y
  | .recur b s n => .recursor ::
      (schemaDefinedRoots b ++ schemaDefinedRoots s ++ schemaDefinedRoots n)

theorem ko7DPRhsSchema_definedRoots :
    schemaDefinedRoots ko7DPRhsSchema = [.recursor] := rfl

/-- Extraction from an actual `DPPair` proof: every concrete pair RHS is an
instance of the same symbolic recursor-call schema. -/
theorem DPPair_rhs_schema_extraction {lhs rhs : Trace} (pair : DPPair lhs rhs) :
    ∃ b s n,
      lhs = instantiate b s n dupSrc
        ∧ rhs = instantiate b s n ko7DPRhsSchema := by
  cases pair with
  | rec_succ b s n =>
      exact ⟨b, s, n, (instantiate_dupSrc b s n).symm, by
        simp [ko7DPRhsSchema, instantiate]⟩

/-- All finite KO7 rules whose defined heads occur in a symbolic DP RHS. -/
def ko7RulesAtSchemaRoots (rhsSchema : STerm) : List KO7RootRule :=
  allKO7RootRules.filter fun r =>
    (schemaDefinedRoots rhsSchema).contains (ko7RuleRoot r)

/-- One finite root-closure step. -/
def ko7RootClosureStep (rules : List KO7RootRule) : List KO7RootRule :=
  allKO7RootRules.filter fun q =>
    rules.contains q || rules.any (fun r => ko7RootDirectCallB r q)

/-- Generated usable rules: exactly all finite rules whose defined roots occur
in the symbolic DP RHS. For KO7 this set is already a root-closure fixed point. -/
def ko7GeneratedUsableRules (rhsSchema : STerm) : List KO7RootRule :=
  ko7RulesAtSchemaRoots rhsSchema

theorem ko7RulesAtDPRhsRoots_exact :
    ko7RulesAtSchemaRoots ko7DPRhsSchema = [.recZero, .recSucc] := by
  decide

theorem ko7GeneratedUsableRules_exact :
    ko7GeneratedUsableRules ko7DPRhsSchema = [.recZero, .recSucc] := by
  decide

theorem ko7GeneratedUsableRules_fixedPoint :
    ko7RootClosureStep (ko7GeneratedUsableRules ko7DPRhsSchema) =
      ko7GeneratedUsableRules ko7DPRhsSchema := by
  decide

theorem ko7GeneratedUsableRules_rootClosed :
    KO7RootClosed (ko7GeneratedUsableRules ko7DPRhsSchema) := by
  rw [ko7GeneratedUsableRules_exact]
  simpa [ko7CanonicalUsableRules] using ko7CanonicalUsableRules_rootClosed

/-- Leastness among root-closed candidates containing the actual DP rule seed.
The closure premise is load-bearing: it forces `recZero` from the retained
`recSucc` rule's recursive `recΔ` call. -/
theorem ko7GeneratedUsableRules_least (rules : List KO7RootRule)
    (closed : KO7RootClosed rules) (dpSeed : KO7RootRule.recSucc ∈ rules) :
    ∀ q, q ∈ ko7GeneratedUsableRules ko7DPRhsSchema → q ∈ rules := by
  intro q hq
  apply ko7CanonicalUsableRules_least rules closed dpSeed q
  rw [ko7GeneratedUsableRules_exact] at hq
  simpa [ko7CanonicalUsableRules] using hq

/-- Projection selected by retention of the actual dependency-pair rule. -/
def retainedDPProjection (rules : List KO7RootRule) : Option (Trace → Nat) :=
  if KO7RootRule.recSucc ∈ rules then
    some ko7DPSubtermCriterionExact.rank
  else none

/-- Retention is consumed to select the exact projection, which then strictly
decreases on the same actual `DPPair`. -/
def RetainedProjectionDecreases
    (rules : List KO7RootRule) {lhs rhs : Trace} (_pair : DPPair lhs rhs) : Prop :=
  ∀ _retained : KO7RootRule.recSucc ∈ rules,
    match retainedDPProjection rules with
    | some rank => rank rhs < rank lhs
    | none => False

theorem retainedProjection_decreases_on_DPPair
    {lhs rhs : Trace} (pair : DPPair lhs rhs) :
    RetainedProjectionDecreases
      (ko7GeneratedUsableRules ko7DPRhsSchema) pair := by
  intro retained
  simp [retainedDPProjection, retained]
  exact ko7DPSubtermCriterionExact.pair_strict_descent pair

/-- Certificate indexed by the symbolic DP RHS and the generated usable-rule
set. Its scope is exact extraction, least root closure, and the exact DP
projection on the same pair; it does not claim generic source termination. -/
structure KO7DPPairUsableRulesCertificate
    (rhsSchema : STerm) (rules : List KO7RootRule) : Prop where
  rhsSchemaExact : rhsSchema = ko7DPRhsSchema
  extractedRootsExact : schemaDefinedRoots rhsSchema = [.recursor]
  rulesGenerated : rules = ko7GeneratedUsableRules rhsSchema
  everyPairExtracts : ∀ {lhs rhs}, DPPair lhs rhs →
    ∃ b s n, lhs = instantiate b s n dupSrc
      ∧ rhs = instantiate b s n rhsSchema
  rulesExact : rules = [.recZero, .recSucc]
  fixedPoint : ko7RootClosureStep rules = rules
  rootClosed : KO7RootClosed rules
  leastRootClosed : ∀ candidate, KO7RootClosed candidate →
    KO7RootRule.recSucc ∈ candidate →
      ∀ q, q ∈ rules → q ∈ candidate
  retainsDuplicatingRule : KO7RootRule.recSucc ∈ rules
  completeStepEnumeration : ∀ {x y},
    Step x y ↔ ∃ r, r ∈ allKO7RootRules ∧ KO7RuleInstance r x y
  retainedProjectionStrict : ∀ {lhs rhs} (pair : DPPair lhs rhs),
    RetainedProjectionDecreases rules pair
  reversePairWellFounded : WellFounded DPPairRev

/-- Typed per-row anchor at the exact symbolic RHS and generated fixed point. -/
theorem ko7_usableRules_rootClosure_minimality_anchor :
    KO7DPPairUsableRulesCertificate ko7DPRhsSchema
      (ko7GeneratedUsableRules ko7DPRhsSchema) where
  rhsSchemaExact := rfl
  extractedRootsExact := ko7DPRhsSchema_definedRoots
  rulesGenerated := rfl
  everyPairExtracts := DPPair_rhs_schema_extraction
  rulesExact := ko7GeneratedUsableRules_exact
  fixedPoint := ko7GeneratedUsableRules_fixedPoint
  rootClosed := ko7GeneratedUsableRules_rootClosed
  leastRootClosed := ko7GeneratedUsableRules_least
  retainsDuplicatingRule := by
    rw [ko7GeneratedUsableRules_exact]
    decide
  completeStepEnumeration := step_iff_complete_KO7RuleInstance
  retainedProjectionStrict := retainedProjection_decreases_on_DPPair
  reversePairWellFounded := ko7DPSubtermCriterionExact.reverse_pair_well_founded

/-- Exact usable-rules row proposition. -/
abbrev UsableRulesConcreteRowClaim : Prop :=
  KO7DPPairUsableRulesCertificate ko7DPRhsSchema
    (ko7GeneratedUsableRules ko7DPRhsSchema)

/-- The semantic content a ledger row would have to carry to count as
theorem-backed.

Each theorem-backed branch reduces to the exact full proposition of the row's
fully-qualified anchor, hypotheses included:

* `standardKBO`: every admissible finite standard KBO on the schema
  signature fails to orient the duplicating rule, with the schema terms tied to
  an actual `Step.R_rec_succ` root instance.
* `subtermCoefficientKBO`: the same for every admissible KBO with subterm
  coefficients, with the coefficient-weighted payload count recorded as
  strictly rising across the rule.
* `dpSubtermCriterion`: the canonical exact DP certificate, its
  zero-based/paper index correspondence,
  strict descent on `DPPair`, and well-foundedness of `DPPairRev`.
* `usableRulesMinimality`: the actual finite root closure generated from the
  symbolic RHS of every `DPPair`, retention of the duplicating root rule, and
  exact KO7 DP subterm-projection descent on the same retained pair.

Every other pair reduces to `False`. A curated row makes no semantic claim. -/
def RowClaim : RDRSMethodFamily → U6Classification → Prop
  | .standardKBO, .payloadSensitiveBlocked =>
      StandardKBORowClaim
  | .subtermCoefficientKBO, .payloadSensitiveBlocked =>
      OperatorKO7.KBOSubtermCoefficient.SubtermCoefficientKBORowClaim
  | .cichonSlowGrowing, .constructionEscape =>
      CichonSlowGrowingExactRowClaim
  | .linearPolyQ, .payloadSensitiveBlocked => LinearPolyQRowClaim
  | .linearPolyR, .payloadSensitiveBlocked => LinearPolyRRowClaim
  | .matrixNScalarProjection, .payloadSensitiveBlocked => NaturalMatrixExactRowClaim
  | .triangularMatrix, .payloadSensitiveBlocked => TriangularMatrixExactRowClaim
  | .dpSubtermCriterion, .projectionTransactionEscape =>
      DPSubtermCriterionRowClaim
  | .dpArgumentFiltering, .projectionTransactionEscape =>
      ArgumentFilteringExactRowClaim
  | .dpNeutralProcessors, .notDirect =>
      NeutralDPProcessorExactRowClaim
  | .usableRulesMinimality, .transformEscape =>
      UsableRulesConcreteRowClaim
  | .sharingNonConservativity, .transformEscape =>
      SharingExactRowClaim
  | .equationalQuotientNonConservativity, .transformEscape =>
      EquationalQuotientExactRowClaim
  | .cycleRewritingInapplicability, .notDirect =>
      ¬ OperatorKO7.Methods.UnarySignatureInapplicability.UnarySignature
          OperatorKO7.Methods.UnarySignatureInapplicability.ko7FunArity
  | .stringRewritingInapplicability, .notDirect =>
      ¬ OperatorKO7.Methods.UnarySignatureInapplicability.UnarySignature
          OperatorKO7.Methods.UnarySignatureInapplicability.ko7FunArity
  | .sizeChangeTerminationEscape, .projectionTransactionEscape =>
      SizeChangeExactRowClaim
  | _, _ => False

/-! ## 2. Method interpretations: closed indexed family with concrete carriers -/

/-- A concrete interpretation of a ledger row as an actual method object.

This is an indexed inductive family. The row index is fixed by the constructor,
so there is no `toFamily` field and no stored equality proof to launder a wrong
row into a right one. Each constructor carries the exact finite object used by
its row claim:

* `DPSubtermCriterionExact` is defined in `Meta/DPSubtermCriterionExact.lean`;
* `KO7DPPairUsableRulesCertificate` is indexed by the extracted DP RHS schema
  and its generated rule fixed point. -/

inductive MethodInterpretation : RDRSMethodFamily → Type
  | rationalAffine (M : FieldAffineMeasure freeSchema NNRat) :
      MethodInterpretation RDRSMethodFamily.linearPolyQ
  | realAffine (M : FieldAffineMeasure freeSchema NNReal) :
      MethodInterpretation RDRSMethodFamily.linearPolyR
  | naturalMatrix {d : Nat} [NeZero d] (M : NaturalMatrixMethod freeSchema d) :
      MethodInterpretation RDRSMethodFamily.matrixNScalarProjection
  | triangularMatrix {d : Nat} [NeZero d] (M : TriangularMatrixMethod freeSchema d) :
      MethodInterpretation RDRSMethodFamily.triangularMatrix
  /-- KBO row carrier: a concrete finite standard KBO. -/
  | kboVariableConditionOrder
      (K : StandardKBO) :
      MethodInterpretation RDRSMethodFamily.standardKBO
  /-- Subterm-coefficient KBO row carrier: a concrete admissible KBO with
  subterm coefficients on the same schema signature. -/
  | subtermCoefficientKBOOrder
      (K : OperatorKO7.KBOSubtermCoefficient.SubtermCoefficientKBO) :
      MethodInterpretation RDRSMethodFamily.subtermCoefficientKBO
  /-- Cichon row carrier: the closed guarded-contextual construction. -/
  | cichonSlowGrowingMethod
      (M : KO7CichonSlowGrowingMethod) :
      MethodInterpretation RDRSMethodFamily.cichonSlowGrowing
  /-- DP subterm row carrier: the concrete
  certificate `ko7DPSubtermCriterionExact`. -/
  | dpSubtermProjectionRow :
      MethodInterpretation RDRSMethodFamily.dpSubtermCriterion
  /-- Argument-filtering row carrier: the closed counter-only constructor filter. -/
  | dpArgumentFilteringMethod
      (M : KO7ArgumentFilteringMethod) :
      MethodInterpretation RDRSMethodFamily.dpArgumentFiltering
  /-- Neutral-DP row carrier: the closed identity processor. -/
  | dpNeutralProcessorMethod
      (M : KO7NeutralDPProcessorMethod) :
      MethodInterpretation RDRSMethodFamily.dpNeutralProcessors
  /-- Usable-rules row carrier: an actual extracted dependency pair. -/
  | usableRulesConcreteRow {lhs rhs : Trace} (pair : DPPair lhs rhs) :
      MethodInterpretation RDRSMethodFamily.usableRulesMinimality
  /-- Sharing row carrier: the closed explicit shared-node substrate. -/
  | sharingMethod
      (M : KO7SharingMethod) :
      MethodInterpretation RDRSMethodFamily.sharingNonConservativity
  /-- Equational-quotient row carrier: the closed merge-commutativity quotient. -/
  | equationalQuotientMethod
      (M : KO7EquationalQuotientMethod) :
      MethodInterpretation RDRSMethodFamily.equationalQuotientNonConservativity
  /-- Cycle-rewriting row: KO7 is not a unary signature. -/
  | cycleRewritingUnaryKill :
      MethodInterpretation RDRSMethodFamily.cycleRewritingInapplicability
  /-- String-rewriting row: KO7 is not a unary signature. -/
  | stringRewritingUnaryKill :
      MethodInterpretation RDRSMethodFamily.stringRewritingInapplicability
  /-- Size-change row carrier: the closed single-call KO7 size-change graph. -/
  | sizeChangeMethod
      (M : KO7SizeChangeMethod) :
      MethodInterpretation RDRSMethodFamily.sizeChangeTerminationEscape

/-- Closed interpreter computing the ledger family an interpretation denotes.
It reads the constructor, not a stored field. -/
def interpretedFamily {f : RDRSMethodFamily} (i : MethodInterpretation f) :
    RDRSMethodFamily :=
  match i with
  | .rationalAffine _ => RDRSMethodFamily.linearPolyQ
  | .realAffine _ => RDRSMethodFamily.linearPolyR
  | @MethodInterpretation.naturalMatrix _ _ _ => RDRSMethodFamily.matrixNScalarProjection
  | @MethodInterpretation.triangularMatrix _ _ _ => RDRSMethodFamily.triangularMatrix
  | .kboVariableConditionOrder _ => RDRSMethodFamily.standardKBO
  | .subtermCoefficientKBOOrder _ => RDRSMethodFamily.subtermCoefficientKBO
  | .cichonSlowGrowingMethod _ => RDRSMethodFamily.cichonSlowGrowing
  | .dpSubtermProjectionRow => RDRSMethodFamily.dpSubtermCriterion
  | .dpArgumentFilteringMethod _ => RDRSMethodFamily.dpArgumentFiltering
  | .dpNeutralProcessorMethod _ => RDRSMethodFamily.dpNeutralProcessors
  | .usableRulesConcreteRow _ => RDRSMethodFamily.usableRulesMinimality
  | .sharingMethod _ => RDRSMethodFamily.sharingNonConservativity
  | .equationalQuotientMethod _ => RDRSMethodFamily.equationalQuotientNonConservativity
  | .cycleRewritingUnaryKill => RDRSMethodFamily.cycleRewritingInapplicability
  | .stringRewritingUnaryKill => RDRSMethodFamily.stringRewritingInapplicability
  | .sizeChangeMethod _ => RDRSMethodFamily.sizeChangeTerminationEscape

/-- The computed family always agrees with the index. -/
theorem interpretedFamily_eq_index {f : RDRSMethodFamily}
    (i : MethodInterpretation f) : interpretedFamily i = f := by
  cases i <;> rfl

/-- Closed interpreter computing the concrete exact DP certificate, where the
row has one. -/
def dpCarrier {f : RDRSMethodFamily} (i : MethodInterpretation f) :
    Option DPSubtermCriterionExact :=
  match i with
  | .rationalAffine _ => none
  | .realAffine _ => none
  | @MethodInterpretation.naturalMatrix _ _ _ => none
  | @MethodInterpretation.triangularMatrix _ _ _ => none
  | .kboVariableConditionOrder _ => none
  | .subtermCoefficientKBOOrder _ => none
  | .cichonSlowGrowingMethod _ => none
  | .dpSubtermProjectionRow => some ko7DPSubtermCriterionExact
  | .dpArgumentFilteringMethod _ => none
  | .dpNeutralProcessorMethod _ => none
  | .usableRulesConcreteRow _ => none
  | .sharingMethod _ => none
  | .equationalQuotientMethod _ => none
  | .cycleRewritingUnaryKill => none
  | .stringRewritingUnaryKill => none
  | .sizeChangeMethod _ => none

/-- Any inhabited DP carrier is definitionally the canonical exact KO7
certificate, rather than a route-only processor tag. -/
theorem dpCarrier_eq_ko7DPSubtermCriterionExact {f : RDRSMethodFamily}
    (i : MethodInterpretation f) (p : DPSubtermCriterionExact)
    (h : dpCarrier i = some p) : p = ko7DPSubtermCriterionExact := by
  cases i with
  | rationalAffine _ => simp [dpCarrier] at h
  | realAffine _ => simp [dpCarrier] at h
  | naturalMatrix _ => simp [dpCarrier] at h
  | triangularMatrix _ => simp [dpCarrier] at h
  | kboVariableConditionOrder _ => simp [dpCarrier] at h
  | subtermCoefficientKBOOrder _ => simp [dpCarrier] at h
  | cichonSlowGrowingMethod _ => simp [dpCarrier] at h
  | dpSubtermProjectionRow =>
      simpa [dpCarrier] using h.symm
  | dpArgumentFilteringMethod _ => simp [dpCarrier] at h
  | dpNeutralProcessorMethod _ => simp [dpCarrier] at h
  | usableRulesConcreteRow _ => simp [dpCarrier] at h
  | sharingMethod _ => simp [dpCarrier] at h
  | equationalQuotientMethod _ => simp [dpCarrier] at h
  | cycleRewritingUnaryKill => simp [dpCarrier] at h
  | stringRewritingUnaryKill => simp [dpCarrier] at h
  | sizeChangeMethod _ => simp [dpCarrier] at h

/-! ## 3. Anchor instances at the carrier, and the adapter laws -/

/-- The named anchor theorem, instantiated at the interpretation's own carrier.
This is what the adapter law transports; it is not a stored field. -/
def AnchorInstanceHolds {f : RDRSMethodFamily} (i : MethodInterpretation f) : Prop :=
  match i with
  | .rationalAffine M => ∀ δ : NNRat, 0 < δ → ¬ FieldAffineOrients M δ
  | .realAffine M => ∀ δ : NNReal, 0 < δ → ¬ FieldAffineOrients M δ
  | @MethodInterpretation.naturalMatrix _ _ M => ¬ ∀ b s n : FreeTerm, VecLeLt 0
      (M.interpretation.eval (.wrap s (.recur b s n)))
      (M.interpretation.eval (.recur b s (.succ n)))
  | @MethodInterpretation.triangularMatrix _ _ M => ¬ ∀ b s n : FreeTerm, VecLeLt 0
      (M.interpretation.eval (.wrap s (.recur b s n)))
      (M.interpretation.eval (.recur b s (.succ n)))
  | .kboVariableConditionOrder K => StandardKBORecSuccObstruction K
  | .subtermCoefficientKBOOrder K =>
      OperatorKO7.KBOSubtermCoefficient.SubtermCoefficientKBORecSuccObstruction K
  | .cichonSlowGrowingMethod M => CichonSlowGrowingCertifies M
  | .dpSubtermProjectionRow => DPSubtermCriterionRowClaim
  | .dpArgumentFilteringMethod M => ArgumentFilteringCertifies M
  | .dpNeutralProcessorMethod M => NeutralDPProcessorCertifies M
  | .usableRulesConcreteRow pair =>
      UsableRulesConcreteRowClaim ∧
        RetainedProjectionDecreases
          (ko7GeneratedUsableRules ko7DPRhsSchema) pair
  | .sharingMethod M => SharingCertifies M
  | .equationalQuotientMethod M => EquationalQuotientCertifies M
  | .cycleRewritingUnaryKill =>
      ¬ OperatorKO7.Methods.UnarySignatureInapplicability.UnarySignature
          OperatorKO7.Methods.UnarySignatureInapplicability.ko7FunArity
  | .stringRewritingUnaryKill =>
      ¬ OperatorKO7.Methods.UnarySignatureInapplicability.UnarySignature
          OperatorKO7.Methods.UnarySignatureInapplicability.ko7FunArity
  | .sizeChangeMethod M => SizeChangeCertifies M

/-- Each actual method interpretation supplies its row's stated theorem. -/
theorem rowClaim_of_interpretation {f : RDRSMethodFamily}
    (i : MethodInterpretation f) : RowClaim f (u6ClassOf f) := by
  cases i with
  | rationalAffine _ => exact linearPolyQ_row_anchor
  | realAffine _ => exact linearPolyR_row_anchor
  | naturalMatrix _ => exact naturalMatrix_exact_row
  | triangularMatrix _ => exact triangularMatrix_exact_row
  | kboVariableConditionOrder _ =>
      exact standardKBO_no_ko7_rec_succ
  | subtermCoefficientKBOOrder _ =>
      exact OperatorKO7.KBOSubtermCoefficient.subtermCoefficientKBO_no_ko7_rec_succ
  | cichonSlowGrowingMethod _ =>
      exact cichonSlowGrowing_certifies
  | dpSubtermProjectionRow =>
      exact ko7_dpSubtermCriterion_row_anchor
  | dpArgumentFilteringMethod _ =>
      exact argumentFiltering_certifies
  | dpNeutralProcessorMethod _ =>
      exact neutralDPProcessor_certifies
  | usableRulesConcreteRow _ =>
      exact ko7_usableRules_rootClosure_minimality_anchor
  | sharingMethod _ =>
      exact sharing_certifies
  | equationalQuotientMethod _ =>
      exact equationalQuotient_certifies
  | cycleRewritingUnaryKill =>
      exact OperatorKO7.Methods.UnarySignatureInapplicability.cycleRewriting_inapplicable
  | stringRewritingUnaryKill =>
      exact OperatorKO7.Methods.UnarySignatureInapplicability.stringRewriting_inapplicable
  | sizeChangeMethod _ =>
      exact sizeChange_certifies

/-- Specialize the exact row claim to the interpretation's concrete carrier.
This is the carrier bridge: the instantiated conclusion is derived from the
same `RowClaim` proof recorded by the theorem-backed disposition. -/
theorem anchorInstance_of_rowClaim {f : RDRSMethodFamily}
    (i : MethodInterpretation f) (h : RowClaim f (u6ClassOf f)) :
    AnchorInstanceHolds i := by
  cases i with
  | rationalAffine M => exact h freeSchema M
  | realAffine M => exact h freeSchema M
  | naturalMatrix M => exact h freeSchema _ M
  | triangularMatrix M => exact h freeSchema _ M
  | kboVariableConditionOrder K =>
      exact h K
  | subtermCoefficientKBOOrder K =>
      exact h K
  | cichonSlowGrowingMethod M =>
      exact h M
  | dpSubtermProjectionRow =>
      exact h
  | dpArgumentFilteringMethod M =>
      exact h M
  | dpNeutralProcessorMethod M =>
      exact h M
  | usableRulesConcreteRow pair =>
      exact ⟨h, h.retainedProjectionStrict pair⟩
  | sharingMethod M =>
      exact h M
  | equationalQuotientMethod M =>
      exact h M
  | cycleRewritingUnaryKill =>
      exact h
  | stringRewritingUnaryKill =>
      exact h
  | sizeChangeMethod M =>
      exact h M

/-- **Adapter law, carrier side.** Every interpretation's carrier carries the
specialization of its exact row claim. No generic variable-condition relation
is relabeled as the standard-KBO carrier. -/
theorem anchorInstance_holds {f : RDRSMethodFamily} (i : MethodInterpretation f) :
    AnchorInstanceHolds i :=
  anchorInstance_of_rowClaim i (rowClaim_of_interpretation i)

/-! ## 4. Theorem-backed evidence -/

/-- Theorem-backed evidence is constructor-closed: it is definitionally a
`MethodInterpretation`, so clients cannot assemble an interpretation, carrier
claim, and row claim independently with a public structure constructor. -/
def TheoremBackedEvidence (f : RDRSMethodFamily) : Type := MethodInterpretation f

namespace TheoremBackedEvidence

/-- Recover the concrete interpretation. -/
def interpretation {f : RDRSMethodFamily} (e : TheoremBackedEvidence f) :
    MethodInterpretation f := e

/-- The carrier instance is always derived through the carrier bridge. -/
theorem anchorInstance {f : RDRSMethodFamily} (e : TheoremBackedEvidence f) :
    AnchorInstanceHolds e :=
  anchorInstance_holds e

/-- The exact reduced row claim is always derived from the interpretation. -/
theorem rowClaim {f : RDRSMethodFamily} (e : TheoremBackedEvidence f) :
    RowClaim f (u6ClassOf f) :=
  rowClaim_of_interpretation e

end TheoremBackedEvidence

/-- Canonical constructor for theorem-backed evidence. Evidence contains only
the interpretation; both adapter laws are derived functions. -/
def theoremBackedEvidenceOf {f : RDRSMethodFamily} (i : MethodInterpretation f) :
    TheoremBackedEvidence f := i

/-! ### Canonical theorem-backed interpretations -/

def rationalAffineInterpretation : MethodInterpretation RDRSMethodFamily.linearPolyQ :=
  .rationalAffine unitRationalAffine

def realAffineInterpretation : MethodInterpretation RDRSMethodFamily.linearPolyR :=
  .realAffine unitRealAffine

def naturalMatrixInterpretation :
    MethodInterpretation RDRSMethodFamily.matrixNScalarProjection :=
  .naturalMatrix (sizeNaturalMatrixMethod 2)

def triangularMatrixInterpretation :
    MethodInterpretation RDRSMethodFamily.triangularMatrix :=
  .triangularMatrix (sizeTriangularMatrixMethod 2)

/-- The canonical finite standard-KBO interpretation used by the ledger. Its
strict-weight and precedence arms are both inhabited above. -/
def standardKBOInterpretation : MethodInterpretation RDRSMethodFamily.standardKBO :=
  MethodInterpretation.kboVariableConditionOrder finiteStandardKBO

/-- The canonical subterm-coefficient KBO interpretation used by the ledger. Its
coefficients are not all one, and both its strict-weight and precedence arms are
inhabited in `Meta/KBO_SubtermCoefficient.lean`. -/
def subtermCoefficientKBOInterpretation :
    MethodInterpretation RDRSMethodFamily.subtermCoefficientKBO :=
  MethodInterpretation.subtermCoefficientKBOOrder
    OperatorKO7.KBOSubtermCoefficient.finiteSubtermCoefficientKBO

/-- Canonical Cichon guarded-contextual interpretation. -/
def cichonSlowGrowingInterpretation :
    MethodInterpretation RDRSMethodFamily.cichonSlowGrowing :=
  MethodInterpretation.cichonSlowGrowingMethod .guardedContextual

/-- Canonical counter-only argument-filtering interpretation. -/
def dpArgumentFilteringInterpretation :
    MethodInterpretation RDRSMethodFamily.dpArgumentFiltering :=
  MethodInterpretation.dpArgumentFilteringMethod .counterOnly

/-- Canonical neutral identity DP-processor interpretation. -/
def dpNeutralProcessorInterpretation :
    MethodInterpretation RDRSMethodFamily.dpNeutralProcessors :=
  MethodInterpretation.dpNeutralProcessorMethod .identity

/-- Canonical finite usable-rule root-closure interpretation. -/
def usableRulesInterpretation :
    MethodInterpretation RDRSMethodFamily.usableRulesMinimality :=
  MethodInterpretation.usableRulesConcreteRow
    (DPPair.rec_succ Trace.void Trace.void Trace.void)

/-- Canonical explicit sharing interpretation. -/
def sharingInterpretation :
    MethodInterpretation RDRSMethodFamily.sharingNonConservativity :=
  MethodInterpretation.sharingMethod .explicitSharedNode

/-- Canonical merge-commutativity quotient interpretation. -/
def equationalQuotientInterpretation :
    MethodInterpretation RDRSMethodFamily.equationalQuotientNonConservativity :=
  MethodInterpretation.equationalQuotientMethod .mergeCommutativity

/-- Canonical unary-signature kill for cycle rewriting. -/
def cycleRewritingInterpretation :
    MethodInterpretation RDRSMethodFamily.cycleRewritingInapplicability :=
  MethodInterpretation.cycleRewritingUnaryKill

/-- Canonical unary-signature kill for string rewriting. -/
def stringRewritingInterpretation :
    MethodInterpretation RDRSMethodFamily.stringRewritingInapplicability :=
  MethodInterpretation.stringRewritingUnaryKill

/-- Canonical single-call size-change interpretation. -/
def sizeChangeInterpretation :
    MethodInterpretation RDRSMethodFamily.sizeChangeTerminationEscape :=
  MethodInterpretation.sizeChangeMethod .schemaSingleCall

/-! ## 5. Curated dispositions -/

/-- Why a row is curated instead of theorem-backed. This is an indexed reason,
not a free-text note. -/
inductive CuratedReason
  /-- The row's cited anchor is a layer-closure capstone with no transport from
  a concrete carrier to this row's semantic claim. -/
  | noTransportAdapter
  /-- The row sits outside the direct payload-sensitive lane by definition
  (admittance criteria, inapplicability markers, relabeling routes). -/
  | externalNonLane
  /-- The row escapes by changing substrate: the certificate lives on a
  transformed system with its own carrier, not on the source RDRS. -/
  | substrateChange
  /-- The row's outcome depends on an imported order or processor pairing that
  the ledger does not fix. -/
  | importDependent
  deriving DecidableEq, Repr

/-- Curated reason per row, with `none` exactly on the theorem-backed rows.
This single function is the source of the theorem-backed/curated split, so the
two buckets cannot drift apart. -/
def curatedReason? : RDRSMethodFamily → Option CuratedReason
  -- Theorem-backed rows carry no curated reason.
  | .standardKBO                      => none
  | .subtermCoefficientKBO            => none
  | .dpSubtermCriterion               => none
  | .usableRulesMinimality            => none
  | .cichonSlowGrowing                => none
  | .dpArgumentFiltering              => none
  | .dpNeutralProcessors              => none
  | .sharingNonConservativity         => none
  | .equationalQuotientNonConservativity => none
  | .cycleRewritingInapplicability    => none
  | .stringRewritingInapplicability   => none
  | .sizeChangeTerminationEscape      => none
  -- KBO family beyond the adapted rows
  | .kboWithStatus                    => some .noTransportAdapter
  | .generalizedKBO                   => some .noTransportAdapter
  | .acKBO                            => some .noTransportAdapter
  | .transfiniteKBO                   => some .noTransportAdapter
  | .lambdaFreeKBO                    => some .noTransportAdapter
  -- Path-order constructions
  | .acRPO                            => some .noTransportAdapter
  | .rpoModuloPermutation             => some .noTransportAdapter
  | .popStarFamily                    => some .noTransportAdapter
  | .simpleTerminationOrderType       => some .noTransportAdapter
  -- Algebraic interpretations
  | .linearPolyQ                      => none
  | .linearPolyR                      => none
  | .negativeCoefficientPolynomial    => some .noTransportAdapter
  | .maxPolynomial                    => some .noTransportAdapter
  | .nonlinearHigherDegreePolynomial  => some .noTransportAdapter
  | .multilinearInterpretation        => some .noTransportAdapter
  | .matrixNScalarProjection          => none
  | .matrixQRScalarProjection         => some .noTransportAdapter
  | .arcticScalarProjection           => some .noTransportAdapter
  | .tropicalScalarProjection         => some .noTransportAdapter
  | .triangularMatrix                 => none
  | .tupleInterpretationStrictS       => some .noTransportAdapter
  | .higherOrderTupleInterpretation   => some .noTransportAdapter
  | .polynomialKBO                    => some .noTransportAdapter
  -- Semantic and structural
  | .strictMonotoneAlgebraArchimedean => some .noTransportAdapter
  | .extendedMonotoneAlgebra          => some .noTransportAdapter
  | .finiteModelTermination           => some .noTransportAdapter
  | .matchBounds                      => some .noTransportAdapter
  | .raiseConsistencyMatchBounds      => some .noTransportAdapter
  | .semanticLabeling                 => some .externalNonLane
  | .predictiveLabeling               => some .externalNonLane
  | .rootLabeling                     => some .externalNonLane
  | .selfLabelingEquational           => some .externalNonLane
  | .categoricalToposTermination      => some .externalNonLane
  | .forwardClosures                  => some .externalNonLane
  | .quasiDecreasingness              => some .externalNonLane
  -- DP processors
  | .dpProcessorClassification        => some .noTransportAdapter
  | .dpReductionPairProcessor         => some .importDependent
  | .orderSortedDP                    => some .noTransportAdapter
  | .contextSensitiveDP               => some .noTransportAdapter
  | .twoDDPForCTRS                    => some .noTransportAdapter
  | .dpReductionTriples               => some .importDependent
  | .formativeRules                   => some .externalNonLane
  -- Typed and transformed substrates
  | .typeIntroduction                 => some .substrateChange
  | .manySortedPersistence            => some .substrateChange
  | .operationalTerminationCTRS       => some .externalNonLane
  | .integerTermRewriting             => some .substrateChange
  | .lctrs                            => some .substrateChange
  | .higherOrderLCTRS                 => some .substrateChange
  -- Higher-order and type-system admittance
  | .horpoAdmittance                  => some .externalNonLane
  | .cpoAdmittance                    => some .externalNonLane
  | .generalSchemaAdmittance          => some .externalNonLane
  | .sizedTypesAdmittance             => some .externalNonLane
  | .coqGuardAdmittance               => some .externalNonLane
  -- Typing barriers
  | .bellantoniCookSplit              => some .noTransportAdapter
  | .linearLogicTypingBarrier         => some .noTransportAdapter
  | .ramifiedRecursionTypingBarrier   => some .noTransportAdapter
  -- Sharing, type graphs, equational quotients
  | .weightedTypeGraphEscape          => some .substrateChange
  | .generalizedWeightedTypeGraphs    => some .substrateChange
  -- Inapplicability markers remaining after the unary-signature promotions
  | .infinitaryRewritingTermination   => some .externalNonLane
  | .abstractInterpretationAdmittance => some .externalNonLane
  -- Remaining conditional and translated rows
  | .leftLinearMatchBounds            => some .noTransportAdapter
  | .piCalculusTerminationTranslation => some .substrateChange
  | .lambdaMuSNViaCPS                 => some .substrateChange
  | .quasiInterpretationsSharingAware => some .substrateChange

/-- A curated row makes no semantic claim. Assigning a status tag does not
inhabit `RowClaim`; on curated rows the claim reduces to `False`. -/
theorem curated_row_has_no_semantic_claim (f : RDRSMethodFamily)
    (h : (curatedReason? f).isSome = true) : ¬ RowClaim f (u6ClassOf f) := by
  intro hc
  cases f <;> first
    | exact hc
    | exact absurd h (by decide)

/-- A curated row has no inhabitant in the closed interpretation family. This is a typed
NO-TRANSPORT certificate for this evidence interface, not a claim that no implementation of the
named method can ever be constructed. -/
theorem curated_methodInterpretation_isEmpty (f : RDRSMethodFamily)
    (h : (curatedReason? f).isSome = true) : IsEmpty (MethodInterpretation f) := by
  refine ⟨?_⟩
  intro i
  cases i <;> simp [curatedReason?] at h

/-- Curated status for a row, defined separately from theorem-backed evidence.
It records the indexed reason, the proved absence of any semantic claim, and
that the row still has a definite six-way classification. -/
structure CuratedDisposition (f : RDRSMethodFamily) (r : CuratedReason) : Prop where
  reasonAssigned  : curatedReason? f = some r
  noSemanticClaim : ¬ RowClaim f (u6ClassOf f)
  noInterpretation : IsEmpty (MethodInterpretation f)
  definiteClass   : u6ClassOf f ≠ U6Classification.temporaryUnclassified

/-- Every row with a curated reason has a curated disposition for that reason. -/
theorem curatedDisposition_of_reason (f : RDRSMethodFamily) (r : CuratedReason)
    (h : curatedReason? f = some r) : CuratedDisposition f r where
  reasonAssigned  := h
  noSemanticClaim := curated_row_has_no_semantic_claim f (by rw [h]; rfl)
  noInterpretation := curated_methodInterpretation_isEmpty f (by rw [h]; rfl)
  definiteClass   := by cases f <;> decide

/-! ## 6. The total row disposition -/

/-- Each of the 76 rows is either theorem-backed or curated with an indexed
reason. There is no third bucket and no unclassified residue. -/
inductive RowDisposition : RDRSMethodFamily → Type
  | theoremBacked {f : RDRSMethodFamily} (e : TheoremBackedEvidence f) : RowDisposition f
  | curated {f : RDRSMethodFamily} (r : CuratedReason) (d : CuratedDisposition f r) :
      RowDisposition f

/-- Marker reading a disposition's bucket. -/
def RowDisposition.isTheoremBacked {f : RDRSMethodFamily} : RowDisposition f → Bool
  | .theoremBacked _ => true
  | .curated _ _ => false

/-- **Total disposition.** Every one of the 76 enum values is assigned. The
sixteen adapted rows get theorem-backed evidence built by the adapter laws; the
other 60 get their indexed curated reason, with the reason assignment
discharged by `rfl` against `curatedReason?` on every row. The arms are written
out rather than routed through a catch-all, so no impossible branch has to be
manufactured for a row that is in fact theorem-backed. -/
def rowDisposition : (f : RDRSMethodFamily) → RowDisposition f
  -- Theorem-backed rows.
  | .linearPolyQ => .theoremBacked (theoremBackedEvidenceOf rationalAffineInterpretation)
  | .linearPolyR => .theoremBacked (theoremBackedEvidenceOf realAffineInterpretation)
  | .matrixNScalarProjection => .theoremBacked (theoremBackedEvidenceOf naturalMatrixInterpretation)
  | .triangularMatrix => .theoremBacked (theoremBackedEvidenceOf triangularMatrixInterpretation)
  | .standardKBO =>
      .theoremBacked (theoremBackedEvidenceOf standardKBOInterpretation)
  | .subtermCoefficientKBO =>
      .theoremBacked (theoremBackedEvidenceOf subtermCoefficientKBOInterpretation)
  | .cichonSlowGrowing =>
      .theoremBacked (theoremBackedEvidenceOf cichonSlowGrowingInterpretation)
  | .dpSubtermCriterion =>
      .theoremBacked (theoremBackedEvidenceOf MethodInterpretation.dpSubtermProjectionRow)
  | .dpArgumentFiltering =>
      .theoremBacked (theoremBackedEvidenceOf dpArgumentFilteringInterpretation)
  | .dpNeutralProcessors =>
      .theoremBacked (theoremBackedEvidenceOf dpNeutralProcessorInterpretation)
  | .usableRulesMinimality =>
      .theoremBacked (theoremBackedEvidenceOf usableRulesInterpretation)
  | .sharingNonConservativity =>
      .theoremBacked (theoremBackedEvidenceOf sharingInterpretation)
  | .equationalQuotientNonConservativity =>
      .theoremBacked (theoremBackedEvidenceOf equationalQuotientInterpretation)
  | .cycleRewritingInapplicability =>
      .theoremBacked (theoremBackedEvidenceOf cycleRewritingInterpretation)
  | .stringRewritingInapplicability =>
      .theoremBacked (theoremBackedEvidenceOf stringRewritingInterpretation)
  | .sizeChangeTerminationEscape =>
      .theoremBacked (theoremBackedEvidenceOf sizeChangeInterpretation)
  -- Curated: no transport adapter from the cited capstone to this row.
  | .kboWithStatus | .generalizedKBO | .acKBO | .transfiniteKBO | .lambdaFreeKBO
  | .acRPO | .rpoModuloPermutation | .popStarFamily
  | .simpleTerminationOrderType
  | .negativeCoefficientPolynomial | .maxPolynomial | .nonlinearHigherDegreePolynomial
  | .multilinearInterpretation | .matrixQRScalarProjection
  | .arcticScalarProjection | .tropicalScalarProjection
  | .tupleInterpretationStrictS | .higherOrderTupleInterpretation | .polynomialKBO
  | .strictMonotoneAlgebraArchimedean | .extendedMonotoneAlgebra
  | .finiteModelTermination | .matchBounds | .raiseConsistencyMatchBounds
  | .dpProcessorClassification | .orderSortedDP
  | .contextSensitiveDP | .twoDDPForCTRS | .bellantoniCookSplit
  | .linearLogicTypingBarrier | .ramifiedRecursionTypingBarrier
  | .leftLinearMatchBounds =>
      .curated CuratedReason.noTransportAdapter
        (curatedDisposition_of_reason _ CuratedReason.noTransportAdapter rfl)
  -- Curated: outside the direct payload-sensitive lane by definition.
  | .semanticLabeling | .predictiveLabeling | .rootLabeling | .selfLabelingEquational
  | .categoricalToposTermination | .forwardClosures | .quasiDecreasingness
  | .formativeRules | .operationalTerminationCTRS
  | .horpoAdmittance | .cpoAdmittance | .generalSchemaAdmittance
  | .sizedTypesAdmittance | .coqGuardAdmittance
  | .infinitaryRewritingTermination
  | .abstractInterpretationAdmittance =>
      .curated CuratedReason.externalNonLane
        (curatedDisposition_of_reason _ CuratedReason.externalNonLane rfl)
  -- Curated: certificate lives on a changed substrate.
  | .typeIntroduction | .manySortedPersistence | .integerTermRewriting | .lctrs
  | .higherOrderLCTRS | .weightedTypeGraphEscape
  | .generalizedWeightedTypeGraphs
  | .piCalculusTerminationTranslation | .lambdaMuSNViaCPS
  | .quasiInterpretationsSharingAware =>
      .curated CuratedReason.substrateChange
        (curatedDisposition_of_reason _ CuratedReason.substrateChange rfl)
  -- Curated: outcome depends on an imported order or pairing.
  | .dpReductionPairProcessor | .dpReductionTriples =>
      .curated CuratedReason.importDependent
        (curatedDisposition_of_reason _ CuratedReason.importDependent rfl)

/-- Every ledger row is resolved at the interpretation boundary: it either carries an actual
closed interpretation or a proof that no inhabitant exists in the current indexed interface. -/
inductive InterpretationResolution (f : RDRSMethodFamily) : Type
  | interpreted (i : MethodInterpretation f) : InterpretationResolution f
  | noTransport (h : IsEmpty (MethodInterpretation f)) : InterpretationResolution f

/-- Total proof-bearing interpretation resolution for all 76 rows. -/
def interpretationResolution (f : RDRSMethodFamily) : InterpretationResolution f :=
  match rowDisposition f with
  | .theoremBacked e => .interpreted e
  | .curated _ d => .noTransport d.noInterpretation

theorem interpretationResolution_total (f : RDRSMethodFamily) :
    Nonempty (InterpretationResolution f) :=
  ⟨interpretationResolution f⟩

/-! ## 7. Disposition-derived lists, split, and exact counts -/

/-- Rows carrying theorem-backed evidence, computed directly from the total
`RowDisposition`. -/
def theoremBackedRows : List RDRSMethodFamily :=
  allMethodFamilies.filter (fun f => (rowDisposition f).isTheoremBacked)

/-- Curated rows, computed as the complementary disposition filter. -/
def curatedRows : List RDRSMethodFamily :=
  allMethodFamilies.filter (fun f => !(rowDisposition f).isTheoremBacked)

theorem theoremBackedRows_mem_iff (f : RDRSMethodFamily) :
    f ∈ theoremBackedRows ↔ (curatedReason? f).isNone = true := by
  cases f <;> decide

theorem curatedRows_mem_iff (f : RDRSMethodFamily) :
    f ∈ curatedRows ↔ (curatedReason? f).isSome = true := by
  cases f <;> decide

/-- Every curated row is absent from the closed interpretation family. -/
theorem curated_rows_have_no_interpretation (f : RDRSMethodFamily)
    (h : f ∈ curatedRows) : IsEmpty (MethodInterpretation f) :=
  curated_methodInterpretation_isEmpty f ((curatedRows_mem_iff f).mp h)

theorem theoremBackedRows_nodup : theoremBackedRows.Nodup := by decide

theorem curatedRows_nodup : curatedRows.Nodup := by decide

/-- The two buckets are disjoint. -/
theorem buckets_disjoint (f : RDRSMethodFamily) :
    ¬ (f ∈ theoremBackedRows ∧ f ∈ curatedRows) := by
  cases f <;> decide

/-- The two buckets are complete: every row lands in one of them. -/
theorem buckets_complete (f : RDRSMethodFamily) :
    f ∈ theoremBackedRows ∨ f ∈ curatedRows := by
  cases f <;> decide

theorem theoremBackedRows_count : theoremBackedRows.length = 16 := by decide

theorem curatedRows_count : curatedRows.length = 60 := by decide

/-- The split accounts for all 76 rows. -/
theorem split_total : theoremBackedRows.length + curatedRows.length = 76 := by decide

/-- **Non-vacuity of the split.** The theorem-backed bucket is not empty. Zero
theorem-backed rows would be a failed semantic repair, not a successful one. -/
theorem theoremBackedRows_nonempty : theoremBackedRows.length > 0 := by decide

/-- The theorem-backed bucket is exactly the sixteen named rows with concrete
carrier-closed evidence. -/
theorem theoremBackedRows_eq :
    theoremBackedRows =
      [RDRSMethodFamily.standardKBO,
        RDRSMethodFamily.subtermCoefficientKBO,
        RDRSMethodFamily.cichonSlowGrowing,
        RDRSMethodFamily.linearPolyQ,
        RDRSMethodFamily.linearPolyR,
        RDRSMethodFamily.matrixNScalarProjection,
        RDRSMethodFamily.triangularMatrix,
        RDRSMethodFamily.dpSubtermCriterion,
        RDRSMethodFamily.dpArgumentFiltering,
        RDRSMethodFamily.dpNeutralProcessors,
        RDRSMethodFamily.usableRulesMinimality,
        RDRSMethodFamily.sharingNonConservativity,
        RDRSMethodFamily.equationalQuotientNonConservativity,
        RDRSMethodFamily.cycleRewritingInapplicability,
        RDRSMethodFamily.stringRewritingInapplicability,
        RDRSMethodFamily.sizeChangeTerminationEscape] := by decide

/-! ### Per-reason curated counts -/

/-- Curated rows carrying a given indexed reason. -/
def curatedRowsWithReason (r : CuratedReason) : List RDRSMethodFamily :=
  allMethodFamilies.filter (fun f => curatedReason? f == some r)

theorem curated_noTransportAdapter_count :
    (curatedRowsWithReason .noTransportAdapter).length = 32 := by decide

theorem curated_externalNonLane_count :
    (curatedRowsWithReason .externalNonLane).length = 16 := by decide

theorem curated_substrateChange_count :
    (curatedRowsWithReason .substrateChange).length = 10 := by decide

theorem curated_importDependent_count :
    (curatedRowsWithReason .importDependent).length = 2 := by decide

/-- The four indexed reasons partition the curated bucket. -/
theorem curated_reason_partition :
    (curatedRowsWithReason .noTransportAdapter).length
      + (curatedRowsWithReason .externalNonLane).length
      + (curatedRowsWithReason .substrateChange).length
      + (curatedRowsWithReason .importDependent).length = 60 := by decide

/-! ## 8. Disposition agrees with the derived lists -/

/-- The data-level disposition and the derived split cannot disagree. -/
theorem rowDisposition_matches_split (f : RDRSMethodFamily) :
    (rowDisposition f).isTheoremBacked = (curatedReason? f).isNone := by
  cases f <;> rfl

/-- The theorem-backed list is exactly the filter computed from the total
`RowDisposition`, not merely a parallel list with the same count. -/
theorem theoremBackedRows_eq_disposition_filter :
    theoremBackedRows =
      allMethodFamilies.filter (fun f => (rowDisposition f).isTheoremBacked) := by
  decide

/-- The curated list is exactly the complementary filter computed from the
total `RowDisposition`. -/
theorem curatedRows_eq_disposition_filter :
    curatedRows =
      allMethodFamilies.filter (fun f => !(rowDisposition f).isTheoremBacked) := by
  decide

/-- The canonical append of the two disjoint buckets is a permutation of the
complete 76-row universe. This strengthens pointwise completeness to an exact
finite-universe closure statement. -/
theorem buckets_append_perm_allMethodFamilies :
    List.Perm (theoremBackedRows ++ curatedRows) allMethodFamilies := by
  decide

/-- Extensional form of the same finite-universe closure. -/
theorem buckets_append_mem_iff (f : RDRSMethodFamily) :
    f ∈ theoremBackedRows ++ curatedRows ↔ f ∈ allMethodFamilies := by
  cases f <;> decide

/-- Zero theorem-backed rows lack an adapter: every row in the theorem-backed
bucket has a concrete interpretation whose adapter laws produced its evidence. -/
theorem theoremBacked_rows_have_interpretations (f : RDRSMethodFamily)
    (h : f ∈ theoremBackedRows) : Nonempty (MethodInterpretation f) := by
  simp only [theoremBackedRows_eq, List.mem_cons, List.not_mem_nil, or_false] at h
  obtain (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) := h
  · exact ⟨standardKBOInterpretation⟩
  · exact ⟨subtermCoefficientKBOInterpretation⟩
  · exact ⟨cichonSlowGrowingInterpretation⟩
  · exact ⟨rationalAffineInterpretation⟩
  · exact ⟨realAffineInterpretation⟩
  · exact ⟨naturalMatrixInterpretation⟩
  · exact ⟨triangularMatrixInterpretation⟩
  · exact ⟨MethodInterpretation.dpSubtermProjectionRow⟩
  · exact ⟨dpArgumentFilteringInterpretation⟩
  · exact ⟨dpNeutralProcessorInterpretation⟩
  · exact ⟨usableRulesInterpretation⟩
  · exact ⟨sharingInterpretation⟩
  · exact ⟨equationalQuotientInterpretation⟩
  · exact ⟨cycleRewritingInterpretation⟩
  · exact ⟨stringRewritingInterpretation⟩
  · exact ⟨sizeChangeInterpretation⟩

/-- Every theorem-backed row has constructor-closed evidence, not merely an
unconnected carrier. -/
theorem theoremBacked_rows_have_evidence (f : RDRSMethodFamily)
    (h : f ∈ theoremBackedRows) : Nonempty (TheoremBackedEvidence f) := by
  obtain ⟨i⟩ := theoremBacked_rows_have_interpretations f h
  exact ⟨theoremBackedEvidenceOf i⟩

/-- Every theorem-backed row really inhabits its reduced semantic claim. -/
theorem theoremBacked_rows_inhabit_rowClaim (f : RDRSMethodFamily)
    (h : f ∈ theoremBackedRows) : RowClaim f (u6ClassOf f) := by
  obtain ⟨e⟩ := theoremBacked_rows_have_evidence f h
  exact e.rowClaim

/-! ## 9. Capstone -/

/-- Closure certificate for the WP-5 evidence ledger. -/
structure CoverageEvidenceLedgerClosed : Prop where
  /-- Every row has a disposition, and it agrees with the derived split. -/
  dispositionTotal :
    ∀ f : RDRSMethodFamily,
      (rowDisposition f).isTheoremBacked = (curatedReason? f).isNone
  /-- The theorem-backed bucket is the exact disposition-derived filter. -/
  theoremBackedFilterExact :
    theoremBackedRows =
      allMethodFamilies.filter (fun f => (rowDisposition f).isTheoremBacked)
  /-- The curated bucket is the exact complementary disposition-derived filter. -/
  curatedFilterExact :
    curatedRows =
      allMethodFamilies.filter (fun f => !(rowDisposition f).isTheoremBacked)
  /-- The two buckets are disjoint. -/
  disjoint : ∀ f : RDRSMethodFamily, ¬ (f ∈ theoremBackedRows ∧ f ∈ curatedRows)
  /-- The two buckets are complete. -/
  complete : ∀ f : RDRSMethodFamily, f ∈ theoremBackedRows ∨ f ∈ curatedRows
  /-- The two buckets enumerate the full universe exactly, up to order. -/
  bucketPermutation : List.Perm (theoremBackedRows ++ curatedRows) allMethodFamilies
  /-- Exact theorem-backed count. -/
  theoremBackedCount : theoremBackedRows.length = 16
  /-- Exact curated count. -/
  curatedCount : curatedRows.length = 60
  /-- Exactly 76 rows. -/
  totalRows : theoremBackedRows.length + curatedRows.length = 76
  /-- The theorem-backed bucket is non-empty. -/
  theoremBackedNonempty : theoremBackedRows.length > 0
  /-- No theorem-backed row lacks constructor-closed evidence. -/
  everyTheoremBackedRowHasAdapter :
    ∀ f : RDRSMethodFamily, f ∈ theoremBackedRows → Nonempty (TheoremBackedEvidence f)
  /-- Every theorem-backed row inhabits its exact reduced claim. -/
  everyTheoremBackedRowInhabitsClaim :
    ∀ f : RDRSMethodFamily, f ∈ theoremBackedRows → RowClaim f (u6ClassOf f)
  /-- Every curated row is excluded from the closed interpretation family. -/
  everyCuratedRowHasNoInterpretation :
    ∀ f : RDRSMethodFamily, f ∈ curatedRows → IsEmpty (MethodInterpretation f)
  /-- Every row has a proof-bearing interpretation/no-transport resolution. -/
  everyRowHasResolution :
    ∀ f : RDRSMethodFamily, Nonempty (InterpretationResolution f)
  /-- No curated row inhabits a semantic claim. -/
  noCuratedRowClaimsSemantics :
    ∀ f : RDRSMethodFamily,
      (curatedReason? f).isSome = true → ¬ RowClaim f (u6ClassOf f)
  /-- Zero rows remain unclassified in the underlying status ledger. -/
  zeroUnclassified : temporaryUnclassifiedFamilies.length = 0

/-- **WP-5 evidence-ledger closeout.** The 76-row RDRS coverage ledger now
carries a semantic layer: sixteen rows are theorem-backed by concrete
carrier-closed interpretations and method certificates, the remaining
60 are curated with indexed reasons and provably claim nothing, the split is
exact and complete, and the theorem-backed subset is inhabited. -/
theorem rdrs_coverage_evidence_ledger_closed : CoverageEvidenceLedgerClosed where
  dispositionTotal := rowDisposition_matches_split
  theoremBackedFilterExact := theoremBackedRows_eq_disposition_filter
  curatedFilterExact := curatedRows_eq_disposition_filter
  disjoint := buckets_disjoint
  complete := buckets_complete
  bucketPermutation := buckets_append_perm_allMethodFamilies
  theoremBackedCount := theoremBackedRows_count
  curatedCount := curatedRows_count
  totalRows := split_total
  theoremBackedNonempty := theoremBackedRows_nonempty
  everyTheoremBackedRowHasAdapter := theoremBacked_rows_have_evidence
  everyTheoremBackedRowInhabitsClaim := theoremBacked_rows_inhabit_rowClaim
  everyCuratedRowHasNoInterpretation := curated_rows_have_no_interpretation
  everyRowHasResolution := interpretationResolution_total
  noCuratedRowClaimsSemantics := curated_row_has_no_semantic_claim
  zeroUnclassified := temporary_unclassified_count

/-! ## 10. Dispatch ORIENTATION: full native-semantic closure -/

namespace Native

open OperatorKO7.Methods.OrientationClosure.NativeSemanticCoverage

/-- Full 76-row indexed interpretation family. Historical theorem-backed rows
retain their original closed `MethodInterpretation`; ORIENTATION rows carry the
new closed `MissingNativeInterpretation`. -/
inductive NativeMethodInterpretation : RDRSMethodFamily → Type 2
  | legacy {f : RDRSMethodFamily} (i : MethodInterpretation f) : NativeMethodInterpretation f
  | orientation {f : RDRSMethodFamily} (i : MissingNativeInterpretation f) :
      NativeMethodInterpretation f

/-- A curated historical row is exactly one of the rows with a new native
ORIENTATION interpretation object. -/
theorem curated_row_has_missingNativeInterpretation
    (f : RDRSMethodFamily) (h : (curatedReason? f).isSome = true) :
    (missingNativeInterpretation f).isSome = true := by
  cases f <;> simp [curatedReason?, missingNativeInterpretation] at h ⊢

/-- Canonical interpretation object for every row. This definition returns
method data, not a proof-only resolution tag. -/
noncomputable def nativeMethodInterpretation (f : RDRSMethodFamily) :
    NativeMethodInterpretation f :=
  match hrow : rowDisposition f with
  | .theoremBacked e => .legacy e
  | .curated r d =>
      match hi : missingNativeInterpretation f with
      | some i => .orientation i
      | none => False.elim (by
          have hs : (curatedReason? f).isSome = true := by
            rw [d.reasonAssigned]
            rfl
          have hn := curated_row_has_missingNativeInterpretation f hs
          simp [hi] at hn)

/-- Every row has an actual indexed interpretation object. -/
theorem every_row_has_native_interpretation (f : RDRSMethodFamily) :
    Nonempty (NativeMethodInterpretation f) :=
  ⟨nativeMethodInterpretation f⟩

/-- Full method-native proposition for every RDRS row. The complementary
sixty are selected by the new proof-bearing `Option`; its `none` complement is
exactly the historical sixteen-row adapter surface. -/
def NativeRowClaim (f : RDRSMethodFamily) : Prop :=
  match missingNativeEvidence f with
  | some _ => MissingNativeRowClaim f
  | none => RowClaim f (u6ClassOf f)

/-- The sixteen-row `none` complement is exactly the historical theorem-backed
adapter list. -/
theorem legacyNativeRows_eq_theoremBackedRows :
    legacyNativeRows = theoremBackedRows := by decide

/-- Every one of the seventy-six rows now has proof-bearing native semantics.
This does not erase the historical 16/60 adapter split above. -/
theorem nativeRowClaim_closed (f : RDRSMethodFamily) : NativeRowClaim f := by
  unfold NativeRowClaim
  cases h : missingNativeEvidence f with
  | some p => exact p.down
  | none =>
      have hf : f ∈ legacyNativeRows := by
        simp [legacyNativeRows, h, allMethodFamilies_complete]
      rw [legacyNativeRows_eq_theoremBackedRows] at hf
      exact theoremBacked_rows_inhabit_rowClaim f hf

/-- Native evidence is the exact row proposition itself, after dispatching to
the legacy adapter or the new method-native complement. -/
def NativeMethodEvidence (f : RDRSMethodFamily) : Type := PLift (NativeRowClaim f)

/-- Constructor-closed native evidence for every row. -/
def nativeMethodEvidence (f : RDRSMethodFamily) : NativeMethodEvidence f :=
  ⟨nativeRowClaim_closed f⟩

/-- The full native-semantic bucket is exactly the closed 76-row universe. -/
def nativeTheoremBackedRows : List RDRSMethodFamily := allMethodFamilies

/-- No row remains curated at the method-native semantic layer. -/
def nativeCuratedRows : List RDRSMethodFamily := []

theorem nativeTheoremBackedRows_count : nativeTheoremBackedRows.length = 76 :=
  allMethodFamilies_length

theorem nativeCuratedRows_count : nativeCuratedRows.length = 0 := rfl

theorem native_split_total :
    nativeTheoremBackedRows.length + nativeCuratedRows.length = 76 := by
  rw [nativeTheoremBackedRows_count, nativeCuratedRows_count]

theorem every_native_row_has_evidence (f : RDRSMethodFamily) :
    Nonempty (NativeMethodEvidence f) :=
  ⟨nativeMethodEvidence f⟩

theorem native_rows_exactly_allMethodFamilies :
    nativeTheoremBackedRows = allMethodFamilies := rfl

/-- Full native-semantic closeout. The old 16/60 adapter remains available as
an audit surface, while the method-native layer has no semantic residue. -/
structure NativeCoverageEvidenceLedgerClosed : Prop where
  totalRows : nativeTheoremBackedRows.length = 76
  zeroNativeCurated : nativeCuratedRows.length = 0
  exactUniverse : nativeTheoremBackedRows = allMethodFamilies
  everyRowHasNativeInterpretation :
    ∀ f : RDRSMethodFamily, Nonempty (NativeMethodInterpretation f)
  everyRowHasNativeEvidence :
    ∀ f : RDRSMethodFamily, Nonempty (NativeMethodEvidence f)
  legacyAdapterSplitPreserved :
    theoremBackedRows.length = 16 ∧ curatedRows.length = 60
  complementaryWaveExact : missingNativeRows.length = 60
  researchPackages :
    OperatorKO7.Methods.OrientationClosure.ResearchPackages.OrientationResearchPackagesClosed

/-- Dispatch ORIENTATION semantic milestone, pending supervisor kernel
validation. -/
theorem rdrs_native_coverage_evidence_ledger_closed :
    NativeCoverageEvidenceLedgerClosed where
  totalRows := nativeTheoremBackedRows_count
  zeroNativeCurated := nativeCuratedRows_count
  exactUniverse := native_rows_exactly_allMethodFamilies
  everyRowHasNativeInterpretation := every_row_has_native_interpretation
  everyRowHasNativeEvidence := every_native_row_has_evidence
  legacyAdapterSplitPreserved := ⟨theoremBackedRows_count, curatedRows_count⟩
  complementaryWaveExact := missingNativeRows_count
  researchPackages :=
    OperatorKO7.Methods.OrientationClosure.ResearchPackages.orientation_research_packages_closed

end Native

/-- Audit anchor String for the historical WP-5 16/60 adapter ledger. -/
def rdrs_coverage_evidence_ledger_anchor : String :=
  "OperatorKO7.RDRSCoverageLedger.Evidence.rdrs_coverage_evidence_ledger_closed"

/-- Audit anchor String for the Dispatch ORIENTATION 76/0 native-semantic
ledger. -/
def rdrs_native_coverage_evidence_ledger_anchor : String :=
  "OperatorKO7.RDRSCoverageLedger.Evidence.Native.rdrs_native_coverage_evidence_ledger_closed"

end OperatorKO7.RDRSCoverageLedger.Evidence
