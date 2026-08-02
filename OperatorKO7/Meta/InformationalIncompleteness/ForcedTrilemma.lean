import OperatorKO7.Meta.BoundaryOperator.TypedRefusalCompleteness
import OperatorKO7.Meta.InformationalIncompleteness.RecursorPayloadErasure
import OperatorKO7.Meta.OperationalInexpressibility.DirectGrammarBoundary

/-!
# Forced Output Trilemma Carrier (ENG-WCC sub-block 12, Brief A-073)

Carrier module for the forced-output trilemma anchor cited by the engine's
witness-carrier certificate. NO new mathematical content: this module is a
thin definitional carrier that names existing substrate so the engine can
emit one stable theorem reference per cert.

Substrate citations (already mechanized; no new proofs):
- `OperatorKO7.Meta.BoundaryOperator.TypedRefusalCompleteness.RefusalType`
  (the four-state finite refusal carrier Y / N / U / H);
- `OperatorKO7.Meta.BoundaryOperator.TypedRefusalCompleteness.refusalType_exhaustive`
  (every `RefusalType` is one of the four named constructors);
- `OperatorKO7.Meta.BoundaryOperator.TypedRefusalCompleteness.TypedRefusalCompleteness_engine_grade`
  (engine-grade four-class exhaustiveness statement).

The manuscript anchor is
`Rahnama_Informational_Incompleteness.tex` Theorem `thm:trilemma`
(forced-output trilemma under denied witness-language ascent).

Relation tag: NA (this module is a metadata / carrier module, not a
rewriting theorem).
Property: definition (a string-typed anchor record plus a structural
identity).
Trust: kernel-only (carriers cite existing theorems by name).
-/

namespace OperatorKO7.Meta.InformationalIncompleteness.ForcedTrilemma

open OperatorKO7.Meta.BoundaryOperator

/-- Forced-output-trilemma anchor record cited by the engine.
Every field is a string-typed name referring to an existing upstream
declaration. No mathematical content is introduced. -/
structure ForcedTrilemmaAnchor where
  /-- Upstream module that contains the finite refusal carrier and the
  exhaustiveness theorem. -/
  refusalCompletenessModule : String
  /-- Name of the engine-grade four-class exhaustiveness theorem. -/
  engineGradeTheoremName : String
  /-- Name of the carrier-side exhaustiveness theorem. -/
  carrierExhaustivenessTheoremName : String
  /-- Manuscript anchor identifier. -/
  manuscriptAnchor : String

/-- Canonical anchor for the engine to cite on every T3 / T4 emission. -/
def canonicalForcedTrilemmaAnchor : ForcedTrilemmaAnchor where
  refusalCompletenessModule :=
    "OperatorKO7.Meta.BoundaryOperator.TypedRefusalCompleteness"
  engineGradeTheoremName :=
    "OperatorKO7.Meta.BoundaryOperator.TypedRefusalCompleteness_engine_grade"
  carrierExhaustivenessTheoremName :=
    "OperatorKO7.Meta.BoundaryOperator.refusalType_exhaustive"
  manuscriptAnchor :=
    "Rahnama_Informational_Incompleteness.thm:trilemma"

/-- Carrier-side identity: the engine's ffl-trilemma sub-block names a
finite refusal carrier whose support is the full four-state surface
`{Y, N, U, H}`. This is a definitional rephrasing of
`refusalType_exhaustive`; it carries no new mathematical content. -/
theorem canonicalForcedTrilemmaAnchor_cites_four_states
    (r : RefusalType) :
    r = RefusalType.Y ∨ r = RefusalType.N
      ∨ r = RefusalType.U ∨ r = RefusalType.H :=
  refusalType_exhaustive r

/-- The canonical anchor names a non-empty manuscript reference.
Proved structurally: the manuscript-anchor string has positive length, so
it cannot equal the empty string. -/
theorem canonicalForcedTrilemmaAnchor_manuscriptAnchor_nonempty :
    canonicalForcedTrilemmaAnchor.manuscriptAnchor ≠ "" := by
  intro h
  have hlen : canonicalForcedTrilemmaAnchor.manuscriptAnchor.length = 0 := by
    rw [h]; rfl
  -- The canonical anchor's literal string has positive length, contradicting
  -- the assumed empty-string equality.
  have : canonicalForcedTrilemmaAnchor.manuscriptAnchor.length =
      "Rahnama_Informational_Incompleteness.thm:trilemma".length := by rfl
  rw [this] at hlen
  exact absurd hlen (by decide)

/-! ## Real theorems (anchor upgraded from anchor-only to anchor + theorem) -/

open OperatorKO7.RDRSDescentLens
open OperatorKO7.RDRSSemanticDirectMeasure
open OperatorKO7.RDRSSemanticPayloadSensitivity
open OperatorKO7.Meta.BoundaryGeneral.DirectMeasureGrammarClosure
open OperatorKO7.Meta.OperationalInexpressibility.DirectGrammarBoundary

/-- The three forced-output cases under denied witness-language ascent
(`thm:trilemma`): divergence, unsupported definite output, or typed abstention. -/
inductive ForcedOutputCase
  | divergence
  | unsupportedDefinite
  | typedAbstention
  deriving DecidableEq, Repr

/--
Proves: the forced-output trilemma is exhaustive: every forced-output case is one
  of divergence / unsupported-definite / typed-abstention.
Does not prove: that a given agent realizes a particular case (that is the
  empirical / per-agent question of `rem:prt-instance`).
Relation: typed-output enumeration; not a rewriting relation.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: every `ForcedOutputCase`.
-/
theorem forced_output_trilemma_exhaustive (c : ForcedOutputCase) :
    c = ForcedOutputCase.divergence ∨
      c = ForcedOutputCase.unsupportedDefinite ∨
        c = ForcedOutputCase.typedAbstention := by
  cases c <;> decide

/--
Proves: on the recursor the unsupported-definite case (II) has no decisive
  payload-sensitive support: no semantic measure is a decisive payload-sensitive
  descent. TOTAL over arbitrary semantic measures. So a forced definite verdict on
  the recursor cannot be internally certified by any direct payload-sensitive measure.
Does not prove: that the verdict is wrong; only that it is unsupported at the
  direct interface.
Relation: the canonical II recursor `iiRecursor` (root single-step orientation).
Closure: root single-step.
Strategy: not applicable.
Trust: kernel-only (re-export of the recursor no-decisive-payload-sensitive theorem).
Scope: every `SemanticMeasureData (Nat × Nat)`.
-/
theorem forced_output_trilemma_no_decisive_support
    (M : SemanticMeasureData (Nat × Nat)) :
    ¬ PayloadSensitiveDecisive RecursorPayloadErasure.iiRecursor M :=
  RecursorPayloadErasure.iiRecursor_no_decisive_payload_sensitive M

/--
Proves: no expression in the reflected direct grammar has decisive support on
  the fixed payload-duplicating carrier, where decisive support is exactly
  `UsesPayload e ∧ AdequateForDupOrientation e`.
Does not prove: transport from the payload-preserving `iiRecursor`; this is a
  separate relation-local theorem proved by the direct-grammar barrier.
Relation: the fixed counter-drop, payload-increasing relation encoded by
  `AdequateForDupOrientation` / `OrientsDupStep` (root single-step).
Closure: root single-step.
Strategy: not applicable.
Trust: kernel-only delegation to
  `no_directGrammar_measure_usesPayload_and_orients`.
Scope: every expression in the reflected direct-measure grammar.
-/
theorem forced_output_trilemma_no_decisive_support_fixedDuplicatingCarrier
    (e : MeasureExpr) :
    ¬ (UsesPayload e ∧ AdequateForDupOrientation e) :=
  no_directGrammar_measure_usesPayload_and_orients e

end OperatorKO7.Meta.InformationalIncompleteness.ForcedTrilemma
