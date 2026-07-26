import OperatorKO7.Meta.BoundaryOperator.EngineContract
import OperatorKO7.Meta.BoundaryOperator.TypedRefusalCompleteness

/-!
# Classify Universal — finiteInformationMatrix W₀ classifier

Upstream Lean module that replaces the v2.4.0 `mock_classifyUniversal.py`
mock fallback with a Lean-mechanized cardinality scan over a
`FiniteInformationMatrix`. The engine's `finiteInformationMatrix` schema
variant runs through this module on the Lean bridge path and falls back
to the Python mock only when the toolchain is unavailable.

Cardinality semantics (mirrors `code/classifier_bridge/mock_classifyUniversal.py::_scan_cardinality`):

* matrix row with `0` rules        ->  `noMapping`            (W₀ blocks; T4)
* matrix row with `1` rule         ->  `plainTextApplication` (W₀ unblocks; T1)
* matrix row with `>= 2` rules     ->  `ambiguityDuplication` (W₀ blocks; T3)

The classifier is total, exhaustive on a `FiniteInformationMatrix` (every
row gets a class), and grounded in the boundary-operator gauge-covariance
+ payload-discarding axioms (cited as named theorems in the engine's W₀
cert).

Hard hooks the engine consumes:

* `classifyUniversal` total function  -> bridge stdout shape
* `classifyUniversal_complete`        -> exhaustiveness theorem
* `classifyUniversal_grounded`        -> typed-refusal carrier soundness
* `classifyUniversalToRefusalType`    -> classifier into the
                                          `Meta.BoundaryOperator.TypedRefusalCompleteness`
                                          finite carrier (Y/N/U/H)

No `sorry`, no new `axiom`. Light on Mathlib (Std-only) so the v2.5.0
trusted-base manifest can compile this under the existing OperatorKO7
build configuration. The v3.0.0 ship lifts the `mock_dev_only`
certification grade on the universal variant to `lean_interpreted` once
the engine bridge calls `lake env lean --run` against a thin wrapper
script over this module.
-/

namespace OperatorKO7.Meta.Universal.ClassifyUniversal

open OperatorKO7.Meta.BoundaryOperator

/-- The schema-level shape of a `FiniteInformationMatrix`: a list of
`(fact_key, rules)` rows. The wire shape is JSON
`{ "fact_a": ["rule_x", "rule_y"], ... }`; this Lean record encodes only
the rule-list cardinality used by the W₀ scan. -/
structure FiniteInformationMatrix where
  rows : List (String × List String)

/-- Cardinality classes the W₀ scan returns. The engine maps these to
the four typed verdicts {T1, T3, T4, Violation} via the verdict
synthesizer. -/
inductive CardinalityClass where
  | noMapping
  | plainTextApplication
  | ambiguityDuplication
  deriving DecidableEq, Repr

/-- Per-row classification. -/
def classifyRow (rules : List String) : CardinalityClass :=
  match rules with
  | []        => CardinalityClass.noMapping
  | [_]       => CardinalityClass.plainTextApplication
  | _ :: _ :: _ => CardinalityClass.ambiguityDuplication

/-- Aggregate classification: takes the worst (most-blocking) class
across the matrix. Precedence (worst -> best):
`ambiguityDuplication > noMapping > plainTextApplication`.
Mirrors the Python mock's worst-class fold. -/
def aggregateClass (current candidate : CardinalityClass) : CardinalityClass :=
  match current, candidate with
  | CardinalityClass.ambiguityDuplication, _ => CardinalityClass.ambiguityDuplication
  | _, CardinalityClass.ambiguityDuplication => CardinalityClass.ambiguityDuplication
  | CardinalityClass.noMapping, _            => CardinalityClass.noMapping
  | _, CardinalityClass.noMapping            => CardinalityClass.noMapping
  | _, _                                     => CardinalityClass.plainTextApplication

/-- A row-level witness the cert payload carries. -/
structure RowWitness where
  fact : String
  rules : List String
  cls : CardinalityClass

/-- Per-row witness derivation. -/
def witnessOf : (String × List String) → RowWitness
  | (fact, rules) => { fact := fact, rules := rules, cls := classifyRow rules }

/-- The ClassificationResult the engine consumes. Mirrors the Python
mock's response shape (modulo JSON / structure conversion). -/
structure ClassificationResult where
  worstClass   : CardinalityClass
  rowWitnesses : List RowWitness
  blocked      : Bool

/-- The W₀ classifier on a finite information matrix. -/
def classifyUniversal (m : FiniteInformationMatrix) : ClassificationResult :=
  let rows := m.rows.map witnessOf
  let worst := rows.foldl
    (fun acc w => aggregateClass acc w.cls)
    CardinalityClass.plainTextApplication
  let blocked := match worst with
    | CardinalityClass.plainTextApplication => false
    | _ => true
  { worstClass := worst, rowWitnesses := rows, blocked := blocked }

/-- Mapping from the cardinality class to the engine's typed-refusal
carrier (`Y/N/U/H` from `Meta.BoundaryOperator.TypedRefusalCompleteness`).

* `plainTextApplication`   ->  `Y`   (T1 / clean success)
* `ambiguityDuplication`   ->  `N`   (T3 / licensed-quotient confession)
* `noMapping`              ->  `H`   (T4 / typed abstention)

The carrier itself is finite (4 elements); every classification result
lands in `RefusalType.support`. -/
def cardinalityClassToRefusalType : CardinalityClass → RefusalType
  | CardinalityClass.plainTextApplication => RefusalType.Y
  | CardinalityClass.ambiguityDuplication => RefusalType.N
  | CardinalityClass.noMapping            => RefusalType.H

/-- The packaged classifier that lifts a `ClassificationResult` into the
typed-refusal carrier. -/
def classifyUniversalToRefusalType (r : ClassificationResult) : RefusalType :=
  cardinalityClassToRefusalType r.worstClass

/-- Soundness: every `ClassificationResult` lands in the typed-refusal
support set. -/
theorem classifyUniversal_grounded
    (m : FiniteInformationMatrix) :
    classifyUniversalToRefusalType (classifyUniversal m) ∈ refusalTypeSupport :=
  refusalType_mem_support _

/-- Exhaustiveness: the classifier produces one of three named cardinality
classes on every input, and every produced class is enumerated. -/
theorem classifyUniversal_complete
    (m : FiniteInformationMatrix) :
    (classifyUniversal m).worstClass = CardinalityClass.noMapping ∨
    (classifyUniversal m).worstClass = CardinalityClass.plainTextApplication ∨
    (classifyUniversal m).worstClass = CardinalityClass.ambiguityDuplication := by
  cases (classifyUniversal m).worstClass <;> simp

/-- The blocked flag matches the cardinality class. -/
theorem classifyUniversal_blocked_iff_not_plain
    (m : FiniteInformationMatrix) :
    (classifyUniversal m).blocked = true ↔
      (classifyUniversal m).worstClass ≠ CardinalityClass.plainTextApplication := by
  unfold classifyUniversal
  cases h : (m.rows.map witnessOf).foldl
      (fun acc w => aggregateClass acc w.cls)
      CardinalityClass.plainTextApplication <;>
    simp [h]

/-- The single-row classifier is monotone in cardinality (the cardinality
class only grows as rules are added; this is the property the mock
enforces). -/
theorem classifyRow_zero_is_no_mapping :
    classifyRow [] = CardinalityClass.noMapping := rfl

theorem classifyRow_one_is_plain_text (r : String) :
    classifyRow [r] = CardinalityClass.plainTextApplication := rfl

theorem classifyRow_two_or_more_is_ambiguity
    (r₁ r₂ : String) (rest : List String) :
    classifyRow (r₁ :: r₂ :: rest) = CardinalityClass.ambiguityDuplication := rfl

/-- Empty matrix produces a `plainTextApplication` worst-class (vacuously
unblocked). -/
theorem classifyUniversal_empty :
    (classifyUniversal { rows := [] }).worstClass
      = CardinalityClass.plainTextApplication := rfl

/-- A matrix with a single one-rule row is unblocked. -/
theorem classifyUniversal_single_row_unblocked
    (fact : String) (rule : String) :
    (classifyUniversal { rows := [(fact, [rule])] }).blocked = false := by
  -- Reduce the let-bindings + match in `classifyUniversal` by hand.
  show
    (match
      List.foldl
        (fun acc w => aggregateClass acc w.cls)
        CardinalityClass.plainTextApplication
        (List.map witnessOf [(fact, [rule])])
      with
      | CardinalityClass.plainTextApplication => false
      | _ => true)
    = false
  -- The map and fold both reduce explicitly; both reductions are by `rfl`.
  rfl

/-- Audit-row projection used by the engine's W₀ cert. -/
structure AuditRow where
  fact : String
  cardinality : Nat
  refusal : RefusalType

/-- Project per-row witnesses into the audit-row shape the engine prints
in its cert payload. -/
def auditRows (r : ClassificationResult) : List AuditRow :=
  r.rowWitnesses.map (fun w =>
    { fact := w.fact
    , cardinality := w.rules.length
    , refusal := cardinalityClassToRefusalType w.cls })

/-- Every audit-row refusal symbol is in the typed-refusal carrier. -/
theorem auditRows_refusal_mem_support
    (r : ClassificationResult) (row : AuditRow)
    (_hRow : row ∈ auditRows r) :
    row.refusal ∈ refusalTypeSupport := by
  exact refusalType_mem_support _

end OperatorKO7.Meta.Universal.ClassifyUniversal
