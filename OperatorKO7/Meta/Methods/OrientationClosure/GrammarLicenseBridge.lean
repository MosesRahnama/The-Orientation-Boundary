import OperatorKO7.Meta.OperationalInexpressibility.DirectGrammarBoundary
import OperatorKO7.Meta.Methods.OrientationClosure.VectorComparison
import Mathlib.Tactic

/-!
# The grammar boundary and the direct-grammar license are one statement

The Orientation grammar theorem characterizes orientation of the duplicating step by a grammar
expression: `OrientsDupStep e.eval ↔ PayloadBlind e.eval ∧ CounterStrict e.eval`. The operational
inexpressibility paper states the direct-grammar license: no grammar expression both uses the payload
and is adequate for orienting the duplicating step. Both quantify over the same grammar `MeasureExpr`
with the same denotation `eval`.

`UsesPayload e` is the negation of `PayloadBlind e.eval` and `AdequateForDupOrientation e` is
`OrientsDupStep e.eval`, so the two vocabularies translate by the identity on the grammar
(`payloadBlind_iff_not_usesPayload`, `adequate_iff_orients`). Under that translation the license
criterion is the grammar theorem (`license_criterion_iff`) and the separation is the payload half of
the grammar theorem (`separation_iff_payload_half`).

The translation is an equivalence of statements. It is not a unique map of grammars: every self-map
of the grammar that preserves the denotation preserves both predicates
(`denotation_preserving_maps_preserve_predicates`), and commuting the arguments of a sum is such a
map different from the identity (`swapAdd_ne_id`).

`aggregation_orients_through_counter_projection` states what a checker that aggregates recursive
arguments can use: through the grammar exactly a payload-blind measure with strict counter response;
under lexicographic aggregation a payload-blind primary coordinate, with later coordinates free to
read the payload; under componentwise strict aggregation payload-blind coordinates only.
-/

set_option autoImplicit false

namespace OperatorKO7.Methods.OrientationClosure.GrammarLicenseBridge

open OperatorKO7.Meta.BoundaryGeneral.DirectMeasureGrammarClosure
open OperatorKO7.Meta.OperationalInexpressibility.DirectGrammarBoundary

theorem payloadBlind_iff_not_usesPayload (e : MeasureExpr) :
    PayloadBlind e.eval ↔ ¬ UsesPayload e := by
  unfold UsesPayload
  exact not_not.symm

theorem adequate_iff_orients (e : MeasureExpr) :
    AdequateForDupOrientation e ↔ OrientsDupStep e.eval :=
  Iff.rfl

/-- The grammar theorem in the vocabulary of the license: an expression is adequate exactly when it
does not use the payload and responds strictly to the counter. -/
theorem license_criterion_iff (e : MeasureExpr) :
    AdequateForDupOrientation e ↔ ¬ UsesPayload e ∧ CounterStrict e.eval := by
  rw [adequate_iff_orients, orients_iff_payloadBlind_and_counterStrict,
    payloadBlind_iff_not_usesPayload]

/-- The license separation is the payload half of the grammar theorem, and conversely. -/
theorem separation_iff_payload_half :
    (∀ e : MeasureExpr, ¬ (UsesPayload e ∧ AdequateForDupOrientation e)) ↔
      (∀ e : MeasureExpr, OrientsDupStep e.eval → PayloadBlind e.eval) := by
  constructor
  · intro h e ho
    by_contra hb
    exact h e ⟨hb, ho⟩
  · rintro h e ⟨hu, ha⟩
    exact hu (h e ha)

/-- Both statements hold; each is derived from the other through the translation. -/
theorem orientation_grammar_and_oi_license :
    (∀ e : MeasureExpr, OrientsDupStep e.eval ↔ PayloadBlind e.eval ∧ CounterStrict e.eval) ∧
      (∀ e : MeasureExpr, ¬ (UsesPayload e ∧ AdequateForDupOrientation e)) ∧
      ((∀ e : MeasureExpr, ¬ (UsesPayload e ∧ AdequateForDupOrientation e)) ↔
        (∀ e : MeasureExpr, OrientsDupStep e.eval → PayloadBlind e.eval)) :=
  ⟨orients_iff_payloadBlind_and_counterStrict, no_directGrammar_measure_usesPayload_and_orients,
    separation_iff_payload_half⟩

/-! ## What else preserves the two predicates -/

/-- Commute the arguments of a top-level sum. -/
def swapAdd : MeasureExpr → MeasureExpr
  | .add e f => .add f e
  | e => e

theorem eval_swapAdd (e : MeasureExpr) : (swapAdd e).eval = e.eval := by
  cases e with
  | add e f =>
    funext c p
    simp only [swapAdd, MeasureExpr.eval]
    omega
  | _ => rfl

/-- Every self-map of the grammar that preserves the denotation preserves both predicates. -/
theorem denotation_preserving_maps_preserve_predicates (φ : MeasureExpr → MeasureExpr)
    (hφ : ∀ e, (φ e).eval = e.eval) (e : MeasureExpr) :
    (UsesPayload (φ e) ↔ UsesPayload e) ∧
      (AdequateForDupOrientation (φ e) ↔ AdequateForDupOrientation e) := by
  unfold UsesPayload AdequateForDupOrientation
  rw [hφ e]
  exact ⟨Iff.rfl, Iff.rfl⟩

/-- Commuting a sum is a predicate-preserving map different from the identity. -/
theorem swapAdd_ne_id : swapAdd ≠ id := by
  intro h
  have := congrFun h (.add .counter .payload)
  simp [swapAdd] at this

/-! ## Aggregation of recursive arguments -/

/-- What a checker aggregating recursive arguments can use to orient the duplicating step: through
the grammar exactly a payload-blind measure with strict counter response; under lexicographic
aggregation a payload-blind primary coordinate, while later coordinates may read the payload; under
componentwise strict aggregation only payload-blind coordinates. -/
theorem aggregation_orients_through_counter_projection :
    (∀ e : MeasureExpr, OrientsDupStep e.eval ↔ PayloadBlind e.eval ∧ CounterStrict e.eval) ∧
      (type_of% @VectorComparison.lex_requires_primary_payloadBlind) ∧
      (type_of% @VectorComparison.allStrict_requires_all_payloadBlind) ∧
      (type_of% @VectorComparison.lex_orientation_keeps_later_payload) :=
  ⟨orients_iff_payloadBlind_and_counterStrict, VectorComparison.lex_requires_primary_payloadBlind,
    VectorComparison.allStrict_requires_all_payloadBlind,
    VectorComparison.lex_orientation_keeps_later_payload⟩

end OperatorKO7.Methods.OrientationClosure.GrammarLicenseBridge
