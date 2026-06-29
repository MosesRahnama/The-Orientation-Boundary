import OperatorKO7.Meta.ReverseMath.GuardedNewmanRCA0
import OperatorKO7.Meta.ReverseMath.ConfluenceOrderType
import OperatorKO7.Meta.DistinctionBoundary.GlobalConfluence

/-!
# Guarded Newman order descriptor

This module packages the exact ordinal descriptor available in Mathlib:
`ω^ω` for the DM multiset measure, lifted to the trace-level `ω^ω * 2`
guarded-Newman upper descriptor. Literal reverse-math provability inside
`RCA₀` is not represented in Mathlib and is not encoded here by a proxy.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.ReverseMath.GuardedNewmanExactCalibration

open OperatorKO7 Trace
open Ordinal

/-- Paper-facing guarded Newman statement descriptor. -/
structure GuardedNewmanStatement where
  ordinalBound : Ordinal
  finiteCriticalPairs : Prop
  decidableLocalJoinability : Prop
  conclusion : Prop

/-- The guarded Newman package with the trace-level `ω^ω * 2` order descriptor. -/
def guardedNewmanOmegaOmegaTwo : GuardedNewmanStatement where
  ordinalBound := ((ω : Ordinal) ^ (ω : Ordinal)) * (2 : Nat)
  finiteCriticalPairs := True
  decidableLocalJoinability := ∀ a : Trace, MetaSN_KO7.LocalJoinAt a
  conclusion := MetaSN_KO7.ConfluentSafe

/-- Exact `ω^ω` order type for the DM multiset measure consumed by the Newman
ascent. -/
theorem safeStepCtx_order_type_exact :
    (∀ m₁ m₂ : Multiset Nat,
        OperatorKO7.MetaCM.DM m₁ m₂ ↔
          OperatorKO7.MetaDM.dmOrdEmbed m₁ <
            OperatorKO7.MetaDM.dmOrdEmbed m₂) ∧
      (∀ m : Multiset Nat,
        OperatorKO7.MetaDM.dmOrdEmbed m <
          (ω : Ordinal) ^ (ω : Ordinal)) ∧
      (∀ α < (ω : Ordinal) ^ (ω : Ordinal),
        ∃ m : Multiset Nat, OperatorKO7.MetaDM.dmOrdEmbed m = α) :=
  OperatorKO7.ReverseMath.confluence_measure_order_type

/-- Lower-bound witness: every ordinal below `ω^ω` is reached by some finite DM
multiset measure. -/
theorem safeStepCtx_order_type_lower_bound
    (α : Ordinal) (hα : α < (ω : Ordinal) ^ (ω : Ordinal)) :
    ∃ m : Multiset Nat, OperatorKO7.MetaDM.dmOrdEmbed m = α :=
  safeStepCtx_order_type_exact.2.2 α hα

/-- Every trace-level guarded Newman measure lies below the `ω^ω * 2` descriptor. -/
theorem safeStepCtx_order_descriptor_omegaOmega (t : Trace) :
    OperatorKO7.MetaDM.lex3cToOrd (OperatorKO7.MetaCM.mu3c t) <
      ((ω : Ordinal) ^ (ω : Ordinal)) * (2 : Nat) :=
  OperatorKO7.ReverseMath.confluence_measure_trace_bound t

/-- The guarded Newman order descriptor remains below `ε₀`. -/
theorem safeStepCtx_order_descriptor_below_epsilon0 :
    ((ω : Ordinal) ^ (ω : Ordinal)) * (2 : Nat) < ε₀ :=
  OperatorKO7.ReverseMath.confluence_measure_order_type_lt_epsilon0

/-- The guarded Newman upper package is the already proven SafeStep Newman
package with the exact ordinal descriptor attached. -/
theorem guardedNewmanOmegaOmegaTwo_closes :
    guardedNewmanOmegaOmegaTwo.conclusion ∧
      (∀ t : Trace,
        OperatorKO7.MetaDM.lex3cToOrd (OperatorKO7.MetaCM.mu3c t) <
          guardedNewmanOmegaOmegaTwo.ordinalBound) :=
  ⟨OperatorKO7.Meta.DistinctionBoundary.GlobalConfluence.safeStep_globally_confluent,
    safeStepCtx_order_descriptor_omegaOmega⟩

#print axioms safeStepCtx_order_type_exact
#print axioms safeStepCtx_order_type_lower_bound
#print axioms safeStepCtx_order_descriptor_omegaOmega
#print axioms safeStepCtx_order_descriptor_below_epsilon0
#print axioms guardedNewmanOmegaOmegaTwo_closes

end OperatorKO7.Meta.ReverseMath.GuardedNewmanExactCalibration
