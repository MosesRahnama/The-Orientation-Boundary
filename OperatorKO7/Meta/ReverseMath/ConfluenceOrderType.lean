import OperatorKO7.Meta.DM_OrderType_LowerBound

/-!
# The confluence-axis order-type descriptor (`ω^ω·2 < ε₀`)

The Dershowitz–Manna multiset measure that drives strong normalization of the KO7 safe relation is the
same measure whose well-foundedness Newman's lemma consumes to deliver confluence. So the order-type
descriptor of the confluence ascent is **inherited** from the termination calibration: it is the exact
`ω^ω` order type of the DM multiset ordering, lifted through the triple-lexicographic safe measure to
the `ω^ω·2 < ε₀` cap already mechanized in `Meta/DM_OrderType_LowerBound.lean`.

This module re-exports those anchors under confluence-axis names. It is a measure order-type
descriptor: it records the ordinal height of the well-founded measure that the Newman ascent recurses
on. The genuine `ω^ω` order-type package (bi-directional order, boundedness, surjectivity) is
`OperatorKO7.MetaDM.dm_order_type_omega_omega`; the `ω^ω·2` trace-level cap is
`OperatorKO7.MetaDM.lex3c_order_type_bound`, and `ω^ω·2 < ε₀` is
`OperatorKO7.MetaDM.opow_omega_mul_two_lt_epsilon0`. All three are already proved baseline-clean; this
module reassembles them as the confluence-axis descriptor without adding any new ordinal arithmetic.

The descriptor is the measure order type, the ordinal height of the SN measure feeding the Newman
ascent. It is distinct from the metatheoretic subsystem placement of Newman's lemma, which lives in the
companion modules.

No `sorry`, `admit`, `axiom`, `constant`, `opaque`, `unsafe`, `partial`, `native_decide`, `bv_decide`,
or `@[csimp]`: every field is a re-export of an existing kernel-checked theorem.
-/

set_option autoImplicit false

namespace OperatorKO7.ReverseMath

open Ordinal

/-- **The confluence-axis order-type descriptor.** The Dershowitz–Manna multiset ordering on
`Multiset Nat` has order type exactly `ω^ω`: the embedding `dmOrdEmbed` is bi-directional on `DM`
edges, bounded by `ω^ω`, and surjective onto the ordinals below `ω^ω`. This is the inherited measure
order type whose well-foundedness Newman's lemma consumes; it is re-exported here from
`OperatorKO7.MetaDM.dm_order_type_omega_omega`. -/
theorem confluence_measure_order_type :
    (∀ m₁ m₂ : Multiset Nat,
        OperatorKO7.MetaCM.DM m₁ m₂ ↔
          OperatorKO7.MetaDM.dmOrdEmbed m₁ < OperatorKO7.MetaDM.dmOrdEmbed m₂) ∧
      (∀ m : Multiset Nat,
        OperatorKO7.MetaDM.dmOrdEmbed m < (ω : Ordinal) ^ (ω : Ordinal)) ∧
      (∀ α < (ω : Ordinal) ^ (ω : Ordinal),
        ∃ m : Multiset Nat, OperatorKO7.MetaDM.dmOrdEmbed m = α) :=
  OperatorKO7.MetaDM.dm_order_type_omega_omega

/-- The confluence ascent recurses on the triple-lexicographic safe measure, whose ordinal height is
capped at `ω^ω·2`: every trace's measure image is `< ω^ω·2`. Re-exported from
`OperatorKO7.MetaDM.lex3c_order_type_bound`. -/
theorem confluence_measure_trace_bound (t : OperatorKO7.Trace) :
    OperatorKO7.MetaDM.lex3cToOrd (OperatorKO7.MetaCM.mu3c t) <
      ((ω : Ordinal) ^ (ω : Ordinal)) * (2 : Nat) :=
  OperatorKO7.MetaDM.lex3c_order_type_bound t

/-- The trace-level cap of the confluence measure sits strictly below `ε₀`: `ω^ω·2 < ε₀`. This places
the inherited descriptor inside the `ε₀` window shared with the termination calibration. Re-exported
from `OperatorKO7.MetaDM.opow_omega_mul_two_lt_epsilon0`. -/
theorem confluence_measure_order_type_lt_epsilon0 :
    ((ω : Ordinal) ^ (ω : Ordinal)) * (2 : Nat) < ε₀ :=
  OperatorKO7.MetaDM.opow_omega_mul_two_lt_epsilon0

/-- The confluence measure of every trace is strictly below `ε₀`, combining the `ω^ω·2` trace cap with
`ω^ω·2 < ε₀`. Re-exported from `OperatorKO7.MetaDM.safeMeasure_below_epsilon0`. -/
theorem confluence_measure_below_epsilon0 (t : OperatorKO7.Trace) :
    OperatorKO7.MetaDM.lex3cToOrd (OperatorKO7.MetaCM.mu3c t) < ε₀ :=
  OperatorKO7.MetaDM.safeMeasure_below_epsilon0 t

#print axioms confluence_measure_order_type
#print axioms confluence_measure_trace_bound
#print axioms confluence_measure_order_type_lt_epsilon0
#print axioms confluence_measure_below_epsilon0

end OperatorKO7.ReverseMath
