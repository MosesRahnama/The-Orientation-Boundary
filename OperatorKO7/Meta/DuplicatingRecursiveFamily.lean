import OperatorKO7.Meta.RightDuplicatingRecursorSchema

/-!
# Duplicating Recursive Family

Phase A wrapper around `RightDuplicatingRecursorSchema` adding the family-level
fields that Phase B and later phases consume to state the generic recursive-family
boundary theorem.

This shell records:

- an underlying RDRS schema,
- a step relation on the schema's term carrier,
- a witness that the rule's lhs steps to its rhs under that step relation,
- a family-level payload pump predicate `HasUnboundedPayloadPump`,
- a family-level payload-exposure predicate `ExposesPayloadStrictly`,
- a witness that the distinguished payload coordinate is strictly exposed,
- a structural certificate `exposure_strict_count`: any coordinate satisfying
  `ExposesPayloadStrictly` exhibits a strict payload-count rise from lhs to rhs.

The structural certificate `exposure_strict_count` is the proved exposure-count
field promoted out of the previous theorem-local bridge: it lifts the schema's
distinguished count asymmetry to every coordinate the family claims to expose
strictly. Concrete carriers (KO7, the textbook duplicating rule, future RDRS
instances) discharge it directly from their concrete count functions.

It excludes:

- the `DirectWholeTermObserver` interface (Phase B),
- the canonical-witness universality theorem (Phase A.3),
- the scope-as-record interface (Phase A.5),
- payload exposure matrices and scalarization certificates (Phase C),
- context / SCC transport (Phase D),
- escape and residual catalogs (Phase F / G).

Existing schema and KO7 theorems are not touched. This file adds a parallel
abstraction layer only.
-/

namespace OperatorKO7.StepDuplicating

/--
A `DuplicatingRecursiveFamily` packages an RDRS schema together with a step
relation and the family-level structural predicates and certificates used by
the recursive-family boundary theorem.

The two predicates `HasUnboundedPayloadPump` and `ExposesPayloadStrictly` are
deliberately kept abstract as `Prop` predicates so concrete carriers can supply
their own witnesses. The structural certificate `exposure_strict_count` ties
the abstract exposure predicate to the schema-level payload-count asymmetry:
whenever `ExposesPayloadStrictly i` holds, the rhs payload count at `i`
strictly exceeds the lhs payload count at `i`.
-/
structure DuplicatingRecursiveFamily where
  /-- The underlying right-duplicating recursor schema. -/
  schema : RightDuplicatingRecursorSchema
  /-- The step relation on the schema's term carrier. -/
  Step : schema.Term → schema.Term → Prop
  /-- The rule's lhs steps to its rhs under the family-level step relation. -/
  duplicating_step : Step schema.lhs schema.rhs
  /-- Family-level predicate: the named payload coordinate admits an unbounded
  pump in some sense to be refined by concrete carriers and observers. -/
  HasUnboundedPayloadPump : schema.PayloadCoord → Prop
  /-- Family-level predicate: the named payload coordinate is strictly exposed
  more on the rhs than on the lhs in a coordinate-indexed sense to be refined
  when payload-exposure matrices arrive in Phase C. -/
  ExposesPayloadStrictly : schema.PayloadCoord → Prop
  /-- The distinguished payload coordinate is strictly exposed by the rule. -/
  distinguished_exposed :
    ExposesPayloadStrictly schema.distinguishedPayload
  /-- Structural certificate: every coordinate the family claims to expose
  strictly exhibits a strict rhs-over-lhs payload-count rise. Concrete carriers
  discharge this directly from their concrete `payloadCount` functions. -/
  exposure_strict_count :
    ∀ {i : schema.PayloadCoord},
      ExposesPayloadStrictly i →
        schema.payloadCount i schema.lhs <
          schema.payloadCount i schema.rhs

namespace DuplicatingRecursiveFamily

variable (F : DuplicatingRecursiveFamily)

/-- Forward the distinguished payload coordinate from the underlying schema. -/
abbrev distinguishedPayload : F.schema.PayloadCoord :=
  F.schema.distinguishedPayload

/-- The distinguished payload count strictly increases across the rule. -/
theorem distinguished_payload_count_strict :
    F.schema.payloadCount F.distinguishedPayload F.schema.lhs <
      F.schema.payloadCount F.distinguishedPayload F.schema.rhs :=
  F.schema.rhs_count_gt_lhs_count

/-- The duplication gap of the underlying schema lifted to the family level. -/
abbrev distinguishedDuplicationGap : Nat :=
  F.schema.distinguishedDuplicationGap

/-- The family-level duplication gap is at least one. -/
theorem one_le_distinguishedDuplicationGap :
    1 ≤ F.distinguishedDuplicationGap :=
  F.schema.one_le_distinguishedDuplicationGap

end DuplicatingRecursiveFamily

end OperatorKO7.StepDuplicating
