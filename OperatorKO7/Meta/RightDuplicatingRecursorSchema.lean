/-!
# Right-Duplicating Recursor Schema (RDRS)

Phase A shell of the recursive-family expansion roadmap.

This module isolates the minimum honest interface for a single rewrite rule whose
right-hand side syntactically duplicates a distinguished payload variable. It is
the framework-parametricity floor below which the schema layer cannot honestly
descend: a position oracle and an occurrence counter are required, so pure
abstract-rewriting parametricity is excluded by construction.

The interface intentionally captures only:

- a term carrier `Term`,
- a payload-coordinate index type `PayloadCoord`,
- a syntactic-position index type `Position`,
- the rule's `lhs` and `rhs`,
- a payload-occurrence predicate `payloadOccursAt` and a count function `payloadCount`,
- a distinguished payload coordinate with one occurrence on the lhs and at least
  two occurrences on the rhs,
- a firability predicate on closed terms.

It excludes:

- direct whole-term observers (Phase B),
- canonical-witness universality (Phase A.3),
- scope-as-record (Phase A.5),
- payload exposure matrices (Phase C),
- step relations and pump predicates (Phase A `DuplicatingRecursiveFamily`).

The existing `Meta/StepDuplicatingSchema.lean` development is left untouched.
RDRS is added in parallel as a separate honest abstraction layer and may be
instantiated by existing schemas via adapter modules introduced in later phases.
-/

namespace OperatorKO7.StepDuplicating

/--
Minimum honest interface for a right-duplicating recursor rule.

A candidate term algebra `Term` is paired with a payload-coordinate index type
`PayloadCoord`, a syntactic-position index type `Position`, an occurrence
predicate, and a count function. The distinguished payload coordinate occurs
exactly once on the lhs and at least twice on the rhs. The firability predicate
keeps the rule from being vacuously inapplicable on closed instances. -/
structure RightDuplicatingRecursorSchema where
  /-- The term carrier. -/
  Term : Type
  /-- Index type for payload coordinates (variables eligible for duplication tracking). -/
  PayloadCoord : Type
  /-- Index type for syntactic positions inside terms. -/
  Position : Type
  /-- The left-hand side of the rewrite rule. -/
  lhs : Term
  /-- The right-hand side of the rewrite rule. -/
  rhs : Term
  /-- `payloadOccursAt p i t` records that the payload coordinate `p` occurs at
  the syntactic position `i` inside the term `t`. -/
  payloadOccursAt : PayloadCoord → Position → Term → Prop
  /-- Total number of occurrences of payload `p` in term `t`. -/
  payloadCount : PayloadCoord → Term → Nat
  /-- The distinguished payload coordinate whose duplication is the rule's content. -/
  distinguishedPayload : PayloadCoord
  /-- The distinguished payload occurs exactly once on the lhs. -/
  lhs_has_payload :
    payloadCount distinguishedPayload lhs = 1
  /-- The distinguished payload occurs at least twice on the rhs. -/
  rhs_duplicates_payload :
    2 ≤ payloadCount distinguishedPayload rhs
  /-- The rule is firable on closed terms; the concrete realization is left to
  the carrier so framework-parametricity stays honest. -/
  firesOnClosedTerms : Prop

namespace RightDuplicatingRecursorSchema

variable (S : RightDuplicatingRecursorSchema)

/-- The duplication gap of the distinguished payload across the rewrite rule.
Defined as the rhs count minus the lhs count on the distinguished coordinate. -/
def distinguishedDuplicationGap : Nat :=
  S.payloadCount S.distinguishedPayload S.rhs -
    S.payloadCount S.distinguishedPayload S.lhs

/-- The duplication gap on the distinguished payload coordinate is at least one. -/
theorem one_le_distinguishedDuplicationGap :
    1 ≤ S.distinguishedDuplicationGap := by
  unfold distinguishedDuplicationGap
  have hl : S.payloadCount S.distinguishedPayload S.lhs = 1 := S.lhs_has_payload
  have hr : 2 ≤ S.payloadCount S.distinguishedPayload S.rhs := S.rhs_duplicates_payload
  omega

/-- The rhs payload count strictly exceeds the lhs payload count on the
distinguished coordinate. This is the core asymmetry that the recursive-family
boundary theorem will exploit in Phase B. -/
theorem rhs_count_gt_lhs_count :
    S.payloadCount S.distinguishedPayload S.lhs <
      S.payloadCount S.distinguishedPayload S.rhs := by
  have hl : S.payloadCount S.distinguishedPayload S.lhs = 1 := S.lhs_has_payload
  have hr : 2 ≤ S.payloadCount S.distinguishedPayload S.rhs := S.rhs_duplicates_payload
  omega

/-- The distinguished payload coordinate occurs on the rhs. -/
theorem distinguished_payload_count_rhs_pos :
    0 < S.payloadCount S.distinguishedPayload S.rhs := by
  have hr : 2 ≤ S.payloadCount S.distinguishedPayload S.rhs := S.rhs_duplicates_payload
  omega

end RightDuplicatingRecursorSchema

end OperatorKO7.StepDuplicating
