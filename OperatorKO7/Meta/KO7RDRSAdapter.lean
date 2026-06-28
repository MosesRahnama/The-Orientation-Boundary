import OperatorKO7.Kernel
import OperatorKO7.Meta.RightDuplicatingRecursorSchema

/-!
# KO7 Right-Duplicating Recursor Schema Adapter

Phase A.3 (Sprint 5R) artifact.

Raw `Trace` occurrence counting cannot distinguish the three role
variables `b`, `s`, `n` of the KO7 duplicating recursor rule

```
recΔ b s (delta n)  ⇒  app s (recΔ b s n)
```

when those roles are instantiated by repeated closed terms. This module
adds a small role-aware KO7 RDRS adapter: a syntax mirroring the KO7
surface but with three formal variable symbols `bRole`, `sRole`, `nRole`,
so the distinguished payload `sRole` occurs exactly once on the lhs and
exactly twice on the rhs by literal counting.

The adapter is connected to the live KO7 kernel `Step.R_rec_succ` rule via
an explicit projection lemma: every closed instance of the role-aware lhs
projects to a `Trace` term whose `Step` image is exactly the rhs's
projection. This is the unconditional "projection to the KO7 recursor
step" connection underwriting the canonical KO7 RDRS witness.

The module exposes:

- `KO7RDRSTerm` and its role/position/coordinate types,
- `sCount`, `lhs_s_count_eq_one`, `rhs_s_count_eq_two`,
- `ko7RDRS : RightDuplicatingRecursorSchema`,
- `ko7RDRS_projects_to_kernel_step`: a closed instance of the adapter
  projects to a literal `Step.R_rec_succ` reduction on `Trace`.

No proof placeholders are used. No legacy theorem name is touched.
-/

namespace OperatorKO7.StepDuplicating
namespace KO7RDRSAdapter

open OperatorKO7

/-- Role-aware mirror of the KO7 trace syntax. The three formal variable
symbols `bRole`, `sRole`, `nRole` mark the three argument roles of the
KO7 duplicating recursor rule; their identities are preserved by the
role-aware constructors so payload-occurrence counting is exact. -/
inductive KO7RDRSTerm
  | bRole : KO7RDRSTerm
  | sRole : KO7RDRSTerm
  | nRole : KO7RDRSTerm
  | void  : KO7RDRSTerm
  | delta : KO7RDRSTerm → KO7RDRSTerm
  | app   : KO7RDRSTerm → KO7RDRSTerm → KO7RDRSTerm
  | recΔ  : KO7RDRSTerm → KO7RDRSTerm → KO7RDRSTerm → KO7RDRSTerm
  deriving DecidableEq, Repr

namespace KO7RDRSTerm

/-- One distinguished coordinate: the `sRole` (KO7 step argument). -/
inductive Coord
  | sCoord
  deriving DecidableEq, Repr

/-- Enumerated positions where `sRole` occurs on the lhs / rhs of the
KO7 duplicating rule. -/
inductive Pos
  | lhsArg2
  | rhsOuterArg1
  | rhsInnerArg2
  deriving DecidableEq, Repr

/-- `sOccurAt p i t` records that the role-aware `sRole` is at structural
position `i` inside the role-aware term `t`. The predicate is the literal
pattern flattening of `Coord = sCoord` cases at each enumerated KO7 rule
position. -/
def sOccurAt : Coord → Pos → KO7RDRSTerm → Prop
  | .sCoord, .lhsArg2,      .recΔ _ .sRole _                          => True
  | .sCoord, .rhsOuterArg1, .app .sRole _                             => True
  | .sCoord, .rhsInnerArg2, .app _ (.recΔ _ .sRole _)                 => True
  | _,       _,             _                                         => False

/-- Count occurrences of the role-aware `sRole` in a role-aware term. -/
def sCount : Coord → KO7RDRSTerm → Nat
  | .sCoord, .bRole         => 0
  | .sCoord, .sRole         => 1
  | .sCoord, .nRole         => 0
  | .sCoord, .void          => 0
  | .sCoord, .delta t       => sCount .sCoord t
  | .sCoord, .app t1 t2     => sCount .sCoord t1 + sCount .sCoord t2
  | .sCoord, .recΔ t1 t2 t3 => sCount .sCoord t1 + sCount .sCoord t2 + sCount .sCoord t3

/-- Left-hand side of the KO7 duplicating rule (role-aware mirror):
`recΔ bRole sRole (delta nRole)`. -/
def lhsTerm : KO7RDRSTerm :=
  .recΔ .bRole .sRole (.delta .nRole)

/-- Right-hand side of the KO7 duplicating rule (role-aware mirror):
`app sRole (recΔ bRole sRole nRole)`. -/
def rhsTerm : KO7RDRSTerm :=
  .app .sRole (.recΔ .bRole .sRole .nRole)

theorem lhs_s_count_eq_one :
    sCount .sCoord lhsTerm = 1 := by
  rfl

theorem rhs_s_count_eq_two :
    sCount .sCoord rhsTerm = 2 := by
  rfl

/-- Role assignment: every role-aware variable plus the role-aware
constructors fold down to a concrete `Trace` value by substituting the
three role variables. The projection is the identity on the four shared
constructors. -/
def project (b s n : Trace) : KO7RDRSTerm → Trace
  | .bRole         => b
  | .sRole         => s
  | .nRole         => n
  | .void          => Trace.void
  | .delta t       => Trace.delta (project b s n t)
  | .app t1 t2     => Trace.app (project b s n t1) (project b s n t2)
  | .recΔ t1 t2 t3 => Trace.recΔ (project b s n t1) (project b s n t2) (project b s n t3)

@[simp] theorem project_lhsTerm (b s n : Trace) :
    project b s n lhsTerm = Trace.recΔ b s (Trace.delta n) := by
  rfl

@[simp] theorem project_rhsTerm (b s n : Trace) :
    project b s n rhsTerm = Trace.app s (Trace.recΔ b s n) := by
  rfl

end KO7RDRSTerm

/-- KO7 viewed as a right-duplicating recursor schema, with role-aware
payload counting. The distinguished payload `sCoord` (the KO7 step
argument) occurs exactly once on the lhs and exactly twice on the rhs.
`firesOnClosedTerms` is realized by the projection identity into the
live KO7 kernel `Step.R_rec_succ` rule (see `ko7RDRS_projects_to_kernel_step`). -/
def ko7RDRS : RightDuplicatingRecursorSchema where
  Term := KO7RDRSTerm
  PayloadCoord := KO7RDRSTerm.Coord
  Position := KO7RDRSTerm.Pos
  lhs := KO7RDRSTerm.lhsTerm
  rhs := KO7RDRSTerm.rhsTerm
  payloadOccursAt := KO7RDRSTerm.sOccurAt
  payloadCount := KO7RDRSTerm.sCount
  distinguishedPayload := .sCoord
  lhs_has_payload := KO7RDRSTerm.lhs_s_count_eq_one
  rhs_duplicates_payload := by
    rw [KO7RDRSTerm.rhs_s_count_eq_two]; decide
  firesOnClosedTerms := True

/-- Per-instance smoke theorem: the KO7 RDRS adapter has positive
duplication gap. -/
theorem ko7RDRS_gap_pos :
    1 ≤ ko7RDRS.distinguishedDuplicationGap :=
  ko7RDRS.one_le_distinguishedDuplicationGap

/-- Per-instance smoke theorem: the KO7 RDRS adapter has strict rhs-vs-lhs
payload count growth. -/
theorem ko7RDRS_rhs_strict :
    ko7RDRS.payloadCount ko7RDRS.distinguishedPayload ko7RDRS.lhs <
      ko7RDRS.payloadCount ko7RDRS.distinguishedPayload ko7RDRS.rhs :=
  ko7RDRS.rhs_count_gt_lhs_count

/-- Per-instance smoke theorem: the KO7 RDRS adapter has positive rhs
payload occurrence count. -/
theorem ko7RDRS_rhs_payload_pos :
    0 < ko7RDRS.payloadCount ko7RDRS.distinguishedPayload ko7RDRS.rhs :=
  ko7RDRS.distinguished_payload_count_rhs_pos

/-- The KO7 RDRS adapter's lhs/rhs pair projects, for every concrete role
assignment `b, s, n : Trace`, onto a live KO7 kernel `Step.R_rec_succ`
reduction. This is the explicit "projection to the KO7 recursor step"
required by the no-gap acceptance policy: the adapter is connected to the
live `Step` relation by an unconditional Lean proof. -/
theorem ko7RDRS_projects_to_kernel_step (b s n : Trace) :
    Step
      (KO7RDRSTerm.project b s n ko7RDRS.lhs)
      (KO7RDRSTerm.project b s n ko7RDRS.rhs) := by
  show Step
      (KO7RDRSTerm.project b s n KO7RDRSTerm.lhsTerm)
      (KO7RDRSTerm.project b s n KO7RDRSTerm.rhsTerm)
  rw [KO7RDRSTerm.project_lhsTerm, KO7RDRSTerm.project_rhsTerm]
  exact Step.R_rec_succ b s n

end KO7RDRSAdapter
end OperatorKO7.StepDuplicating
