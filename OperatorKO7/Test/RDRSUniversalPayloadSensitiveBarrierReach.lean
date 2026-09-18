import OperatorKO7.Meta.RDRSUniversalPayloadSensitiveBarrier

set_option autoImplicit false

/-!
# Reach test: RDRS Universal Payload-Sensitive Direct-Measure Barrier capstone (Milestone U7 / U11)

Verifies that all public names exported by
`OperatorKO7.RDRSUniversalPayloadSensitiveBarrier` are reachable, that
the capstone closure marker
`rdrs_universal_payload_sensitive_barrier_closed` is reachable, and
that the audit anchor String constants are reachable.

The reach test does not prove any new mathematical content; it only
exercises the capstone's public surface so a downstream consumer
(Paper A claim-to-code index, supervisory engine audit log, future
ledger agents) can rely on the capstone being importable.

## Audit slots (Lean Development Bible W8 / R4)

```
Relation:  N/A. This is a reach test, not a rewriting theorem.
Closure:   N/A.
Strategy:  N/A.
Trust:     kernel-only. The reach test consists of `#check` directives
           and `rfl` field-equality theorems against the capstone's
           public surface. No `sorry`, `admit`, `axiom`, `native_decide`,
           etc.
Scope:     reachability of the capstone surface only. No new
           mathematics; no new theorems beyond `rfl` reach lemmas.
```

## Capstone-name adequacy note (Lean Development Bible stop-the-line #9)

The capstone marker `rdrs_universal_payload_sensitive_barrier_closed`
contains the risk words "universal" and "closed". Their intended
scope:

* **"universal"**: universal over the *closed-grammar
  direct-payload-sensitive surface* (U1-U6 milestones), NOT universal
  over all termination methods, all recursive systems, full DP /
  MSPO / WPO / gWPO, or arbitrary semantic quotients. Per Lean
  Development Bible Section 1 R4 and stop-the-line #9, this scope
  qualification is recorded on every public docstring that cites the
  capstone.
* **"closed"**: closed in the sense that every field of the capstone
  `Prop` is discharged by an upstream `decide`-proved or kernel-
  proved theorem; NOT closed in any TPDB / external-tool
  certification sense. The Lean kernel acceptance is the entire
  trust claim.

## Honesty record (re-asserted at the reach layer)

* The U3 retained-coordinate counter factorisation theorem is
  conditional on a caller-supplied factor hypothesis. The reach test
  cites the conditional re-export
  `retainedCoordinate_factorsThrough_counter_conditional_capstone`
  (named factor hypothesis), not an unconditional version.
* The capstone does not claim unrestricted monotone-algebra coverage,
  MSPO, full DP processors, full WPO/gWPO, or arbitrary semantic
  quotient coverage; those scope carve-outs sit in the underlying
  U1/U1.5/U2/U3/U4/U5/U6 modules and are preserved on the capstone
  Prop without widening.
-/

open OperatorKO7.RDRSUniversalPayloadSensitiveBarrier

/-! ## Public name reachability checks -/

-- Capstone closure structure and theorem
#check @UniversalBarrierClosed
#check @rdrs_universal_payload_sensitive_barrier_closed

-- Conditional re-exports of the U3 retained-coordinate theorem
#check @retainedCoordinate_factorsThrough_counter_is_conditional_capstone
#check @retainedCoordinate_factorsThrough_counter_conditional_capstone

-- Audit anchor String constants
#check @rdrs_universal_payload_sensitive_barrier_closed_anchor
#check @rdrs_universal_barrier_retained_coordinate_conditional_anchor

/-! ## Anchor-String surface theorems -/

/-- The capstone audit anchor names the capstone theorem.

**Proves:** equality of the anchor String to its expected value.
**Does not prove:** that the named theorem itself is sound; only that
the anchor String matches.
**Trust:** kernel-only (`rfl`). -/
theorem reach_capstone_anchor_value :
    rdrs_universal_payload_sensitive_barrier_closed_anchor
      = "OperatorKO7.RDRSUniversalPayloadSensitiveBarrier.rdrs_universal_payload_sensitive_barrier_closed" :=
  rfl

/-- The retained-coordinate conditional anchor names the named-
hypothesis re-export.

**Proves:** equality of the anchor String.
**Does not prove:** that the named re-export proves an unconditional
factorisation; the anchor explicitly references the conditional form.
**Trust:** kernel-only. -/
theorem reach_retained_coordinate_conditional_anchor_value :
    rdrs_universal_barrier_retained_coordinate_conditional_anchor
      = "OperatorKO7.RDRSUniversalPayloadSensitiveBarrier.retainedCoordinate_factorsThrough_counter_conditional_capstone" :=
  rfl

/-! ## Capstone field-access reach -/

/-- The capstone Prop has its expected field on coverage-ledger zero
residual.

**Proves:** the capstone field equals the underlying U6 proof.
**Does not prove:** the underlying theorem itself; only the
field-equality at the capstone layer.
**Trust:** kernel-only. -/
theorem reach_capstone_coverage_ledger_zero_residual :
    rdrs_universal_payload_sensitive_barrier_closed.coverageLedgerZeroResidual
      = OperatorKO7.RDRSCoverageLedger.Full.temporary_unclassified_count :=
  rfl

/-- The capstone Prop's `kappaTruthBoundaryDistinct` field aliases the
underlying U5 export. -/
theorem reach_capstone_kappa_truth_boundary_distinct :
    rdrs_universal_payload_sensitive_barrier_closed.kappaTruthBoundaryDistinct
      = OperatorKO7.RDRSBoundaryBottleneck.kappa_truth_vs_boundary_distinct :=
  rfl

/-- The capstone Prop's `coverageLedgerClosed` field aliases the
underlying U6 capstone certificate. -/
theorem reach_capstone_coverage_ledger_closed :
    rdrs_universal_payload_sensitive_barrier_closed.coverageLedgerClosed
      = OperatorKO7.RDRSCoverageLedger.Full.rdrs_coverage_ledger_closed :=
  rfl

/-! ## Conditional retained-coordinate shape exercises -/

/-- The conditional capstone re-export, applied to the factor
hypothesis, yields the same conclusion as the underlying U3 theorem.

**Proves:** the capstone's conditional shape passes the factor
hypothesis through to the conclusion.
**Does not prove:** an unconditional factorisation. The capstone
re-export is conditional by construction; this reach theorem only
documents that the hypothesis is required.
**Trust:** kernel-only.
**Scope:** parametric over `B S N T : Type`, `R : RDRSStep B S N T`,
`P : ProjectionTransaction R`, `SH : StaticRetainedHypotheses R`,
plus the caller-supplied factor existence hypothesis. -/
theorem reach_retained_coordinate_factors_through_counter_capstone_shape
    {B S N T : Type}
    {R : OperatorKO7.RDRSDescentLens.RDRSStep B S N T}
    (P : OperatorKO7.RDRSProjectionTransaction.ProjectionTransaction R)
    (SH : OperatorKO7.RDRSRetainedCoordinate.StaticRetainedHypotheses R)
    (h : ∃ factor : Nat → P.CounterIndex,
        ∀ t, P.retainedCoordinate (P.pi t) = factor (SH.counter t)) :
    ∃ factorFromCounter : Nat → P.A',
      ∀ t, P.mu' (P.pi t) = factorFromCounter (SH.counter t) :=
  retainedCoordinate_factorsThrough_counter_conditional_capstone P SH h
