import OperatorKO7.Meta.EscapeRouteRefined
import OperatorKO7.Meta.KO7EscapeRouteCharacterization

set_option autoImplicit false

/-!
# Per-route extractors for the refined escape-route surface

Every declaration here projects proof data that is **already present** in the
object it destructs. Nothing is manufactured.

## Extraction discipline

* A route whose success datum carries a concrete rank, relation, or evidence
  value is projected into an existential over that same datum. `Exists` is a
  `Prop`, so eliminating the `Prop`-valued `KO7LicensedMethod` into it is a
  legitimate small elimination and needs no choice.
* A route whose datum is a **negative universal** statement (for example
  `¬ WrapSubtermSensitive ko7Schema rank`) is returned as that same negative
  proposition. No witness pair is produced from a `¬ ∀`, and
  `Classical.choice` is never used to turn a negation into data.
* `ko7_direct_escape_trichotomy_extended` is proved with the `classical`
  tactic, so the trichotomy extractor below inherits `Classical.choice` in its
  axiom footprint. That is recorded visibly here and in the reach file; the
  route extractors themselves do not depend on it.

## Audit slots (Lean Development Bible W8 / R4)

```text
Relation:  as carried by the destructed route datum; see each docstring.
Closure:   root.
Strategy:  full.
Trust:     kernel-only, except `escape_trichotomy_negative_clauses`, which
           inherits `Classical.choice`.
Scope:     the five `KO7Route` tags and the explicit `KO7DirectOrienter`
           universe.
```
-/

namespace OperatorKO7.EscapeRouteExtractors

open OperatorKO7
open OperatorKO7.Trace
open OperatorKO7.StepDuplicating
open OperatorKO7.CompositionalImpossibility
open OperatorKO7.EscapeTrichotomy
open OperatorKO7.EscapeRouteRefined

/-! ## 1. Positive route projections -/

/-- Projects the rank and its two theorems from a sensitivity-violating
projection method. The sensitivity failure is returned as the same negative
universal proposition that the method carries. -/
theorem sensitivityRoute_projection
    (h : KO7LicensedMethod .sensitivityViolatingProjection) :
    ∃ rank : Trace → Nat,
      (∀ b s n : Trace,
          rank (app s (recΔ b s n)) < rank (recΔ b s (delta n))) ∧
        ¬ StepDuplicatingSchema.WrapSubtermSensitive ko7Schema rank := by
  cases h with
  | sensitivityViolatingProjection rank horients hviolates =>
      exact ⟨rank, horients, hviolates⟩

/-- Projects the interpretation and its three theorems from a
transparency-violating interpretation method. -/
theorem transparencyRoute_projection
    (h : KO7LicensedMethod .transparencyViolatingInterpretation) :
    ∃ μ : Trace → Nat,
      (∀ a b : Trace, Step a b → μ b < μ a) ∧
        StepDuplicatingSchema.WrapSubtermSensitive ko7Schema μ ∧
        ¬ StepDuplicatingSchema.TransparentAtBase ko7Schema μ := by
  cases h with
  | transparencyViolatingInterpretation μ horients hsensitive htransparency =>
      exact ⟨μ, fun _ _ hstep => horients hstep, hsensitive, htransparency⟩

/-- Projects the interpretation and its coupling refutations from a
cross-coupled interpretation method. Both refutations are negative
existential statements and are returned unchanged. -/
theorem crossCouplingRoute_projection
    (h : KO7LicensedMethod .crossCoupledInterpretation) :
    ∃ μ : Trace → Nat,
      (∀ a b : Trace, Step a b → μ b < μ a) ∧
        (¬ ∃ c : Nat, ∀ b s n : Trace,
            μ (recΔ b s n) = c + μ b + μ s + μ n) ∧
        (¬ ∃ α β γ δr : Nat, ∀ b s n : Trace,
            μ (recΔ b s n) = α + β * μ b + γ * μ s + δr * μ n) := by
  cases h with
  | crossCoupledInterpretation μ horients hnotAdditive hnotAffine =>
      exact ⟨μ, fun _ _ hstep => horients hstep, hnotAdditive, hnotAffine⟩

/-- Projects the W2 transformed-call transform evidence and the direct-witness
refutation. Nothing about dependency-pair processor soundness is projected,
because the method carries none. -/
theorem w2TransformedCallRoute_projection
    (h : KO7LicensedMethod .w2TransformedCallProjection) :
    TransformedCallClassification.PermittedW2Transform
        .ko7DPProjection BenchmarkedPRCFamily.fullDuplicating ∧
      ¬ BenchmarkedPRCFamily.HasDirectWitness BenchmarkedPRCFamily.fullDuplicating := by
  cases h with
  | w2TransformedCallProjection htransform hnotDirect => exact ⟨htransform, hnotDirect⟩

/-- Projects the precedence comparison, the root-step orientation, and the
well-foundedness of the reversed path order from a structural path-order
method. -/
theorem structuralPathOrderRoute_projection
    (h : KO7LicensedMethod .structuralPathOrder) :
    MetaMPO.symPrec MetaMPO.Sym.app MetaMPO.Sym.recΔ ∧
      (∀ a b : Trace, Step a b → MetaMPO.MPO a b) ∧
      WellFounded MetaMPO.MPORev := by
  cases h with
  | structuralPathOrder hprec horients hwf =>
      exact ⟨hprec, fun _ _ hstep => horients hstep, hwf⟩

/-! ## 2. Negative-universal pass-through -/

/-- The canonical sensitivity failure is returned as the negative universal
proposition itself. No `x`, `y` pair is extracted from it. -/
theorem canonical_sensitivityRoute_negation :
    ¬ StepDuplicatingSchema.WrapSubtermSensitive ko7Schema dpProjection :=
  dpProjection_violates_wrapSubtermSensitive

/-- The canonical transparency failure is returned as the negative proposition
itself. -/
theorem canonical_transparencyRoute_negation :
    ¬ StepDuplicatingSchema.TransparentAtBase ko7Schema PolyInterpretation.W :=
  ConstructionMethodClassification.poly_not_transparent_at_base

/--
Proves: the direct-observer negative clauses for an orienting observer,
  re-exported unchanged from the retained three-way theorem.
Does not prove: any constructive witness inside those negations.
Relation: `KO7DirectOrienter.Orients`.
Closure: root.
Strategy: full.
Trust: kernel-only plus `Classical.choice`, inherited from the `classical`
  tactic in `ko7_direct_escape_trichotomy_extended`. This is the only
  declaration in this module carrying that axiom.
Scope: the explicit `KO7DirectOrienter` universe.
-/
theorem escape_trichotomy_negative_clauses
    (O : KO7DirectOrienter) (horient : O.Orients) :
    ¬ StepDuplicatingSchema.WrapSubtermSensitive ko7Schema O.primaryScalar ∨
      ¬ StepDuplicatingSchema.TransparentAtBase ko7Schema O.primaryScalar ∨
      ¬ KO7DirectBarrierRepresentable O :=
  ko7_direct_three_way_remains_universal (O := O) horient

/-- The represented-barrier incompatibility is returned as a negation of
orientation. It is not converted into data about the orienter. -/
theorem represented_barrier_negation (O : KO7DirectOrienter)
    (h : KO7DirectBarrierRepresentable O) : ¬ O.Orients :=
  no_orientation_of_represented_barrier h

/-! ## 3. Disposition projection -/

/-- A disposition either yields its positive licensed method or its indexed
missing-structure record. Both branches are `Prop`; nothing is chosen. -/
theorem routeDisposition_projection (r : KO7Route) (d : RouteDisposition r) :
    KO7LicensedMethod r ∨ MissingRouteStructure r := by
  cases d with
  | supported method => exact Or.inl method
  | noTransport missing => exact Or.inr missing

/-- Since `MissingRouteStructure` is uninhabited at every index, the projection
above always lands in the positive branch. -/
theorem routeDisposition_projection_is_positive
    (r : KO7Route) (d : RouteDisposition r) : KO7LicensedMethod r := by
  rcases routeDisposition_projection r d with hmethod | hmissing
  · exact hmethod
  · exact absurd hmissing (missingRouteStructure_uninhabited r)

/-- Every route projects to its positive licensed method on the current Lean
surface, because `ko7_route_disposition_total` dispositions all five tags
`supported`. -/
theorem routeDisposition_positive (r : KO7Route) : KO7LicensedMethod r :=
  ko7_every_route_licensed r

/-- The canonical disposition status of any dispositioned route is
`supported`. -/
theorem routeDisposition_canonical_status (r : KO7Route) :
    canonicalRouteStatus r = RouteStatus.supported :=
  routeDisposition_agrees_with_canonicalStatus r (ko7_route_disposition_total r)

end OperatorKO7.EscapeRouteExtractors
