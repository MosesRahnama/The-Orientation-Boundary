import OperatorKO7.Meta.EscapeTrichotomy
import OperatorKO7.Meta.PolyInterpretation_FullStep
import OperatorKO7.Meta.MPO_FullStep
import OperatorKO7.Meta.ConstructionRouteCatalog_Payload

set_option autoImplicit false

/-!
# Refined escape-route partition and the positive licensed-method universe

This module refines the KO7 direct barrier universe and adds a positive,
proof-carrying route universe. It does **not** strengthen the direct
observer theorem.

## What is refined

`KO7DirectBarrierRepresentable` (`Meta/EscapeTrichotomy.lean`) has fourteen
constructors. Ten of them index a `.nat` orienter (scalar payload
projections); four index the tracked-primary matrix orienters (imported
structural orders). This module splits those constructors into

* `KO7ScalarBarrierRepresentable`, and
* `KO7StructuralBarrierRepresentable`,

proves the exact partition equivalence
`ko7_barrier_partition`, proves the **actual** overlap result
`ko7_barrier_partition_disjoint` (disjointness is derived from the
orienter-constructor index, it is not assumed), and proves that orientation is
incompatible with each represented subfamily separately
(`no_orientation_of_scalar_barrier`, `no_orientation_of_structural_barrier`).

## What is NOT claimed

The genuine direct-observer result stays the **three-way** theorem: every
orienting observer in the explicit `KO7DirectOrienter` universe fails wrapper
sensitivity, fails base transparency, or is non-representable
(`ko7_direct_three_way_remains_universal`). The refined partition is bridged to
it by `ko7_direct_escape_trichotomy_refined` and
`ko7_refined_third_clause_iff_nonrepresentable`. There is **no** five-way
direct theorem in this file, and none is advertised anywhere in it.

## The positive route universe

`KO7Route` is a closed five-tag catalog. `KO7LicensedMethod r` is a positive,
proof-carrying method universe: each constructor stores the real success datum
of that route (a rank plus its orientation/violation theorems, the W2
transformed-call projection evidence, or the MPO precedence and
well-foundedness data). It has **no** NO-TRANSPORT constructor, and it never
stores a bare `KO7DirectOrienter.Orients`.

`RouteDisposition r` is separate: it either carries a `KO7LicensedMethod r` or
a closed indexed `MissingRouteStructure r`. It never carries a caller-selected
`Prop`. `MissingRouteStructure` has **no constructor at any index**, because
every one of the five indices is genuinely supported here; a premise-free
missing-route constructor would let a caller assert NO-TRANSPORT at an index
that is simultaneously licensed.

## The W2 transformed-call route is not a certified DP processor

The fourth tag is `w2TransformedCallProjection`, not a certified
dependency-pair route. Its stored evidence is
`TransformedCallClassification.PermittedW2Transform .ko7DPProjection
BenchmarkedPRCFamily.fullDuplicating`, whose transformed-call component
`HasTransformedCallWitness` unfolds to a strictly decreasing natural rank over
`BenchmarkedPRCFamily.FamilyCallStep`. It contains no complete all-rule
dependency-pair extraction, no SCC or processor soundness, no external
artifact identity, and no transport to source termination. The certified DP
processor is recorded as indexed NO-TRANSPORT in
`Meta/ClosedCarrierSemanticsAdapters.lean`
(`MissingAdapterStructure.noCompleteExtractionAndProcessorSoundness`), and no
declaration in this module uses certified-DP wording.

## Audit slots (Lean Development Bible W8 / R4)

```text
Relation:  OperatorKO7.Step (root single step) for the interpretation and path
           order routes; the KO7 duplicating rule instance for the
           sensitivity-violating projection route; the RecCore transformed-call
           relation for the payload-projection route.
Closure:   root. No contextual closure and no reflexive-transitive closure is
           claimed by any route datum in this file.
Strategy:  full rewriting. No innermost/outermost restriction is used.
Trust:     kernel-only. `Classical.choice` is inherited from
           `ko7_direct_escape_trichotomy_extended`, which is proved with the
           `classical` tactic; every theorem in this file that reduces to it
           carries that axiom. The route inhabitants do not.
Scope:     the explicit `KO7DirectOrienter` universe and the five named route
           carriers. No claim about arbitrary termination methods.
```
-/

namespace OperatorKO7.EscapeRouteRefined

open OperatorKO7
open OperatorKO7.Trace
open OperatorKO7.StepDuplicating
open OperatorKO7.CompositionalImpossibility
open OperatorKO7.MetaConjectureBoundary
open OperatorKO7.DepthBarrier
open OperatorKO7.PrecedenceBarrier
open OperatorKO7.EscapeTrichotomy

/-! ## 1. Scalar / structural split of the represented barrier universe -/

/--
Proves: the scalar half of `KO7DirectBarrierRepresentable`. Every constructor
  indexes a `.nat` orienter, i.e. a direct scalar projection of the duplicated
  payload.
Does not prove: that the represented orienter orients KO7; representability is
  a membership statement, not a success statement.
Relation: not a rewriting relation (a membership predicate on orienters).
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: the ten scalar constructors of `KO7DirectBarrierRepresentable`.
-/
inductive KO7ScalarBarrierRepresentable : KO7DirectOrienter → Prop
  | additive (M : AdditiveCompositionalMeasure) :
      KO7ScalarBarrierRepresentable (.nat M.eval)
  | compositionalTransparent (CM : CompositionalMeasure)
      (htransparent : CM.c_delta CM.c_void = CM.c_void) :
      KO7ScalarBarrierRepresentable (.nat CM.eval)
  | affineWithPump (M : StepDuplicatingSchema.AffineMeasureWithPump ko7Schema) :
      KO7ScalarBarrierRepresentable (.nat M.eval)
  | quadraticWithPump
      (M : StepDuplicatingSchema.QuadraticCounterMeasureWithPump ko7Schema) :
      KO7ScalarBarrierRepresentable (.nat M.eval)
  | crossQuadraticWithPump
      (M : StepDuplicatingSchema.CrossTermQuadraticMeasureWithPump ko7Schema) :
      KO7ScalarBarrierRepresentable (.nat M.eval)
  | multilinearWithPump
      (M : StepDuplicatingSchema.MultilinearMeasureWithPump ko7Schema) :
      KO7ScalarBarrierRepresentable (.nat M.eval)
  | polynomialWithPump
      (M : StepDuplicatingSchema.PolynomialMeasureWithPump ko7Schema) :
      KO7ScalarBarrierRepresentable (.nat M.eval)
  | maxWithPump
      (M : StepDuplicatingSchema.MaxMeasureWithPump ko7Schema) :
      KO7ScalarBarrierRepresentable (.nat M.eval)
  | depth (M : MaxDepthMeasure) :
      KO7ScalarBarrierRepresentable (.nat M.eval)
  | precedence (M : HeadPrecedenceFamily) :
      KO7ScalarBarrierRepresentable (.nat M.eval)

/--
Proves: the structural half of `KO7DirectBarrierRepresentable`. Every
  constructor indexes one of the tracked-primary matrix orienters, i.e. an
  imported structural order rather than a scalar payload projection.
Does not prove: that the represented orienter orients KO7.
Relation: not a rewriting relation (a membership predicate on orienters).
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: the four matrix constructors of `KO7DirectBarrierRepresentable`.
-/
inductive KO7StructuralBarrierRepresentable : KO7DirectOrienter → Prop
  | matrix2Componentwise
      (M : StepDuplicatingSchema.MatrixMeasure2WithPrimaryPump ko7Schema) :
      KO7StructuralBarrierRepresentable (.pairComponentwise M.eval)
  | matrix2Lex
      (M : StepDuplicatingSchema.MatrixMeasure2WithPrimaryPump ko7Schema) :
      KO7StructuralBarrierRepresentable (.pairLex M.eval)
  | matrixLexD {d : Nat}
      (M : StepDuplicatingSchema.MatrixLexMeasureDWithPrimaryPump ko7Schema d) :
      KO7StructuralBarrierRepresentable (.vecLex d M.eval)
  | matrixLexPerm {d : Nat}
      (M : StepDuplicatingSchema.MatrixLexPermMeasureDWithPrimaryPump ko7Schema d) :
      KO7StructuralBarrierRepresentable (.vecPermLex d M.priority M.eval)

/--
Proves: the **exact** partition equivalence. Representability in the extended
  KO7 direct universe holds precisely when the orienter is scalar-represented
  or structurally represented.
Does not prove: disjointness (that is `ko7_barrier_partition_disjoint`, proved
  separately and not assumed here).
Relation: not a rewriting relation.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: every `O : KO7DirectOrienter`.
-/
theorem ko7_barrier_partition (O : KO7DirectOrienter) :
    KO7DirectBarrierRepresentable O ↔
      (KO7ScalarBarrierRepresentable O ∨ KO7StructuralBarrierRepresentable O) := by
  constructor
  · intro hrepr
    cases hrepr with
    | additive M => exact Or.inl (.additive M)
    | compositionalTransparent CM htransparent =>
        exact Or.inl (.compositionalTransparent CM htransparent)
    | affineWithPump M => exact Or.inl (.affineWithPump M)
    | quadraticWithPump M => exact Or.inl (.quadraticWithPump M)
    | crossQuadraticWithPump M => exact Or.inl (.crossQuadraticWithPump M)
    | multilinearWithPump M => exact Or.inl (.multilinearWithPump M)
    | polynomialWithPump M => exact Or.inl (.polynomialWithPump M)
    | maxWithPump M => exact Or.inl (.maxWithPump M)
    | depth M => exact Or.inl (.depth M)
    | precedence M => exact Or.inl (.precedence M)
    | matrix2ComponentwiseWithPrimaryPump M => exact Or.inr (.matrix2Componentwise M)
    | matrix2LexWithPrimaryPump M => exact Or.inr (.matrix2Lex M)
    | matrixLexDWithPrimaryPump M => exact Or.inr (.matrixLexD M)
    | matrixLexPermWithPrimaryPump M => exact Or.inr (.matrixLexPerm M)
  · intro hsplit
    cases hsplit with
    | inl hscalar =>
        cases hscalar with
        | additive M => exact .additive M
        | compositionalTransparent CM htransparent =>
            exact .compositionalTransparent CM htransparent
        | affineWithPump M => exact .affineWithPump M
        | quadraticWithPump M => exact .quadraticWithPump M
        | crossQuadraticWithPump M => exact .crossQuadraticWithPump M
        | multilinearWithPump M => exact .multilinearWithPump M
        | polynomialWithPump M => exact .polynomialWithPump M
        | maxWithPump M => exact .maxWithPump M
        | depth M => exact .depth M
        | precedence M => exact .precedence M
    | inr hstructural =>
        cases hstructural with
        | matrix2Componentwise M => exact .matrix2ComponentwiseWithPrimaryPump M
        | matrix2Lex M => exact .matrix2LexWithPrimaryPump M
        | matrixLexD M => exact .matrixLexDWithPrimaryPump M
        | matrixLexPerm M => exact .matrixLexPermWithPrimaryPump M

/-- Every scalar-represented orienter is literally a `.nat` orienter. -/
theorem ko7_scalar_orienter_is_nat {O : KO7DirectOrienter}
    (h : KO7ScalarBarrierRepresentable O) :
    ∃ μ : Trace → Nat, O = KO7DirectOrienter.nat μ := by
  cases h with
  | additive M => exact ⟨M.eval, rfl⟩
  | compositionalTransparent CM _ => exact ⟨CM.eval, rfl⟩
  | affineWithPump M => exact ⟨M.eval, rfl⟩
  | quadraticWithPump M => exact ⟨M.eval, rfl⟩
  | crossQuadraticWithPump M => exact ⟨M.eval, rfl⟩
  | multilinearWithPump M => exact ⟨M.eval, rfl⟩
  | polynomialWithPump M => exact ⟨M.eval, rfl⟩
  | maxWithPump M => exact ⟨M.eval, rfl⟩
  | depth M => exact ⟨M.eval, rfl⟩
  | precedence M => exact ⟨M.eval, rfl⟩

/-- No structurally represented orienter is a `.nat` orienter. -/
theorem ko7_structural_orienter_not_nat {O : KO7DirectOrienter}
    (h : KO7StructuralBarrierRepresentable O) :
    ∀ μ : Trace → Nat, O ≠ KO7DirectOrienter.nat μ := by
  cases h with
  | matrix2Componentwise M => intro μ hEq; cases hEq
  | matrix2Lex M => intro μ hEq; cases hEq
  | matrixLexD M => intro μ hEq; cases hEq
  | matrixLexPerm M => intro μ hEq; cases hEq

/--
Proves: the **actual** overlap result. The two halves of the partition are
  disjoint, because scalar representability forces a `.nat` orienter index and
  structural representability forbids it. Disjointness is derived, not assumed.
Does not prove: that either half is inhabited at a given orienter.
Relation: not a rewriting relation.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only (constructor no-confusion only).
Scope: every `O : KO7DirectOrienter`.
-/
theorem ko7_barrier_partition_disjoint (O : KO7DirectOrienter) :
    ¬ (KO7ScalarBarrierRepresentable O ∧ KO7StructuralBarrierRepresentable O) := by
  rintro ⟨hscalar, hstructural⟩
  obtain ⟨μ, hμ⟩ := ko7_scalar_orienter_is_nat hscalar
  exact ko7_structural_orienter_not_nat hstructural μ hμ

/-! ## 2. Orientation is incompatible with each represented subfamily -/

/--
Proves: no scalar-represented orienter orients KO7, by cases on the
  representability proof. Each branch discharges the goal with the barrier
  theorem for that concrete family.
Does not prove: anything about orienters outside the represented universe.
Relation: `KO7DirectOrienter.Orients`, which unfolds to the root-step global
  orientation predicate of the indexed orienter.
Closure: root.
Strategy: full.
Trust: kernel-only.
Scope: the ten scalar barrier families.
-/
theorem no_orientation_of_scalar_barrier {O : KO7DirectOrienter}
    (h : KO7ScalarBarrierRepresentable O) : ¬ O.Orients := by
  cases h with
  | additive M => exact no_global_step_orientation_additive_compositional M
  | compositionalTransparent CM htransparent =>
      exact no_global_step_orientation_compositional_transparent_delta CM htransparent
  | affineWithPump M =>
      exact PumpedBarrierClasses.no_global_step_orientation_affine_with_pump M
  | quadraticWithPump M =>
      exact PumpedBarrierClasses.no_global_step_orientation_quadratic_with_pump M
  | crossQuadraticWithPump M =>
      exact PumpedBarrierClasses.no_global_step_orientation_cross_quadratic_with_pump M
  | multilinearWithPump M =>
      exact PumpedBarrierClasses.no_global_step_orientation_multilinear_with_pump M
  | polynomialWithPump M =>
      exact PumpedBarrierClasses.no_global_step_orientation_polynomial_with_pump M
  | maxWithPump M =>
      exact PumpedBarrierClasses.no_global_step_orientation_max_with_pump M
  | depth M => exact no_global_step_orientation_maxDepth M
  | precedence M => exact no_global_step_orientation_headPrecedenceFamily M

/--
Proves: no structurally represented orienter orients KO7, by cases on the
  representability proof.
Does not prove: anything about structural orders outside the four tracked
  matrix families.
Relation: `KO7DirectOrienter.Orients`.
Closure: root.
Strategy: full.
Trust: kernel-only.
Scope: the four tracked-primary matrix families.
-/
theorem no_orientation_of_structural_barrier {O : KO7DirectOrienter}
    (h : KO7StructuralBarrierRepresentable O) : ¬ O.Orients := by
  cases h with
  | matrix2Componentwise M =>
      exact PumpedBarrierClasses.no_global_step_orientation_matrix2_with_primary_pump M
  | matrix2Lex M =>
      exact PumpedBarrierClasses.no_global_step_orientation_matrix2_lex_with_primary_pump M
  | matrixLexD M =>
      exact
        OperatorKO7.MatrixBarrierLexD.no_global_step_orientation_matrixLexD_with_primary_pump M
  | matrixLexPerm M =>
      exact
        OperatorKO7.MatrixBarrierLexPermD.no_global_step_orientation_matrixLexPermD_with_primary_pump
          M

/-- Combined incompatibility over the whole represented universe. -/
theorem no_orientation_of_represented_barrier {O : KO7DirectOrienter}
    (h : KO7DirectBarrierRepresentable O) : ¬ O.Orients := by
  rcases (ko7_barrier_partition O).1 h with hscalar | hstructural
  · exact no_orientation_of_scalar_barrier hscalar
  · exact no_orientation_of_structural_barrier hstructural

/-! ## 3. Bridge to the retained three-way direct-observer theorem -/

/--
Proves: the genuine direct-observer result, retained verbatim as the
  **three-way** disjunction. This is the strongest universal statement about
  direct orienters in this development.
Does not prove: a five-way direct theorem. None is claimed anywhere.
Relation: `KO7DirectOrienter.Orients`.
Closure: root.
Strategy: full.
Trust: kernel-only plus `Classical.choice` (inherited from the `classical`
  tactic inside `ko7_direct_escape_trichotomy_extended`).
Scope: the explicit `KO7DirectOrienter` universe.
-/
theorem ko7_direct_three_way_remains_universal {O : KO7DirectOrienter}
    (horient : O.Orients) :
    ¬ StepDuplicatingSchema.WrapSubtermSensitive ko7Schema O.primaryScalar ∨
      ¬ StepDuplicatingSchema.TransparentAtBase ko7Schema O.primaryScalar ∨
      ¬ KO7DirectBarrierRepresentable O :=
  ko7_direct_escape_trichotomy_extended (O := O) horient

/-- The refined third clause is exactly the legacy non-representability clause. -/
theorem ko7_refined_third_clause_iff_nonrepresentable (O : KO7DirectOrienter) :
    (¬ KO7ScalarBarrierRepresentable O ∧ ¬ KO7StructuralBarrierRepresentable O) ↔
      ¬ KO7DirectBarrierRepresentable O := by
  constructor
  · rintro ⟨hscalar, hstructural⟩ hrepr
    rcases (ko7_barrier_partition O).1 hrepr with h | h
    · exact hscalar h
    · exact hstructural h
  · intro hnon
    exact ⟨fun hscalar => hnon ((ko7_barrier_partition O).2 (Or.inl hscalar)),
      fun hstructural => hnon ((ko7_barrier_partition O).2 (Or.inr hstructural))⟩

/--
Proves: the refined restatement of the retained three-way theorem, with the
  non-representability clause split along the proved partition. It is a
  restatement, not a strengthening: `ko7_refined_third_clause_iff_nonrepresentable`
  shows the third clause is equivalent to the legacy one.
Does not prove: a five-way direct disjunction.
Relation: `KO7DirectOrienter.Orients`.
Closure: root.
Strategy: full.
Trust: kernel-only plus inherited `Classical.choice`.
Scope: the explicit `KO7DirectOrienter` universe.
-/
theorem ko7_direct_escape_trichotomy_refined {O : KO7DirectOrienter}
    (horient : O.Orients) :
    ¬ StepDuplicatingSchema.WrapSubtermSensitive ko7Schema O.primaryScalar ∨
      ¬ StepDuplicatingSchema.TransparentAtBase ko7Schema O.primaryScalar ∨
      (¬ KO7ScalarBarrierRepresentable O ∧ ¬ KO7StructuralBarrierRepresentable O) := by
  rcases ko7_direct_three_way_remains_universal (O := O) horient with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ((ko7_refined_third_clause_iff_nonrepresentable O).2 h))

/-! ## 4. Carrier-level facts used by the positive route universe -/

/-- The KO7 DP counter projection genuinely fails wrapper-subterm sensitivity.
The negative universal statement is returned as-is; no witness pair is
extracted from it. -/
theorem dpProjection_violates_wrapSubtermSensitive :
    ¬ StepDuplicatingSchema.WrapSubtermSensitive ko7Schema dpProjection := by
  intro hsensitive
  obtain ⟨x, y, hviolate⟩ := dp_projection_violates_sensitivity
  exact hviolate (hsensitive x y).1

/-- The nonlinear polynomial interpretation `W` **is** wrapper-subterm
sensitive: both `app` arguments are strictly below the wrapped term. -/
theorem poly_wrapSubtermSensitive :
    StepDuplicatingSchema.WrapSubtermSensitive ko7Schema PolyInterpretation.W := by
  intro x y
  have hx := PolyInterpretation.W_pos x
  have hy := PolyInterpretation.W_pos y
  refine ⟨?_, ?_⟩
  · show PolyInterpretation.W x < PolyInterpretation.W (app x y)
    simp only [PolyInterpretation.W]
    omega
  · show PolyInterpretation.W y < PolyInterpretation.W (app x y)
    simp only [PolyInterpretation.W]
    omega

/-! ## 5. Closed five-tag route catalog and the positive licensed universe -/

/--
Proves: the closed five-tag KO7 route catalog.
Does not prove: that the tags are semantically disjoint. Constructor
  disequality gives catalog separation only; see section 7.
Relation: closed enum.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: exactly five tags.
-/
inductive KO7Route where
  /-- A rank that orients the duplicating rule by failing wrapper sensitivity. -/
  | sensitivityViolatingProjection
  /-- A full root-step interpretation that fails base transparency. -/
  | transparencyViolatingInterpretation
  /-- A full root-step interpretation with genuine cross-variable coupling. -/
  | crossCoupledInterpretation
  /-- The W2 transformed-call projection route. This is a decreasing natural
  rank over `FamilyCallStep` plus the absence of a direct whole-term witness.
  It is deliberately **not** a certified dependency-pair processor. -/
  | w2TransformedCallProjection
  /-- The specialized MPO structural path order. -/
  | structuralPathOrder
  deriving DecidableEq, Repr

/--
Proves: the positive, proof-carrying licensed-method universe. Each constructor
  stores the concrete success datum of its route: an actual rank or relation
  plus the theorems that make it that route's method, never a bare
  `KO7DirectOrienter.Orients`.
Does not prove: that a licensed method at one tag is not a licensed method at
  another tag. There is deliberately **no** NO-TRANSPORT constructor here; the
  no-transport branch lives in `RouteDisposition`.
Relation: `OperatorKO7.Step` (root single step) for the interpretation and path
  order routes; the duplicating rule instance for the sensitivity-violating
  projection route; `BenchmarkedPRCFamily.FamilyCallStep` for the W2
  transformed-call projection route.
Closure: root.
Strategy: full.
Trust: kernel-only.
Scope: five route indices.
-/
inductive KO7LicensedMethod : KO7Route → Prop
  /-- Success datum: a rank that strictly orients the KO7 duplicating rule and
  provably fails wrapper-subterm sensitivity on `ko7Schema`. The orientation
  scope is the duplicating rule instance, not full `Step`. -/
  | sensitivityViolatingProjection
      (rank : Trace → Nat)
      (orientsDuplicatingRule :
        ∀ b s n : Trace,
          rank (app s (recΔ b s n)) < rank (recΔ b s (delta n)))
      (violatesWrapSensitivity :
        ¬ StepDuplicatingSchema.WrapSubtermSensitive ko7Schema rank) :
      KO7LicensedMethod .sensitivityViolatingProjection
  /-- Success datum: an interpretation that strictly orients every root `Step`,
  **is** wrapper-subterm sensitive, and fails base-level successor
  transparency. The sensitivity field is required so this route cannot be
  inhabited by a sensitivity-violating projection in disguise. -/
  | transparencyViolatingInterpretation
      (μ : Trace → Nat)
      (orientsStep : ∀ {a b : Trace}, Step a b → μ b < μ a)
      (wrapSensitive : StepDuplicatingSchema.WrapSubtermSensitive ko7Schema μ)
      (violatesTransparency :
        ¬ StepDuplicatingSchema.TransparentAtBase ko7Schema μ) :
      KO7LicensedMethod .transparencyViolatingInterpretation
  /-- Success datum: an interpretation that strictly orients every root `Step`
  and whose recursor value is neither the additive nor the affine combination
  of its argument values, i.e. genuine cross-variable coupling. -/
  | crossCoupledInterpretation
      (μ : Trace → Nat)
      (orientsStep : ∀ {a b : Trace}, Step a b → μ b < μ a)
      (notAdditive :
        ¬ ∃ c : Nat, ∀ b s n : Trace,
          μ (recΔ b s n) = c + μ b + μ s + μ n)
      (notAffine :
        ¬ ∃ α β γ δr : Nat, ∀ b s n : Trace,
          μ (recΔ b s n) = α + β * μ b + γ * μ s + δr * μ n) :
      KO7LicensedMethod .crossCoupledInterpretation
  /-- Success datum: the W2 transformed-call projection evidence for the
  duplicating benchmark member, together with the refutation of a direct
  whole-term witness for the same member. The stored `PermittedW2Transform`
  value carries the RecCore projection-route inequality and the
  transformed-call witness, and `HasTransformedCallWitness` is a strictly
  decreasing natural rank over `FamilyCallStep`.

  Not carried, and therefore not claimed: complete all-rule dependency-pair
  extraction, SCC or processor soundness, external artifact identity, and
  transport to source termination. This route is not a certified DP
  processor. -/
  | w2TransformedCallProjection
      (transform :
        TransformedCallClassification.PermittedW2Transform
          .ko7DPProjection BenchmarkedPRCFamily.fullDuplicating)
      (notDirect :
        ¬ BenchmarkedPRCFamily.HasDirectWitness BenchmarkedPRCFamily.fullDuplicating) :
      KO7LicensedMethod .w2TransformedCallProjection
  /-- Success datum: the specialized KO7 MPO structural order, carrying the
  strict precedence comparison used by the recursor-step clause, the
  orientation of every root `Step`, and well-foundedness of the reversed
  path order. -/
  | structuralPathOrder
      (recursorStepPrecedence : MetaMPO.symPrec MetaMPO.Sym.app MetaMPO.Sym.recΔ)
      (orientsStep : ∀ {a b : Trace}, Step a b → MetaMPO.MPO a b)
      (pathOrderWellFounded : WellFounded MetaMPO.MPORev) :
      KO7LicensedMethod .structuralPathOrder

/-! ### Route inhabitants (NameGate/TypeGate targets constructed) -/

/-- The sensitivity-violating projection route is inhabited by the KO7 DP
counter projection. Only a real sensitivity violation licenses this route. -/
theorem ko7_licensed_sensitivityViolatingProjection :
    KO7LicensedMethod .sensitivityViolatingProjection :=
  .sensitivityViolatingProjection dpProjection
    dp_projection_orients_rec_succ
    dpProjection_violates_wrapSubtermSensitive

/-- The transparency-violating interpretation route is inhabited by the
nonlinear polynomial interpretation `W`. -/
theorem ko7_licensed_transparencyViolatingInterpretation :
    KO7LicensedMethod .transparencyViolatingInterpretation :=
  .transparencyViolatingInterpretation PolyInterpretation.W
    PolyInterpretation.W_orients_step
    poly_wrapSubtermSensitive
    ConstructionMethodClassification.poly_not_transparent_at_base

/-- The cross-coupled interpretation route is inhabited by the same nonlinear
polynomial interpretation `W`, using its non-additivity and non-affinity. -/
theorem ko7_licensed_crossCoupledInterpretation :
    KO7LicensedMethod .crossCoupledInterpretation :=
  .crossCoupledInterpretation PolyInterpretation.W
    PolyInterpretation.W_orients_step
    PolyInterpretation.W_not_additive
    PolyInterpretation.W_not_affine

/-- The W2 transformed-call projection route is inhabited by the duplicating
benchmark member's W2 transformed-call evidence. No certified DP processor
claim is attached to it. -/
theorem ko7_licensed_w2TransformedCallProjection :
    KO7LicensedMethod .w2TransformedCallProjection :=
  .w2TransformedCallProjection
    TransformedCallClassification.fullDuplicating_w2_success_requires_ko7_dp_projection
    BenchmarkedPRCFamily.fullDuplicating_has_no_direct_witness

/-- The structural path-order route is inhabited by the KO7 MPO witness. -/
theorem ko7_licensed_structuralPathOrder :
    KO7LicensedMethod .structuralPathOrder :=
  .structuralPathOrder
    ConstructionMethodClassification.mpo_recursor_step_precedence_holds
    MetaMPO.mpo_orients_step
    MetaMPO.wf_MPORev

/-- Every one of the five route indices is inhabited by a real method. -/
theorem ko7_every_route_licensed (r : KO7Route) : KO7LicensedMethod r := by
  cases r with
  | sensitivityViolatingProjection =>
      exact ko7_licensed_sensitivityViolatingProjection
  | transparencyViolatingInterpretation =>
      exact ko7_licensed_transparencyViolatingInterpretation
  | crossCoupledInterpretation =>
      exact ko7_licensed_crossCoupledInterpretation
  | w2TransformedCallProjection =>
      exact ko7_licensed_w2TransformedCallProjection
  | structuralPathOrder =>
      exact ko7_licensed_structuralPathOrder

/-! ## 6. Route dispositions -/

/--
Proves: the closed indexed record of missing route structure. It has **no
  constructor at any index**. That is the exact current state: all five route
  indices are inhabited in the positive licensed universe, so there is no
  unsupported index at which a missing-route record could legitimately exist.
  A premise-free constructor here would let a caller assert NO-TRANSPORT at an
  index that is simultaneously licensed, which is precisely the contradiction
  this design forbids.
Does not prove: that no route can ever become unsupported. If a future route
  loses its witness, a constructor is added at that index only.
Relation: closed indexed family.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: five route indices, none of them inhabited here.
-/
inductive MissingRouteStructure : KO7Route → Prop

/-- The missing-route family is uninhabited at every index. -/
theorem missingRouteStructure_uninhabited (r : KO7Route) :
    ¬ MissingRouteStructure r := by
  intro hmissing
  cases hmissing

/-- No route can be simultaneously licensed and missing. -/
theorem route_not_licensed_and_missing (r : KO7Route) :
    ¬ (KO7LicensedMethod r ∧ MissingRouteStructure r) :=
  fun hboth => missingRouteStructure_uninhabited r hboth.2

/--
Proves: the two-valued disposition status.
Does not prove: which status a route has; that is `canonicalRouteStatus`.
Relation: closed enum.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: two constants.
-/
inductive RouteStatus where
  | supported
  | noTransport
  deriving DecidableEq, Repr

/--
Proves: the closed canonical disposition function. It is total and computed by
  constructor index. It is not caller-selected and it is not metadata attached
  to a row.
Does not prove: by itself, that the status is correct; the correctness is
  `canonicalRouteStatus_supported_iff` and
  `canonicalRouteStatus_noTransport_iff`.
Relation: closed enum function.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: five route indices.
-/
def canonicalRouteStatus : KO7Route → RouteStatus
  | .sensitivityViolatingProjection => .supported
  | .transparencyViolatingInterpretation => .supported
  | .crossCoupledInterpretation => .supported
  | .w2TransformedCallProjection => .supported
  | .structuralPathOrder => .supported

/-- Boolean view of the canonical disposition, used to derive the supported and
unsupported sublists by filtering. -/
def routeIsSupported (r : KO7Route) : Bool :=
  match canonicalRouteStatus r with
  | .supported => true
  | .noTransport => false

/-- Supported characterization: the canonical status is `supported` exactly
when the positive licensed universe is inhabited at that index. -/
theorem canonicalRouteStatus_supported_iff (r : KO7Route) :
    canonicalRouteStatus r = RouteStatus.supported ↔ KO7LicensedMethod r := by
  constructor
  · intro _
    exact ko7_every_route_licensed r
  · intro _
    cases r <;> rfl

/-- Unsupported characterization: the canonical status is `noTransport` exactly
when the missing-route family is inhabited at that index. Both sides are
uninhabited, and that agreement is the point. -/
theorem canonicalRouteStatus_noTransport_iff (r : KO7Route) :
    canonicalRouteStatus r = RouteStatus.noTransport ↔ MissingRouteStructure r := by
  constructor
  · intro hstatus
    exact absurd hstatus (by cases r <;> decide)
  · intro hmissing
    exact absurd hmissing (missingRouteStructure_uninhabited r)

/-- The Boolean view agrees with the licensed universe. -/
theorem routeIsSupported_iff_licensed (r : KO7Route) :
    routeIsSupported r = true ↔ KO7LicensedMethod r := by
  constructor
  · intro _
    exact ko7_every_route_licensed r
  · intro _
    cases r <;> rfl

/--
Proves: the indexed disposition of a route. The supported branch carries a
  positive `KO7LicensedMethod`; the NO-TRANSPORT branch carries the closed
  indexed `MissingRouteStructure`. No branch accepts an arbitrary `Prop`, and
  by `route_not_licensed_and_missing` the two branches cannot both apply.
Does not prove: that a disposition proof is unique as a term.
Relation: closed indexed family.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: five route indices.
-/
inductive RouteDisposition : KO7Route → Prop
  | supported {r : KO7Route} (method : KO7LicensedMethod r) : RouteDisposition r
  | noTransport {r : KO7Route} (missing : MissingRouteStructure r) : RouteDisposition r

/-- Total disposition over all five tags, produced by the canonical function. -/
theorem ko7_route_disposition_total (r : KO7Route) : RouteDisposition r :=
  .supported (ko7_every_route_licensed r)

/-- A disposition projects back to the canonical status. -/
theorem routeDisposition_agrees_with_canonicalStatus
    (r : KO7Route) (d : RouteDisposition r) :
    canonicalRouteStatus r = RouteStatus.supported := by
  cases d with
  | supported method => exact (canonicalRouteStatus_supported_iff r).2 method
  | noTransport missing =>
      exact absurd missing (missingRouteStructure_uninhabited r)

/-! ## 7. Supported subset, counts, and separation discipline -/

/-- The closed five-tag route catalog as a list. -/
def allKO7Routes : List KO7Route :=
  [ .sensitivityViolatingProjection,
    .transparencyViolatingInterpretation,
    .crossCoupledInterpretation,
    .w2TransformedCallProjection,
    .structuralPathOrder ]

/-- The supported subset, **derived** by filtering the catalog with the closed
canonical disposition function. It is not asserted as a literal. -/
def supportedRoutes : List KO7Route := allKO7Routes.filter routeIsSupported

/-- The unsupported subset, the exact complement of `supportedRoutes` under the
same canonical function. -/
def unsupportedRoutes : List KO7Route :=
  allKO7Routes.filter (fun r => ! routeIsSupported r)

theorem allKO7Routes_length : allKO7Routes.length = 5 := rfl

theorem allKO7Routes_nodup : allKO7Routes.Nodup := by decide

/-- The catalog list is total over the closed tag type. -/
theorem mem_allKO7Routes (r : KO7Route) : r ∈ allKO7Routes := by
  cases r <;> decide

/-- The derived supported subset is the whole catalog, computed rather than
declared. -/
theorem supportedRoutes_eq_all : supportedRoutes = allKO7Routes := by decide

/-- The derived unsupported subset is empty. -/
theorem unsupportedRoutes_eq_nil : unsupportedRoutes = [] := by decide

/-- Coverage is proved only over the positive licensed universe. -/
theorem ko7_supportedRoutes_iff_licensed (r : KO7Route) :
    r ∈ supportedRoutes ↔ KO7LicensedMethod r := by
  constructor
  · intro _
    exact ko7_every_route_licensed r
  · intro _
    cases r <;> decide

/-- Membership in the unsupported subset is exactly missing-route structure. -/
theorem ko7_unsupportedRoutes_iff_missing (r : KO7Route) :
    r ∈ unsupportedRoutes ↔ MissingRouteStructure r := by
  constructor
  · intro hmem
    rw [unsupportedRoutes_eq_nil] at hmem
    simp at hmem
  · intro hmissing
    exact absurd hmissing (missingRouteStructure_uninhabited r)

/-- Supported and unsupported subsets are disjoint. -/
theorem ko7_route_subsets_disjoint :
    ∀ r ∈ supportedRoutes, r ∉ unsupportedRoutes := by decide

/-- Supported and unsupported subsets together permute the whole catalog. -/
theorem ko7_route_subsets_partition_perm :
    (supportedRoutes ++ unsupportedRoutes).Perm allKO7Routes :=
  List.filter_append_perm routeIsSupported allKO7Routes

/-- The supported subset is non-empty. -/
theorem ko7_supportedRoutes_nonempty : 0 < supportedRoutes.length := by decide

/-- Exact supported count. -/
theorem ko7_supportedRoutes_length : supportedRoutes.length = 5 := by decide

/-- Exact unsupported count. -/
theorem ko7_unsupportedRoutes_length : unsupportedRoutes.length = 0 := by decide

/-- Exact split of the five-tag catalog. -/
theorem ko7_route_split_total :
    supportedRoutes.length + unsupportedRoutes.length = 5 := by decide

/-- Explicit inhabitant of the positive licensed universe. -/
theorem ko7_structuralPathOrder_inhabits_licensed_universe :
    KO7LicensedMethod KO7Route.structuralPathOrder :=
  ko7_licensed_structuralPathOrder

/--
Proves: **catalog** separation only. Distinct constructors of `KO7Route` are
  distinct tags.
Does not prove: that the methods licensed at distinct tags are semantically
  distinct. Two tags may be inhabited by the same carrier; see
  `ko7_transparency_and_crossCoupling_share_carrier`.
Relation: closed enum.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only (`decide`).
Scope: syntactic tag separation.
-/
theorem ko7_route_tag_separation_is_syntactic_only : allKO7Routes.Nodup :=
  allKO7Routes_nodup

/--
Proves: a genuine **semantic** separation. The sensitivity-violating route's
  carrier provably fails wrapper-subterm sensitivity, while the
  transparency/cross-coupling routes' carrier provably satisfies it, so the two
  carriers cannot be exchanged.
Does not prove: separation of the route tags in general.
Relation: `ko7Schema` wrapper-subterm sensitivity.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: the two named carriers `dpProjection` and `PolyInterpretation.W`.
-/
theorem ko7_sensitivity_carrier_semantically_separated_from_interpretation_carrier :
    ¬ StepDuplicatingSchema.WrapSubtermSensitive ko7Schema dpProjection ∧
      StepDuplicatingSchema.WrapSubtermSensitive ko7Schema PolyInterpretation.W :=
  ⟨dpProjection_violates_wrapSubtermSensitive, poly_wrapSubtermSensitive⟩

/--
Proves: a genuine **semantic** separation for the W2 transformed-call route:
  the duplicating benchmark member has a transformed-call witness and provably
  has no direct whole-term witness.
Does not prove: that the W2 transformed-call route is disjoint from the other
  four tags, and nothing about dependency-pair processor soundness.
Relation: benchmark-family witness predicates over `FamilyCallStep`.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: `BenchmarkedPRCFamily.fullDuplicating`.
-/
theorem ko7_w2TransformedCall_carrier_separated_from_direct_search :
    BenchmarkedPRCFamily.HasTransformedCallWitness BenchmarkedPRCFamily.fullDuplicating ∧
      ¬ BenchmarkedPRCFamily.HasDirectWitness BenchmarkedPRCFamily.fullDuplicating :=
  ⟨BenchmarkedPRCFamily.fullDuplicating_has_transformed_call_witness,
    BenchmarkedPRCFamily.fullDuplicating_has_no_direct_witness⟩

/--
Proves: the transparency-violating and cross-coupled routes are **both**
  inhabited by the same carrier `PolyInterpretation.W`. Their tags are
  therefore separated at the catalog level only, and no semantic-disjointness
  claim is made between them. The structural path-order tag likewise carries no
  semantic-disjointness claim against the interpretation tags.
Does not prove: any disjointness.
Relation: `OperatorKO7.Step` (root single step).
Closure: root.
Strategy: full.
Trust: kernel-only.
Scope: the two named tags.
-/
theorem ko7_transparency_and_crossCoupling_share_carrier :
    KO7LicensedMethod .transparencyViolatingInterpretation ∧
      KO7LicensedMethod .crossCoupledInterpretation :=
  ⟨ko7_licensed_transparencyViolatingInterpretation,
    ko7_licensed_crossCoupledInterpretation⟩

/--
Proves: the retained direct three-way theorem remains the stronger universal
  statement for direct orienters, alongside the refined partition and the
  proved partition disjointness. The route catalog is a separate positive
  object and adds no direct-observer disjunct.
Does not prove: a five-way direct theorem.
Relation: `KO7DirectOrienter.Orients`.
Closure: root.
Strategy: full.
Trust: kernel-only plus inherited `Classical.choice`.
Scope: the explicit `KO7DirectOrienter` universe.
-/
theorem ko7_refined_escape_route_closure :
    (∀ O : KO7DirectOrienter, O.Orients →
        ¬ StepDuplicatingSchema.WrapSubtermSensitive ko7Schema O.primaryScalar ∨
          ¬ StepDuplicatingSchema.TransparentAtBase ko7Schema O.primaryScalar ∨
          ¬ KO7DirectBarrierRepresentable O) ∧
      (∀ O : KO7DirectOrienter,
        KO7DirectBarrierRepresentable O ↔
          (KO7ScalarBarrierRepresentable O ∨ KO7StructuralBarrierRepresentable O)) ∧
      (∀ O : KO7DirectOrienter,
        ¬ (KO7ScalarBarrierRepresentable O ∧ KO7StructuralBarrierRepresentable O)) ∧
      (∀ r : KO7Route, RouteDisposition r) ∧
      (∀ r : KO7Route, ¬ (KO7LicensedMethod r ∧ MissingRouteStructure r)) ∧
      (∀ r : KO7Route, r ∈ supportedRoutes ↔ KO7LicensedMethod r) ∧
      (∀ r : KO7Route, r ∈ unsupportedRoutes ↔ MissingRouteStructure r) ∧
      (supportedRoutes ++ unsupportedRoutes).Perm allKO7Routes ∧
      supportedRoutes.length = 5 ∧
      unsupportedRoutes.length = 0 :=
  ⟨fun O horient => ko7_direct_three_way_remains_universal (O := O) horient,
    ko7_barrier_partition,
    ko7_barrier_partition_disjoint,
    ko7_route_disposition_total,
    route_not_licensed_and_missing,
    ko7_supportedRoutes_iff_licensed,
    ko7_unsupportedRoutes_iff_missing,
    ko7_route_subsets_partition_perm,
    ko7_supportedRoutes_length,
    ko7_unsupportedRoutes_length⟩

end OperatorKO7.EscapeRouteRefined
