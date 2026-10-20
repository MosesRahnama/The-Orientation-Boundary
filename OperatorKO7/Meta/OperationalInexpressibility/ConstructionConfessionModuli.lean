import OperatorKO7.Meta.PolyInterpretation_Family
import OperatorKO7.Meta.ConfessionMethod_UniversalInstances
import OperatorKO7.Meta.ScopeBoundaryWitnesses

/-!
# Construction and confession moduli for the KO7 recursor

Relation: the full eight-rule root relation `Step` and the extracted KO7
dependency-pair relation.
Closure: root, one step.
Strategy: root-only.
Trust: kernel-checked mathematics plus the foundational quotient principles
reported by the paired reach file.

The construction side remembers the complete strict order induced on all
terms. Its quotient contains infinitely many classes represented by positive
members of `Wam`. The confession side starts from four independently defined
route-evidence objects: dependency pairs, direct counter projection,
size-change termination, and argument filtering. Only after those objects have
been constructed do the theorems prove that their retained ranks factor through
the same counter projection. Their full-order quotient therefore has exactly
one class, even though the route origins and license metadata remain distinct.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.OperationalInexpressibility.ConstructionConfessionModuli

open OperatorKO7
open OperatorKO7.Trace
open OperatorKO7.CompositionalImpossibility
open OperatorKO7.ConfessionMethodFamily
open OperatorKO7.Meta.ConfessionMethodUniversalInstances
open OperatorKO7.PolyInterpretation.Family
open OperatorKO7.ScopeBoundaryWitnesses

/-! ## Independently constructed confession presentations -/

/-- The four method presentations whose concrete adapters are already
formalized. This is a closed index, not a claim about every termination method. -/
inductive ConfessionRoute
  | dependencyPairs
  | directCounterProjection
  | sizeChange
  | argumentFiltering
  deriving DecidableEq, Repr, Fintype

/-- The route-local evidence type belonging to each method presentation. -/
def ConfessionRoute.Evidence : ConfessionRoute → Type
  | .dependencyPairs => DPRouteEvidence
  | .directCounterProjection => DirectCounterProjectionRouteEvidence
  | .sizeChange => SCTRouteEvidence
  | .argumentFiltering => ArgumentFilteringRouteEvidence

/-- The concrete evidence constructed by the module devoted to each route. -/
def confessionRouteEvidence : (r : ConfessionRoute) → r.Evidence
  | .dependencyPairs => schemaDPRouteEvidence
  | .directCounterProjection => schemaDirectCounterProjectionRouteEvidence
  | .sizeChange => schemaSCTRouteEvidence
  | .argumentFiltering => schemaArgumentFilteringRouteEvidence

/-- Forget route-specific evidence only after the concrete evidence exists. -/
def ConfessionRoute.toGenericRouteEvidence :
    (r : ConfessionRoute) → r.Evidence →
      OperatorKO7.StepDuplicating.StepDuplicatingSchema.RouteEvidence ko7Schema
  | .dependencyPairs, E => E.toRouteEvidence
  | .directCounterProjection, E => E.toRouteEvidence
  | .sizeChange, E => E.toRouteEvidence
  | .argumentFiltering, E => E.toRouteEvidence

/-- Generic evidence obtained from the concrete route-local construction. -/
def canonicalGenericRouteEvidence (r : ConfessionRoute) :
    OperatorKO7.StepDuplicating.StepDuplicatingSchema.RouteEvidence ko7Schema :=
  r.toGenericRouteEvidence (confessionRouteEvidence r)

/-- The concrete confession method associated with a route. -/
def confessionRouteMethod : ConfessionRoute → ConfessionMethod ko7Schema
  | .dependencyPairs => dpConfession
  | .directCounterProjection => counterProjectionConfession
  | .sizeChange => sctConfession
  | .argumentFiltering => argumentFilteringConfession

/-- The retained rank is read from the concrete route evidence, not supplied
as a common-core field. -/
def confessionRouteRank (r : ConfessionRoute) : Trace → Nat :=
  (canonicalGenericRouteEvidence r).rank

/-- Every concrete evidence adapter agrees with its independently constructed
method package. -/
theorem confessionRouteEvidence_rank_eq_method (r : ConfessionRoute) :
    confessionRouteRank r = (confessionRouteMethod r).rank := by
  cases r with
  | dependencyPairs => exact dpRouteEvidence_rank_eq_dpConfession
  | directCounterProjection =>
      exact counterProjectionRouteEvidence_rank_eq_counterProjectionConfession
  | sizeChange => exact sctRouteEvidence_rank_eq_sctConfession
  | argumentFiltering =>
      exact argumentFilteringRouteEvidence_rank_eq_argumentFilteringConfession

/-- The common semantic core is a derived theorem: every concrete route
retains exactly `dpProjection`. -/
theorem confessionRouteRank_eq_dpProjection (r : ConfessionRoute) :
    confessionRouteRank r = dpProjection := by
  rw [confessionRouteEvidence_rank_eq_method]
  cases r with
  | dependencyPairs => rfl
  | directCounterProjection =>
      exact counterProjection_eq_dp_rank
  | sizeChange => exact sct_eq_dp_rank
  | argumentFiltering => exact argumentFiltering_eq_dp_rank

/-- The four closed origins are non-vacuous and exhaustive. -/
theorem confessionRoute_card : Fintype.card ConfessionRoute = 4 := by
  decide

/-- License metadata is obtained from the actual method package. -/
def confessionRouteLicense (r : ConfessionRoute) : SoundnessLicense :=
  (confessionRouteMethod r).license

/-- The four route origins and their four license tags correspond exactly. -/
def confessionRouteLicenseEquiv : ConfessionRoute ≃ SoundnessLicense where
  toFun := confessionRouteLicense
  invFun
    | .artsGiesl2000 => .dependencyPairs
    | .subtermCriterionDirect => .directCounterProjection
    | .leeJonesBenAmram2001 => .sizeChange
    | .argumentFilteringSoundness => .argumentFiltering
  left_inv := by
    intro r
    cases r <;> rfl
  right_inv := by
    intro l
    cases l <;> rfl

/-- Distinct DP and SCT origins retain the same rank while carrying different
license metadata. -/
theorem dp_sct_distinct_origin_same_rank :
    ConfessionRoute.dependencyPairs ≠ ConfessionRoute.sizeChange
      ∧ confessionRouteLicense .dependencyPairs ≠ confessionRouteLicense .sizeChange
      ∧ confessionRouteRank .dependencyPairs = confessionRouteRank .sizeChange := by
  refine ⟨by decide, by decide, ?_⟩
  rw [confessionRouteRank_eq_dpProjection, confessionRouteRank_eq_dpProjection]

/-! ## Exact confession quotient -/

/-- Two concrete route presentations are equivalent when their retained ranks
induce the same strict comparison on every pair of terms. -/
def SameConfessionFullOrder (r s : ConfessionRoute) : Prop :=
  SameFullOrder (confessionRouteRank r) (confessionRouteRank s)

theorem sameConfessionFullOrder_refl (r : ConfessionRoute) :
    SameConfessionFullOrder r r :=
  sameFullOrder_refl _

theorem sameConfessionFullOrder_symm {r s : ConfessionRoute}
    (h : SameConfessionFullOrder r s) : SameConfessionFullOrder s r :=
  sameFullOrder_symm h

theorem sameConfessionFullOrder_trans {r s t : ConfessionRoute}
    (hrs : SameConfessionFullOrder r s)
    (hst : SameConfessionFullOrder s t) : SameConfessionFullOrder r t :=
  sameFullOrder_trans hrs hst

def confessionFullOrderSetoid : Setoid ConfessionRoute where
  r := SameConfessionFullOrder
  iseqv := ⟨sameConfessionFullOrder_refl, sameConfessionFullOrder_symm,
    sameConfessionFullOrder_trans⟩

abbrev ConfessionFullOrderQuotient := Quotient confessionFullOrderSetoid

def confessionFullOrderClass (r : ConfessionRoute) : ConfessionFullOrderQuotient :=
  Quotient.mk confessionFullOrderSetoid r

theorem confessionFullOrderClass_eq_iff (r s : ConfessionRoute) :
    confessionFullOrderClass r = confessionFullOrderClass s ↔
      SameConfessionFullOrder r s := by
  exact Quotient.eq_iff_equiv

/-- All four independently constructed presentations induce the same full
strict order after their route-specific evidence is forgotten. -/
theorem all_confession_routes_same_full_order (r s : ConfessionRoute) :
    SameConfessionFullOrder r s := by
  rw [SameConfessionFullOrder, confessionRouteRank_eq_dpProjection,
    confessionRouteRank_eq_dpProjection]
  exact sameFullOrder_refl _

instance confessionFullOrderQuotient_subsingleton :
    Subsingleton ConfessionFullOrderQuotient where
  allEq q q' := by
    refine Quotient.inductionOn q ?_
    intro r
    refine Quotient.inductionOn q' ?_
    intro s
    exact Quotient.sound (all_confession_routes_same_full_order r s)

instance confessionFullOrderQuotient_nonempty :
    Nonempty ConfessionFullOrderQuotient :=
  ⟨confessionFullOrderClass .dependencyPairs⟩

/-- Exact one-class classification of the confession quotient. -/
def confessionFullOrderQuotientEquivPUnit :
    ConfessionFullOrderQuotient ≃ PUnit where
  toFun := fun _ => PUnit.unit
  invFun := fun _ => confessionFullOrderClass .dependencyPairs
  left_inv := fun _ => Subsingleton.elim _ _
  right_inv := by
    intro u
    cases u
    rfl

/-- The distinct DP and SCT presentations map to the same confession class. -/
theorem dp_sct_distinct_presentations_same_class :
    ConfessionRoute.dependencyPairs ≠ ConfessionRoute.sizeChange
      ∧ confessionFullOrderClass .dependencyPairs =
          confessionFullOrderClass .sizeChange :=
  ⟨by decide,
    (confessionFullOrderClass_eq_iff _ _).mpr
      (all_confession_routes_same_full_order _ _)⟩

/-! ## Construction-versus-confession modulus -/

/-- The full-order construction quotient is infinite, whereas the confession
quotient has exactly one class. -/
theorem construction_infinite_confession_one_class :
    Infinite RootOrienterFullOrderQuotient
      ∧ Nonempty ConfessionFullOrderQuotient
      ∧ ∀ q q' : ConfessionFullOrderQuotient, q = q' :=
  ⟨rootOrienterFullOrderQuotient_infinite,
    confessionFullOrderQuotient_nonempty,
    fun q q' => Subsingleton.elim q q'⟩

/-- No function from the construction modulus to the confession modulus can
retain all full-order classes injectively. -/
theorem no_injective_construction_to_confession_quotient :
    ¬ ∃ f : RootOrienterFullOrderQuotient → ConfessionFullOrderQuotient,
        Function.Injective f := by
  rintro ⟨f, hf⟩
  have himages : f (WamRootOrienterClass 0) = f (WamRootOrienterClass 1) :=
    Subsingleton.elim _ _
  have hclasses : WamRootOrienterClass 0 = WamRootOrienterClass 1 := hf himages
  have hindices : (0 : Nat) = 1 := WamRootOrienterClass_injective hclasses
  omega

/-! ## Non-uniqueness before quotienting -/

/-- The two concrete KO7 dependency-pair reduction pairs remain distinct as
rank functions but induce the same strict order. Thus rank non-uniqueness and
one-class confession semantics coexist on the same pair problem. -/
theorem ko7_dp_reduction_pair_nonunique_same_full_order :
    ko7_dp_reduction_pair_nonunique.first.rank ≠
        ko7_dp_reduction_pair_nonunique.second.rank
      ∧ SameFullOrder ko7_dp_reduction_pair_nonunique.first.rank
          ko7_dp_reduction_pair_nonunique.second.rank := by
  refine ⟨ko7_dp_reduction_pair_nonunique.ranksDiffer, ?_⟩
  intro x y
  change OperatorKO7.MetaDependencyPairs.dpRank x <
      OperatorKO7.MetaDependencyPairs.dpRank y ↔
    2 * OperatorKO7.MetaDependencyPairs.dpRank x <
      2 * OperatorKO7.MetaDependencyPairs.dpRank y
  omega

/-! ## Every actual dependency-pair rank, not only the four canonical routes -/

/-- The outer recursive-call base coordinate. It is invariant across every
actual KO7 dependency-pair edge, although the canonical confession ranks erase
it. -/
@[simp] def dpBaseProjection : Trace → Nat
  | .recΔ b _ _ => dpProjection b
  | _ => 0

/-- A family of actual dependency-pair ranks that retains the counter and an
arbitrary multiple of the invariant base coordinate. -/
def baseSensitiveDPRank (k : Nat) (t : Trace) : Nat :=
  OperatorKO7.MetaDependencyPairs.dpRank t + k * dpBaseProjection t

/-- Every member of the base-sensitive family strictly decreases on every
actual KO7 dependency-pair edge. -/
theorem baseSensitiveDPRank_decreases (k : Nat) {x y : Trace}
    (hxy : OperatorKO7.MetaDependencyPairs.DPPair x y) :
    baseSensitiveDPRank k y < baseSensitiveDPRank k x := by
  cases hxy with
  | rec_succ b s n =>
      simp [baseSensitiveDPRank, OperatorKO7.MetaDependencyPairs.dpRank,
        dpProjection]

/-- The base-sensitive rank packaged as an actual reduction pair for the
extracted KO7 dependency-pair relation. -/
def baseSensitiveKO7DPReductionPair (k : Nat) : KO7DPReductionPair where
  rank := baseSensitiveDPRank k
  decreases := baseSensitiveDPRank_decreases k

/-- Two different coefficients produce different full term orders. The
separating pair compares one unit of retained base depth with `k+1` units of
counter depth. -/
theorem baseSensitiveDPRank_full_order_separating_pair {k l : Nat} (hkl : k < l) :
    let x := Trace.recΔ (Trace.delta Trace.void) Trace.void Trace.void
    let y := Trace.recΔ Trace.void Trace.void
      (OperatorKO7.MetaDependencyPairs.dpCounterTower (k + 1))
    baseSensitiveDPRank k x < baseSensitiveDPRank k y
      ∧ ¬ baseSensitiveDPRank l x < baseSensitiveDPRank l y := by
  dsimp only
  simp [baseSensitiveDPRank, OperatorKO7.MetaDependencyPairs.dpRank,
    dpProjection]
  omega

/-- Full-order equivalence on the entire type of actual KO7 dependency-pair
reduction pairs. -/
def SameDPReductionPairFullOrder (P Q : KO7DPReductionPair) : Prop :=
  SameFullOrder P.rank Q.rank

theorem sameDPReductionPairFullOrder_refl (P : KO7DPReductionPair) :
    SameDPReductionPairFullOrder P P :=
  sameFullOrder_refl P.rank

theorem sameDPReductionPairFullOrder_symm {P Q : KO7DPReductionPair}
    (h : SameDPReductionPairFullOrder P Q) : SameDPReductionPairFullOrder Q P :=
  sameFullOrder_symm h

theorem sameDPReductionPairFullOrder_trans {P Q R : KO7DPReductionPair}
    (hPQ : SameDPReductionPairFullOrder P Q)
    (hQR : SameDPReductionPairFullOrder Q R) :
    SameDPReductionPairFullOrder P R :=
  sameFullOrder_trans hPQ hQR

def dpReductionPairFullOrderSetoid : Setoid KO7DPReductionPair where
  r := SameDPReductionPairFullOrder
  iseqv := ⟨sameDPReductionPairFullOrder_refl,
    sameDPReductionPairFullOrder_symm, sameDPReductionPairFullOrder_trans⟩

abbrev DPReductionPairFullOrderQuotient :=
  Quotient dpReductionPairFullOrderSetoid

def dpReductionPairFullOrderClass (P : KO7DPReductionPair) :
    DPReductionPairFullOrderQuotient :=
  Quotient.mk dpReductionPairFullOrderSetoid P

theorem dpReductionPairFullOrderClass_eq_iff (P Q : KO7DPReductionPair) :
    dpReductionPairFullOrderClass P = dpReductionPairFullOrderClass Q ↔
      SameDPReductionPairFullOrder P Q := by
  exact Quotient.eq_iff_equiv

def baseSensitiveDPFullOrderClass (k : Nat) :
    DPReductionPairFullOrderQuotient :=
  dpReductionPairFullOrderClass (baseSensitiveKO7DPReductionPair k)

theorem baseSensitiveDPFullOrderClass_injective :
    Function.Injective baseSensitiveDPFullOrderClass := by
  intro k l hclass
  have horder : SameFullOrder (baseSensitiveDPRank k) (baseSensitiveDPRank l) :=
    (dpReductionPairFullOrderClass_eq_iff _ _).mp hclass
  rcases lt_trichotomy k l with hkl | hkl | hkl
  · obtain ⟨hsmall, hlarge⟩ := baseSensitiveDPRank_full_order_separating_pair hkl
    exact False.elim (hlarge ((horder _ _).mp hsmall))
  · exact hkl
  · obtain ⟨hsmall, hlarge⟩ := baseSensitiveDPRank_full_order_separating_pair hkl
    exact False.elim (hlarge ((horder _ _).mpr hsmall))

/-- The full-order quotient of all actual KO7 dependency-pair reduction pairs
is infinite. Thus the one-class result for the four canonical route
presentations is exact and does not assert uniqueness of every sound rank. -/
theorem dpReductionPairFullOrderQuotient_infinite :
    Infinite DPReductionPairFullOrderQuotient :=
  Infinite.of_injective baseSensitiveDPFullOrderClass
    baseSensitiveDPFullOrderClass_injective

/-- Any two rank functions that each induce exactly the counter order induce
the same full order. This is the universal semantic core of the canonical
four-route classification. -/
theorem same_full_order_of_exact_counter_order {f g : Trace → Nat}
    (hf : ∀ x y, f x < f y ↔ dpProjection x < dpProjection y)
    (hg : ∀ x y, g x < g y ↔ dpProjection x < dpProjection y) :
    SameFullOrder f g := by
  intro x y
  exact (hf x y).trans (hg x y).symm

/-- Complete comparison package: infinitely many full-order construction
classes, one confession class, distinct route origins, and no injective lossless
map from construction classes into the confession quotient. -/
theorem construction_confession_moduli_exact :
    Infinite RootOrienterFullOrderQuotient
      ∧ Nonempty (ConfessionFullOrderQuotient ≃ PUnit)
      ∧ Infinite DPReductionPairFullOrderQuotient
      ∧ ConfessionRoute.dependencyPairs ≠ ConfessionRoute.sizeChange
      ∧ confessionRouteLicense .dependencyPairs ≠ confessionRouteLicense .sizeChange
      ∧ ¬ ∃ f : RootOrienterFullOrderQuotient → ConfessionFullOrderQuotient,
          Function.Injective f :=
  ⟨rootOrienterFullOrderQuotient_infinite,
    ⟨confessionFullOrderQuotientEquivPUnit⟩,
    dpReductionPairFullOrderQuotient_infinite,
    dp_sct_distinct_origin_same_rank.1,
    dp_sct_distinct_origin_same_rank.2.1,
    no_injective_construction_to_confession_quotient⟩

end OperatorKO7.Meta.OperationalInexpressibility.ConstructionConfessionModuli
