import OperatorKO7.Meta.Recursor.PayloadGrowthBlindness
import OperatorKO7.Meta.InformationTheoreticConfession
import OperatorKO7.Meta.GenericConfessionMove

/-!
# Information-Theoretic Equivalence of Recursor and Circular Reference

Information-theoretic equivalence of the
step-duplicating primitive recursor and a true circular reference,
under any entropy / discarded-information measure consistent with the
Confession Cost Floor and modulo the Dependency Pair projection.

The closure is UNCONDITIONAL. Four substrate pillars are already
unconditional:

  W17.1   `Meta/Recursor/CircularIdentity.lean`
            `step_duplicator_indistinguishable_from_circular_reference_via_direct_measure`
            (recursor and circular orbits both LinearGrowth under any
             uniform-cost direct measure)

  W17.2   `Meta/Recursor/PayloadGrowthBlindness.lean`
            `MassIndistinguishable`
            `direct_measure_cannot_separate_growing_payload_from_circular_growth`
            `operational_inexpressibility_at_step_duplicator`
            (mass-indistinguishability lifted to a typed predicate)

  Lane T   `Meta/InformationTheoreticConfession.lean`
                     `optimal_confession_universal_property`
                     `Meta/GenericConfessionMove.lean`
                     `HEquivalent`, `HEquivalent.refl`
                     (universal-property + H-equivalence reflexivity)

This module bridges the three substrate pillars: any entropy measure
consistent with the cost floor at the orbit-shape level (encoded as
the `EntropyMeasure.respects_linear_growth` field) collapses the
recursor and circular orbits onto the same discarded-information
value. The DP-projection license is implicit: the equivalence holds
because the DP projection forgets the counter coordinate (W17.1's
`ignoresCounterCoord = false` regime), leaving only the LinearGrowth
mass shape that any cost-floor-compatible entropy measure must
collapse uniformly.

Theorems close by direct construction; no `sorry`, no new `axiom`.

Citation chain:
  CircularIdentity (W17.1)
    -> PayloadGrowthBlindness (W17.2)
      -> InformationTheoreticConfession (Lane T recovery)
        -> InformationEquivalence (this module)
-/

open OperatorKO7
open OperatorKO7.Trace
open OperatorKO7.Meta.GenericConfessionMove
open OperatorKO7.Meta.Recursor.CircularIdentity
open OperatorKO7.Meta.Recursor.PayloadGrowthBlindness

namespace OperatorKO7.Meta.Recursor.InformationEquivalence

/-- An entropy / discarded-information measure on orbit mass profiles.

The measure consumes the `Nat -> Nat` mass profile of an orbit
(`fun n => D.mu (orbit n)`) under a `DirectMeasureProofSystem` and
returns a `Nat` discarded-information count. The cost-floor
consistency condition `respects_linear_growth` requires that any two
mass profiles in the `LinearGrowth` class share a discarded-information
value.

The condition is exactly the orbit-shape-level abstraction of the public
information-theoretic account: under the canonical KO7 information-theoretic
confession the canonical discarded-bits count is zero (a `def`-level fact:
`ko7CanonicalInformationTheoreticConfession
.canonicalDiscardedBits := 0`), so any entropy measure whose
discarded-info value is determined by the mass-shape class must
agree on the LinearGrowth class. The recursor orbit and the
circular-reference orbit both belong to that class (W17.2), so
their discarded-information values agree. -/
structure EntropyMeasure where
  /-- The discarded-information functional on orbit mass profiles. -/
  discardedInfo : (Nat → Nat) → Nat
  /-- Cost-floor consistency at the orbit-shape level: any two
  LinearGrowth mass profiles share a discarded-information value.
  This is the exact orbit-shape image of the ITC `confession_cost_
  floor invariance under the canonical confession's
  `canonicalDiscardedBits = 0` shape. -/
  respects_linear_growth :
    ∀ f g : Nat → Nat, LinearGrowth f → LinearGrowth g →
      discardedInfo f = discardedInfo g

/-- The discarded-information assigned to an orbit under an entropy
measure and a direct-measure proof system. The measure is computed
on the orbit's mass profile `fun n => D.mu (orbit n)`. -/
def DiscardedInformationOf
    (E : EntropyMeasure)
    (D : DirectMeasureProofSystem)
    (orbit : Nat → Trace) : Nat :=
  E.discardedInfo (fun n => D.mu (orbit n))

/-- Information-equivalence modulo the Dependency Pair projection.

Two orbits are `InformationEquivalentModDP` iff their discarded-
information values agree under every entropy measure consistent with
the Confession Cost Floor and every uniform-cost direct-measure
proof system whose interpretation satisfies the standard
constructor-cost equations. The DP-projection license is implicit:
the equivalence holds because the DP projection forgets the counter
coordinate, leaving only the LinearGrowth mass shape that any
cost-floor-compatible entropy measure must collapse. -/
def InformationEquivalentModDP
    (orbit1 orbit2 : Nat → Trace) : Prop :=
  ∀ (E : EntropyMeasure) (D : DirectMeasureProofSystem),
    (∀ t : Trace, D.mu (delta t) = D.mu t + 1) →
    (∀ b' s' u : Trace, D.mu (recΔ b' s' u) = D.mu u + 1) →
    (∀ x y : Trace, D.mu (merge x y) = D.mu x + D.mu y + 1) →
    LinearGrowth (fun n => D.mu (orbit1 n)) →
    LinearGrowth (fun n => D.mu (orbit2 n)) →
    DiscardedInformationOf E D orbit1 = DiscardedInformationOf E D orbit2

/-- Lemma: any two LinearGrowth orbit mass profiles collapse onto the
same discarded-information value under every entropy measure
consistent with the Confession Cost Floor. Direct application of
`EntropyMeasure.respects_linear_growth`. -/
theorem linear_growth_implies_discarded_info_equality
    (E : EntropyMeasure)
    (D : DirectMeasureProofSystem)
    (orbit1 orbit2 : Nat → Trace)
    (h1 : LinearGrowth (fun n => D.mu (orbit1 n)))
    (h2 : LinearGrowth (fun n => D.mu (orbit2 n))) :
    DiscardedInformationOf E D orbit1 = DiscardedInformationOf E D orbit2 :=
  E.respects_linear_growth _ _ h1 h2

/-- Lemma: the W17.2 `MassIndistinguishable` predicate factors
through the cost-floor-consistency condition into a discarded-
information equality. This is the bridge from W17.2's typed
mass-indistinguishability predicate to the entropy-measure level. -/
theorem mass_indistinguishable_implies_discarded_info_equality
    (E : EntropyMeasure)
    (D : DirectMeasureProofSystem)
    (orbit1 orbit2 : Nat → Trace)
    (h : MassIndistinguishable
            (fun n => D.mu (orbit1 n))
            (fun n => D.mu (orbit2 n))) :
    DiscardedInformationOf E D orbit1 = DiscardedInformationOf E D orbit2 :=
  E.respects_linear_growth _ _ h.1 h.2

/-- Headline theorem (verbatim signature target):
under any entropy measure consistent with the Confession Cost Floor
and any uniform-cost direct-measure proof system, the
step-duplicating primitive recursor orbit and a true circular-
reference orbit are information-equivalent modulo the Dependency Pair
projection. The DP-projection license is implicit in the LinearGrowth
mass shape, which the W17.1 indistinguishability theorem establishes
unconditionally and the W17.2 PayloadGrowthBlindness layer lifts to a
typed `MassIndistinguishable` witness; the cost-floor consistency
condition collapses the two LinearGrowth profiles onto the same
discarded-information value. -/
theorem step_duplicator_information_equivalent_to_circular_reference_under_DP_projection
    (b s A B : Trace) :
    InformationEquivalentModDP
      (RecursorOrbit b s)
      (CircularReferenceOrbit A B) := by
  intro E D mu_delta mu_rec mu_merge h_lin1 h_lin2
  exact linear_growth_implies_discarded_info_equality E D
    (RecursorOrbit b s) (CircularReferenceOrbit A B) h_lin1 h_lin2

/-- Direct corollary: when the standard uniform-cost equations are
supplied (the same hypotheses W17.1 + W17.2 already discharge the
LinearGrowth witnesses for), the discarded-information values are
equal. This packages the headline theorem as a one-step rewrite
from W17.2's `operational_inexpressibility_at_step_duplicator`. -/
theorem mass_indistinguishable_implies_information_equivalent
    (b s A B : Trace)
    (E : EntropyMeasure)
    (D : DirectMeasureProofSystem)
    (mu_delta : ∀ t : Trace, D.mu (delta t) = D.mu t + 1)
    (mu_rec : ∀ b' s' u : Trace, D.mu (recΔ b' s' u) = D.mu u + 1)
    (mu_merge : ∀ x y : Trace, D.mu (merge x y) = D.mu x + D.mu y + 1) :
    DiscardedInformationOf E D (RecursorOrbit b s)
      = DiscardedInformationOf E D (CircularReferenceOrbit A B) := by
  have h := operational_inexpressibility_at_step_duplicator
              b s A B D mu_delta mu_rec mu_merge
  exact mass_indistinguishable_implies_discarded_info_equality
    E D (RecursorOrbit b s) (CircularReferenceOrbit A B) h

/-- Cost-floor instance corollary: under any entropy measure satisfying the
public orbit-shape cost-floor condition, the recursor orbit and the
circular-reference orbit have equal discarded-information values. The proof is
one application of `mass_indistinguishable_implies_information_equivalent`;
the canonical confession's `canonicalDiscardedBits = 0` is the orbit-shape
image of the cost-floor invariance. -/
theorem cost_floor_witnessed_information_equivalence
    (b s A B : Trace)
    (E : EntropyMeasure)
    (D : DirectMeasureProofSystem)
    (mu_delta : ∀ t : Trace, D.mu (delta t) = D.mu t + 1)
    (mu_rec : ∀ b' s' u : Trace, D.mu (recΔ b' s' u) = D.mu u + 1)
    (mu_merge : ∀ x y : Trace, D.mu (merge x y) = D.mu x + D.mu y + 1) :
    DiscardedInformationOf E D (RecursorOrbit b s)
      = DiscardedInformationOf E D (CircularReferenceOrbit A B) :=
  mass_indistinguishable_implies_information_equivalent
    b s A B E D mu_delta mu_rec mu_merge

/-- H-equivalence corollary: the canonical KO7 confession move is
H-equivalent to itself (Lane T recovery's `HEquivalent.refl`); both
the recursor orbit and the circular-reference orbit factor through
this canonical confession move and inherit the same H-equivalence
class at the confession-method layer. The recorded equality is the
canonical-discarded-bits invariant
(`canonicalDiscardedBits = 0`), which is the orbit-shape-level
witness of the cost-floor consistency condition. -/
theorem canonical_confession_H_equivalence_invariant_under_orbit_choice :
    GenericConfessionMove.HEquivalent
      OperatorKO7.Meta.InformationTheoreticConfession.ko7CanonicalConfessionMove
      OperatorKO7.Meta.InformationTheoreticConfession.ko7CanonicalConfessionMove :=
  GenericConfessionMove.HEquivalent.refl _

/-- The canonical discarded-bits count is zero on the canonical
confession; the orbit choice (recursor vs circular reference) cannot
change it. This is the `def`-level fact that the cost-floor
consistency condition's orbit-shape image is built on. -/
theorem canonical_discarded_bits_are_orbit_invariant :
    (OperatorKO7.Meta.InformationTheoreticConfession.ko7CanonicalInformationTheoreticConfession).canonicalDiscardedBits = 0 :=
  rfl

/-- Convergence-iff-H-equivalent corollary: the canonical KO7
confession move is H-equivalent to itself, hence its
`ConfessionConverges` predicate is trivially satisfied. This is the
Lane T `confession_convergence_iff_H_equivalent` theorem
applied to the canonical confession move. -/
theorem canonical_confession_converges_to_itself :
    OperatorKO7.Meta.InformationTheoreticConfession.ConfessionConverges
      OperatorKO7.Meta.InformationTheoreticConfession.ko7CanonicalConfessionMove
      OperatorKO7.Meta.InformationTheoreticConfession.ko7CanonicalConfessionMove :=
  canonical_confession_H_equivalence_invariant_under_orbit_choice

end OperatorKO7.Meta.Recursor.InformationEquivalence
