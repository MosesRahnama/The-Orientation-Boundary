import OperatorKO7.Meta.Recursor.InformationEquivalence

/-!
# Reach test for Meta/Recursor/InformationEquivalence

Confirms the public surface of the information-equivalence module
resolves under `lake env lean --run`. Mirrors the substrate-pillar
reach pattern used by `Test/RecursorPayloadGrowthBlindnessReach.lean`
(W17.2) and `Test/InformationTheoreticConfessionReach.lean` (Lane U).
-/

open OperatorKO7
open OperatorKO7.Meta.Recursor.CircularIdentity
open OperatorKO7.Meta.Recursor.InformationEquivalence

namespace RecursorInformationEquivalenceReach

#check EntropyMeasure
#check DiscardedInformationOf
#check InformationEquivalentModDP
#check linear_growth_implies_discarded_info_equality
#check mass_indistinguishable_implies_discarded_info_equality
#check step_duplicator_information_equivalent_to_circular_reference_under_DP_projection
#check mass_indistinguishable_implies_information_equivalent
#check cost_floor_witnessed_information_equivalence
#check canonical_confession_H_equivalence_invariant_under_orbit_choice
#check canonical_discarded_bits_are_orbit_invariant
#check canonical_confession_converges_to_itself

/-- A canonical zero entropy measure: every mass profile receives
discarded-information value `0`. Trivially satisfies the cost-floor
consistency condition. Used to exhibit the headline theorem on a
concrete EntropyMeasure instance. -/
def zeroEntropy : EntropyMeasure where
  discardedInfo := fun _ => 0
  respects_linear_growth := by
    intro _ _ _ _
    rfl

/-- A canonical uniform-cost direct measure on `Trace`. Counts every
constructor as one. Used to exhibit the orbit-mass shape on a
concrete DirectMeasureProofSystem. -/
def uniformDirectMeasure : DirectMeasureProofSystem where
  mu := fun _ => 1

/-- Toy fixture: the recursor orbit and the circular-reference orbit
on synthetic base / step / source / target traces are
information-equivalent under `zeroEntropy` (trivially; the entropy
function is constantly zero). The example exists to confirm the
headline theorem types out and the supporting lemmas reduce on a
concrete fixture. -/
example (b s A B : Trace) :
    DiscardedInformationOf zeroEntropy uniformDirectMeasure (RecursorOrbit b s)
      = DiscardedInformationOf zeroEntropy uniformDirectMeasure
          (CircularReferenceOrbit A B) := by
  rfl

/-- The headline theorem applies on the same fixture once the
`LinearGrowth` witnesses are supplied externally; here the
`InformationEquivalentModDP` predicate fires as a Prop without a
concrete construction. -/
example (b s A B : Trace) :
    InformationEquivalentModDP
      (RecursorOrbit b s)
      (CircularReferenceOrbit A B) :=
  step_duplicator_information_equivalent_to_circular_reference_under_DP_projection
    b s A B

end RecursorInformationEquivalenceReach
