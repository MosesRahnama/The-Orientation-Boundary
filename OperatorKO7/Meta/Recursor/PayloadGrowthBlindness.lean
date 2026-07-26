import OperatorKO7.Meta.Recursor.CircularIdentity

/-!
# Linear-Growth Profiles for Two Recursor Traces

This module defines an arithmetic payload profile, a counter-index profile, and the
predicate `MassIndistinguishable`. The predicate means that each of two sequences satisfies
`LinearGrowth`; sequence equality and observational equivalence lie outside this definition.
The two concluding theorems prove this conjunction from the normalization hypotheses stated
in their types.
-/

open OperatorKO7
open OperatorKO7.Trace

namespace OperatorKO7.Meta.Recursor.PayloadGrowthBlindness

open OperatorKO7.Meta.Recursor.CircularIdentity

/-- Declared arithmetic profile `mu s + n + mu void + 2`. Relating this profile to the
measure of a concrete payload trace requires a separate theorem. -/
def PayloadGrowthRate
  (_b s : Trace) (mu : Trace → Nat) (n : Nat) : Nat :=
  mu s + n + mu void + 2

/-- Counter-index profile at orbit index `n`. -/
def CounterDropRate (n : Nat) : Nat := n

/-- Advancing the index by one increments both declared numerical profiles by one. -/
theorem recursor_payload_grows_linearly_while_counter_drops_linearly
    (b s : Trace) (mu : Trace → Nat) (n : Nat) :
    PayloadGrowthRate b s mu (n + 1) = PayloadGrowthRate b s mu n + 1
      ∧ CounterDropRate n + 1 = CounterDropRate (n + 1) := by
  refine ⟨?_, ?_⟩
  · show mu s + (n + 1) + mu void + 2 = mu s + n + mu void + 2 + 1
    omega
  · rfl

/-- Conjunction asserting that each of two natural-number sequences satisfies
`LinearGrowth`. Equality and observer equivalence require separate structure. -/
def MassIndistinguishable (f g : Nat → Nat) : Prop :=
  LinearGrowth f ∧ LinearGrowth g

/-- Under the displayed normalization equations, the recursor-orbit and
circular-reference-orbit measure sequences each satisfy `LinearGrowth`. -/
theorem direct_measure_cannot_separate_growing_payload_from_circular_growth
    (b s A B : Trace) (mu : Trace → Nat)
    (mu_delta : ∀ t : Trace, mu (delta t) = mu t + 1)
    (mu_rec : ∀ b' s' u : Trace, mu (recΔ b' s' u) = mu u + 1)
    (mu_merge : ∀ x y : Trace, mu (merge x y) = mu x + mu y + 1) :
    MassIndistinguishable
      (fun n => mu (RecursorOrbit b s n))
      (fun n => mu (CircularReferenceOrbit A B n)) := by
  refine ⟨?_, ?_⟩
  · exact recursor_orbit_mu_is_linear b s mu mu_delta mu_rec
  · exact circular_orbit_mu_is_linear A B mu mu_merge

/-- Restatement of `direct_measure_cannot_separate_growing_payload_from_circular_growth`
for the measure field of a `DirectMeasureProofSystem`. The conclusion is the conjunction of
two `LinearGrowth` properties defined by `MassIndistinguishable`. -/
theorem operational_inexpressibility_at_step_duplicator
    (b s A B : Trace) (D : DirectMeasureProofSystem)
    (mu_delta : ∀ t : Trace, D.mu (delta t) = D.mu t + 1)
    (mu_rec : ∀ b' s' u : Trace, D.mu (recΔ b' s' u) = D.mu u + 1)
    (mu_merge : ∀ x y : Trace, D.mu (merge x y) = D.mu x + D.mu y + 1) :
    MassIndistinguishable
      (fun n => D.mu (RecursorOrbit b s n))
      (fun n => D.mu (CircularReferenceOrbit A B n)) :=
  direct_measure_cannot_separate_growing_payload_from_circular_growth
    b s A B D.mu mu_delta mu_rec mu_merge

end OperatorKO7.Meta.Recursor.PayloadGrowthBlindness
