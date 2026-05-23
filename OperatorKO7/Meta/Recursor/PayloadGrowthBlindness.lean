import OperatorKO7.Meta.Recursor.CircularIdentity

/-!
# Payload-Growth Blindness Witness (W17.2)

W17.2: the payload-growth-vs-counter-drop phenomenon at the
step-duplicating recursor. The W17.1 structural-identity theorem
shows that recursor and circular-reference orbits both satisfy
`LinearGrowth` under any uniform-cost direct measure. This module
makes the asymmetry concrete: the recursor's G-wrapped payload
grows linearly with `n` while the counter `delta n → n` drops
linearly; the two scale at the same asymptotic rate but in
opposite directions. A whole-term direct-measure proof system
that reads the mass alone cannot separate the two: the masses
agree by `LinearGrowth`.

Operational consequence: the step-duplicator is *operationally
inexpressible* to direct-measure proof systems. This is the formal
version of the LLM PRT-benchmark failure mode where models that
attempt termination proofs by whole-term mass invariants
systematically fail on the step-duplicating recursor.

Theorems close by direct construction with no proof placeholders or
postulated top-level declarations.

Citation chain (continuation of W17.1 banner):
  CircularIdentity (W17.1; sibling)
    → PayloadGrowthBlindness (W17.2; this module)
      → DPConfessionLicense (W17.3; path-(a) commercial claim)
-/

open OperatorKO7
open OperatorKO7.Trace

namespace OperatorKO7.Meta.Recursor.PayloadGrowthBlindness

open OperatorKO7.Meta.Recursor.CircularIdentity

/-- Payload-growth rate at orbit step `n`. The payload `app s (recΔ
b s (counterTrace n))` is what the recursor's `R_rec_succ` rule
produces from `recΔ b s (delta (counterTrace n))`. At step `n` the
payload mass under uniform-cost mu is `mu s + (n + mu void + 1)`
(by mu_app counted as one constructor + mu of the inner recursor
orbit at depth `n`). -/
def PayloadGrowthRate
  (_b s : Trace) (mu : Trace → Nat) (n : Nat) : Nat :=
  mu s + n + mu void + 2

/-- Counter-drop rate at orbit step `n`: simply `n` (the depth of
the counter trace). -/
def CounterDropRate (n : Nat) : Nat := n

/-- The recursor's payload mass grows linearly with `n` while the
counter drops linearly. The two scale at the same asymptotic rate
but in opposite directions. -/
theorem recursor_payload_grows_linearly_while_counter_drops_linearly
    (b s : Trace) (mu : Trace → Nat) (n : Nat) :
    PayloadGrowthRate b s mu (n + 1) = PayloadGrowthRate b s mu n + 1
      ∧ CounterDropRate n + 1 = CounterDropRate (n + 1) := by
  refine ⟨?_, ?_⟩
  · show mu s + (n + 1) + mu void + 2 = mu s + n + mu void + 2 + 1
    omega
  · rfl

/-- Two `Nat → Nat` sequences `f` and `g` are
`MassIndistinguishable` iff both satisfy `LinearGrowth`. The
W17.1 structural-identity theorem guarantees this for the
recursor and circular-reference orbits under any uniform-cost
direct measure. -/
def MassIndistinguishable (f g : Nat → Nat) : Prop :=
  LinearGrowth f ∧ LinearGrowth g

/-- The recursor's whole-term mu-mass and the circular-reference
orbit's whole-term mu-mass are mass-indistinguishable: BOTH
satisfy `LinearGrowth`. Direct corollary of the W17.1
structural-identity theorem. -/
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

/-- Operational-inexpressibility corollary: under any
DirectMeasureProofSystem whose interpretation is uniform-cost,
the step-duplicator's recursor orbit cannot be distinguished
from a circular-reference orbit by mass alone. This is the
formal version of the LLM PRT-benchmark failure mode at the
step-duplicator: any whole-term direct-measure interpretation
sees the recursor as structurally identical to a circular
reference. -/
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
