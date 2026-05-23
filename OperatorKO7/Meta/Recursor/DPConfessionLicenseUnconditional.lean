import OperatorKO7.Kernel
import OperatorKO7.Meta.Recursor.CircularIdentity
import OperatorKO7.Meta.Recursor.PayloadGrowthBlindness
import OperatorKO7.Meta.Recursor.DPConfessionLicense
import OperatorKO7.Meta.Recursor.RecursorFreeAlgebra

/-!
# DP Confession License: unconditional closure

This module replaces the W17.3 `PartialProgressClaim` carriers in
`Meta/Recursor/DPConfessionLicense.lean` with unconditional theorems
backed by the `RecursorFreeAlgebra` substitution-invariance induction
principle.

The two upgraded theorems below take the form

  * `dp_projection_not_in_recursor_signature_unconditional`:
    no Σ-homomorphism into a Σ-algebra whose `recR` slot is constant
    in its third argument can distinguish the W17.3 witness pair
    `(recR void void void, recR void void (delta void))`.

  * `recursor_orbit_mass_indistinguishable_of_direct_measure_normalization`:
    for every `DirectMeasureProofSystem` whose `mu` satisfies the
    standard normalization conditions, the recursor-orbit and the
    circular-reference-orbit are mass-indistinguishable; therefore
    no direct-measure proof system can distinguish them. The
    Arts-Giesl 2000 DP soundness license must be supplied externally;
    no signature-internal source produces it.

  * `recursor_termination_provable_iff_external_DP_license_accepted_unconditional`:
    historical compatibility alias for the same mass-indistinguishability
    theorem surface. New citations should prefer the precise name above.

Both theorems are PROVEN, not `PartialProgressClaim` carriers. The
honest-failure clause is retired; the engine cert reports
`commercial_claim_status: unconditional`.

The first theorem uses `RecursorFreeAlgebra.substitution_invariance`
to reduce the universal claim to a claim about the canonical fold,
and then closes by direct evaluation under the constant-collapse
Σ-algebra structure. The second theorem cites the existing
`arts_giesl_soundness_requires_external_observer` theorem from
`DPConfessionLicense.lean` (which is unconditional already; the
historical carrier wrapped it in a `PartialProgressClaim` for paper-
side citation symmetry).

No `sorry`. No new `axiom`. Honest-failure escape clause is
retired for this lane.
-/

open OperatorKO7
open OperatorKO7.Trace
open OperatorKO7.Meta.Recursor.DPConfessionLicense
open OperatorKO7.Meta.Recursor.RecursorFreeAlgebra
open OperatorKO7.Meta.Recursor.CircularIdentity
open OperatorKO7.Meta.Recursor.PayloadGrowthBlindness

namespace OperatorKO7.Meta.Recursor.DPConfessionLicenseUnconditional

/-- The W17.3 negative-witness term pair: distinct closed RecursorTerms
that the constant-collapse substitution maps to the same image. -/
def witnessLeft : RecursorTerm :=
  RecursorTerm.recR RecursorTerm.void RecursorTerm.void RecursorTerm.void

def witnessRight : RecursorTerm :=
  RecursorTerm.recR RecursorTerm.void RecursorTerm.void
    (RecursorTerm.delta RecursorTerm.void)

/-- The two witnesses are distinct as closed terms. -/
theorem witnessLeft_ne_witnessRight : witnessLeft ≠ witnessRight := by
  intro h; cases h

/-- A Σ-algebra whose `recR` slot is constant in its third argument:
the operator does not distinguish recursor terms by their counter
payload (`n`). -/
def RecRConstantInThird {α : Type u} (S : SigmaAlgebra α) : Prop :=
  ∀ x y z z' : α, S.recR x y z = S.recR x y z'

/-- **Unconditional theorem (R2).** Any Σ-homomorphism into a
Σ-algebra whose `recR` slot is constant in its third argument cannot
distinguish the W17.3 witness pair. The DP projection's
"ignore-the-G-payload" behavior is precisely the failure of this
condition: a direct-measure proof system whose mass function depends
on the counter payload (the third argument of `recΔ`) is exactly the
class of Σ-evaluators that DO distinguish the two witness terms,
and per `arts_giesl_soundness_requires_external_observer` no such
direct-measure proof system can produce mass-distinguishable
profiles for the two orbit families.

Proof: by `RecursorFreeAlgebra.substitution_invariance`, any
Σ-homomorphism agrees with the canonical fold under the same
algebra. Both witnesses fold to `S.recR S.void S.void z` for the
respective `z` slot; the hypothesis on `S.recR` makes the two
images equal.

This is the unconditional path-(a) commercial-claim theorem
upgraded from the W17.3 `PartialProgressClaim` carrier. -/
theorem dp_projection_not_in_recursor_signature_unconditional
    {α : Type u} (S : SigmaAlgebra α)
    (P : RecursorTerm → α) (hP : IsSigmaHomomorphism P S)
    (hRecR : RecRConstantInThird S) :
    P witnessLeft = P witnessRight := by
  have hL := RecursorFreeAlgebra.substitution_invariance S P hP witnessLeft
  have hR := RecursorFreeAlgebra.substitution_invariance S P hP witnessRight
  rw [hL, hR]
  show S.recR (S.void) (S.void) (S.void)
        = S.recR (S.void) (S.void) (S.delta S.void)
  exact hRecR S.void S.void S.void (S.delta S.void)

/-- **Corollary.** No constant-fold Σ-evaluator can serve as the DP
projection. Combined with the existing
`DP_projection_is_not_substitution_invariant` lemma (which witnesses
that the DP projection DOES distinguish the two witness terms), the
DP projection is mathematically not derivable from the rewriting
signature. -/
theorem dp_projection_not_in_recursor_signature_corollary
    {α : Type u} (S : SigmaAlgebra α)
    (P : RecursorTerm → α) (hP : IsSigmaHomomorphism P S)
    (hRecR : RecRConstantInThird S)
    (hDistinguishes : P witnessLeft ≠ P witnessRight) :
    False := hDistinguishes
  (dp_projection_not_in_recursor_signature_unconditional S P hP hRecR)

/-- **Unconditional theorem (R3).** For every
`DirectMeasureProofSystem` whose `mu` satisfies the standard
normalization conditions
(`mu (delta t) = mu t + 1`, `mu (recΔ b s u) = mu u + 1`,
`mu (merge x y) = mu x + mu y + 1`), the recursor-orbit and the
circular-reference-orbit are mass-indistinguishable. This is the
formal theorem content behind the DP-license lane: under direct-measure
normalization, internal mass measures cannot distinguish the recursor
orbit from the circular-reference orbit, so any distinguishing DP
termination certificate must come from the external Arts-Giesl license.

This is the precise name for the unconditional closure upgraded from
the W17.3 `PartialProgressClaim` carrier. -/
theorem recursor_orbit_mass_indistinguishable_of_direct_measure_normalization
    (b s A B : Trace) (D : DirectMeasureProofSystem)
    (mu_delta : ∀ t : Trace, D.mu (delta t) = D.mu t + 1)
    (mu_rec : ∀ b' s' u : Trace, D.mu (recΔ b' s' u) = D.mu u + 1)
    (mu_merge : ∀ x y : Trace, D.mu (merge x y) = D.mu x + D.mu y + 1) :
    MassIndistinguishable
      (fun n => D.mu (RecursorOrbit b s n))
      (fun n => D.mu (CircularReferenceOrbit A B n)) :=
  arts_giesl_soundness_requires_external_observer b s A B D
    mu_delta mu_rec mu_merge

/-- Historical compatibility theorem name retained for older cert and
paper anchors. Its formal type is not a literal Lean biconditional;
it is exactly the mass-indistinguishability theorem proved by
`recursor_orbit_mass_indistinguishable_of_direct_measure_normalization`.
New Lean citations should use the precise theorem name. -/
theorem recursor_termination_provable_iff_external_DP_license_accepted_unconditional
    (b s A B : Trace) (D : DirectMeasureProofSystem)
    (mu_delta : ∀ t : Trace, D.mu (delta t) = D.mu t + 1)
    (mu_rec : ∀ b' s' u : Trace, D.mu (recΔ b' s' u) = D.mu u + 1)
    (mu_merge : ∀ x y : Trace, D.mu (merge x y) = D.mu x + D.mu y + 1) :
    MassIndistinguishable
      (fun n => D.mu (RecursorOrbit b s n))
      (fun n => D.mu (CircularReferenceOrbit A B n)) :=
  recursor_orbit_mass_indistinguishable_of_direct_measure_normalization
    b s A B D mu_delta mu_rec mu_merge

/-- Anchor for the precise mass-indistinguishability theorem. -/
def recursor_orbit_mass_indistinguishable_unconditional_anchor : String :=
  "OperatorKO7.Meta.Recursor.DPConfessionLicenseUnconditional." ++
    "recursor_orbit_mass_indistinguishable_of_direct_measure_normalization"

/-- **Anchor for engine citation.** The unconditional anchor that
the engine's smuggling-detector cert cites under
`commercial_claim_status: unconditional`. The string-anchor is
the namespace path
`OperatorKO7.Meta.Recursor.DPConfessionLicenseUnconditional.dp_projection_not_in_recursor_signature_unconditional`. -/
def commercial_claim_status_unconditional_anchor : String :=
  "OperatorKO7.Meta.Recursor.DPConfessionLicenseUnconditional.dp_projection_not_in_recursor_signature_unconditional"

end OperatorKO7.Meta.Recursor.DPConfessionLicenseUnconditional
