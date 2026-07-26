import OperatorKO7.Kernel
import OperatorKO7.Meta.Recursor.CircularIdentity
import OperatorKO7.Meta.Recursor.PayloadGrowthBlindness
import OperatorKO7.Meta.Recursor.DPConfessionLicense
import OperatorKO7.Meta.Recursor.RecursorFreeAlgebra

/-!
# Recursor fold and orbit-profile lemmas

The first theorem proves equality of two recursor terms under a supplied
Sigma homomorphism whose `recR` operation is constant in its third argument.
It does not formalize a dependency-pair projection.

The second theorem imports a result named
`arts_giesl_soundness_requires_external_observer`; its formal conclusion is
`MassIndistinguishable`, which is defined as `LinearGrowth` of each of two mass
profiles. It proves neither equality of the profiles nor a dependency-pair
soundness or license theorem. The long theorem names retained below are
compatibility names; their types determine their mathematical content.
-/

open OperatorKO7
open OperatorKO7.Trace
open OperatorKO7.Meta.Recursor.DPConfessionLicense
open OperatorKO7.Meta.Recursor.RecursorFreeAlgebra
open OperatorKO7.Meta.Recursor.CircularIdentity
open OperatorKO7.Meta.Recursor.PayloadGrowthBlindness

namespace OperatorKO7.Meta.Recursor.DPConfessionLicenseUnconditional

universe u

/-- The first of two distinct closed `RecursorTerm` values. -/
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

/-- A Sigma homomorphism maps the witness pair to equal values when the target
algebra's `recR` operation is constant in its third argument. The proof uses
the free-algebra fold equation and the supplied constancy hypothesis. -/
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

/-- The equality theorem contradicts an additional hypothesis that the same
homomorphism distinguishes the witness pair. -/
theorem dp_projection_not_in_recursor_signature_corollary
    {α : Type u} (S : SigmaAlgebra α)
    (P : RecursorTerm → α) (hP : IsSigmaHomomorphism P S)
    (hRecR : RecRConstantInThird S)
    (hDistinguishes : P witnessLeft ≠ P witnessRight) :
    False := hDistinguishes
  (dp_projection_not_in_recursor_signature_unconditional S P hP hRecR)

/-- Under the three supplied normalization equations, both displayed orbit
mass functions satisfy `LinearGrowth`, the two fields of the imported
`MassIndistinguishable` predicate. -/
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

/-- Compatibility name for
`recursor_orbit_mass_indistinguishable_of_direct_measure_normalization`; the
type is `MassIndistinguishable`, not a biconditional. -/
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

/-- Stable declaration-name string for the mass-profile theorem. -/
def recursor_orbit_mass_indistinguishable_unconditional_anchor : String :=
  "OperatorKO7.Meta.Recursor.DPConfessionLicenseUnconditional." ++
    "recursor_orbit_mass_indistinguishable_of_direct_measure_normalization"

/-- Stable declaration-name string for the constant-third-slot theorem. -/
def commercial_claim_status_unconditional_anchor : String :=
  "OperatorKO7.Meta.Recursor.DPConfessionLicenseUnconditional.dp_projection_not_in_recursor_signature_unconditional"

end OperatorKO7.Meta.Recursor.DPConfessionLicenseUnconditional
