import OperatorKO7.Meta.LicensedBoundaryCalculus.LicensedAscentObject
import OperatorKO7.Meta.LicensedBoundaryCalculus.LicenseExpiryTransport

set_option autoImplicit false

/-!
# Licensed-ascent transport

Three live licensed-ascent objects, one over each expiry object of
`Meta/LicensedBoundaryCalculus/LicenseExpiryCategory.lean`, and the transport table between
them. The expiry table of `Meta/LicensedBoundaryCalculus/LicenseExpiryTransport.lean` lifts
unchanged: five ordered pairs carry a typed obstruction, one carries a morphism.

The point of the module is the headline `licensed_ascent_identity_split`. The distinction and
orientation objects have the same six-step truth profile, since both realize it by
`toAscentProfile_realizes`, and both directions of the witness-level morphism are empty. The
identity at the profile layer and the separation at the witness layer are both theorems, and
they are about different things.

Scope. The six-step profile of the orientation boundary in
`Meta/SafeStep/DistinctionAscentProfile.lean` draws its stage witnesses from
`structural_identity`, which is the dependency-pair side of the termination axis. The
carrier-level object here is `roleExpiry`, the role channel the expiry table assigns to the
dependency-pair side. Those are the same axis and not the same object, and nothing beyond the
stated theorems is claimed of either.
-/

namespace OperatorKO7.Meta.LicensedBoundaryCalculus.LicensedAscentTransport

open OperatorKO7 Trace
open OperatorKO7.ProofTheoreticRegister
open OperatorKO7.ClassicalAscentProfile
open OperatorKO7.StructuralIdentityComparison
open OperatorKO7.Meta.DistinctionBoundary.PersistentLicense
open OperatorKO7.Meta.DistinctionBoundary.GodelPartial
open OperatorKO7.Meta.DistinctionBoundary.RoleErasureInstance
open OperatorKO7.Meta.LicensedBoundaryCalculus.LicenseExpiryCategory
open OperatorKO7.Meta.LicensedBoundaryCalculus.LicenseExpiryTransport
open OperatorKO7.Meta.LicensedBoundaryCalculus.LicensedAscent

/-! ## The three live objects -/

/-- Distinction side: the equality-guard expiry, obstructed at the diagonal, repaired by the
licensed comparator steps. -/
def distinctionAscent : LicensedAscentObject where
  toExpiryObject := eqWExpiry
  obstruction := (void, void)
  obstruction_unlicensed := fun h => h rfl
  repaired := fun x y => PairStep x y ∧ Distinct x
  repaired_sub := fun h => h.1
  repaired_licensed := fun h => h.2
  repair_witness :=
    ⟨(merge void void, void), (void, void),
      PairStep.left merge_void_void_steps_void, coalescing_is_distinct⟩

/-- Orientation side: the role-erasure expiry, obstructed at the frame occurrence, repaired by
the role-collapse steps out of active occurrences. -/
def orientationAscent : LicensedAscentObject where
  toExpiryObject := roleExpiry
  obstruction := ((), Role.frame)
  obstruction_unlicensed := by intro h; exact Role.noConfusion h
  repaired := fun x y => RoleCollapseStep x y ∧ isActive x
  repaired_sub := fun h => h.1
  repaired_licensed := fun h => h.2
  repair_witness := ⟨((), Role.active), ((), Role.frame), rfl, rfl⟩

/-- Quotation side: the quote/eval expiry, obstructed at the value, repaired by the quote and
evaluation steps out of reducible configurations. -/
def quotationAscent : LicensedAscentObject where
  toExpiryObject := quoteExpiry
  obstruction := .value void
  obstruction_unlicensed := quoteExpiry.consume_unlicensed
  repaired := fun c d => QuoteEvalStep true c d ∧ QuoteReducible c
  repaired_sub := fun h => h.1
  repaired_licensed := fun h => h.2
  repair_witness :=
    ⟨freezePeakSource, .value void, freeze_peak_eval_converge,
      ⟨.value void, freeze_peak_eval_converge⟩⟩

/-! ## The five blocked directions -/

theorem no_ascentHom_distinction_orientation :
    IsEmpty (AscentHom distinctionAscent orientationAscent) :=
  ⟨fun f => no_hom_eqW_role.false f.toExpiryHom⟩

theorem no_ascentHom_orientation_distinction :
    IsEmpty (AscentHom orientationAscent distinctionAscent) :=
  ⟨fun f => no_hom_role_eqW.false f.toExpiryHom⟩

theorem no_ascentHom_orientation_quotation :
    IsEmpty (AscentHom orientationAscent quotationAscent) :=
  ⟨fun f => no_hom_role_quote.false f.toExpiryHom⟩

theorem no_ascentHom_quotation_orientation :
    IsEmpty (AscentHom quotationAscent orientationAscent) :=
  ⟨fun f => no_hom_quote_role.false f.toExpiryHom⟩

theorem no_ascentHom_quotation_distinction :
    IsEmpty (AscentHom quotationAscent distinctionAscent) :=
  ⟨fun f => no_hom_quote_eqW.false f.toExpiryHom⟩

/-! ## The one construction -/

/-- The equality-to-quotation morphism of the expiry table lifts to the licensed-ascent
objects: it sends the diagonal to the value, and it carries repaired steps to repaired steps
because it preserves both the dynamics and the license. -/
noncomputable def ascentHom_distinction_quotation :
    AscentHom distinctionAscent quotationAscent where
  toHom := hom_eqW_quote
  obstruction_map := eqWToQuoteMap_consume
  repaired_preserve := fun h => ⟨eqWToQuoteMap_step h.1, eqWToQuoteMap_license h.2⟩

/-! ## The transport table -/

/-- Complete six-way transport table for the licensed-ascent objects: five typed obstructions
and one concrete morphism, matching `expiry_pairwise_transport_table` cell for cell. -/
theorem licensed_ascent_transport_table :
    IsEmpty (AscentHom orientationAscent distinctionAscent) ∧
    IsEmpty (AscentHom orientationAscent quotationAscent) ∧
    IsEmpty (AscentHom distinctionAscent orientationAscent) ∧
    IsEmpty (AscentHom quotationAscent orientationAscent) ∧
    IsEmpty (AscentHom quotationAscent distinctionAscent) ∧
    Nonempty (AscentHom distinctionAscent quotationAscent) :=
  ⟨no_ascentHom_orientation_distinction, no_ascentHom_orientation_quotation,
    no_ascentHom_distinction_orientation, no_ascentHom_quotation_orientation,
    no_ascentHom_quotation_distinction, ⟨ascentHom_distinction_quotation⟩⟩

/-- The failing law of each blocked direction, read off the expiry table. -/
theorem licensed_ascent_failing_laws :
    failingLaw .role .eqW = some .dynamicsPreservation ∧
    failingLaw .role .quote = some .dynamicsPreservation ∧
    failingLaw .eqW .role = some .licensePreservation ∧
    failingLaw .quote .role = some .licensePreservation ∧
    failingLaw .quote .eqW = some .dynamicsPreservation ∧
    failingLaw .eqW .quote = none :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## The split -/

/-- **Identical truth profile, no witness-level morphism.** The distinction and orientation
licensed-ascent objects are comparison-equivalent at the six-step profile layer, because both
realize it and both carry the reflection tag, and the witness layer separates them: neither
direction admits a morphism. Each blocked direction fails a law named in the expiry table,
license preservation from the distinction side and dynamics preservation from the orientation
side. -/
theorem licensed_ascent_identity_split :
    Nonempty (ComparisonWitness (toAscentProfile distinctionAscent)
        (toAscentProfile orientationAscent))
      ∧ IsEmpty (AscentHom distinctionAscent orientationAscent)
      ∧ IsEmpty (AscentHom orientationAscent distinctionAscent) :=
  ⟨⟨OperatorKO7.Meta.SafeStep.AscentProfileDegeneracy.comparisonOfRealized
      (toAscentProfile_realizes distinctionAscent)
      (toAscentProfile_realizes orientationAscent) rfl⟩,
    no_ascentHom_distinction_orientation, no_ascentHom_orientation_distinction⟩

end OperatorKO7.Meta.LicensedBoundaryCalculus.LicensedAscentTransport
