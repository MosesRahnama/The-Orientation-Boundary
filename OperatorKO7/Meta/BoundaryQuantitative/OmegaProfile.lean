import OperatorKO7.Meta.BoundaryGeneral.OverproductionGapProfileBridge
import OperatorKO7.Meta.BoundaryQuantitative.OrientationInstance
import OperatorKO7.Meta.BoundaryQuantitative.PRTTasks
import OperatorKO7.Meta.BoundaryQuantitative.QECProfiles
import OperatorKO7.Meta.BoundaryQuantitative.Transaction

/-!
# Why the legacy obstruction atlas cannot compute Omega by itself

`ObstructionProfile` stores four natural-number coordinates but no operational
relation/source and no licensed information channel. Omega is therefore not a
function of the legacy profile. This is a theorem, not an editorial caveat.
-/
set_option autoImplicit false

namespace OperatorKO7.Meta.BoundaryQuantitative.OmegaProfile

open OperatorKO7.Meta.BoundaryQuantitative
open OperatorKO7.Meta.BoundaryGeneral.OverproductionGap
open OperatorKO7.Meta.DistinctionBoundary.MinimalFork

/-- The five profile families named by W14, preserved exactly as legacy data. -/
def fiveProfileAtlas : List ObstructionProfile :=
  [ distinctionRawBadProfile 1 0,
    orientationRawProfile 3 3 6,
    prtAlwaysDifferentProfile (Fin 8),
    qecCorrectableProfile,
    sampleStrictTransaction.before ]

theorem fiveProfileAtlas_length : fiveProfileAtlas.length = 5 := rfl

/-- **W14 impossibility theorem.** The same legacy profile can support two
different Omega values because the evidence channel is absent from the profile.
The raw distinction profile paired with echo evidence has Omega one, while the
same profile paired with resolving evidence has Omega zero. -/
theorem legacy_profile_does_not_determine_omega :
    ∃ (p : ObstructionProfile),
      p = distinctionRawBadProfile 1 0 ∧
      overproductionGap Fork3Step Fork3.source
          unitSurface uniformChannelWeights echoChannel = 1 ∧
      overproductionGap Fork3Step Fork3.source
          unitSurface uniformChannelWeights resolvingChannel = 0 :=
  ⟨distinctionRawBadProfile 1 0, rfl,
    fork3_raw_overproduction_eq_one,
    fork3_raw_gap_closed_by_resolving_channel⟩

/-- Stronger non-function statement: no proposed scalar function of the legacy
profile alone can equal both canonical Omega realizations of that profile. -/
theorem no_legacy_profile_scalar_can_recover_all_omega
    (f : ObstructionProfile → Real) :
    ¬ (f (distinctionRawBadProfile 1 0) =
          overproductionGap Fork3Step Fork3.source
            unitSurface uniformChannelWeights echoChannel ∧
       f (distinctionRawBadProfile 1 0) =
          overproductionGap Fork3Step Fork3.source
            unitSurface uniformChannelWeights resolvingChannel) := by
  rw [fork3_raw_overproduction_eq_one,
    fork3_raw_gap_closed_by_resolving_channel]
  rintro ⟨h1, h0⟩
  linarith

/-- A certified Omega realization of a legacy profile.  The constructors are
semantic realizations, not freely supplied scalar labels. -/
inductive ProfileOmegaRealization : ObstructionProfile → Real → Prop where
  | fork3Echo
      (h : overproductionGap Fork3Step Fork3.source
          unitSurface uniformChannelWeights echoChannel = 1) :
      ProfileOmegaRealization (distinctionRawBadProfile 1 0) 1
  | fork3Resolving
      (h : overproductionGap Fork3Step Fork3.source
          unitSurface uniformChannelWeights resolvingChannel = 0) :
      ProfileOmegaRealization (distinctionRawBadProfile 1 0) 0

/-- The explicit semantic adapter required to attach an Omega value to a
legacy profile. -/
structure OmegaAdapter (p : ObstructionProfile) where
  omega : Real
  certified : ProfileOmegaRealization p omega

/-- Echo evidence realizes Omega one on the raw distinction profile. -/
def fork3EchoAdapter : OmegaAdapter (distinctionRawBadProfile 1 0) :=
  ⟨1, .fork3Echo fork3_raw_overproduction_eq_one⟩

/-- Resolving evidence realizes Omega zero on the same profile. -/
def fork3ResolvingAdapter : OmegaAdapter (distinctionRawBadProfile 1 0) :=
  ⟨0, .fork3Resolving fork3_raw_gap_closed_by_resolving_channel⟩

/-- No profile-only scalar agrees with every certified semantic adapter. -/
theorem no_profile_only_scalar_agrees_with_all_adapters
    (f : ObstructionProfile → Real) :
    ¬ ∀ (p : ObstructionProfile) (A : OmegaAdapter p), f p = A.omega := by
  intro h
  have h1 := h (distinctionRawBadProfile 1 0) fork3EchoAdapter
  have h0 := h (distinctionRawBadProfile 1 0) fork3ResolvingAdapter
  simp [fork3EchoAdapter, fork3ResolvingAdapter] at h1 h0
  linarith

/-- The W14 resolution.  The atlas has five rows, and every profile-only
candidate misses a certified Omega realization of a row in that atlas.  Thus
Omega certification must consume an operational/evidence adapter. -/
theorem five_profile_atlas_requires_omega_adapters :
    fiveProfileAtlas.length = 5 ∧
    (∀ f : ObstructionProfile → Real,
      ∃ (p : ObstructionProfile), p ∈ fiveProfileAtlas ∧
        ∃ A : OmegaAdapter p, f p ≠ A.omega) := by
  constructor
  · rfl
  · intro f
    let p := distinctionRawBadProfile 1 0
    have hp : p ∈ fiveProfileAtlas := by
      simp [p, fiveProfileAtlas]
    by_cases h : f p = 1
    · refine ⟨p, hp, fork3ResolvingAdapter, ?_⟩
      simpa [p, fork3ResolvingAdapter, h]
    · exact ⟨p, hp, fork3EchoAdapter, by simpa [p, fork3EchoAdapter] using h⟩

end OperatorKO7.Meta.BoundaryQuantitative.OmegaProfile
