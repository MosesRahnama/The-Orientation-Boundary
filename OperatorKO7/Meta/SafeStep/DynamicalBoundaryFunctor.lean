import OperatorKO7.Meta.SafeStep.BoundaryDuality
import OperatorKO7.Meta.SafeStep.EqWVoidAnomaly

set_option autoImplicit false

/-!
# Dynamical boundary functor for the distinction/orientation collapse boundary

This module is the dynamics-level companion to
`SafeStep.BoundaryDuality`.  `BoundaryDuality` proves that the
distinction and orientation collapse boundaries are isomorphic as boundary
operators.  Here we add the functorial dynamics that the manuscript had been
treating as the next target.

The construction is intentionally precise:

* every one-step transition of a source rewrite relation is transported to the
  boundary verdict channel;
* both the full kernel relation `Step` and the guarded relation `SafeStep` are
  supported;
* the construction is proved non-faithful, because the collapse boundary
  discards payload and cannot reconstruct the underlying rewrite dynamics.

So the theorem proves a full collapse-preserving dynamical boundary functor.  It
does not claim an invertible encoding of the full rewrite graph.
-/

open OperatorKO7 Trace
open MetaSN_KO7
open OperatorKO7.Meta.BoundaryOperator
open OperatorKO7.Meta.SafeStep.BoundaryDuality

namespace OperatorKO7.Meta.SafeStep.DynamicalBoundaryFunctor

set_option linter.unusedVariables false

/-- A rewrite-to-boundary functor for one-step dynamics.  The object map embeds
`Trace` terms into the boundary carrier, and `mapStep` says that every source
rewrite edge commutes through the boundary verdict channel. -/
structure RewriteBoundaryFunctor (R : Trace → Trace → Prop)
    (B : BoundaryOperator (Option Trace) Trace) where
  mapObj : Trace → Option Trace
  mapObj_domain : ∀ t, B.domain (mapObj t)
  mapStep :
    ∀ {a b : Trace}, R a b →
      B.apply (mapObj a) (mapObj_domain a)
        = B.apply (mapObj b) (mapObj_domain b)

/-- The generic collapse functor: any source one-step relation maps into the
constant collapse boundary.  This is non-vacuous as a dynamics carrier because
the source relation may be the full KO7 kernel `Step` or the guarded `SafeStep`,
while the target channel intentionally remembers only the boundary verdict. -/
noncomputable def collapseRewriteBoundaryFunctor
    (R : Trace → Trace → Prop) (y0 : Trace) :
    RewriteBoundaryFunctor R (collapseBoundaryOperator y0) where
  mapObj := some
  mapObj_domain := by
    intro t
    simp [collapseBoundaryOperator]
  mapStep := by
    intro a b hstep
    rfl

/-- Full-kernel dynamics mapped to the distinction collapse boundary. -/
noncomputable def step_distinction_dynamical_boundary_functor :
    RewriteBoundaryFunctor Step distinctionBoundaryOperator :=
  collapseRewriteBoundaryFunctor Step void

/-- Guarded SafeStep dynamics mapped to the distinction collapse boundary. -/
noncomputable def safeStep_distinction_dynamical_boundary_functor :
    RewriteBoundaryFunctor SafeStep distinctionBoundaryOperator :=
  collapseRewriteBoundaryFunctor SafeStep void

/-- Full-kernel dynamics mapped to the orientation collapse boundary. -/
noncomputable def step_orientation_dynamical_boundary_functor :
    RewriteBoundaryFunctor Step orientationBoundaryOperator :=
  collapseRewriteBoundaryFunctor Step (delta void)

/-- Guarded SafeStep dynamics mapped to the orientation collapse boundary. -/
noncomputable def safeStep_orientation_dynamical_boundary_functor :
    RewriteBoundaryFunctor SafeStep orientationBoundaryOperator :=
  collapseRewriteBoundaryFunctor SafeStep (delta void)

/-- The eqW critical pair is transported by the full-kernel distinction functor:
both outgoing root edges from `eqW void void` commute through the boundary
verdict channel. -/
theorem eqW_critical_pair_maps_to_distinction_boundary :
    distinctionBoundaryOperator.apply
        (step_distinction_dynamical_boundary_functor.mapObj (eqW void void))
        (step_distinction_dynamical_boundary_functor.mapObj_domain (eqW void void))
      =
      distinctionBoundaryOperator.apply
        (step_distinction_dynamical_boundary_functor.mapObj void)
        (step_distinction_dynamical_boundary_functor.mapObj_domain void)
      ∧
    distinctionBoundaryOperator.apply
        (step_distinction_dynamical_boundary_functor.mapObj (eqW void void))
        (step_distinction_dynamical_boundary_functor.mapObj_domain (eqW void void))
      =
      distinctionBoundaryOperator.apply
        (step_distinction_dynamical_boundary_functor.mapObj (integrate (merge void void)))
        (step_distinction_dynamical_boundary_functor.mapObj_domain
          (integrate (merge void void))) := by
  exact ⟨step_distinction_dynamical_boundary_functor.mapStep (Step.R_eq_refl void),
    step_distinction_dynamical_boundary_functor.mapStep (Step.R_eq_diff void void)⟩

/-- The guarded off-diagonal SafeStep branch is transported by the distinction
functor whenever a distinction license supplies the disequality side condition. -/
theorem distinction_license_maps_offdiagonal_safeStep
    {a b : Trace} (h : a ≠ b) :
    distinctionBoundaryOperator.apply
        (safeStep_distinction_dynamical_boundary_functor.mapObj (eqW a b))
        (safeStep_distinction_dynamical_boundary_functor.mapObj_domain (eqW a b))
      =
      distinctionBoundaryOperator.apply
        (safeStep_distinction_dynamical_boundary_functor.mapObj (integrate (merge a b)))
        (safeStep_distinction_dynamical_boundary_functor.mapObj_domain
          (integrate (merge a b))) := by
  exact safeStep_distinction_dynamical_boundary_functor.mapStep
    (SafeStep.R_eq_diff a b h)

/-- The guarded diagonal SafeStep branch is transported by the distinction
functor whenever the zero-carrier guard supplies the reflexive side condition. -/
theorem zero_carrier_maps_diagonal_safeStep
    {a : Trace} (h0 : MetaSN_DM.kappaM a = 0) :
    distinctionBoundaryOperator.apply
        (safeStep_distinction_dynamical_boundary_functor.mapObj (eqW a a))
        (safeStep_distinction_dynamical_boundary_functor.mapObj_domain (eqW a a))
      =
      distinctionBoundaryOperator.apply
        (safeStep_distinction_dynamical_boundary_functor.mapObj void)
        (safeStep_distinction_dynamical_boundary_functor.mapObj_domain void) := by
  exact safeStep_distinction_dynamical_boundary_functor.mapStep
    (SafeStep.R_eq_refl a h0)

/-- Non-faithfulness fence: the collapse functor identifies distinct inputs.
This theorem is load-bearing manuscript hygiene.  The dynamical boundary functor
preserves boundary verdicts, but it cannot reconstruct the source term from the
verdict. -/
theorem distinction_dynamical_functor_not_faithful :
    ∃ a b : Trace,
      a ≠ b ∧
      distinctionBoundaryOperator.apply
          (step_distinction_dynamical_boundary_functor.mapObj a)
          (step_distinction_dynamical_boundary_functor.mapObj_domain a)
        =
        distinctionBoundaryOperator.apply
          (step_distinction_dynamical_boundary_functor.mapObj b)
          (step_distinction_dynamical_boundary_functor.mapObj_domain b) := by
  refine ⟨void, delta void, ?_, ?_⟩
  · intro h
    cases h
  · rfl

/-- A collapse-preserving functor exists for both the full and guarded
distinction dynamics, and it transports every source edge to a commuting
boundary-verdict equality. The witnessing property is the step-preservation
law itself, made explicit in the conclusion rather than hidden in the
functor's record type. -/
theorem distinction_dynamics_has_full_and_guarded_functors :
    (∃ F : RewriteBoundaryFunctor Step distinctionBoundaryOperator,
        ∀ (a b : Trace), Step a b →
          distinctionBoundaryOperator.apply (F.mapObj a) (F.mapObj_domain a)
            = distinctionBoundaryOperator.apply (F.mapObj b) (F.mapObj_domain b))
      ∧
    (∃ F : RewriteBoundaryFunctor SafeStep distinctionBoundaryOperator,
        ∀ (a b : Trace), SafeStep a b →
          distinctionBoundaryOperator.apply (F.mapObj a) (F.mapObj_domain a)
            = distinctionBoundaryOperator.apply (F.mapObj b) (F.mapObj_domain b)) := by
  exact ⟨⟨step_distinction_dynamical_boundary_functor,
            fun _ _ h => step_distinction_dynamical_boundary_functor.mapStep h⟩,
         ⟨safeStep_distinction_dynamical_boundary_functor,
            fun _ _ h => safeStep_distinction_dynamical_boundary_functor.mapStep h⟩⟩

/-- A collapse-preserving functor exists for both the full and guarded
orientation dynamics, with the step-preservation law made explicit in the
conclusion. -/
theorem orientation_dynamics_has_full_and_guarded_functors :
    (∃ F : RewriteBoundaryFunctor Step orientationBoundaryOperator,
        ∀ (a b : Trace), Step a b →
          orientationBoundaryOperator.apply (F.mapObj a) (F.mapObj_domain a)
            = orientationBoundaryOperator.apply (F.mapObj b) (F.mapObj_domain b))
      ∧
    (∃ F : RewriteBoundaryFunctor SafeStep orientationBoundaryOperator,
        ∀ (a b : Trace), SafeStep a b →
          orientationBoundaryOperator.apply (F.mapObj a) (F.mapObj_domain a)
            = orientationBoundaryOperator.apply (F.mapObj b) (F.mapObj_domain b)) := by
  exact ⟨⟨step_orientation_dynamical_boundary_functor,
            fun _ _ h => step_orientation_dynamical_boundary_functor.mapStep h⟩,
         ⟨safeStep_orientation_dynamical_boundary_functor,
            fun _ _ h => safeStep_orientation_dynamical_boundary_functor.mapStep h⟩⟩

#print axioms eqW_critical_pair_maps_to_distinction_boundary
#print axioms distinction_license_maps_offdiagonal_safeStep
#print axioms zero_carrier_maps_diagonal_safeStep
#print axioms distinction_dynamical_functor_not_faithful
#print axioms distinction_dynamics_has_full_and_guarded_functors
#print axioms orientation_dynamics_has_full_and_guarded_functors

end OperatorKO7.Meta.SafeStep.DynamicalBoundaryFunctor
