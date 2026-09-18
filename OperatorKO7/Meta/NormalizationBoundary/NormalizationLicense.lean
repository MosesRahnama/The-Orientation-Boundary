import OperatorKO7.Meta.NormalizationBoundary.AntiNormalizationMap
import OperatorKO7.Meta.NormalizationBoundary.DeltaIntegrateLoop
import OperatorKO7.Meta.DistinctionBoundary.SharedRoot

set_option autoImplicit false

namespace OperatorKO7.Meta.NormalizationBoundary.NormalizationLicense

open OperatorKO7 Trace
open OperatorKO7.Meta.NormalizationBoundary.DeltaIntegrateAsymmetry
open OperatorKO7.Meta.NormalizationBoundary.AntiNormalizationMap
open OperatorKO7.Meta.NormalizationBoundary.DeltaIntegrateLoop

def licensedRecover (historyToken : Trace) : Trace :=
  integrate (delta historyToken)

theorem anti_normalization_licensed_recovery (t : Trace) :
    licensedRecover t = integrate (delta t)
      ∧ OneWayNorm (integrate (delta t)) void :=
  ⟨rfl, OneWayNorm.integrate_delta t⟩

/-- The normalization face is an irreversibility obstruction: the one-way rule is
well-founded, adding the reverse rule creates a cycle, collapse has no internal
inverse, and an external history token licenses recovery. -/
structure IrreversibilityFace : Prop where
  oneWayWellFounded : WellFounded OneWayNormRev
  twoWayCycle :
    ∀ t, TwoWayNorm (integrate (delta t)) void
      ∧ TwoWayNorm void (integrate (delta t))
  noInternalInverse :
    ¬ ∃ f : Trace -> Trace,
      ∀ t, f (normalForm (integrate (delta t))) = integrate (delta t)
  licensedRecovery : ∀ t, licensedRecover t = integrate (delta t)

theorem normalization_boundary_is_irreversibility_face :
    IrreversibilityFace where
  oneWayWellFounded := one_way_normalization_well_founded
  twoWayCycle := two_way_delta_integrate_loops
  noInternalInverse := anti_normalization_no_internal_inverse
  licensedRecovery := fun _ => rfl

/-- The normalization obstruction shares the obstruction-plus-license shape: the
one-way normal form collapses two different erased histories, while the external
history token distinguishes them. This is an irreversibility instance of the
same abstract shape, not the substitution-invariance theorem's orientation or
distinction instance. -/
def normalizationObstruction :
    OperatorKO7.Meta.DistinctionBoundary.SharedRoot.SubstitutionInvariantObstruction
      Trace Trace where
  collapse := normalForm
  license := fun t => t
  a := integrate (delta void)
  b := integrate (delta (delta void))
  distinct := integrate_delta_void_ne_integrate_delta_delta_void
  collapse_identifies := rfl
  license_separates := integrate_delta_void_ne_integrate_delta_delta_void

inductive NormalizationRedex : Trace -> Prop
  | integrate_delta (t : Trace) : NormalizationRedex (integrate (delta t))

theorem normalization_relation_not_diagonal_fork :
    ¬ ∃ a : Trace, NormalizationRedex (eqW a a) := by
  rintro ⟨a, h⟩
  cases h

theorem normalization_not_godel_diagonal :
    ¬ ∃ a : Trace, NormalizationRedex (eqW a a) :=
  normalization_relation_not_diagonal_fork

#print axioms anti_normalization_licensed_recovery
#print axioms normalization_boundary_is_irreversibility_face
#print axioms normalizationObstruction
#print axioms normalization_relation_not_diagonal_fork
#print axioms normalization_not_godel_diagonal

end OperatorKO7.Meta.NormalizationBoundary.NormalizationLicense
