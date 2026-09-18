import OperatorKO7.Meta.NormalizationBoundary.DeltaIntegrateAsymmetry

set_option autoImplicit false

namespace OperatorKO7.Meta.NormalizationBoundary.AntiNormalizationMap

open OperatorKO7 Trace
open OperatorKO7.Meta.NormalizationBoundary.DeltaIntegrateAsymmetry

def normalForm : Trace -> Trace
  | integrate (delta _) => void
  | t => t

theorem normalForm_integrate_delta (t : Trace) :
    normalForm (integrate (delta t)) = void := rfl

theorem integrate_delta_void_ne_integrate_delta_delta_void :
    integrate (delta void) ≠ integrate (delta (delta void)) := by
  intro h
  cases h

theorem anti_normalization_no_internal_inverse :
    ¬ ∃ f : Trace -> Trace,
      ∀ t, f (normalForm (integrate (delta t))) = integrate (delta t) := by
  rintro ⟨f, hf⟩
  have hvoid := hf void
  have hdelta := hf (delta void)
  have hsame :
      integrate (delta void) = integrate (delta (delta void)) := by
    calc
      integrate (delta void) = f void := by
        simpa [normalForm] using hvoid.symm
      _ = integrate (delta (delta void)) := by
        simpa [normalForm] using hdelta
  exact integrate_delta_void_ne_integrate_delta_delta_void hsame

#print axioms normalForm_integrate_delta
#print axioms integrate_delta_void_ne_integrate_delta_delta_void
#print axioms anti_normalization_no_internal_inverse

end OperatorKO7.Meta.NormalizationBoundary.AntiNormalizationMap
