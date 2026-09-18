import OperatorKO7.Kernel
import Mathlib.Order.RelClasses

set_option autoImplicit false

namespace OperatorKO7.Meta.NormalizationBoundary.DeltaIntegrateAsymmetry

open OperatorKO7 Trace

inductive OneWayNorm : Trace -> Trace -> Prop
  | integrate_delta (t : Trace) : OneWayNorm (integrate (delta t)) void

inductive TwoWayNorm : Trace -> Trace -> Prop
  | integrate_delta (t : Trace) : TwoWayNorm (integrate (delta t)) void
  | anti_normalize (t : Trace) : TwoWayNorm void (integrate (delta t))

def OneWayNormRev : Trace -> Trace -> Prop := fun a b => OneWayNorm b a

def oneWayRank : Trace -> Nat
  | integrate (delta _) => 1
  | _ => 0

theorem oneWayNormRev_rank_decreases {a b : Trace}
    (h : OneWayNormRev a b) : oneWayRank a < oneWayRank b := by
  cases h
  simp [oneWayRank]

theorem oneWayNormRev_wf : WellFounded OneWayNormRev := by
  refine Subrelation.wf ?_ (InvImage.wf oneWayRank Nat.lt_wfRel.wf)
  intro a b h
  exact oneWayNormRev_rank_decreases h

theorem twoWayNorm_has_cycle (t : Trace) :
    TwoWayNorm (integrate (delta t)) void ∧
      TwoWayNorm void (integrate (delta t)) :=
  ⟨TwoWayNorm.integrate_delta t, TwoWayNorm.anti_normalize t⟩

theorem twoWayNorm_not_wellFounded_rev :
    ¬ WellFounded (fun a b => TwoWayNorm b a) := by
  intro h
  have hxy : (fun a b => TwoWayNorm b a) void (integrate (delta void)) :=
    TwoWayNorm.integrate_delta void
  have hyx : (fun a b => TwoWayNorm b a) (integrate (delta void)) void :=
    TwoWayNorm.anti_normalize void
  exact (h.asymmetric void (integrate (delta void)) hxy) hyx

#print axioms oneWayNormRev_wf
#print axioms twoWayNorm_has_cycle
#print axioms twoWayNorm_not_wellFounded_rev

end OperatorKO7.Meta.NormalizationBoundary.DeltaIntegrateAsymmetry
