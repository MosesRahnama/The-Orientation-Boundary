import OperatorKO7.Meta.InformationalIncompleteness.EqWDiagonalDeficit

set_option autoImplicit false

noncomputable section

namespace OperatorKO7.Meta.InformationalIncompleteness.EqWDiagonalCapacity

open OperatorKO7 Trace
open OperatorKO7.Meta.InformationalIncompleteness.ShannonFinite
open OperatorKO7.Meta.InformationalIncompleteness.LicensedChannelDeficit
open OperatorKO7.Meta.InformationalIncompleteness.EqWDiagonalDeficit
open OperatorKO7.Meta.SafeStep.EqWVoidAnomaly

/-- Zero-capacity diagonal channel: the diagonal licensed-channel deficit is exactly zero. -/
theorem eqW_diagonal_is_zero_capacity_channel :
    deficit (W := Fin 1) (Cn := Fin 2) (X := Fin 2)
      (fun _ => 1) (fun _ _ => (1 : Real) / 2) (fun _ _ => pointMass (0 : Fin 2)) = 0 :=
  eqW_diagonal_echo_vacuum

/-- The zero-capacity channel also has zero residual uncertainty on the diagonal. -/
theorem eqW_diagonal_deficit_zero_corollary :
    deficit (W := Fin 1) (Cn := Fin 2) (X := Fin 2)
        (fun _ => 1) (fun _ _ => (1 : Real) / 2) (fun _ _ => pointMass (0 : Fin 2)) = 0
      ∧ condEntropyDirect (W := Fin 1) (Cn := Fin 2) (X := Fin 2)
        (fun _ => 1) (fun _ _ => (1 : Real) / 2) (fun _ _ => pointMass (0 : Fin 2)) = 0 :=
  ⟨eqW_diagonal_echo_vacuum, eqW_diagonal_zero_residual⟩

/-- The zero-capacity diagonal channel is exactly where the unguarded rewrite fork emits a non-null token. -/
theorem eqW_diagonal_zero_capacity_with_fork :
    deficit (W := Fin 1) (Cn := Fin 2) (X := Fin 2)
        (fun _ => 1) (fun _ _ => (1 : Real) / 2) (fun _ _ => pointMass (0 : Fin 2)) = 0
      ∧ CriticalPairAt (eqW void void) void (integrate (merge void void)) :=
  ⟨eqW_diagonal_echo_vacuum, local_confluence_fails_at_eqW_void_void⟩

#print axioms eqW_diagonal_is_zero_capacity_channel
#print axioms eqW_diagonal_deficit_zero_corollary
#print axioms eqW_diagonal_zero_capacity_with_fork

end OperatorKO7.Meta.InformationalIncompleteness.EqWDiagonalCapacity

end
