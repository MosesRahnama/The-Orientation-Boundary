import Mathlib

set_option autoImplicit false

/-!
# UUET horizon-ledger arithmetic (U-18)

This module formalizes the finite algebraic carrier behind UUET Section 14:

* the Landauer saturation ratio is one when the horizon heat-per-bit equals
 the Landauer unit;
* the Schwarzschild Smarr identity `E = 2 T S` is equivalent to the
 entropy-energy term being one half of total energy;
* the arithmetic complement is also one half under that identity;
* the generalized Smarr residual is zero exactly when the finite bookkeeping
 equation closes.

The module proves only rational bookkeeping. It does not prove that any
physical black hole satisfies the substrate assumptions.
-/

namespace OperatorKO7.Meta.UUET

/-- Finite rational horizon ledger with total energy, entropy-energy term,
rotation term, and charge/work term. -/
structure HorizonLedger where
  totalEnergy : ℚ
  entropyEnergy : ℚ
  rotationalEnergy : ℚ
  chargeEnergy : ℚ
  deriving DecidableEq, Repr

/-- Finite Landauer saturation ratio. -/
def landauerSaturationRatio (heatPerBit landauerUnit : ℚ) : ℚ :=
  heatPerBit / landauerUnit

/-- The finite Schwarzschild-style two-term Smarr predicate. -/
def schwarzschildSmarr (H : HorizonLedger) : Prop :=
  H.totalEnergy = 2 * H.entropyEnergy

/-- The finite generalized Smarr residual. -/
def generalizedSmarrResidual (H : HorizonLedger) : ℚ :=
  H.totalEnergy - (2 * H.entropyEnergy + 2 * H.rotationalEnergy + H.chargeEnergy)

/-- The arithmetic complement to the entropy-energy term. -/
def horizonComplementEnergy (H : HorizonLedger) : ℚ :=
  H.totalEnergy - H.entropyEnergy

/-- Canonical normalized Schwarzschild ledger: total one, entropy half. -/
def canonicalSchwarzschildLedger : HorizonLedger where
  totalEnergy := 1
  entropyEnergy := 1 / 2
  rotationalEnergy := 0
  chargeEnergy := 0

/-- If the heat-per-bit equals the Landauer unit, the finite saturation ratio is one. -/
theorem landauerSaturationRatio_eq_one
    {heatPerBit landauerUnit : ℚ}
    (hunit : landauerUnit ≠ 0) (h : heatPerBit = landauerUnit) :
    landauerSaturationRatio heatPerBit landauerUnit = 1 := by
  unfold landauerSaturationRatio
  rw [h]
  exact div_self hunit

/-- The two-term Smarr identity forces the entropy-energy term to be half the total. -/
theorem entropyEnergy_eq_half_of_schwarzschildSmarr
    (H : HorizonLedger) (h : schwarzschildSmarr H) :
    H.entropyEnergy = H.totalEnergy / 2 := by
  unfold schwarzschildSmarr at h
  linarith

/-- Conversely, a half-energy entropy term closes the two-term Smarr identity. -/
theorem schwarzschildSmarr_of_entropyEnergy_half
    (H : HorizonLedger) (h : H.entropyEnergy = H.totalEnergy / 2) :
    schwarzschildSmarr H := by
  unfold schwarzschildSmarr
  linarith

/-- Under the two-term Smarr identity, the complement is also half the total. -/
theorem horizonComplement_eq_half_of_schwarzschildSmarr
    (H : HorizonLedger) (h : schwarzschildSmarr H) :
    horizonComplementEnergy H = H.totalEnergy / 2 := by
  unfold horizonComplementEnergy
  have hhalf := entropyEnergy_eq_half_of_schwarzschildSmarr H h
  linarith

/-- Generalized Smarr residual zero is equivalent to the finite Smarr bookkeeping equation. -/
theorem generalizedSmarrResidual_zero_iff
    (H : HorizonLedger) :
    generalizedSmarrResidual H = 0 ↔
      H.totalEnergy = 2 * H.entropyEnergy + 2 * H.rotationalEnergy + H.chargeEnergy := by
  unfold generalizedSmarrResidual
  constructor
  · intro h
    linarith
  · intro h
    linarith

/-- The canonical normalized ledger satisfies the two-term Smarr identity. -/
theorem canonicalSchwarzschildLedger_smarr :
    schwarzschildSmarr canonicalSchwarzschildLedger := by
  norm_num [schwarzschildSmarr, canonicalSchwarzschildLedger]

/-- The canonical normalized ledger has entropy-energy one half. -/
theorem canonicalSchwarzschildLedger_entropy_half :
    canonicalSchwarzschildLedger.entropyEnergy =
      canonicalSchwarzschildLedger.totalEnergy / 2 := by
  norm_num [canonicalSchwarzschildLedger]

/-- The canonical normalized ledger has complement one half. -/
theorem canonicalSchwarzschildLedger_complement_half :
    horizonComplementEnergy canonicalSchwarzschildLedger = 1 / 2 := by
  norm_num [horizonComplementEnergy, canonicalSchwarzschildLedger]

/-- The finite horizon-ledger carrier is non-vacuous. -/
theorem horizonLedger_nonvacuous :
    schwarzschildSmarr canonicalSchwarzschildLedger
      ∧ canonicalSchwarzschildLedger.entropyEnergy = 1 / 2
      ∧ horizonComplementEnergy canonicalSchwarzschildLedger = 1 / 2
      ∧ landauerSaturationRatio 7 7 = 1 := by
  norm_num [schwarzschildSmarr, canonicalSchwarzschildLedger,
    horizonComplementEnergy, landauerSaturationRatio]

#print axioms landauerSaturationRatio_eq_one
#print axioms entropyEnergy_eq_half_of_schwarzschildSmarr
#print axioms schwarzschildSmarr_of_entropyEnergy_half
#print axioms horizonComplement_eq_half_of_schwarzschildSmarr
#print axioms generalizedSmarrResidual_zero_iff
#print axioms canonicalSchwarzschildLedger_smarr
#print axioms canonicalSchwarzschildLedger_entropy_half
#print axioms canonicalSchwarzschildLedger_complement_half
#print axioms horizonLedger_nonvacuous

end OperatorKO7.Meta.UUET
