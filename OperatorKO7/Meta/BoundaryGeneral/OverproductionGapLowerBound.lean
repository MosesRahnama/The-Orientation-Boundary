import OperatorKO7.Meta.BoundaryGeneral.OverproductionGap

/-!
# Lower bounds for Omega

A lower bound on terminal entropy and an upper bound on licensed information imply a lower bound on Omega. The generic theorem combines these bounds, and the Fork3 theorem gives a one-bit lower bound under echo evidence.
-/
set_option autoImplicit false

namespace OperatorKO7.Meta.BoundaryGeneral.OverproductionGapLowerBound

open OperatorKO7.Meta.BoundaryGeneral.OverproductionGap
open OperatorKO7.Meta.DistinctionBoundary.Quantitative

/-- Generic lower-bound rule. -/
theorem omega_ge_of_envelope_ge_of_evidence_le
    {T : Type} [Fintype T] (R : T → T → Prop) (source : T)
    {X W C : Type} [Fintype X] [Fintype W] [Fintype C]
    (μ : W → Real) (ν : W → C → Real) (r : W → C → X → Real)
    (L D : Real)
    (hH : L ≤ terminalHartleyEntropy R source)
    (hD : deficitBits μ ν r ≤ D) :
    L - D ≤ overproductionGap R source μ ν r := by
  unfold overproductionGap
  linarith

/-- If terminal entropy is at least `L` bits and licensed information is at most `D<L`, then Omega is positive. -/
theorem boundaryEvent_of_uniform_lower_gap
    {T : Type} [Fintype T] (R : T → T → Prop) (source : T)
    {X W C : Type} [Fintype X] [Fintype W] [Fintype C]
    (μ : W → Real) (ν : W → C → Real) (r : W → C → X → Real)
    (L D : Real) (hDL : D < L)
    (hH : L ≤ terminalHartleyEntropy R source)
    (hD : deficitBits μ ν r ≤ D) :
    BoundaryEvent R source μ ν r := by
  unfold BoundaryEvent
  have hΩ := omega_ge_of_envelope_ge_of_evidence_le R source μ ν r L D hH hD
  linarith

/-- With zero licensed gain, a lower bound on terminal entropy is also a lower bound on Omega. -/
theorem omega_ge_envelope_lower_bound_of_zero_evidence
    {T : Type} [Fintype T] (R : T → T → Prop) (source : T)
    {X W C : Type} [Fintype X] [Fintype W] [Fintype C]
    (μ : W → Real) (ν : W → C → Real) (r : W → C → X → Real)
    (L : Real) (hH : L ≤ terminalHartleyEntropy R source)
    (hzero : deficitBits μ ν r = 0) :
    L ≤ overproductionGap R source μ ν r := by
  have h := omega_ge_of_envelope_ge_of_evidence_le R source μ ν r L 0 hH (by simp [hzero])
  simpa using h

/-- Fork3 has a one-bit Omega lower bound under echo evidence. -/
theorem fork3_one_bit_lower_bound :
    1 ≤ overproductionGap
      OperatorKO7.Meta.DistinctionBoundary.MinimalFork.Fork3Step
      OperatorKO7.Meta.DistinctionBoundary.MinimalFork.Fork3.source
      unitSurface uniformChannelWeights echoChannel := by
  rw [fork3_raw_overproduction_eq_one]

/-- The bridge records a lower bound on terminal entropy and an upper bound on licensed information. The upper bound must be below the lower bound; together they imply a boundary event. -/
structure QuantitativeObstructionBridge
    {T : Type} [Fintype T] (R : T → T → Prop) (source : T)
    {X W C : Type} [Fintype X] [Fintype W] [Fintype C]
    (μ : W → Real) (ν : W → C → Real) (r : W → C → X → Real) where
  lowerBits : Real
  evidenceUpperBits : Real
  evidenceUpper_lt_lower : evidenceUpperBits < lowerBits
  envelopeLower : lowerBits ≤ terminalHartleyEntropy R source
  evidenceUpper : deficitBits μ ν r ≤ evidenceUpperBits

/-- Every inhabited quantitative obstruction bridge produces a boundary event. -/
theorem QuantitativeObstructionBridge.boundaryEvent
    {T : Type} [Fintype T] {R : T → T → Prop} {source : T}
    {X W C : Type} [Fintype X] [Fintype W] [Fintype C]
    {μ : W → Real} {ν : W → C → Real} {r : W → C → X → Real}
    (B : QuantitativeObstructionBridge R source μ ν r) :
    BoundaryEvent R source μ ν r :=
  boundaryEvent_of_uniform_lower_gap R source μ ν r
    B.lowerBits B.evidenceUpperBits B.evidenceUpper_lt_lower
    B.envelopeLower B.evidenceUpper

end OperatorKO7.Meta.BoundaryGeneral.OverproductionGapLowerBound
