import OperatorKO7.Meta.DistinctionBoundary.TransactionGalois
import OperatorKO7.Meta.DistinctionBoundary.CostDual
import OperatorKO7.Meta.SafeStep.BranchTransaction

/-!
# Finite axis-duality functor for obstruction and license descriptors

This module packages the finite duality surface used by the Distinction Boundary
paper. The duality is an involution on two axis descriptors. It is not stated as
a monad or comonad: those stronger words require extra categorical structure not
present in the finite transaction data.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.DistinctionBoundary.AxisDualityFunctor

/-- The two axes linked by the finite boundary-duality descriptor. -/
inductive Axis
  | orientation
  | distinction
  deriving DecidableEq, Repr

/-- Obstruction-side descriptor: an axis, the number of nonlinear sites touched,
and whether the route retains a verdict. -/
structure ObstructionDescriptor where
  axis : Axis
  nonlinearSite : Nat
  verdictRetained : Prop

/-- License-side descriptor: the dual axis, the number of boundary events charged,
and whether the route retains a verdict. -/
structure LicenseDescriptor where
  axis : Axis
  boundaryEventCount : Nat
  verdictRetained : Prop

/-- The finite left/right axis swap. -/
def dualAxis : Axis -> Axis
  | .orientation => .distinction
  | .distinction => .orientation

theorem axis_duality_involutive (A : Axis) :
    dualAxis (dualAxis A) = A := by
  cases A <;> rfl

/-- Obstruction preorder: more nonlinear sites and no loss of verdict evidence. -/
def ObstructionLe (A B : ObstructionDescriptor) : Prop :=
  A.nonlinearSite ≤ B.nonlinearSite ∧
    (A.verdictRetained -> B.verdictRetained)

/-- License preorder: more boundary events and no loss of verdict evidence. -/
def LicenseLe (A B : LicenseDescriptor) : Prop :=
  A.boundaryEventCount ≤ B.boundaryEventCount ∧
    (A.verdictRetained -> B.verdictRetained)

/-- Send an obstruction descriptor to its dual license descriptor. -/
def obstructionToLicense (O : ObstructionDescriptor) : LicenseDescriptor where
  axis := dualAxis O.axis
  boundaryEventCount := O.nonlinearSite
  verdictRetained := O.verdictRetained

/-- Send a license descriptor back to its dual obstruction descriptor. -/
def licenseToObstruction (L : LicenseDescriptor) : ObstructionDescriptor where
  axis := dualAxis L.axis
  nonlinearSite := L.boundaryEventCount
  verdictRetained := L.verdictRetained

/-- The descriptor swap is an order equivalence in Galois-connection form. -/
theorem obstruction_license_duality_galois
    (O : ObstructionDescriptor) (L : LicenseDescriptor) :
    LicenseLe (obstructionToLicense O) L ↔
      ObstructionLe O (licenseToObstruction L) := by
  rfl

def projectionAsObstruction
    (P : TransactionGalois.ProjectionLicense) : ObstructionDescriptor where
  axis := .orientation
  nonlinearSite := P.droppedDimension
  verdictRetained := P.retainedVerdict

def branchAsLicense
    (B : TransactionGalois.BranchLicense) : LicenseDescriptor where
  axis := .distinction
  boundaryEventCount := B.refusedBranchCount
  verdictRetained := B.retainedVerdict

/-- On projection/branch transactions, the descriptor duality is exactly the
finite transaction Galois connection already proved in `TransactionGalois`. -/
theorem transaction_galois_is_axis_duality
    (P : TransactionGalois.ProjectionLicense)
    (B : TransactionGalois.BranchLicense) :
    (LicenseLe (obstructionToLicense (projectionAsObstruction P))
        (branchAsLicense B) ↔
      ObstructionLe (projectionAsObstruction P)
        (licenseToObstruction (branchAsLicense B))) ↔
      (TransactionGalois.BranchLe (TransactionGalois.projectionToBranch P) B ↔
        TransactionGalois.ProjectionLe P (TransactionGalois.branchToProjection B)) := by
  rfl

/-- The descriptor-level license cost is the same unit-cost law used by the
distinction transaction surface. -/
theorem descriptor_distinction_unit_cost (N : Nat) :
    CostDual.totalCharge CostDual.distinctionChargeLaw (List.replicate N ()) = N :=
  TransactionGalois.transaction_unit_cost_matches_refusal N

#print axioms axis_duality_involutive
#print axioms obstruction_license_duality_galois
#print axioms transaction_galois_is_axis_duality
#print axioms descriptor_distinction_unit_cost

end OperatorKO7.Meta.DistinctionBoundary.AxisDualityFunctor
