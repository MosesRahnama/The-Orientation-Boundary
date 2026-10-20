import OperatorKO7.Meta.LicensedBoundaryCalculus.LicensedReductionMorphism
import OperatorKO7.Meta.SafeStep.BranchTransaction

/-!
# Distinction face as a licensed reduction morphism

The distinction face reads the KO7 branch transaction as an edge-filter
morphism. The state map is identity on traces; the license retains the raw
kernel edges admitted by `SafeStep`.

## Audit slots

Relation: raw `Step` and guarded `SafeStep` on KO7 traces.
Closure: one-step simulation plus finite-path transport inherited from
`LicensedReductionMorphism`.
Trust: kernel-only; non-vacuity reuses the eqW diagonal breaker.
Scope: root branch filtering under the local relation. Global confluence
requires the corresponding closure theorems.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.LicensedBoundaryCalculus

open OperatorKO7
open OperatorKO7.Trace
open OperatorKO7.Meta.SafeStep.BranchTransaction

/-- Raw KO7 kernel as an abstract reduction system. -/
def ko7RawARS : ARS where
  Carrier := Trace
  step := Step
  scope :=
    { location := .root
      closure := .oneStep
      admission := .full
      layer := .original }

/-- Guarded KO7 `SafeStep` kernel as an abstract reduction system. -/
def ko7SafeARS : ARS where
  Carrier := Trace
  step := MetaSN_KO7.SafeStep
  scope :=
    { location := .root
      closure := .oneStep
      admission := .guarded
      layer := .original }

/-- Distinction-face carrier for a branch transaction. -/
structure DistinctionFace where
  transaction :
    BranchTransaction Step MetaSN_KO7.SafeStep
      (¬ OperatorKO7.Meta.SafeStep.GaugeFixingGuard.DistinctionLicense
        (void : Trace) void)
      (fun t => ¬ ((t : Trace) ≠ t))
      MetaSN_KO7.LocalJoinSafe

namespace DistinctionFace

/-- The branch transaction induces the identity state map with a guarded edge
filter. -/
def toMorphism (_F : DistinctionFace) :
    LicensedReductionMorphism ko7RawARS ko7SafeARS where
  admitted := MetaSN_KO7.SafeStep
  admitted_sub_raw := fun h => safeStep_imp_step h
  map := id
  map_step := fun h => h

/-- The identity state map is injective. -/
theorem toMorphism_injective (F : DistinctionFace) :
    Function.Injective F.toMorphism.map := by
  intro x y h
  exact h

/-- Canonical distinction face at the eqW diagonal breaker. -/
def ko7DistinctionFace_fixture : DistinctionFace where
  transaction := ko7_branchTransaction

/-- The distinction fixture contains a raw edge rejected by the guard. -/
theorem ko7DistinctionFace_rejects_diagonal_branch :
    exists x y : Trace,
      ko7RawARS.step x y /\ ¬ ko7DistinctionFace_fixture.toMorphism.admitted x y := by
  exact
    ⟨eqW void void, integrate (merge void void),
      diagonal_forbiddenBranch.raw,
      diagonal_forbiddenBranch.refused⟩

#check ko7RawARS
#check ko7SafeARS
#check DistinctionFace.toMorphism
#check DistinctionFace.toMorphism_injective
#check ko7DistinctionFace_rejects_diagonal_branch
#print axioms DistinctionFace.toMorphism_injective
#print axioms ko7DistinctionFace_rejects_diagonal_branch

end DistinctionFace

end OperatorKO7.Meta.LicensedBoundaryCalculus
