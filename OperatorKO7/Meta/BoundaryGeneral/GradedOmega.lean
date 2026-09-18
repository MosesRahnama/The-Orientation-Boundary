import OperatorKO7.Meta.DistinctionBoundary.DiagonalGradeStratification
import OperatorKO7.Meta.BoundaryGeneral.OverproductionGap

/-!
# Diagonal grades do not determine Omega without evidence adapters

Grades classify structural/dynamic diagonal strength. Omega additionally depends
on a licensed information channel. The same realized grade on the same relation
can therefore carry different Omega values.
-/
set_option autoImplicit false

namespace OperatorKO7.Meta.BoundaryGeneral.GradedOmega

open OperatorKO7.Meta.DistinctionBoundary.DiagonalGradeStratification
open OperatorKO7.Meta.DistinctionBoundary.MinimalFork
open OperatorKO7.Meta.BoundaryGeneral.OverproductionGap

/-- A grade realization and an Omega computation coupled to the same operational
relation. -/
structure GradeOmegaObservation (tag : GradeTag) where
  T : Type
  instT : Fintype T
  R : T → T → Prop
  source : T
  observer : T → Bool
  x : T
  y : T
  Represented : (T → T → Prop) → Prop
  gradeHolds : gradeRealization tag Represented R observer x y
  X : Type
  W : Type
  C : Type
  instX : Fintype X
  instW : Fintype W
  instC : Fintype C
  μ : W → Real
  ν : W → C → Real
  conditional : W → C → X → Real

attribute [instance] GradeOmegaObservation.instT GradeOmegaObservation.instX
  GradeOmegaObservation.instW GradeOmegaObservation.instC

noncomputable def GradeOmegaObservation.omega {tag : GradeTag}
    (O : GradeOmegaObservation tag) : Real :=
  overproductionGap O.R O.source O.μ O.ν O.conditional

/-- D0 is realized on Fork3 independently of the evidence channel. -/
noncomputable def fork3D0Echo : GradeOmegaObservation (.dynamic .d0) where
  T := Fork3
  instT := inferInstance
  R := Fork3Step
  source := Fork3.source
  observer := fun _ => false
  x := Fork3.source
  y := Fork3.source
  Represented := fun _ => True
  gradeHolds := trivial
  X := Fin 2
  W := Fin 1
  C := Fin 2
  instX := inferInstance
  instW := inferInstance
  instC := inferInstance
  μ := unitSurface
  ν := uniformChannelWeights
  conditional := echoChannel

/-- Same grade, same operational carrier, resolving evidence. -/
noncomputable def fork3D0Resolving : GradeOmegaObservation (.dynamic .d0) where
  T := Fork3
  instT := inferInstance
  R := Fork3Step
  source := Fork3.source
  observer := fun _ => false
  x := Fork3.source
  y := Fork3.source
  Represented := fun _ => True
  gradeHolds := trivial
  X := Fin 2
  W := Fin 1
  C := Fin 2
  instX := inferInstance
  instW := inferInstance
  instC := inferInstance
  μ := unitSurface
  ν := uniformChannelWeights
  conditional := resolvingChannel

/-- Same D0 grade, Omega one under echo evidence. -/
theorem fork3D0Echo_omega_eq_one : fork3D0Echo.omega = 1 :=
  fork3_raw_overproduction_eq_one

/-- Same D0 grade, Omega zero under resolving evidence. -/
theorem fork3D0Resolving_omega_eq_zero : fork3D0Resolving.omega = 0 :=
  fork3_raw_gap_closed_by_resolving_channel

/-- **W27 scope theorem.** A diagonal grade alone does not determine Omega, even
when the operational relation/source/observer are held fixed. -/
theorem grade_tag_does_not_determine_omega :
    fork3D0Echo.R = fork3D0Resolving.R ∧
    fork3D0Echo.source = fork3D0Resolving.source ∧
    fork3D0Echo.observer = fork3D0Resolving.observer ∧
    fork3D0Echo.omega ≠ fork3D0Resolving.omega := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  rw [fork3D0Echo_omega_eq_one, fork3D0Resolving_omega_eq_zero]
  norm_num

/-- Consequently, strict Omega separation between grade tags requires additional
channel hypotheses; it cannot be a theorem of `GradeTag` alone. -/
theorem no_grade_only_omega_scalar
    (f : GradeTag → Real)
    (hEcho : f (.dynamic .d0) = fork3D0Echo.omega)
    (hResolve : f (.dynamic .d0) = fork3D0Resolving.omega) : False := by
  rw [fork3D0Echo_omega_eq_one] at hEcho
  rw [fork3D0Resolving_omega_eq_zero] at hResolve
  linarith

end OperatorKO7.Meta.BoundaryGeneral.GradedOmega
