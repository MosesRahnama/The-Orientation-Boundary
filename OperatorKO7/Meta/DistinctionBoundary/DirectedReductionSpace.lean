import OperatorKO7.Meta.DistinctionBoundary.GlobalConfluence
import OperatorKO7.Meta.Confluence_Safe

/-!
# Finite directed reduction spaces

This file supplies the finite directed graph substrate behind the paper's
directed-space language. It uses the rewrite relation as directed edges and the
reflexive-transitive closure as directed paths.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.DistinctionBoundary

open OperatorKO7 Trace
open MetaSN_KO7

/-- A finite directed reduction-space interface. -/
structure DirectedReductionSpace (X : Type) where
  step : X -> X -> Prop
  path : X -> X -> Prop
  path_refl : forall x, path x x
  path_step : forall {x y}, step x y -> path x y
  path_trans : forall {x y z}, path x y -> path y z -> path x z

/-- Local directed joinability in the path relation. -/
def LocallyDirectedJoinable {X : Type}
    (D : DirectedReductionSpace X) (x : X) : Prop :=
  forall {b c}, D.step x b -> D.step x c ->
    exists d, D.path b d ∧ D.path c d

/-- A directed puncture: two outgoing branches exist but no directed join exists. -/
def DiagonalPuncture {X : Type}
    (D : DirectedReductionSpace X) (x : X) : Prop :=
  exists b c, D.step x b ∧ D.step x c ∧ b ≠ c ∧
    ¬ exists d, D.path b d ∧ D.path c d

/-- The raw KO7 reduction graph as a directed reduction space. -/
def rawStepDirectedSpace : DirectedReductionSpace Trace where
  step := Step
  path := StepStar
  path_refl := StepStar.refl
  path_step := stepstar_of_step
  path_trans := stepstar_trans

/-- The guarded KO7 reduction graph as a directed reduction space. -/
def safeStepDirectedSpace : DirectedReductionSpace Trace where
  step := SafeStep
  path := SafeStepStar
  path_refl := SafeStepStar.refl
  path_step := safestar_of_step
  path_trans := safestar_trans

/-- The raw diagonal is a directed puncture. -/
theorem raw_step_space_diagonal_puncture :
    DiagonalPuncture rawStepDirectedSpace (eqW void void) := by
  refine ⟨void, integrate (merge void void),
    Step.R_eq_refl void, Step.R_eq_diff void void, ?_, ?_⟩
  · intro h
    cases h
  · intro hjoin
    rcases hjoin with ⟨d, hbStar, hcStar⟩
    have hnf_void : NormalForm void := by
      intro ex
      rcases ex with ⟨u, hu⟩
      cases hu
    have hnf_int_merge : NormalForm (integrate (merge void void)) := by
      intro ex
      rcases ex with ⟨u, hu⟩
      cases hu
    have hd_eq_void : d = void := (nf_no_stepstar_forward hnf_void hbStar).symm
    have hd_eq_int : d = integrate (merge void void) :=
      (nf_no_stepstar_forward hnf_int_merge hcStar).symm
    have hneq : (integrate (merge void void) : Trace) ≠ void := by
      intro h
      cases h
    exact hneq (hd_eq_int.symm.trans hd_eq_void)

/-- Guarding fills the diagonal puncture at `eqW void void`: the guarded graph is
locally directed-joinable there. -/
theorem safeStep_space_locally_directed_joinable_at_diagonal :
    LocallyDirectedJoinable safeStepDirectedSpace (eqW void void) := by
  intro b c hb hc
  exact (GlobalConfluence.safeStep_locally_confluent (eqW void void)) hb hc

#print axioms raw_step_space_diagonal_puncture
#print axioms safeStep_space_locally_directed_joinable_at_diagonal

end OperatorKO7.Meta.DistinctionBoundary
