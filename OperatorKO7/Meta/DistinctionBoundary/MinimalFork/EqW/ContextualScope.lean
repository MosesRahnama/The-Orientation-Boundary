import OperatorKO7.Meta.DistinctionBoundary.MinimalFork.EqW.Confluence

/-!
# Contextual scope wall for the syntactic disequality guard

The root guard repairs the diagonal, but unrestricted rewriting below `eqW`
allows two initially distinct arguments to converge. This file exhibits the
smallest nested witness and proves both target verdicts are normal, so the
result is a genuine contextual nonconfluence theorem, not a search artifact.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.DistinctionBoundary.MinimalFork

open OperatorKO7.Meta.DistinctionBoundary.Quantitative

/-- `same` is a normal form under guarded full-context rewriting. -/
theorem miniEqW_same_guardedCtx_normal :
    NormalForm MiniEqWGuardedCtxStep .same := by
  intro y h
  cases h with
  | root hr => cases hr

/-- `different` is a normal form under guarded full-context rewriting. -/
theorem miniEqW_different_guardedCtx_normal :
    NormalForm MiniEqWGuardedCtxStep .different := by
  intro y h
  cases h with
  | root hr => cases hr

/-- Minimal nested source where an initially off-diagonal outer guard expires. -/
def contextualCounterexample : MiniEqWTerm :=
  .eqW (.eqW .same .different) .different

/-- The outer arguments are initially syntactically distinct. -/
theorem contextualCounterexample_initially_offDiagonal :
    (MiniEqWTerm.eqW .same .different) ≠ MiniEqWTerm.different := by
  intro h
  cases h

/-- Taking the outer guarded difference edge immediately reaches `different`. -/
theorem contextualCounterexample_to_different :
    Reach MiniEqWGuardedCtxStep contextualCounterexample .different := by
  apply reach_step
  exact MiniEqWGuardedCtxStep.root
    (MiniEqWGuardedRootStep.diff _ _
      contextualCounterexample_initially_offDiagonal)

/-- Reducing the left argument first makes the outer comparison diagonal, then
its reflexive rule reaches `same`. -/
theorem contextualCounterexample_to_same :
    Reach MiniEqWGuardedCtxStep contextualCounterexample .same := by
  let middle : MiniEqWTerm := .eqW .different .different
  have hInner : MiniEqWGuardedCtxStep contextualCounterexample middle := by
    exact MiniEqWGuardedCtxStep.left
      (MiniEqWGuardedCtxStep.root
        (MiniEqWGuardedRootStep.diff .same .different
          miniEqW_same_ne_different))
  have hOuter : MiniEqWGuardedCtxStep middle .same := by
    exact MiniEqWGuardedCtxStep.root
      (MiniEqWGuardedRootStep.refl .different)
  exact reach_trans (reach_step hInner) (reach_step hOuter)

/-- The two contextual verdicts are unjoinable. -/
theorem miniEqW_guardedCtx_verdicts_unjoinable :
    ¬ Joinable MiniEqWGuardedCtxStep .same .different := by
  rintro ⟨z, hs, hd⟩
  have hzs : z = .same :=
    eq_of_normalForm_reach miniEqW_same_guardedCtx_normal hs
  have hzd : z = .different :=
    eq_of_normalForm_reach miniEqW_different_guardedCtx_normal hd
  exact miniEqW_same_ne_different (hzs.symm.trans hzd)

/-- Root guarding alone does not imply confluence of unrestricted context closure. -/
theorem guarded_full_context_not_confluent :
    ¬ ConfluentAt MiniEqWGuardedCtxStep contextualCounterexample := by
  intro hconf
  exact miniEqW_guardedCtx_verdicts_unjoinable
    (hconf .same .different
      contextualCounterexample_to_same
      contextualCounterexample_to_different)

/-- Forward persistence of syntactic disequality under independent guarded
argument evolution. This property is *not* true for unrestricted contexts. -/
def SyntacticDisequalityPersistent : Prop :=
  ∀ {a b a' b' : MiniEqWTerm},
    a ≠ b →
    Reach MiniEqWGuardedCtxStep a a' →
    Reach MiniEqWGuardedCtxStep b b' →
    a' ≠ b'

/-- The unrestricted guarded context relation refutes persistence of syntactic
disequality: the left argument can contract to the right argument. -/
theorem syntacticDisequality_coalescence_witness :
    ∃ a b a' b' : MiniEqWTerm,
      a ≠ b ∧
      Reach MiniEqWGuardedCtxStep a a' ∧
      Reach MiniEqWGuardedCtxStep b b' ∧
      a' = b' := by
  refine ⟨.eqW .same .different, .different, .different, .different,
    contextualCounterexample_initially_offDiagonal, ?_, ?_, rfl⟩
  · apply reach_step
    exact MiniEqWGuardedCtxStep.root
      (MiniEqWGuardedRootStep.diff .same .different miniEqW_same_ne_different)
  · exact reach_refl (R := MiniEqWGuardedCtxStep) MiniEqWTerm.different

/-- Roadmap-stable existential name. -/
theorem syntactic_disequality_not_persistent :
    ∃ a b a' b' : MiniEqWTerm,
      a ≠ b ∧
      Reach MiniEqWGuardedCtxStep a a' ∧
      Reach MiniEqWGuardedCtxStep b b' ∧
      a' = b' :=
  syntacticDisequality_coalescence_witness

/-- Roadmap-stable name for the direct outer-first branch. -/
theorem guarded_context_counterexample_to_different :
    Reach MiniEqWGuardedCtxStep contextualCounterexample .different :=
  contextualCounterexample_to_different

/-- Roadmap-stable name for the inner-first branch. -/
theorem guarded_context_counterexample_to_equal :
    Reach MiniEqWGuardedCtxStep contextualCounterexample .same :=
  contextualCounterexample_to_same

/-- Roadmap-stable guarded-context normal-form name for the equal verdict. -/
theorem minimalEqW_same_guardedCtx_normal :
    NormalForm MiniEqWGuardedCtxStep .same :=
  miniEqW_same_guardedCtx_normal

/-- Roadmap-stable guarded-context normal-form name for the different verdict. -/
theorem minimalEqW_different_guardedCtx_normal :
    NormalForm MiniEqWGuardedCtxStep .different :=
  miniEqW_different_guardedCtx_normal

/-- The unrestricted guarded context relation refutes persistence globally. -/
theorem syntacticDisequality_not_persistent :
    ¬ SyntacticDisequalityPersistent := by
  intro hp
  have hleft : Reach MiniEqWGuardedCtxStep
      (.eqW .same .different) .different := by
    apply reach_step
    exact MiniEqWGuardedCtxStep.root
      (MiniEqWGuardedRootStep.diff .same .different miniEqW_same_ne_different)
  have hright : Reach MiniEqWGuardedCtxStep
      MiniEqWTerm.different MiniEqWTerm.different :=
    reach_refl (R := MiniEqWGuardedCtxStep) MiniEqWTerm.different
  exact hp contextualCounterexample_initially_offDiagonal hleft hright rfl

end OperatorKO7.Meta.DistinctionBoundary.MinimalFork
