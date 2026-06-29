import OperatorKO7.Meta.DistinctionBoundary.SemanticsPreservingMaximality

set_option autoImplicit false

namespace OperatorKO7.Meta.DistinctionBoundary.TerminalRepair

open OperatorKO7 Trace
open OperatorKO7.Meta.DistinctionBoundary

structure RepairObject where
  R : Trace -> Trace -> Prop
  ok : SemanticsPreservingSafeSubrel R

def RepairHom (A B : RepairObject) : Prop :=
  ∀ {a b : Trace}, A.R a b -> B.R a b

def safeStepRepair : RepairObject where
  R := MetaSN_KO7.SafeStep
  ok := safeStep_semanticsPreservingSafeSubrel

theorem safeStep_terminal_repair (A : RepairObject) :
    RepairHom A safeStepRepair := by
  intro a b h
  exact semantics_preserving_subrel_subset_safestep A.ok h

theorem safeStep_terminal_repair_hom_nonempty (A : RepairObject) :
    Nonempty (RepairHom A safeStepRepair) :=
  ⟨safeStep_terminal_repair A⟩

#print axioms safeStep_terminal_repair
#print axioms safeStep_terminal_repair_hom_nonempty

end OperatorKO7.Meta.DistinctionBoundary.TerminalRepair
