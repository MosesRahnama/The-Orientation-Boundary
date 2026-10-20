import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
import OperatorKO7.Meta.DistinctionBoundary.TerminalRepair

/-!
# CategoryTheory wrapper for the SafeStep repair object

`TerminalRepair.lean` proves terminality in the thin repair preorder. This file
wraps that preorder as an actual Mathlib category and exposes the final-object
statement with `CategoryTheory.Limits.IsTerminal`.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.DistinctionBoundary.RepairCategory

open CategoryTheory

/-- The category of semantics-preserving repair relations. -/
abbrev RepairCat : Type :=
  TerminalRepair.RepairObject

/-- A Type-valued wrapper around the Prop-valued thin repair hom. -/
structure RepairHomCat (A B : RepairCat) : Type where
  map : TerminalRepair.RepairHom A B

instance (A B : RepairCat) : Subsingleton (RepairHomCat A B) where
  allEq f g := by
    cases f
    cases g
    rfl

instance : Category RepairCat where
  Hom A B := RepairHomCat A B
  id A := by
    exact ⟨by
      intro a b h
      exact h⟩
  comp f g := by
    exact ⟨by
      intro a b h
      exact g.map (f.map h)⟩
  id_comp := by
    intro A B f
    rfl
  comp_id := by
    intro A B f
    rfl
  assoc := by
    intro A B C D f g h
    rfl

/-- The guarded `SafeStep` relation as an object of the repair category. -/
def safeStepRepair : RepairCat :=
  TerminalRepair.safeStepRepair

/-- `SafeStep` is terminal in the Mathlib category of repair objects. -/
def safeStepFinalObject :
    Limits.IsTerminal safeStepRepair :=
  Limits.IsTerminal.ofUniqueHom
    (fun X => ⟨TerminalRepair.safeStep_terminal_repair X⟩)
    (fun X m => by
      haveI : Subsingleton (X ⟶ safeStepRepair) :=
        inferInstanceAs (Subsingleton (RepairHomCat X safeStepRepair))
      exact Subsingleton.elim m
        ⟨TerminalRepair.safeStep_terminal_repair X⟩)

theorem safeStep_final_object_hom_nonempty (A : RepairCat) :
    Nonempty (A ⟶ safeStepRepair) :=
  ⟨⟨TerminalRepair.safeStep_terminal_repair A⟩⟩

#print axioms safeStepFinalObject
#print axioms safeStep_final_object_hom_nonempty

end OperatorKO7.Meta.DistinctionBoundary.RepairCategory
