import OperatorKO7.Meta.Methods.OrientationClosure.SchemaCore
import OperatorKO7.Meta.StepDuplicatingSchema

/-!
# Orientation Boundary ablations

This module isolates two exact escapes from the duplicating direct-measure
obstruction on the same free syntax.

* `NonDuplicatingStep` removes the duplicated payload occurrence from the
  successor rule. Ordinary tree size then strictly decreases.
* `counterRank` keeps the original duplicating rule but erases wrapper payload
  information. It strictly decreases on every successor instance and therefore
  witnesses the failure of any theorem that omits payload sensitivity.

No concrete KO7 term or rewrite relation is imported.
-/

set_option autoImplicit false

namespace OperatorKO7.Methods.OrientationClosure.AblationComparisons

open OperatorKO7.Methods.OrientationClosure.SchemaCore

universe u

/-- Tree-node count on the independent free recursor syntax. -/
def treeSize {ν : Type u} : FreeTerm ν → Nat
  | .var _ => 1
  | .zero => 1
  | .succ t => treeSize t + 1
  | .wrap s t => treeSize s + treeSize t + 1
  | .recur b s n => treeSize b + treeSize s + treeSize n + 1

/-- Ablated root relation in which the successor rule keeps the recursive call
but does not duplicate the payload into a wrapper. -/
inductive NonDuplicatingStep {ν : Type u} : FreeTerm ν → FreeTerm ν → Prop
  | recurZero (b s : FreeTerm ν) : NonDuplicatingStep (.recur b s .zero) b
  | recurSucc (b s n : FreeTerm ν) :
      NonDuplicatingStep (.recur b s (.succ n)) (.recur b s n)

/-- Tree size strictly decreases on both nonduplicating root rules. -/
theorem treeSize_decreases_nonDuplicatingStep
    {ν : Type u} {t v : FreeTerm ν} (h : NonDuplicatingStep t v) :
    treeSize v < treeSize t := by
  cases h <;> simp only [treeSize] <;> omega

/-- The reverse nonduplicating root relation is well founded by tree size. -/
theorem nonDuplicatingStep_reverse_wellFounded (ν : Type u) :
    WellFounded (fun v t : FreeTerm ν => NonDuplicatingStep t v) := by
  apply Subrelation.wf (r := InvImage (fun a b : Nat => a < b) treeSize)
  · intro v t h
    exact treeSize_decreases_nonDuplicatingStep h
  · exact InvImage.wf treeSize Nat.lt_wfRel.wf

/-- The original duplicating successor rule increases ordinary tree size for a
concrete nonempty payload. This prevents reusing the nonduplication proof for
the original rule. -/
theorem treeSize_original_duplication_control :
    let s : FreeTerm Empty := .succ .zero
    let b : FreeTerm Empty := .zero
    let n : FreeTerm Empty := .zero
    treeSize (.recur b s (.succ n)) < treeSize (.wrap s (.recur b s n)) := by
  decide

/-- Universe-polymorphic counter projection on the free recursor syntax. The
wrapper erases its left payload and the recursor follows only its counter. -/
def counterRank {ν : Type u} : FreeTerm ν → Nat
  | .var _ => 0
  | .zero => 0
  | .succ t => counterRank t + 1
  | .wrap _ t => counterRank t
  | .recur _ _ n => counterRank n

/-- The counter projection ignores the entire wrapper payload. -/
theorem counterRank_wrap_payload_blind
    {ν : Type u} (s t : FreeTerm ν) :
    counterRank (.wrap s t) = counterRank t := by
  rfl

/-- The payload-blind counter projection strictly orients every original
recursor-successor root instance. -/
theorem counterRank_orients_original_successor
    {ν : Type u} (b s n : FreeTerm ν) :
    counterRank (.wrap s (.recur b s n)) <
      counterRank (.recur b s (.succ n)) := by
  simp [counterRank]

/-- The counter projection fails first-wrapper-argument sensitivity on an
explicit positive counter term. -/
theorem counterRank_not_wrapper_left_sensitive :
    ∃ x y : FreeTerm Empty,
      ¬ counterRank x < counterRank (.wrap x y) := by
  refine ⟨.succ .zero, .zero, ?_⟩
  simp [counterRank]

/-- Both ablations in one theorem: removing payload duplication admits ordinary
size descent, while retaining duplication but erasing wrapper payload admits a
counter projection. -/
theorem duplication_and_payload_sensitivity_are_independent_obligations :
    WellFounded (fun v t : FreeTerm Empty => NonDuplicatingStep t v) ∧
      (∀ b s n : FreeTerm Empty,
        counterRank (.wrap s (.recur b s n)) <
          counterRank (.recur b s (.succ n))) ∧
      (∃ x y : FreeTerm Empty,
        ¬ counterRank x < counterRank (.wrap x y)) := by
  exact ⟨nonDuplicatingStep_reverse_wellFounded Empty,
    counterRank_orients_original_successor,
    counterRank_not_wrapper_left_sensitive⟩

end OperatorKO7.Methods.OrientationClosure.AblationComparisons
