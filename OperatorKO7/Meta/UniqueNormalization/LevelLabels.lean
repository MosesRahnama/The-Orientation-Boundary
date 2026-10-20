import OperatorKO7.Meta.UniqueNormalization.Transfer
import Mathlib.Data.Prod.Lex

/-!
# RTA #79 route R2: decreasing-diagram labels

This module implements the label carrier frozen in
`Distinction_Boundary/Roadmaps/klop/label-design.md`.

A label records the conditional-rewrite level and a finite unifier rank.  The
strict order is lexicographic: lower condition level wins, and at equal level a
lower unifier rank wins.  Both coordinates are natural numbers, so the order is
well-founded.  This is the exact order required by the planned decreasing-
diagrams summit; this module does not claim that any peak decreases in it.

Trust: kernel checked. No external certificate or new axiom.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniqueNormalization

/-- The route-R2 label: conditional level first, unifier rank second. -/
structure LevelLabel where
  conditionLevel : Nat
  unifierRank : Nat
  deriving DecidableEq, Repr

/-- Concrete pair representation used by the standard lexicographic order. -/
def LevelLabel.toPair (a : LevelLabel) : Nat × Nat :=
  (a.conditionLevel, a.unifierRank)

/-- Strict route-R2 label order. -/
def LevelLabelLt (a b : LevelLabel) : Prop :=
  Prod.Lex (fun x y : Nat => x < y) (fun x y : Nat => x < y) a.toPair b.toPair

/-- The route-R2 order has the expected explicit two-case form. -/
theorem levelLabelLt_iff {a b : LevelLabel} :
    LevelLabelLt a b ↔
      a.conditionLevel < b.conditionLevel ∨
        (a.conditionLevel = b.conditionLevel ∧ a.unifierRank < b.unifierRank) := by
  rw [LevelLabelLt, Prod.lex_def]
  rfl

/-- Any strict decrease of the condition level decreases the full label,
independently of the unifier rank. -/
theorem LevelLabelLt.of_conditionLevel_lt {a b : LevelLabel}
    (h : a.conditionLevel < b.conditionLevel) : LevelLabelLt a b := by
  exact levelLabelLt_iff.mpr (Or.inl h)

/-- At a fixed condition level, a strict unifier-rank decrease decreases the
full label. -/
theorem LevelLabelLt.of_unifierRank_lt {a b : LevelLabel}
    (hlevel : a.conditionLevel = b.conditionLevel)
    (hrank : a.unifierRank < b.unifierRank) : LevelLabelLt a b := by
  exact levelLabelLt_iff.mpr (Or.inr ⟨hlevel, hrank⟩)

/-- The lexicographic route-R2 label order is well-founded. -/
theorem levelLabelLt_wellFounded : WellFounded LevelLabelLt := by
  have hnat : WellFounded (fun x y : Nat => x < y) := Nat.lt_wfRel.wf
  exact InvImage.wf LevelLabel.toPair (WellFounded.prod_lex hnat hnat)

/-- Labels available below either side of a local peak. -/
def BelowEither (a b x : LevelLabel) : Prop :=
  LevelLabelLt x a ∨ LevelLabelLt x b

/-- A label below the left peak label belongs to the combined lower-label set. -/
theorem BelowEither.of_left {a b x : LevelLabel} (h : LevelLabelLt x a) :
    BelowEither a b x :=
  Or.inl h

/-- A label below the right peak label belongs to the combined lower-label set. -/
theorem BelowEither.of_right {a b x : LevelLabel} (h : LevelLabelLt x b) :
    BelowEither a b x :=
  Or.inr h

end OperatorKO7.Meta.UniqueNormalization

#check @OperatorKO7.Meta.UniqueNormalization.LevelLabel
#check @OperatorKO7.Meta.UniqueNormalization.LevelLabel.toPair
#check @OperatorKO7.Meta.UniqueNormalization.LevelLabelLt
#check @OperatorKO7.Meta.UniqueNormalization.levelLabelLt_iff
#check @OperatorKO7.Meta.UniqueNormalization.LevelLabelLt.of_conditionLevel_lt
#check @OperatorKO7.Meta.UniqueNormalization.LevelLabelLt.of_unifierRank_lt
#check @OperatorKO7.Meta.UniqueNormalization.levelLabelLt_wellFounded
#check @OperatorKO7.Meta.UniqueNormalization.BelowEither
#check @OperatorKO7.Meta.UniqueNormalization.BelowEither.of_left
#check @OperatorKO7.Meta.UniqueNormalization.BelowEither.of_right

#print axioms OperatorKO7.Meta.UniqueNormalization.levelLabelLt_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.LevelLabelLt.of_conditionLevel_lt
#print axioms OperatorKO7.Meta.UniqueNormalization.LevelLabelLt.of_unifierRank_lt
#print axioms OperatorKO7.Meta.UniqueNormalization.levelLabelLt_wellFounded
#print axioms OperatorKO7.Meta.UniqueNormalization.BelowEither.of_left
#print axioms OperatorKO7.Meta.UniqueNormalization.BelowEither.of_right
