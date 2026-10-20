import OperatorKO7.Meta.Methods.OrientationClosure.DependencyPairSoundness

/-!
# Payload relabellings fix the projected pair of the free recursor

Clause (3) of Proposition 7.10: dependency-pair extraction removes the wrapper context, and the
counter projection selects the coordinate fixed by every payload-label permutation. On the
first-order free recursor `freeRecursorTRS`, with payload variable `1` and counter variable `2`:

* `extraction_drops_wrapper`: the only `recur`-rooted subterm of the successor right side is the
  recursive call, and a pair whose target is the wrapper is no chain step.
* `projected_pair`: the call projection reads argument `2`, the counter: `succ(x₂)` on the left
  side and `x₂` on the extracted call.
* `payloadRelabelling_fixes_projected_pair`: every substitution that moves only the payload
  variable leaves both projected terms unchanged.
* `payload_coordinate_moves`: a payload relabelling moves the payload argument, so the payload
  coordinate is not fixed.

Trust: kernel-only. No `sorry`, no `admit`, no new `axiom`.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.OperationalInexpressibility.AuditUpgrades.PairProjectionInvariance

open OperatorKO7.Meta.Rewriting
open OperatorKO7.Methods.OrientationClosure.DependencyPairSoundness

/-- The argument list of the successor rule's left side. -/
def succLhsArgs : List (Term FreeSym Nat) := [.var 0, .var 1, .app .succ [.var 2]]

/-- The argument list of the recursive call of the successor rule's right side. -/
def succCallArgs : List (Term FreeSym Nat) := [.var 0, .var 1, .var 2]

theorem succRule_lhs_eq : succRule.lhs = .app .recur succLhsArgs := rfl

theorem succRule_rhs_eq : succRule.rhs = .app .wrap [.var 1, .app .recur succCallArgs] := rfl

/-- Extraction keeps the recursive call alone and drops the wrapper. -/
theorem extraction_drops_wrapper :
    (∀ targs : List (Term FreeSym Nat),
        IsSubterm (.app .recur targs) succRule.rhs → targs = succCallArgs) ∧
      (∀ (c : FreeSym × List (Term FreeSym Nat)) (ys : List (Term FreeSym Nat)),
        ¬ MinChainStep freeRecursorTRS c (FreeSym.wrap, ys)) :=
  ⟨fun _ h => succRule_rhs_recur_subterm h, freeRecursor_no_wrapper_target⟩

/-- The call projection reads the counter argument of the left side and of the extracted call. -/
theorem projected_pair :
    succLhsArgs[freeProj FreeSym.recur]? = some (.app .succ [.var 2]) ∧
      succCallArgs[freeProj FreeSym.recur]? = some (.var 2) :=
  ⟨rfl, rfl⟩

/-- A substitution that moves only the payload variable. -/
def PayloadRelabelling (s : Subst FreeSym Nat) : Prop := ∀ v : Nat, v ≠ 1 → s v = .var v

/-- Every substitution fixing the counter variable leaves the projected pair unchanged. -/
theorem projected_pair_fixed (s : Subst FreeSym Nat) (h2 : s 2 = .var 2) :
    (Subst.applyList s succLhsArgs)[freeProj FreeSym.recur]? = some (.app .succ [.var 2]) ∧
      (Subst.applyList s succCallArgs)[freeProj FreeSym.recur]? = some (.var 2) := by
  simp [succLhsArgs, succCallArgs, freeProj, h2]

/-- Every payload relabelling fixes the projected pair. -/
theorem payloadRelabelling_fixes_projected_pair (s : Subst FreeSym Nat)
    (hs : PayloadRelabelling s) :
    (Subst.applyList s succLhsArgs)[freeProj FreeSym.recur]? =
        succLhsArgs[freeProj FreeSym.recur]? ∧
      (Subst.applyList s succCallArgs)[freeProj FreeSym.recur]? =
        succCallArgs[freeProj FreeSym.recur]? := by
  obtain ⟨h1, h2⟩ := projected_pair_fixed s (hs 2 (by decide))
  exact ⟨h1.trans projected_pair.1.symm, h2.trans projected_pair.2.symm⟩

/-- A payload relabelling moves the payload argument. -/
theorem payload_coordinate_moves :
    ∃ s : Subst FreeSym Nat, PayloadRelabelling s ∧
      (Subst.applyList s succLhsArgs)[1]? ≠ succLhsArgs[1]? := by
  refine ⟨fun v => if v = 1 then .var 3 else .var v, ?_, ?_⟩
  · intro v hv
    simp [hv]
  · simp [succLhsArgs]

end OperatorKO7.Meta.OperationalInexpressibility.AuditUpgrades.PairProjectionInvariance
