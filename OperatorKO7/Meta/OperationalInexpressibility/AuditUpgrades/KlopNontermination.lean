import OperatorKO7.Meta.UniqueNormalization.Examples

/-!
# Klop's system: no overlap, no confluence, an infinite reduction

Remark 13.4 contrasts the equality-certificate peak of the kernel with Klop's system
`A -> C(A)`, `C(x) -> D(x, C(x))`, `D(x, x) -> E`: that system has no critical pair and fails
confluence through a nonterminating reduction. `KlopSystem` in `UniqueNormalization/Examples.lean`
proves the absence of overlap and the failure of confluence; this module adds the infinite
reduction `A -> C(A) -> C(C(A)) -> ...` and packages the three facts.

Trust: kernel-only. No `sorry`, no `admit`, no new `axiom`.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.OperationalInexpressibility.AuditUpgrades.KlopNontermination

open OperatorKO7.Meta.Rewriting
open OperatorKO7.Meta.UniqueNormalization
open OperatorKO7.Meta.UniqueNormalization.KlopSystem

/-- The term `C^n(A)`. -/
def cPow : Nat → Term Nat Nat
  | 0 => tA
  | n + 1 => .app 1 [cPow n]

/-- Each `C^n(A)` rewrites to `C^(n+1)(A)`: the innermost `A` contracts by `A -> C(A)`. -/
theorem cPow_step : ∀ n : Nat, Step trs (cPow n) (cPow (n + 1))
  | 0 => Step.rootStep_step trs (rule := ruleA) List.mem_cons_self Subst.id
  | n + 1 => Step.arg 1 [] [] (cPow_step n)

/-- Klop's system has an infinite reduction from `A`. -/
theorem klop_infinite_reduction :
    ∃ f : Nat → Term Nat Nat, f 0 = tA ∧ ∀ n : Nat, Step trs (f n) (f (n + 1)) :=
  ⟨cPow, rfl, cPow_step⟩

/-- The three facts the remark uses: no overlap, failure of confluence, and an infinite
reduction. -/
theorem klop_contrast :
    NonOmegaOverlapping trs ∧ ¬ confluent trs ∧
      ∃ f : Nat → Term Nat Nat, f 0 = tA ∧ ∀ n : Nat, Step trs (f n) (f (n + 1)) :=
  ⟨nonOmegaOverlapping, not_confluent, klop_infinite_reduction⟩

end OperatorKO7.Meta.OperationalInexpressibility.AuditUpgrades.KlopNontermination
