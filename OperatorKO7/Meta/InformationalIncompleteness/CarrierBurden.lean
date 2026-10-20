import Mathlib.Tactic.Ring

/-!
# Raw carrier burden (Informational Incompleteness, Definition 4.3)

Mechanizes the raw whole-term carrier burden `Carr_raw(K, b)` of the canonical
trace of `F(a, b, S^K(0))` from `Rahnama_Informational_Incompleteness.tex`
Definition `def:raw-burden`:

    Carr_raw(K, b) = sum_{i=0}^{K} (i+1) * L(b) = (K+1)(K+2)/2 * L(b).

The closed form is stated division-free as `2 * carrierRaw L K = (K+1)(K+2)*L`
so it holds in `Nat` with no rounding side condition. Pure `Nat` arithmetic; no
information-theory or rewriting substrate is consumed.

## Audit slots

```
Relation: not applicable (pure Nat arithmetic; no Step / SafeStep / DPProblem).
Closure:  not applicable.
Strategy: not applicable.
Trust:    kernel-only. No sorry/admit/axiom/native_decide/csimp/unsafe.
Scope:    the canonical-trace raw carrier-burden sum and its closed form.
```
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.InformationalIncompleteness.CarrierBurden

/--
Proves: the raw whole-term carrier burden through trace depth `K`, i.e.
  `sum_{i=0}^{K} (i+1) * L`, by structural recursion on `K`.
Does not prove: any orientation, entropy, or information property; this is the
  carrier-length count only.
Relation: not applicable (pure Nat).
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: every payload code length `L : Nat` and depth `K : Nat`.
-/
def carrierRaw (L : Nat) : Nat → Nat
  | 0 => L
  | (k + 1) => carrierRaw L k + (k + 2) * L

/--
Proves: the division-free closed form `2 * carrierRaw L K = (K+1)*(K+2)*L`.
Does not prove: the `/2` form directly (avoided so the statement holds in `Nat`
  with no rounding hypothesis); divide both sides by 2 downstream if needed.
Relation: not applicable (pure Nat).
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only (induction on `K`, then `ring`).
Scope: every `L K : Nat`.
-/
theorem carrierRaw_two_mul (L K : Nat) :
    2 * carrierRaw L K = (K + 1) * (K + 2) * L := by
  induction K with
  | zero => rfl
  | succ k ih =>
      have h : carrierRaw L (k + 1) = carrierRaw L k + (k + 2) * L := rfl
      rw [h, Nat.mul_add, ih]; ring

/--
Proves: monotonicity of the raw carrier burden in the depth `K`
  (`carrierRaw L K ≤ carrierRaw L (K+1)`).
Does not prove: strict growth when `L = 0`.
Relation: not applicable (pure Nat).
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: every `L K : Nat`.
-/
theorem carrierRaw_le_succ (L K : Nat) :
    carrierRaw L K ≤ carrierRaw L (K + 1) := by
  have h : carrierRaw L (K + 1) = carrierRaw L K + (K + 2) * L := rfl
  rw [h]; exact Nat.le_add_right _ _

/-- Audit anchor for the raw carrier-burden surface. -/
def carrier_burden_anchor : String :=
  "OperatorKO7.Meta.InformationalIncompleteness.CarrierBurden.carrierRaw_two_mul"

end OperatorKO7.Meta.InformationalIncompleteness.CarrierBurden
