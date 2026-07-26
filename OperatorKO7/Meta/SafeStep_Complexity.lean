import OperatorKO7.Meta.ContextClosed_SN_Full

/-!
# Counted contextual reductions

`StepCtxFullPow` records the exact number of full contextual `Step` reductions.
The imported strict descent of the polynomial witness `W` yields an additive
drop bound and, using positivity of `W`, a strict source-weight bound. The
relation here is the full unguarded contextual relation `StepCtxFull`.
-/

open OperatorKO7 Trace
open OperatorKO7.PolyInterpretation

namespace MetaSN_KO7

/-- Exact-length reflexive-transitive closure of the full contextual relation. -/
inductive StepCtxFullPow : Trace → Nat → Trace → Prop
| refl (t : Trace) : StepCtxFullPow t 0 t
| tail {a b c : Trace} {n : Nat} (hab : StepCtxFull a b) (hbc : StepCtxFullPow b n c) :
    StepCtxFullPow a (n + 1) c

/-- Every counted full-context derivation has length bounded by the drop in `W`. -/
theorem stepCtxFullPow_length_le_W :
    ∀ {a b : Trace} {n : Nat}, StepCtxFullPow a n b → n + W b ≤ W a
  | _, _, _, StepCtxFullPow.refl t => by
      omega
  | _, _, _, StepCtxFullPow.tail (b := b) hab hbc => by
      have hdec : W b < W _ := W_orients_stepCtxFull hab
      have hstep : W b + 1 ≤ W _ := Nat.succ_le_of_lt hdec
      have htail := stepCtxFullPow_length_le_W hbc
      omega

/-- In particular, every full-context derivation has length strictly below the source weight. -/
theorem stepCtxFullPow_length_lt_W :
    ∀ {a b : Trace} {n : Nat}, StepCtxFullPow a n b → n < W a
  | _, b, _, hpow => by
      have hle := stepCtxFullPow_length_le_W hpow
      have hpos : 1 ≤ W b := W_pos b
      omega

end MetaSN_KO7
