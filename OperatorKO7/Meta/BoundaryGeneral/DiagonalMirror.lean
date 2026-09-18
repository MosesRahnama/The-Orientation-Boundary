/-!
# Theory X: Diagonal mirror recognition

Boundary-general cross-paper packet, Theory X. The "mirror test" formalized: a system either
recognizes the reflexive equality-witness diagonal `eqW a a` as already-known (the null record
`void`, zero carrier burden), or misrecognizes it as a fresh non-null trace and pays strictly
positive carrier burden for a diagonal that carries no distinction.

This is the equality-witness reading of the `SafeStep`/`eqW` confluence anomaly of the Orientation
Boundary calculus: `eqW a a → void` (`R_eq_refl`) is exactly diagonal recognition, while treating
`eqW a a` as a fresh redex is diagonal misrecognition and creates circular carrier burden.

`mirror_cost_separation` is the load-bearing theorem (recognition burden `<` misrecognition burden
on the same diagonal); `ko7_mirror_cost_separation` instantiates it on a concrete `eqW` surface so
the statement is non-vacuous.

No `sorry`, `axiom`, or `native_decide`.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.BoundaryGeneral.DiagonalMirror

/-! ### Abstract equality-witness surface and the mirror criterion -/

/-- An equality-witness surface: witness terms, a trace space, the `eqW` constructor, a null record
`void` with zero carrier burden, and a carrier-burden measure on traces. -/
structure EqWSurface where
  Witness : Type
  Trace : Type
  eqW : Witness → Witness → Trace
  void : Trace
  burden : Trace → Nat
  burden_void : burden void = 0

/-- A mirror recognizer is a partial evaluator that sends every reflexive diagonal `eqW a a` to the
null record: it treats the reflexive diagonal as already known rather than as a fresh query. -/
structure MirrorRecognizer (S : EqWSurface) where
  eval : S.Trace → S.Trace
  diagonal_to_void : ∀ a : S.Witness, eval (S.eqW a a) = S.void

/-- A mirror recognizer spends zero carrier burden on every reflexive diagonal. -/
theorem MirrorRecognizer.diagonal_burden_zero {S : EqWSurface} (R : MirrorRecognizer S)
    (a : S.Witness) : S.burden (R.eval (S.eqW a a)) = 0 := by
  rw [R.diagonal_to_void a, S.burden_void]

/-- A distinction probe returns the null record on every reflexive diagonal: it can fire only on
genuinely distinct witnesses. The reflexive diagonal carries identity data but no distinction. -/
def IsDistinctionProbe (S : EqWSurface) (probe : S.Witness → S.Witness → S.Trace) : Prop :=
  ∀ a : S.Witness, probe a a = S.void

theorem distinctionProbe_burden_zero {S : EqWSurface}
    {probe : S.Witness → S.Witness → S.Trace} (h : IsDistinctionProbe S probe) (a : S.Witness) :
    S.burden (probe a a) = 0 := by
  rw [h a, S.burden_void]

/-- A diagonal misrecognition: the evaluator sends some reflexive diagonal to a non-null trace with
strictly positive carrier burden. -/
structure DiagonalMisrecognition (S : EqWSurface) where
  eval : S.Trace → S.Trace
  witness : S.Witness
  nonvoid : eval (S.eqW witness witness) ≠ S.void
  positive_burden : 0 < S.burden (eval (S.eqW witness witness))

/-- **Mirror cost separation (Theorem 10.6).** On the same reflexive diagonal, any mirror
recognizer spends strictly less carrier burden (namely zero) than any misrecognizer. The diagonal
carries no distinction, so the misrecognizer's extra burden is paid for nothing. -/
theorem mirror_cost_separation {S : EqWSurface} (R : MirrorRecognizer S)
    (D : DiagonalMisrecognition S) :
    S.burden (R.eval (S.eqW D.witness D.witness))
      < S.burden (D.eval (S.eqW D.witness D.witness)) := by
  rw [R.diagonal_burden_zero D.witness]
  exact D.positive_burden

/-! ### A concrete `eqW` surface (non-vacuity) -/

/-- The KO7-style equality-witness record: `void` (from `eqW a a → void`) or a `diff` record (from
`eqW a b → integrate(merge a b)` for `a ≠ b`). -/
inductive EqWTrace (W : Type) where
  | void
  | diff (a b : W)
  deriving DecidableEq

/-- Carrier burden: `void` is free; a `diff` record costs one unit. -/
def EqWTrace.burden {W : Type} : EqWTrace W → Nat
  | .void => 0
  | .diff _ _ => 1

/-- A concrete equality-witness surface modeling KO7's `eqW`. -/
def ko7EqWSurface (W : Type) : EqWSurface where
  Witness := W
  Trace := EqWTrace W
  eqW := EqWTrace.diff
  void := EqWTrace.void
  burden := EqWTrace.burden
  burden_void := rfl

/-- The canonical mirror recognizer: collapse a reflexive `diff a a` to `void`, leave genuinely
distinct records intact. -/
def ko7MirrorEval {W : Type} [DecidableEq W] : EqWTrace W → EqWTrace W
  | .void => .void
  | .diff a b => if a = b then .void else .diff a b

/-- The canonical mirror recognizer on the concrete `eqW` surface. -/
def ko7MirrorRecognizer (W : Type) [DecidableEq W] : MirrorRecognizer (ko7EqWSurface W) where
  eval := ko7MirrorEval
  diagonal_to_void := by
    intro a
    show ko7MirrorEval (EqWTrace.diff a a) = EqWTrace.void
    show (if a = a then EqWTrace.void else EqWTrace.diff a a) = EqWTrace.void
    exact if_pos rfl

/-- A concrete misrecognition: the identity evaluator leaves the reflexive diagonal `diff w w`
non-null, paying one unit of carrier burden for zero distinction. -/
def ko7DiagonalMisrecognition (W : Type) (w : W) : DiagonalMisrecognition (ko7EqWSurface W) where
  eval := id
  witness := w
  nonvoid := by
    show EqWTrace.diff w w ≠ EqWTrace.void
    intro h
    exact EqWTrace.noConfusion h
  positive_burden := by
    show (0 : Nat) < 1
    exact Nat.one_pos

/-- **Non-vacuity.** On the concrete `eqW` surface, the canonical mirror recognizer strictly beats
the identity misrecognizer on the reflexive diagonal: zero burden versus one. -/
theorem ko7_mirror_cost_separation (W : Type) [DecidableEq W] (w : W) :
    (ko7EqWSurface W).burden
        ((ko7MirrorRecognizer W).eval ((ko7EqWSurface W).eqW w w))
      < (ko7EqWSurface W).burden
        ((ko7DiagonalMisrecognition W w).eval ((ko7EqWSurface W).eqW w w)) :=
  mirror_cost_separation (ko7MirrorRecognizer W) (ko7DiagonalMisrecognition W w)

#print axioms mirror_cost_separation
#print axioms ko7_mirror_cost_separation

end OperatorKO7.Meta.BoundaryGeneral.DiagonalMirror
