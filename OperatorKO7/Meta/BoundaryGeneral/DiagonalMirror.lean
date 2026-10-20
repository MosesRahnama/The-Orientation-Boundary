/-!
# Diagonal mirror recognition

An equality surface maps pairs of terms to traces and assigns zero carrier burden to the null record `void`. A `MirrorRecognizer` maps every reflexive trace `eqW a a` to `void`. A `DiagonalMisrecognition` maps one reflexive trace to a non-null trace with positive burden.

`mirror_cost_separation` proves that every mirror recognizer has lower burden on the same diagonal than the given misrecognition. `ko7_mirror_cost_separation` proves the strict inequality for the concrete `eqW` surface, with burden zero for the mirror recognizer and one for the identity misrecognizer.

Trust: no `sorry`, `axiom`, or `native_decide` occurs in this module.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.BoundaryGeneral.DiagonalMirror

/-! ### Abstract equality surface and mirror criterion -/

/-- A surface with a term type, trace type, `eqW` constructor, null record `void`, and carrier-burden measure assigning zero to `void`. -/
structure EqWSurface where
  Witness : Type
  Trace : Type
  eqW : Witness → Witness → Trace
  void : Trace
  burden : Trace → Nat
  burden_void : burden void = 0

/-- A mirror recognizer maps every reflexive trace `eqW a a` to the null record. -/
structure MirrorRecognizer (S : EqWSurface) where
  eval : S.Trace → S.Trace
  diagonal_to_void : ∀ a : S.Witness, eval (S.eqW a a) = S.void

/-- A mirror recognizer spends zero carrier burden on every reflexive diagonal. -/
theorem MirrorRecognizer.diagonal_burden_zero {S : EqWSurface} (R : MirrorRecognizer S)
    (a : S.Witness) : S.burden (R.eval (S.eqW a a)) = 0 := by
  rw [R.diagonal_to_void a, S.burden_void]

/-- A distinction probe returns the null record on every reflexive diagonal. The diagonal carries identity data but no distinction. -/
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

/-- On the same reflexive diagonal, every mirror recognizer has strictly lower carrier burden than the given misrecognition. -/
theorem mirror_cost_separation {S : EqWSurface} (R : MirrorRecognizer S)
    (D : DiagonalMisrecognition S) :
    S.burden (R.eval (S.eqW D.witness D.witness))
      < S.burden (D.eval (S.eqW D.witness D.witness)) := by
  rw [R.diagonal_burden_zero D.witness]
  exact D.positive_burden

/-! ### Concrete `eqW` surface -/

/-- The trace type distinguishes the null trace `void` from pair traces `diff a b`. -/
inductive EqWTrace (W : Type) where
  | void
  | diff (a b : W)
  deriving DecidableEq

/-- Carrier burden: `void` is free; a `diff` record costs one unit. -/
def EqWTrace.burden {W : Type} : EqWTrace W → Nat
  | .void => 0
  | .diff _ _ => 1

/-- A concrete surface whose pair map is `EqWTrace.diff`. -/
def ko7EqWSurface (W : Type) : EqWSurface where
  Witness := W
  Trace := EqWTrace W
  eqW := EqWTrace.diff
  void := EqWTrace.void
  burden := EqWTrace.burden
  burden_void := rfl

/-- The mirror evaluator maps reflexive `diff a a` traces to `void` and leaves distinct pairs unchanged. -/
def ko7MirrorEval {W : Type} [DecidableEq W] : EqWTrace W → EqWTrace W
  | .void => .void
  | .diff a b => if a = b then .void else .diff a b

/-- The mirror recognizer for the concrete `eqW` surface. -/
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

/-- On the concrete `eqW` surface, the mirror recognizer has burden zero on the reflexive diagonal, while the identity misrecognizer has burden one. -/
theorem ko7_mirror_cost_separation (W : Type) [DecidableEq W] (w : W) :
    (ko7EqWSurface W).burden
        ((ko7MirrorRecognizer W).eval ((ko7EqWSurface W).eqW w w))
      < (ko7EqWSurface W).burden
        ((ko7DiagonalMisrecognition W w).eval ((ko7EqWSurface W).eqW w w)) :=
  mirror_cost_separation (ko7MirrorRecognizer W) (ko7DiagonalMisrecognition W w)

#print axioms mirror_cost_separation
#print axioms ko7_mirror_cost_separation

end OperatorKO7.Meta.BoundaryGeneral.DiagonalMirror
