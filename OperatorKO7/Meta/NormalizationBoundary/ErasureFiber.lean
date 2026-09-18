import OperatorKO7.Meta.NormalizationBoundary.AntiNormalizationMap
import Mathlib.Data.Fintype.EquivFin

set_option autoImplicit false

/-!
# The erased fiber of the normalization redex

The normalization redex `integrate (delta t) -> void` is the kernel's erasing
site.  `AntiNormalizationMap.lean` proves that its collapse `normalForm` has no
internal inverse.  This module supplies the quantitative content behind that
qualitative fact: it measures how much the collapse destroys.

* **The erased fiber is infinite** (`erasedFiberInfinite`).  The whole family
  `integrate (delta (deltaPow n))` is collapsed to `void`, and that family is
  injective, so one normal form is reached from infinitely many
  pairwise-distinct sources.

* **No finite token recovers the erased history**
  (`no_finite_token_separates_erased_history`).  For every `k`, every labelling
  of the fiber by `Fin k` identifies two distinct erased histories.  This is the
  normalization axis's cost law and it is a third regime: the confluence axis
  refuses exactly one bit per diagonal event, the orientation axis confesses a
  burden that grows with trace depth while remaining a computable function of
  it, and this axis erases a fiber no bounded token can separate.

* **The collapse is not a constant map** (`normalForm_not_constant`).  It fixes
  every term outside the redex family.  This is what distinguishes the
  normalization collapse from the two collapses already recorded on the
  orientation and confluence axes, both of which are constant.

* **The erasing site is its own site** (`normalization_redex_is_not_recursor_redex`,
  `normalization_redex_is_not_eqW_diagonal`).  The normalization redex is
  neither the duplicating recursor redex nor the `eqW` diagonal, so the three
  obstructions sit at three different rules of the same eight-rule kernel.

Recovery in the other direction is exact: `integrate_delta_injective` says the
redex constructor is injective, so an external history token distinguishes every
member of the fiber the collapse identified.  Erasure is unbounded and
many-to-one; licensed recovery is one-to-one.

The import base is deliberately minimal (`AntiNormalizationMap` and one Mathlib
finiteness module) so that this cost law does not depend on the shared-root
layer.  The three-face headline that does depend on it lives in
`ThreeFaces.lean`.

Relation: metatheoretic statements about the collapse map `normalForm` on the
KO7 `Trace` carrier.  These are not `Step`, `SafeStep`, or any contextual
closure of them, and nothing here is a termination, confluence, or
normalization theorem about the kernel relation.
Closure: not applicable.
Strategy: not applicable.
Property: irreversibility, specifically collapse non-injectivity and fiber
cardinality.
Trust: kernel-only; allowed axioms only.
-/

namespace OperatorKO7.Meta.NormalizationBoundary.ErasureFiber

universe u

open OperatorKO7 Trace
open OperatorKO7.Meta.NormalizationBoundary.AntiNormalizationMap

/-! ## The erased family -/

/-- The `delta` tower of height `n`. -/
def deltaPow : Nat → Trace
  | 0 => void
  | n + 1 => delta (deltaPow n)

/-- Height of the outermost `delta` chain. -/
def deltaHeight : Trace → Nat
  | delta t => deltaHeight t + 1
  | _ => 0

/-- The tower of height `n` has height `n`. -/
theorem deltaHeight_deltaPow (n : Nat) : deltaHeight (deltaPow n) = n := by
  induction n with
  | zero => rfl
  | succ k ih => simp only [deltaPow, deltaHeight, ih]

/-- Distinct heights give distinct towers. -/
theorem deltaPow_injective : Function.Injective deltaPow := by
  intro m n h
  have hh := congrArg deltaHeight h
  rwa [deltaHeight_deltaPow, deltaHeight_deltaPow] at hh

/-- **The redex constructor is injective.**  Distinct payloads give distinct
normalization redexes, so an external history token that carries the payload
distinguishes every source the collapse identifies.

Proves: `Function.Injective (fun t => integrate (delta t))`.
Trust: kernel-only. -/
theorem integrate_delta_injective :
    Function.Injective (fun t : Trace => integrate (delta t)) :=
  fun _ _ h => Trace.delta.inj (Trace.integrate.inj h)

/-- The `n`-th erased history: a normalization redex whose payload is the tower
of height `n`.  Every member of this family is collapsed to `void`. -/
def erasedHistory (n : Nat) : Trace := integrate (delta (deltaPow n))

/-- Every erased history lies in the fiber of `normalForm` over `void`. -/
theorem erasedHistory_normalForm (n : Nat) :
    normalForm (erasedHistory n) = void := rfl

/-- The erased histories are pairwise distinct. -/
theorem erasedHistory_injective : Function.Injective erasedHistory :=
  fun _ _ h => deltaPow_injective (integrate_delta_injective h)

/-! ## The fiber is infinite -/

/-- The fiber of the normalization collapse over `void`. -/
def ErasedFiber : Type := { t : Trace // normalForm t = void }

/-- The `n`-th erased history, as a point of the fiber. -/
def erasedPoint (n : Nat) : ErasedFiber :=
  ⟨erasedHistory n, erasedHistory_normalForm n⟩

/-- The erased histories are pairwise distinct as fiber points. -/
theorem erasedPoint_injective : Function.Injective erasedPoint :=
  fun _ _ h => erasedHistory_injective (congrArg Subtype.val h)

/-- **The erased fiber is infinite.**  One normal form is reached from
infinitely many pairwise-distinct sources, so the normalization redex destroys
an unbounded amount of structure.

Proves: `Infinite ErasedFiber`.
Does not prove: any statement about `Step`, `SafeStep`, or their closures.
Trust: kernel-only. -/
instance erasedFiberInfinite : Infinite ErasedFiber :=
  Infinite.of_injective erasedPoint erasedPoint_injective

/-- **No token from a finite alphabet recovers the erased history.**  For every
`k` and every labelling of the fiber by `Fin k`, two distinct erased histories
receive the same label.  This is the sharp form of the normalization cost law:
the confluence axis pays one bit per diagonal event and the orientation axis
pays a depth-indexed burden, while here no finite budget suffices at all.

Proves: `¬ Function.Injective tok` for every `tok : ErasedFiber → Fin k`.
Does not prove: a lower bound for any particular encoding scheme, or any
physical (Landauer) statement.
Trust: kernel-only. -/
theorem no_finite_token_separates_erased_history
    (k : Nat) (tok : ErasedFiber → Fin k) : ¬ Function.Injective tok := by
  intro hinj
  haveI : Finite ErasedFiber := Finite.of_injective tok hinj
  exact not_finite ErasedFiber

/-- The finite-alphabet theorem is not special to `Fin k`: no token valued in any finite type can
separate the erased fiber. -/
theorem no_finite_type_token_separates_erased_history
    {Token : Type u} [Finite Token] (tok : ErasedFiber → Token) :
    ¬ Function.Injective tok := by
  intro hinj
  haveI : Finite ErasedFiber := Finite.of_injective tok hinj
  exact not_finite ErasedFiber

/-- Equivalently, every exact recovery token for the erased history has an infinite carrier. -/
theorem exact_erasure_token_carrier_infinite
    {Token : Type u} (tok : ErasedFiber → Token) (hinj : Function.Injective tok) :
    Infinite Token :=
  Infinite.of_injective tok hinj

/-! ## The collapse is not constant -/

/-- `normalForm` fixes `void`. -/
theorem normalForm_void : normalForm void = void := rfl

/-- `normalForm` fixes a non-redex. -/
theorem normalForm_delta_void : normalForm (delta void) = delta void := rfl

/-- **The normalization collapse is not a constant map.**  It fixes every term
outside the redex family, so it separates `void` from `delta void`.

Proves: `¬ ∃ c, ∀ t, normalForm t = c`.
Trust: kernel-only. -/
theorem normalForm_not_constant : ¬ ∃ c : Trace, ∀ t : Trace, normalForm t = c := by
  rintro ⟨c, hc⟩
  have h1 : void = c := by rw [← normalForm_void]; exact hc void
  have h2 : delta void = c := by rw [← normalForm_delta_void]; exact hc (delta void)
  exact Trace.noConfusion (h1.trans h2.symm)

/-! ## Three distinct sites in one kernel -/

/-- The normalization redex is not the duplicating recursor redex. -/
theorem normalization_redex_is_not_recursor_redex (b s n t : Trace) :
    integrate (delta t) ≠ recΔ b s (delta n) := by
  intro h
  exact Trace.noConfusion h

/-- The normalization redex is not the `eqW` diagonal. -/
theorem normalization_redex_is_not_eqW_diagonal (a t : Trace) :
    integrate (delta t) ≠ eqW a a := by
  intro h
  exact Trace.noConfusion h

/-- **The normalization cost law, packaged.**  The erased fiber is infinite, no
finite token separates it, the collapse is not constant, and the redex
constructor is injective so the external history token is exact.

Proves: the conjunction of the four facts above.
Does not prove: any kernel-relation termination or confluence statement.
Trust: kernel-only. -/
theorem normalization_erasure_is_unbounded :
    Infinite ErasedFiber
      ∧ (∀ (k : Nat) (tok : ErasedFiber → Fin k), ¬ Function.Injective tok)
      ∧ (¬ ∃ c : Trace, ∀ t : Trace, normalForm t = c)
      ∧ Function.Injective (fun t : Trace => integrate (delta t)) :=
  ⟨erasedFiberInfinite, no_finite_token_separates_erased_history,
    normalForm_not_constant, integrate_delta_injective⟩

#print axioms deltaHeight_deltaPow
#print axioms deltaPow_injective
#print axioms integrate_delta_injective
#print axioms erasedHistory_normalForm
#print axioms erasedHistory_injective
#print axioms erasedPoint_injective
#print axioms erasedFiberInfinite
#print axioms no_finite_token_separates_erased_history
#print axioms no_finite_type_token_separates_erased_history
#print axioms exact_erasure_token_carrier_infinite
#print axioms normalForm_void
#print axioms normalForm_delta_void
#print axioms normalForm_not_constant
#print axioms normalization_redex_is_not_recursor_redex
#print axioms normalization_redex_is_not_eqW_diagonal
#print axioms normalization_erasure_is_unbounded

end OperatorKO7.Meta.NormalizationBoundary.ErasureFiber
