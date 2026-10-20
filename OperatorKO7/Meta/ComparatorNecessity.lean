import OperatorKO7.Kernel

/-!
# Comparator necessity: exact total Boolean comparison ⇔ decidable equality (WAVE2-C)

This self-contained file isolates the *comparator-necessity* fact behind the KO7
memory/distinction reading: an exact, total `Bool` comparator on a carrier `W` is
exactly the same data as `DecidableEq W`. Neither direction is deep; both are
near-definitional. The file's job is to *name* the equivalence and to state its
KO7 reading precisely, not to oversell it.

## What is proved (PROVEN-IN-LEAN)

* `ExactComparator W`: a total `cmp : W → W → Bool` that is **sound** (`cmp a b = true → a = b`)
  and **complete** (`a = b → cmp a b = true`) for equality.
* `exactComparator_decidableEq` (⇒): an exact total comparator manufactures `DecidableEq W`.
* `decidableEq_exactComparator` (⇐): `DecidableEq W` manufactures an exact total comparator
  (namely `fun a b => decide (a = b)`).

Together: *exact total Boolean comparison ⇔ decidable equality.* This is the comparator-necessity
result; honest typing is "clean, near-definitional equivalence", not "deep".

## Framework connection (KO7 reading)

The information-theoretic content of *why* such a comparator is non-trivial to obtain lives in two
already-proven anchors, cited here by full name (not re-proved):

* `OperatorKO7.Meta.InformationalIncompleteness.MemoryDistinction.equality_not_one_cell_observable`:
  on a carrier with two distinct elements there is **no** `f : W → Bool` deciding equality from ONE
  held cell. So an `ExactComparator W` cannot be a one-cell observer; its `cmp` is irreducibly a
  function of BOTH arguments.
* `OperatorKO7.Meta.InformationalIncompleteness.MemoryDistinction.equality_is_two_cell_observable`:
  with `DecidableEq W`, the two-cell comparator `decide (· = ·)` does decide the distinction. This is
  exactly the `cmp` produced by `decidableEq_exactComparator` below. The two-cell / disequality
  resource is precisely what an `ExactComparator` packages.

The object-signature reading is the W16.7 anchor
`OperatorKO7.Meta.SafeStep.SyntacticNonDerivability.disequality_not_sigma_expressible_unconditional`:
the disequality predicate is **not** Σ-expressible by any finite combination of the KO7 rewriting
symbols. Read against this file: the *meta-level* carrier `OperatorKO7.Trace` has `DecidableEq`
(derived in `OperatorKO7/Kernel.lean`), so by `decidableEq_exactComparator` it has an
`ExactComparator`; but the *object signature* cannot manufacture that comparator internally, because
its disequality decision is not Σ-expressible. The comparator is a meta-level resource, supplied from
outside the rewriting layer — never synthesised by the object calculus. `Trace` witnesses the meta
side (`exactComparator_Trace` below); the object side is closed by the cited W16.7 theorem.

## Audit slots (Gate R2–R5, W1/W8/W9)
* Relation: none. No rewriting relation appears; this is pure typeclass/`Bool` bookkeeping.
* Trust: no `sorry`/`admit`/`axiom`/`opaque`/`partial`/`unsafe`/`native_decide`/`bv_decide`/`@[csimp]`.
  `DecidableEq` is reused from core, never redefined.
* Non-vacuity (R5): `ExactComparator` is inhabited — `exactComparator_Trace` exhibits one on the KO7
  kernel carrier `OperatorKO7.Trace`, and the round-trip lemma `exactComparator_decidableEq_cmp`
  shows the two directions agree definitionally on `Bool` values.
* Closure: axiom inventory printed below; each headline decl must stay inside
  `{propext, Classical.choice, Quot.sound}`.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.ComparatorNecessity

/-- An **exact total Boolean comparator** on `W`: a total `cmp : W → W → Bool` that decides equality,
both ways. `sound_same` is soundness (a `true` verdict forces equality); `complete_same` is
completeness (equal inputs force a `true` verdict). This is the "exact total comparison" side of the
comparator-necessity equivalence. -/
structure ExactComparator (W : Type _) where
  /-- The total comparison function. -/
  cmp : W → W → Bool
  /-- Soundness: a positive verdict forces equality. -/
  sound_same : ∀ a b, cmp a b = true → a = b
  /-- Completeness: equal inputs force a positive verdict. -/
  complete_same : ∀ a b, a = b → cmp a b = true

/-- **(⇒) An exact total comparator yields decidable equality.** Decide `a = b` by inspecting
`C.cmp a b`: a `true` verdict is upgraded to `a = b` by soundness; a `false` verdict refutes `a = b`,
since completeness would otherwise force the verdict to be `true`. Near-definitional; no classical
input. -/
def exactComparator_decidableEq {W : Type _} (C : ExactComparator W) : DecidableEq W :=
  fun a b =>
    match h : C.cmp a b with
    | true  => isTrue (C.sound_same a b h)
    | false => isFalse (fun hab => by
        have : C.cmp a b = true := C.complete_same a b hab
        rw [this] at h
        exact Bool.noConfusion h)

/-- **(⇐) Decidable equality yields an exact total comparator.** Take `cmp a b := decide (a = b)`.
Soundness is `of_decide_eq_true`; completeness is `decide_eq_true` applied to the supplied equality.
Near-definitional; no classical input. -/
def decidableEq_exactComparator (W : Type _) [DecidableEq W] : ExactComparator W where
  cmp a b := decide (a = b)
  sound_same := fun _ _ h => of_decide_eq_true h
  complete_same := fun _ _ hab => decide_eq_true hab

/-- Round-trip sanity (R5 non-vacuity support): the comparator built from `DecidableEq W` computes
`decide (a = b)` definitionally, so the ⇐ then ⇒ trip returns the ambient decision procedure on every
pair. Stated as the pointwise equation on `cmp`. -/
theorem exactComparator_decidableEq_cmp {W : Type _} [DecidableEq W] (a b : W) :
    (decidableEq_exactComparator W).cmp a b = decide (a = b) := rfl

/-- **Non-vacuity witness.** The KO7 kernel carrier `OperatorKO7.Trace` derives `DecidableEq`
(`OperatorKO7/Kernel.lean`), so it carries an `ExactComparator`. This is the *meta-level* comparator
that the object signature cannot synthesise internally (W16.7,
`disequality_not_sigma_expressible_unconditional`). -/
noncomputable def exactComparator_Trace : ExactComparator OperatorKO7.Trace :=
  decidableEq_exactComparator OperatorKO7.Trace

/-! ## Axiom inventory (must be a subset of `{propext, Classical.choice, Quot.sound}`) -/

#print axioms exactComparator_decidableEq
#print axioms decidableEq_exactComparator
#print axioms exactComparator_decidableEq_cmp
#print axioms exactComparator_Trace

end OperatorKO7.Meta.ComparatorNecessity
