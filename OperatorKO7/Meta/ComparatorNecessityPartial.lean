import OperatorKO7.Meta.ComparatorNecessity

/-!
# Partial (abstaining) comparator necessity: decisive sound three-valued comparison ⇔ decidable equality (G6)

`ComparatorNecessity.lean` characterises the **exact total** Boolean comparator: a total
`cmp : W → W → Bool` that is both sound and complete for equality is exactly the data of
`DecidableEq W`. But the program's actual decision interface is **three-valued** Y/N/U
(yes / no / abstain): a real comparator is allowed to *refuse* (abstain) rather than commit.
This file isolates the resource of that partial, abstaining interface.

A **sound partial comparator** is a `pcmp : W → W → Option Bool` that never lies when it commits:
`some true` forces `a = b`, `some false` forces `a ≠ b`, and `none` (abstain / U) makes no claim.
Soundness alone is cheap: `fun _ _ => none` (always abstain) is sound and decides nothing. The
characterisation is therefore about the *decisive* fragment — comparators that never abstain.

## What is proved (PROVEN-IN-LEAN)

* `SoundPartialComparator W`: a `pcmp : W → W → Option Bool` with the two soundness fields
  (`sound_pos`, `sound_neg`); `none` is the abstain verdict carrying no claim.
* `Decisive P`: the predicate `∀ a b, (P.pcmp a b).isSome` ("never abstains").
* `decisive_exactComparator` (⇒, the bridge): a *decisive* sound partial comparator induces an
  `ExactComparator` (the exact-total object of `ComparatorNecessity`), reading the verdict off the
  forced `some` value.
* `decisive_decidableEq` (⇒): consequently a decisive sound partial comparator yields
  `DecidableEq W`, obtained by **reusing** `ComparatorNecessity.exactComparator_decidableEq` on the
  induced exact comparator (the exact-total result is cited, not re-proved).
* `decidableEq_decisivePartial` (⇐): `DecidableEq W` yields a sound partial comparator
  `pcmp a b := some (decide (a = b))`, with both soundness fields discharged, and that comparator is
  decisive (`decidableEq_decisivePartial_decisive`).

Together: *a decisive sound three-valued comparator ⇔ decidable equality.* The partial interface
with abstention permitted is **strictly weaker**: `alwaysAbstain` (below) is a genuinely sound
partial comparator that is not decisive, so it manufactures no `DecidableEq`.

## Three-valued classification (the Y/N/U refusal interface)

`Verdict` is the Y/N/U codomain; `classify : Option Bool → Verdict` sends
`some true ↦ Y`, `some false ↦ N`, `none ↦ U`. We prove:

* `classify_exhaustive`: every output is exactly one of `Y`, `N`, `U` (and they are pairwise
  distinct), so the classification is total and non-overlapping;
* `classify_yes_eq` / `classify_no_ne`: a *sound* comparator never misclassifies — a `Y` verdict
  entails `a = b`, an `N` verdict entails `a ≠ b`. `U` (abstain) entails nothing, by design.

This is the abstaining analogue of the exact-total comparator: the program's refusal interface is a
sound partial comparator whose three-valued read-out is `classify`.

## Framework connection (KO7 reading)

The exact-total file explains *why* a comparator is a meta-level resource (the object signature
cannot synthesise equality decision internally, W16.7
`disequality_not_sigma_expressible_unconditional`). This file refines that reading to the honest
operational shape: the engine does not expose a total Bool oracle, it exposes a *partial* one that
may abstain (U). Decisiveness — never abstaining — is the exact extra resource that upgrades the
abstaining interface to full `DecidableEq`, equivalently to an `ExactComparator`. Non-vacuity is
witnessed on the kernel carrier `OperatorKO7.Trace` (which derives `DecidableEq` in
`OperatorKO7/Kernel.lean`).

## Audit slots (Gate R2–R5, W1/W8/W9)
* Relation: none. No rewriting relation appears; this is pure typeclass / `Option Bool` bookkeeping.
* Trust: no `sorry`/`admit`/`axiom`/`constant`/`opaque`/`partial`/`unsafe`/`native_decide`/
  `bv_decide`/`@[csimp]`/`extern`/`implemented_by`. `DecidableEq` and `ExactComparator` are reused
  from core / `ComparatorNecessity`, never redefined.
* Non-vacuity (R5): `decisivePartial_Trace` exhibits a concrete decisive sound partial comparator on
  `OperatorKO7.Trace`; `alwaysAbstain` exhibits a sound but non-decisive one (over `Bool`), proving
  the partial interface is strictly weaker than the decisive one (`alwaysAbstain_not_decisive`).
* Closure: axiom inventory printed below; each headline decl must stay inside
  `{propext, Classical.choice, Quot.sound}`.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.ComparatorNecessityPartial

open OperatorKO7.Meta.ComparatorNecessity

/-! ## 1. Sound partial (abstaining) comparator -/

/-- A **sound partial comparator** on `W`: a three-valued `pcmp : W → W → Option Bool` that never
lies when it commits. `some true` is a positive verdict (Y) that *forces* equality; `some false` is
a negative verdict (N) that *forces* disequality; `none` is abstention (U) and carries no claim.
Only soundness is required — no completeness, and no obligation ever to commit. This is the honest
shape of the program's Y/N/U decision interface. -/
structure SoundPartialComparator (W : Type _) where
  /-- The three-valued comparison function (`none` = abstain). -/
  pcmp : W → W → Option Bool
  /-- Positive soundness: a `some true` (Y) verdict forces equality. -/
  sound_pos : ∀ a b, pcmp a b = some true → a = b
  /-- Negative soundness: a `some false` (N) verdict forces disequality. -/
  sound_neg : ∀ a b, pcmp a b = some false → a ≠ b

/-! ## 2. Decisiveness (never abstains) -/

/-- A sound partial comparator is **decisive** when it never abstains: every pair receives a
committed verdict (`some _`), equivalently `pcmp a b ≠ none`. This is the exact extra resource over
soundness that the characterisation below pins down. -/
def Decisive {W : Type _} (P : SoundPartialComparator W) : Prop :=
  ∀ a b, (P.pcmp a b).isSome

/-- Restatement of decisiveness in `≠ none` form, for convenience. -/
theorem decisive_iff_ne_none {W : Type _} (P : SoundPartialComparator W) :
    Decisive P ↔ ∀ a b, P.pcmp a b ≠ none := by
  unfold Decisive
  constructor
  · intro h a b hnone
    have := h a b
    rw [hnone] at this
    exact Bool.noConfusion this
  · intro h a b
    cases hc : P.pcmp a b with
    | none => exact absurd hc (h a b)
    | some v => rfl

/-! ## 3. (⇒) A decisive sound partial comparator induces an exact total comparator, hence `DecidableEq`.

The bridge `decisive_exactComparator` produces the `ExactComparator` object of
`ComparatorNecessity`; `decisive_decidableEq` then **reuses**
`ComparatorNecessity.exactComparator_decidableEq` on it (the exact-total ⇒ decidable-equality result
is cited, not re-proved). -/

/-- **(⇒ bridge) A decisive sound partial comparator induces an exact total comparator.**
Take `cmp a b := (P.pcmp a b).getD false`; decisiveness guarantees the `getD` default is never
reached, so `cmp` reads off the forced verdict. Soundness of `cmp` comes from `sound_pos`;
completeness comes from decisiveness together with `sound_neg` (a `false` verdict on an equal pair
would contradict `sound_neg`). This is the abstaining-to-exact upgrade that decisiveness licenses. -/
def decisive_exactComparator {W : Type _} (P : SoundPartialComparator W) (hP : Decisive P) :
    ExactComparator W where
  cmp a b := (P.pcmp a b).getD false
  sound_same := fun a b h => by
    -- `(P.pcmp a b).getD false = true`; decisiveness fixes `P.pcmp a b = some v`.
    cases hc : P.pcmp a b with
    | none =>
        have hsome := hP a b
        rw [hc] at hsome
        exact Bool.noConfusion hsome
    | some v =>
        rw [hc] at h
        -- `Option.getD (some v) false = v`, so `v = true`.
        simp only [Option.getD_some] at h
        subst h
        exact P.sound_pos a b hc
  complete_same := fun a b h => by
    -- `a = b`; show `(P.pcmp a b).getD false = true` using decisiveness + negative soundness.
    cases hc : P.pcmp a b with
    | none =>
        have hsome := hP a b
        rw [hc] at hsome
        exact Bool.noConfusion hsome
    | some v =>
        cases v with
        | true => rfl
        | false =>
            -- a `some false` verdict on `a = b` contradicts negative soundness.
            exact absurd h (P.sound_neg a b hc)

/-- **(⇒) A decisive sound partial comparator yields decidable equality.** Obtained by reusing
`ComparatorNecessity.exactComparator_decidableEq` on the exact comparator induced by
`decisive_exactComparator`. The exact-total ⇒ `DecidableEq` step is *not* re-proved here. -/
def decisive_decidableEq {W : Type _} (P : SoundPartialComparator W) (hP : Decisive P) :
    DecidableEq W :=
  exactComparator_decidableEq (decisive_exactComparator P hP)

/-! ## 4. (⇐) Decidable equality yields a decisive sound partial comparator. -/

/-- **(⇐) Decidable equality yields a sound partial comparator.** Take
`pcmp a b := some (decide (a = b))`; this comparator never abstains. Positive soundness is
`of_decide_eq_true` after `Option.some.inj`; negative soundness is `of_decide_eq_false` after
`Option.some.inj`. -/
def decidableEq_decisivePartial (W : Type _) [DecidableEq W] : SoundPartialComparator W where
  pcmp a b := some (decide (a = b))
  sound_pos := fun a b h => by
    -- `some (decide (a = b)) = some true` ⇒ `decide (a = b) = true` ⇒ `a = b`.
    have : decide (a = b) = true := Option.some.inj h
    exact of_decide_eq_true this
  sound_neg := fun a b h => by
    -- `some (decide (a = b)) = some false` ⇒ `decide (a = b) = false` ⇒ `a ≠ b`.
    have : decide (a = b) = false := Option.some.inj h
    exact of_decide_eq_false this

/-- The ⇐ comparator is **decisive**: it commits on every pair (`some _` is always `isSome`). So the
⇐ direction lands in the decisive fragment, matching the ⇒ direction's hypothesis. -/
theorem decidableEq_decisivePartial_decisive (W : Type _) [DecidableEq W] :
    Decisive (decidableEq_decisivePartial W) := by
  intro a b
  rfl

/-! ## 5. Three-valued (Y/N/U) classification of a partial comparator's output. -/

/-- The three-valued verdict codomain: `Y` (yes, equal), `N` (no, distinct), `U` (abstain). This is
the refusal interface's external alphabet. -/
inductive Verdict
  | Y
  | N
  | U
deriving DecidableEq, Repr

/-- Classify a raw `Option Bool` comparator output into the Y/N/U alphabet:
`some true ↦ Y`, `some false ↦ N`, `none ↦ U`. -/
def classify : Option Bool → Verdict
  | some true  => Verdict.Y
  | some false => Verdict.N
  | none       => Verdict.U

/-- **Exhaustiveness / mutual exclusion of the three-valued classification.** Every comparator
output classifies to exactly one of `Y`, `N`, `U`, and the three verdicts are pairwise distinct, so
the read-out is total and non-overlapping. Stated as: the classification is one of the three, and
each forces a definite shape of the underlying `Option Bool`. -/
theorem classify_exhaustive (o : Option Bool) :
    (classify o = Verdict.Y ∧ o = some true) ∨
    (classify o = Verdict.N ∧ o = some false) ∨
    (classify o = Verdict.U ∧ o = none) := by
  cases o with
  | none => exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  | some b =>
      cases b with
      | true  => exact Or.inl ⟨rfl, rfl⟩
      | false => exact Or.inr (Or.inl ⟨rfl, rfl⟩)

/-- The three verdicts are genuinely distinct (the classification alphabet has three points, so
"exactly one of three" in `classify_exhaustive` is non-degenerate). -/
theorem verdict_distinct :
    Verdict.Y ≠ Verdict.N ∧ Verdict.Y ≠ Verdict.U ∧ Verdict.N ≠ Verdict.U := by
  refine ⟨?_, ?_, ?_⟩ <;> intro h <;> exact Verdict.noConfusion h

/-- **No misclassification (Y).** For a *sound* partial comparator, a `Y` read-out forces equality.
`classify (pcmp a b) = Y` unfolds to `pcmp a b = some true`, then `sound_pos` applies. -/
theorem classify_yes_eq {W : Type _} (P : SoundPartialComparator W) (a b : W)
    (h : classify (P.pcmp a b) = Verdict.Y) : a = b := by
  -- `classify o = Y` iff `o = some true`; extract that, then apply positive soundness.
  cases hc : P.pcmp a b with
  | none => rw [hc] at h; exact Verdict.noConfusion h
  | some v =>
      cases v with
      | true => exact P.sound_pos a b hc
      | false => rw [hc] at h; exact Verdict.noConfusion h

/-- **No misclassification (N).** For a *sound* partial comparator, an `N` read-out forces
disequality. `classify (pcmp a b) = N` unfolds to `pcmp a b = some false`, then `sound_neg`
applies. -/
theorem classify_no_ne {W : Type _} (P : SoundPartialComparator W) (a b : W)
    (h : classify (P.pcmp a b) = Verdict.N) : a ≠ b := by
  cases hc : P.pcmp a b with
  | none => rw [hc] at h; exact Verdict.noConfusion h
  | some v =>
      cases v with
      | true => rw [hc] at h; exact Verdict.noConfusion h
      | false => exact P.sound_neg a b hc

/-! ## Non-vacuity (R5).

A concrete *decisive* sound partial comparator on the kernel carrier `OperatorKO7.Trace`, and a
genuinely *abstaining* (non-decisive) sound partial comparator, proving the partial interface is
strictly weaker than the decisive one. -/

/-- **Non-vacuity (decisive side).** `OperatorKO7.Trace` derives `DecidableEq`
(`OperatorKO7/Kernel.lean`), so `decidableEq_decisivePartial` gives a concrete decisive sound partial
comparator on it. -/
def decisivePartial_Trace : SoundPartialComparator OperatorKO7.Trace :=
  decidableEq_decisivePartial OperatorKO7.Trace

/-- The `Trace` comparator is decisive (reuses `decidableEq_decisivePartial_decisive`). -/
theorem decisivePartial_Trace_decisive : Decisive decisivePartial_Trace :=
  decidableEq_decisivePartial_decisive OperatorKO7.Trace

/-- **Non-vacuity (abstaining side).** The always-abstain comparator on `Bool`: it commits to no
verdict anywhere, yet is trivially sound (the soundness hypotheses `none = some _` are
unsatisfiable). A concrete inhabitant showing soundness does *not* entail decisiveness. -/
def alwaysAbstain : SoundPartialComparator Bool where
  pcmp _ _ := none
  sound_pos := fun _ _ h => Option.noConfusion h
  sound_neg := fun _ _ h => Option.noConfusion h

/-- **The partial interface is strictly weaker than the decisive one.** `alwaysAbstain` is a sound
partial comparator that is **not** decisive: on the pair `(true, true)` it abstains, so it cannot be
decisive. Hence a sound partial comparator need not yield `DecidableEq`; decisiveness is genuinely
extra. -/
theorem alwaysAbstain_not_decisive : ¬ Decisive alwaysAbstain := by
  intro h
  -- decisiveness would force `(alwaysAbstain.pcmp true true).isSome = true`, but it is `none`.
  have := h true true
  exact Bool.noConfusion this

/-- The abstaining comparator classifies every pair as `U`, confirming `none ↦ U` is the abstain
read-out. -/
theorem alwaysAbstain_classify_U (a b : Bool) :
    classify (alwaysAbstain.pcmp a b) = Verdict.U := rfl

/-! ## Axiom inventory (must be a subset of `{propext, Classical.choice, Quot.sound}`) -/

#print axioms decisive_exactComparator
#print axioms decisive_decidableEq
#print axioms decidableEq_decisivePartial
#print axioms decidableEq_decisivePartial_decisive
#print axioms decisive_iff_ne_none
#print axioms classify_exhaustive
#print axioms verdict_distinct
#print axioms classify_yes_eq
#print axioms classify_no_ne
#print axioms decisivePartial_Trace_decisive
#print axioms alwaysAbstain_not_decisive

end OperatorKO7.Meta.ComparatorNecessityPartial
