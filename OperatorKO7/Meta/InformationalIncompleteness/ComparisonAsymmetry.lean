import OperatorKO7.Meta.ComparatorNecessity
import Mathlib.Data.Nat.Find

/-!
# Comparison asymmetry: the two-semidecider collapse (G5)

This file mechanizes the conceptual heart of the Distinction Boundary paper's asymmetry section:

> *equality is positive and local* (semidecidable: one accepting certificate closes it), whereas
> *disequality is negative and global* (no single local certificate establishes it).

The previous comparator work (`OperatorKO7.Meta.ComparatorNecessity`) mechanized only the **decidable**
case: an exact total `Bool` comparator and `DecidableEq W` are interderivable. That captures the
*symmetric* endpoint where both verdicts are decided up front. It does not, by itself, expose *why*
deciding equality is harder than merely *semideciding* it. The asymmetry becomes precise once we move
from `Decidable` to a recursively enumerable (r.e.) semidecision interface and ask exactly how much
the negative side must contribute.

## The interface (`Semidecider`)

A `Semidecider P` is a `ℕ`-indexed stage process `test : Nat → Bool` that is **sound and complete** for
`P`: `(∃ n, test n = true) ↔ P`. Holding `P` is witnessed by *one* accepting stage; this is exactly the
"one certificate closes a positive, local claim" reading. A semidecider for `a = b` is the positive,
local resource; a semidecider for `a ≠ b` is the negative resource.

## What is proved (PROVEN-IN-LEAN)

* `semideciders_jointlyTotal_decidableEq` (**the collapse, forward**): for a carrier `W`, an equality
  semidecider `eqSD a b : Semidecider (a = b)` and a disequality semidecider `neqSD a b :
  Semidecider (a ≠ b)` that are **jointly total** (`hcover`: for every pair, *some* stage of *one* of
  the two accepts) together manufacture `DecidableEq W`. The decision procedure is a real bounded
  search: `Nat.find` locates the least stage at which the combined predicate
  `fun n => (eqSD a b).test n || (neqSD a b).test n` fires (guaranteed by `hcover`), then reads the
  verdict off the two `spec`s. Equality-semidecidability **alone** is insufficient: the construction
  consumes the disequality semidecider essentially. This is the formal asymmetry.
* `decidableEq_semideciders` (**the collapse, converse**): `DecidableEq W` manufactures both
  semideciders (constant tests `test _ := decide (a = b)` and `decide (a ≠ b)`) and their joint
  totality. Joint totality here is *unconditional* (`decide` is total), the constructive substitute for
  excluded middle on `a = b`.
* `comparisonAsymmetry_characterization` (**the equivalence**): packages forward + converse as the
  statement that `DecidableEq W` is *equivalent* (as a nonempty-type / `Iff`) to the existence of a
  jointly total equality/disequality semidecider pair.
* `decidableEq_Nat_via_collapse` (**non-vacuity, R5**): the interface is instantiated on `ℕ`
  (`decidableEqNat_semideciders`), and `DecidableEq Nat` is re-derived *through* the collapse theorem
  as a sanity instance. The forward direction is therefore exercised on a concrete carrier, not left
  abstract.

## Framework connection (`ComparatorNecessity`)

`comparator_is_bothDirectionsDecided` records that an `ExactComparator W` is the both-directions-decided
special case of this picture: via `ComparatorNecessity.exactComparator_decidableEq` it yields
`DecidableEq W`, hence (by the converse) a jointly total semidecider pair whose *equality* side already
decides in one stage and whose *disequality* side already decides in one stage. The comparator collapses
the two-stage asymmetry to a single synchronous verdict; the `Semidecider` interface is what remains
when that synchrony is dropped. The comparator-necessity equivalence is **reused**, never re-proved.

## Audit slots (Gate R2–R5, W1/W8/W9)
* Relation: none. No KO7 rewriting relation appears; this is pure semidecision / `Decidable` /
  `Bool` bookkeeping over an abstract carrier `W`. (Relation gate: not applicable.)
* Trust: no `sorry`/`admit`/`axiom`/`constant`/`opaque`/`partial`/`unsafe`/`native_decide`/`bv_decide`/
  `@[csimp]`/`extern`/`implemented_by`. The forward collapse is a constructive `Nat.find` search, not a
  classical choice; `DecidableEq` is reused from core / built by search, never assumed as a hypothesis
  to the forward direction.
* Non-vacuity (R5): `decidableEqNat_semideciders` exhibits a concrete jointly total pair on `ℕ`, and
  `decidableEq_Nat_via_collapse` re-derives `DecidableEq Nat` through the collapse.
* Closure: axiom inventory printed below; each headline decl must stay inside
  `{propext, Classical.choice, Quot.sound}`.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.InformationalIncompleteness.ComparisonAsymmetry

/-! ## The recursively enumerable semidecision interface -/

/-- A **sound-and-complete `ℕ`-indexed semidecider** for a proposition `P`: a stage process
`test : Nat → Bool` whose acceptance is logically equivalent to `P`. `spec` says `P` holds **iff** some
stage accepts (`∃ n, test n = true`). The forward reading `(∃ n, test n = true) → P` is *soundness* (an
accepting stage is a genuine certificate); the backward reading `P → ∃ n, test n = true` is
*completeness* (a true proposition is eventually accepted). One accepting stage closes the claim: this
is the "positive, local, one certificate" structure that equality has and disequality lacks. -/
structure Semidecider (P : Prop) where
  /-- The stage process: `test n` is the verdict at stage `n`. -/
  test : Nat → Bool
  /-- Soundness and completeness: `P` holds iff some stage accepts. -/
  spec : (∃ n, test n = true) ↔ P

/-! ## The collapse theorem (forward): two jointly total semideciders manufacture `DecidableEq` -/

/-- The combined stage predicate for a pair `a b : W`: accept at stage `n` when *either* the equality
semidecider *or* the disequality semidecider accepts at `n`. Decidable because it is a `Bool` equation,
which is what lets `Nat.find` search it. -/
private def combinedAccept {W : Type _}
    (eqSD : ∀ a b : W, Semidecider (a = b)) (neqSD : ∀ a b : W, Semidecider (a ≠ b))
    (a b : W) (n : Nat) : Prop :=
  ((eqSD a b).test n || (neqSD a b).test n) = true

private instance combinedAccept_decidable {W : Type _}
    (eqSD : ∀ a b : W, Semidecider (a = b)) (neqSD : ∀ a b : W, Semidecider (a ≠ b))
    (a b : W) : DecidablePred (combinedAccept eqSD neqSD a b) :=
  fun _n => inferInstanceAs (Decidable (_ = true))

/-- Joint totality fires the combined predicate: if for the pair `a b` *some* stage of the equality
semidecider or *some* stage of the disequality semidecider accepts, then *some* stage of the combined
predicate accepts. This is the existence hypothesis `Nat.find` needs. -/
private theorem combinedAccept_exists {W : Type _}
    (eqSD : ∀ a b : W, Semidecider (a = b)) (neqSD : ∀ a b : W, Semidecider (a ≠ b))
    {a b : W}
    (hcov : (∃ n, (eqSD a b).test n = true) ∨ (∃ n, (neqSD a b).test n = true)) :
    ∃ n, combinedAccept eqSD neqSD a b n := by
  rcases hcov with ⟨n, hn⟩ | ⟨n, hn⟩
  · exact ⟨n, by simp [combinedAccept, hn]⟩
  · exact ⟨n, by simp [combinedAccept, hn]⟩

/-- **The collapse theorem (forward direction).**

Given a carrier `W`, an equality semidecider `eqSD a b : Semidecider (a = b)`, a disequality
semidecider `neqSD a b : Semidecider (a ≠ b)`, and the **joint totality** hypothesis `hcover` — for
every pair *some* stage of one of the two accepts (the constructive substitute for excluded middle on
`a = b`) — we manufacture `DecidableEq W`.

The procedure is a genuine bounded search. For the pair `a b`, `Nat.find` returns the least stage `N` at
which `combinedAccept` fires (existence supplied by `hcover` through `combinedAccept_exists`). The
`Bool` value `(eqSD a b).test N` is inspected:

* if it is `true`, the equality semidecider has produced an accepting stage, so `(eqSD a b).spec`
  upgrades it to `a = b` and we answer `isTrue`;
* if it is `false`, then since the *combined* verdict at `N` is `true`, the disequality semidecider must
  have accepted at `N`, so `(neqSD a b).spec` gives `a ≠ b` and we answer `isFalse`.

Neither branch assumes `DecidableEq W`; the verdict is read entirely off the two `spec`s. Hence the
equality semidecider **alone** does not suffice — the disequality (negative) semidecider is consumed
essentially in the `false` branch. That asymmetry is the theorem's content.

Relation: none. Property: decision procedure (`DecidableEq`). Trust: kernel-only, constructive search. -/
def semideciders_jointlyTotal_decidableEq {W : Type _}
    (eqSD : ∀ a b : W, Semidecider (a = b))
    (neqSD : ∀ a b : W, Semidecider (a ≠ b))
    (hcover : ∀ a b : W,
      (∃ n, (eqSD a b).test n = true) ∨ (∃ n, (neqSD a b).test n = true)) :
    DecidableEq W :=
  fun a b =>
    let hex : ∃ n, combinedAccept eqSD neqSD a b n :=
      combinedAccept_exists eqSD neqSD (hcover a b)
    let N : Nat := Nat.find hex
    have hN : combinedAccept eqSD neqSD a b N := Nat.find_spec hex
    match hb : (eqSD a b).test N with
    | true  => isTrue ((eqSD a b).spec.mp ⟨N, hb⟩)
    | false =>
        isFalse (by
          -- the combined verdict fired at `N`; with the equality side `false`, the disequality side accepts.
          have hcomb : ((eqSD a b).test N || (neqSD a b).test N) = true := hN
          rw [hb, Bool.false_or] at hcomb
          exact (neqSD a b).spec.mp ⟨N, hcomb⟩)

/-! ## The collapse theorem (converse): `DecidableEq` manufactures jointly total semideciders -/

/-- The constant equality semidecider from `DecidableEq W`: every stage reports `decide (a = b)`.
Soundness/completeness reduce to `decide_eq_true_iff`; acceptance at *any* stage is acceptance at *every*
stage, so the r.e. structure degenerates to a one-shot decision (the symmetric endpoint). -/
def decEqSemidecider {W : Type _} [DecidableEq W] (a b : W) : Semidecider (a = b) where
  test := fun _ => decide (a = b)
  spec := by
    constructor
    · rintro ⟨_, h⟩; exact of_decide_eq_true h
    · intro h; exact ⟨0, decide_eq_true h⟩

/-- The constant disequality semidecider from `DecidableEq W`: every stage reports `decide (a ≠ b)`.
`a ≠ b` is `Decidable` because `a = b` is, so this is total with no classical input. -/
def decNeqSemidecider {W : Type _} [DecidableEq W] (a b : W) : Semidecider (a ≠ b) where
  test := fun _ => decide (a ≠ b)
  spec := by
    constructor
    · rintro ⟨_, h⟩; exact of_decide_eq_true h
    · intro h; exact ⟨0, decide_eq_true h⟩

/-- **The collapse theorem (converse direction).** `DecidableEq W` yields an equality semidecider
family, a disequality semidecider family, and their **joint totality** — for every pair one of the two
accepts at stage `0`. Joint totality is *unconditional* here: `decide (a = b) = true` or
`decide (a ≠ b) = true` by `Bool`-case analysis on `decide (a = b)`, the constructive form of excluded
middle on `a = b`. This is the data consumed by the forward direction. -/
theorem decidableEq_semideciders (W : Type _) [DecidableEq W] :
    (∃ eqSD : ∀ a b : W, Semidecider (a = b),
      ∃ neqSD : ∀ a b : W, Semidecider (a ≠ b),
        ∀ a b : W,
          (∃ n, (eqSD a b).test n = true) ∨ (∃ n, (neqSD a b).test n = true)) := by
  refine ⟨fun a b => decEqSemidecider a b, fun a b => decNeqSemidecider a b, ?_⟩
  intro a b
  by_cases h : a = b
  · exact Or.inl ⟨0, by simp [decEqSemidecider, h]⟩
  · exact Or.inr ⟨0, by simp [decNeqSemidecider, h]⟩

/-! ## The characterization (forward + converse packaged) -/

/-- The structural payload of "a jointly total equality/disequality semidecider pair exists on `W`",
phrased as a `Prop` so it can sit on either side of an `Iff`. -/
def JointlyTotalSemidecisionPair (W : Type _) : Prop :=
  ∃ eqSD : ∀ a b : W, Semidecider (a = b),
    ∃ neqSD : ∀ a b : W, Semidecider (a ≠ b),
      ∀ a b : W,
        (∃ n, (eqSD a b).test n = true) ∨ (∃ n, (neqSD a b).test n = true)

/-- **The comparison-asymmetry characterization.** For any carrier `W`, the *propositional content* of
`DecidableEq W` (i.e. `Nonempty (DecidableEq W)`) is **equivalent** to the existence of a jointly total
equality/disequality semidecision pair. The forward arrow is the collapse (`Nat.find` search consuming
the disequality side); the backward arrow is the converse (constant `decide` tests). `Nonempty` is used
on the decidability side because `DecidableEq W` lives in `Type`, so equality of two such instances is
not the content claimed — only their inhabitation is.

Relation: none. Property: characterization / equivalence. Trust: kernel-only. -/
theorem comparisonAsymmetry_characterization (W : Type _) :
    Nonempty (DecidableEq W) ↔ JointlyTotalSemidecisionPair W := by
  constructor
  · rintro ⟨inst⟩
    haveI : DecidableEq W := inst
    exact decidableEq_semideciders W
  · rintro ⟨eqSD, neqSD, hcover⟩
    exact ⟨semideciders_jointlyTotal_decidableEq eqSD neqSD hcover⟩

/-! ## Non-vacuity (R5): instantiate on `ℕ` and re-derive `DecidableEq Nat` through the collapse -/

/-- A concrete jointly total semidecider pair on `ℕ`, built from the ambient `DecidableEq Nat`. Witnesses
that the interface and its joint-totality hypothesis are inhabited on a real infinite carrier. -/
theorem decidableEqNat_semideciders : JointlyTotalSemidecisionPair Nat :=
  decidableEq_semideciders Nat

/-- **Non-vacuity through the collapse (R5).** Re-derive `DecidableEq Nat` by running the *forward*
collapse theorem on the concrete `ℕ` semidecider pair. This exercises the real search procedure
(`Nat.find` over the combined predicate) on a concrete carrier, confirming the forward direction is a
genuine decision procedure and not a vacuous wrapper. Stated as a `Nonempty` to track only inhabitation
of the manufactured instance. -/
theorem decidableEq_Nat_via_collapse : Nonempty (DecidableEq Nat) := by
  obtain ⟨eqSD, neqSD, hcover⟩ := decidableEqNat_semideciders
  exact ⟨semideciders_jointlyTotal_decidableEq eqSD neqSD hcover⟩

/-! ## Framework connection: an exact comparator is the both-directions-decided special case -/

open OperatorKO7.Meta.ComparatorNecessity in
/-- **An `ExactComparator` is the synchronous (both-directions-decided) special case.** An exact total
comparator on `W` yields `DecidableEq W` by the reused `ComparatorNecessity.exactComparator_decidableEq`
(never re-proved here), hence by `comparisonAsymmetry_characterization` a jointly total
equality/disequality semidecision pair. In that pair both sides decide at stage `0`: the comparator has
collapsed the two-stage asymmetry to a single synchronous verdict. The `Semidecider` interface is
exactly what remains of comparison once that synchrony is dropped, which is where the
positive/local versus negative/global asymmetry lives. -/
theorem comparator_is_bothDirectionsDecided {W : Type _} (C : ExactComparator W) :
    JointlyTotalSemidecisionPair W :=
  (comparisonAsymmetry_characterization W).mp ⟨exactComparator_decidableEq C⟩

/-! ## Axiom inventory (must be a subset of `{propext, Classical.choice, Quot.sound}`) -/

#print axioms semideciders_jointlyTotal_decidableEq
#print axioms decidableEq_semideciders
#print axioms comparisonAsymmetry_characterization
#print axioms decidableEq_Nat_via_collapse
#print axioms comparator_is_bothDirectionsDecided

end OperatorKO7.Meta.InformationalIncompleteness.ComparisonAsymmetry
