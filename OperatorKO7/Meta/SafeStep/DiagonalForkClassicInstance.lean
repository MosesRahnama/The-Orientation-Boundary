import OperatorKO7.Meta.SafeStep.GenericDiagonalFork

/-!
# Second diagonal-fork instance: a varying comparator with a TOTALIZED difference rule

This file instantiates `DiagonalForkSchema` (from
`OperatorKO7/Meta/SafeStep/GenericDiagonalFork.lean`) at a **second, non-`eqW`
carrier** that is the true non-`eqW` analogue of KO7's `eqW`: a small standalone
first-order system whose verdict constructor `cmp` genuinely depends on *both*
arguments, with a reflexive rule overlapping a **totalized** difference rule that
fires on every pair, exactly mirroring the kernel's overlapping `Step.R_eq_refl`
(`eqW a a -> void`) and `Step.R_eq_diff` (`eqW a b -> integrate (merge a b)`,
which fires on every pair).

```
cmp(x, x) -> eq            -- reflexive rule  (reflexive verdict),  KO7: R_eq_refl
cmp(x, y) -> diff          -- difference rule (difference verdict), KO7: R_eq_diff
                              TOTALIZED: fires on EVERY pair (x, y)
```

with `eq` and `diff` distinct normal forms. Both rules fire at every diagonal
source `cmp(t, t)`: from such a source one step yields `eq` (reflexive rule) and
another yields `diff` (difference rule at `y := t`). `eq` and `diff` are
non-joinable because each is a distinct normal form. Hence local confluence of
this system fails at every diagonal source `cmp(t, t)`.

## Why this is the faithful (varying-`E`, totalized-difference) instance

The schema's force comes from a binary verdict constructor `E` whose diagonal
`E a a` is hit by *two* overlapping rules: a reflexive `E a a -> Z` and a
difference `E a b -> D a b` that itself fires on the diagonal. KO7 realizes this
with `E := eqW` (which depends on both arguments) and a difference rule
`R_eq_diff` that is totalized over all pairs. The faithful analogue here uses

* `E := cmp`, a genuine binary constructor: `cmp a b` depends on *both* `a` and
  `b` (it is NOT a constant function), so `E a a` for distinct `a` are distinct
  diagonal sources, just as `eqW a a` are;
* a difference rule `cmpDiff x y : Rel (cmp x y) diff` that is **totalized** — it
  fires on EVERY pair `(x, y)`, exactly like `R_eq_diff`, so in particular it
  overlaps the reflexive rule on the entire diagonal.

The schema fields are then discharged from the two *real, totalized* rules at the
diagonal, with `E` substituted at the diagonal `cmp a a`:

* `refl_rule a : Rel (cmp a a) eq`  is `Rel.cmpRefl a` (`cmp(x,x)->eq` at `x := a`);
* `diff_rule a b : Rel (cmp a b) diff` is `Rel.cmpDiff a b` (`cmp(x,y)->diff`, all pairs).

The carrier `Tm`, the relation `Rel`, its closure `RelStar`, and the
unjoinability proof are built **from scratch** with no reference to the KO7
kernel. The same abstract breaker `localConfluence_fails_at_diagonal` consumes
both this instance and `ko7DiagonalFork`, showing the diagonal-fork failure is a
genus (overlapping reflexive/totalized-difference verdict rules with unjoinable
outputs), not a one-symbol property of `eqW`.

## Note on the classical Klop rule (why it does NOT fit this schema)

The textbook Klop/Terese non-left-linear example uses a difference rule
`f(x, b) -> c` whose second argument is pinned to the constant `b`. That rule is
**non-totalized**: it fires only on pairs whose second component is `b`, so it
does not match the schema's totalized `diff_rule : ∀ a b, R (E a b) (D a b)`
without artificially restricting the index. The faithful instance therefore uses
the **totalized comparator** `cmp(x, y) -> diff` (the genuine non-`eqW` analogue
of the totalized `R_eq_diff`), not the pinned Klop rule.

## Audit notes (LASOT)

* Relation: a fresh standalone one-step system `Rel` on carrier `Tm` (instance) /
  abstract `R` (schema). Closure `RelStar` (instance), reflexive-transitive,
  mirroring the kernel's `StepStar` shape. NOT `Step`, NOT `SafeStep`,
  NOT the KO7 kernel at all.
* Property: `local_confluence` (its negation at a diagonal source `cmp t t`).
* Non-triviality (the entire point of this rework):
  - `E := cmp` genuinely VARIES — it is a binary constructor, not a constant
    function (see `cmp_varies`, a proof that `cmp a a ≠ cmp b b` for `a ≠ b`);
  - the difference rule `cmpDiff` is TOTALIZED — it fires on every pair, witnessed
    by `diff_rule_total`;
  - the unjoinability of `eq` and `diff` is a *genuine* proof by constructor
    analysis (each is a normal form, by `cases` on the impossible step; `eq ≠ diff`
    by constructor injectivity), not a tautology or assumed obligation.
* The fork theorem is *derived* by applying the abstract
  `GenericDiagonalFork.localConfluence_fails_at_diagonal`; the abstract schema
  theorem is NOT re-proved here.
* `set_option autoImplicit false`. No `sorry`, `admit`, added `axiom`,
  `constant`, `native_decide`, `bv_decide`, `@[csimp]`, `extern`,
  `implemented_by`, `unsafe`, `partial`, or `opaque`.
* `#print axioms` on every headline declaration is a subset of
  `{propext, Classical.choice, Quot.sound}`.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.SafeStep.DiagonalForkClassicInstance

open OperatorKO7.Meta.SafeStep.GenericDiagonalFork

/-- Standalone first-order term carrier for the comparator counterexample.

`eq` and `diff` are the two verdict constants; `base0`, `base1` are two distinct
base elements (so the diagonal `cmp · ·` is genuinely indexed by more than one
source); `cmp` is the binary verdict constructor. This is a deliberately minimal
signature — exactly the symbols needed for the totalized comparator rules
`cmp(x,x) -> eq` and `cmp(x,y) -> diff`. It is unrelated to the KO7 `Trace`
kernel. -/
inductive Tm : Type
  /-- The reflexive verdict constant `eq` (output of `cmp(x,x)->eq`; a normal form). -/
  | eq : Tm
  /-- The difference verdict constant `diff` (output of `cmp(x,y)->diff`; a normal form). -/
  | diff : Tm
  /-- First base element. -/
  | base0 : Tm
  /-- Second base element (distinct from `base0`). -/
  | base1 : Tm
  /-- The binary comparator (verdict) constructor; the schema's `E`. Depends on both arguments. -/
  | cmp : Tm → Tm → Tm
  deriving DecidableEq

/-- One-step rewrite relation of the standalone system: *exactly* the two
comparator rules, with no extra rules.

* `cmpRefl x  : Rel (cmp x x) eq`    encodes the reflexive rule `cmp(x, x) -> eq`;
* `cmpDiff x y : Rel (cmp x y) diff` encodes the **totalized** difference rule
  `cmp(x, y) -> diff`, which fires on EVERY pair `(x, y)`.

These are the only constructors, so a term has an outgoing step only if it is a
`cmp _ _` redex. In particular the verdict constants `eq` and `diff` are normal
forms. The two rules overlap on the entire diagonal: at any `cmp t t`, the
reflexive rule gives `eq` and the difference rule (at `y := t`) gives `diff`. -/
inductive Rel : Tm → Tm → Prop
  /-- Reflexive rule `cmp(x, x) -> eq` (the reflexive verdict). -/
  | cmpRefl : ∀ x, Rel (Tm.cmp x x) Tm.eq
  /-- Difference rule `cmp(x, y) -> diff`, totalized over all pairs (the difference verdict). -/
  | cmpDiff : ∀ x y, Rel (Tm.cmp x y) Tm.diff

/-- Reflexive-transitive closure of `Rel`, mirroring the kernel's `StepStar`
shape (`refl` + left-extension `tail`). -/
inductive RelStar : Tm → Tm → Prop
  /-- Reflexivity. -/
  | refl : ∀ t, RelStar t t
  /-- Prepend one `Rel` step to a closure derivation. -/
  | tail : ∀ {x y z}, Rel x y → RelStar y z → RelStar x z

/-- Any single `Rel` step embeds into the closure. -/
theorem relstar_of_rel {x y : Tm} (h : Rel x y) : RelStar x y :=
  RelStar.tail h (RelStar.refl y)

/-- Normal-form predicate for the standalone relation: no outgoing `Rel` step. -/
def NF (t : Tm) : Prop := ¬ ∃ u, Rel t u

/-- A reduction out of a normal form is trivial: `NF x → RelStar x y → x = y`.
Mirrors the kernel's `nf_no_stepstar_forward`. -/
theorem nf_no_relstar_forward {x y : Tm} (hnf : NF x) (h : RelStar x y) : x = y := by
  cases h with
  | refl _ => rfl
  | tail hs _ => exact False.elim (hnf ⟨_, hs⟩)

/-- `eq` is a normal form: no `Rel` constructor has source `eq`
(both constructors have a `cmp _ _` source). -/
theorem nf_eq : NF Tm.eq := by
  rintro ⟨u, hu⟩; cases hu

/-- `diff` is a normal form: no `Rel` constructor has source `diff`. -/
theorem nf_diff : NF Tm.diff := by
  rintro ⟨u, hu⟩; cases hu

/-- The two diagonal outputs `eq` and `diff` are non-joinable: no common reduct
exists in the closure. Genuine proof — each output is a distinct normal form, so
any common reduct would have to equal both `eq` and `diff`, contradicting
`eq ≠ diff` (constructor injectivity). -/
theorem eq_diff_unjoinable : ¬ ∃ d, RelStar Tm.eq d ∧ RelStar Tm.diff d := by
  rintro ⟨d, hEd, hDd⟩
  have hde : d = Tm.eq := (nf_no_relstar_forward nf_eq hEd).symm
  have hdd : d = Tm.diff := (nf_no_relstar_forward nf_diff hDd).symm
  have : (Tm.eq : Tm) = Tm.diff := hde.symm.trans hdd
  exact Tm.noConfusion this

/-- **Non-triviality of `E`: the comparator genuinely VARIES.**

`cmp` is not a constant function: distinct base elements give distinct diagonal
sources. Concretely `cmp base0 base0 ≠ cmp base1 base1`, so the family of
diagonal sources `E a a` is genuinely indexed (this is the analogue of `eqW a a`
ranging over distinct `a`, and is exactly what a constant `E` would destroy). -/
theorem cmp_varies : Tm.cmp Tm.base0 Tm.base0 ≠ Tm.cmp Tm.base1 Tm.base1 := by
  intro h
  -- `cmp` injective in its first argument; `base0 ≠ base1` by constructor injectivity.
  exact Tm.noConfusion (Tm.cmp.injEq _ _ _ _ ▸ h).1

/-- **The comparator diagonal-fork schema instance.**

`E := cmp` (the genuine binary verdict constructor; it VARIES in both arguments),
`Z := eq`, `D _ _ := diff`. The two schema rules are discharged by the two real
*totalized* comparator rules, with `E` taken at the diagonal:

* `refl_rule a`   := `Rel.cmpRefl a  : Rel (cmp a a) eq`;
* `diff_rule a b` := `Rel.cmpDiff a b : Rel (cmp a b) diff`  (fires on every pair). -/
def comparatorDiagonalFork : DiagonalForkSchema Tm where
  R := Rel
  RStar := RelStar
  E := Tm.cmp
  Z := Tm.eq
  D := fun _ _ => Tm.diff
  refl_rule := fun a => Rel.cmpRefl a
  diff_rule := fun a b => Rel.cmpDiff a b
  rstar_refl := RelStar.refl
  rstar_single := relstar_of_rel

/-- The difference field of the instance is the TOTALIZED difference rule: it
fires on every pair `(a, b)`, not just on a pinned diagonal or a constant
source. This is the explicit witness that the rework totalizes the difference
rule (the analogue of `R_eq_diff` firing on all pairs). -/
theorem diff_rule_total :
    ∀ a b, comparatorDiagonalFork.R (comparatorDiagonalFork.E a b) Tm.diff :=
  fun a b => Rel.cmpDiff a b

/-- The instance's diagonal verdicts at `base0` are `eq` (`= Z`) and `diff`
(`= D _ _`); their non-joinability is `eq_diff_unjoinable`, restated in the
schema's `DiagonalVerdictsJoin` shape so the generic theorem can consume it. -/
theorem comparator_diagonalVerdicts_not_join :
    ¬ DiagonalVerdictsJoin comparatorDiagonalFork Tm.base0 :=
  eq_diff_unjoinable

/-- **Second instance, derived from the generic theorem.**

Local confluence of the standalone comparator system `Rel` fails at the diagonal
source `cmp base0 base0` (`= comparatorDiagonalFork.E base0 base0`). Obtained by
applying the abstract breaker `localConfluence_fails_at_diagonal` to this
instance and the reused non-joinability witness — NOT an independent re-proof of
the breaker.

Relation: standalone `Rel` (closure `RelStar`). Not `Step`, not `SafeStep`.
Property: negation of `local_confluence` at `cmp base0 base0`. -/
theorem localConfluence_fails_comparator :
    ¬ LocalJoinAt comparatorDiagonalFork
        (comparatorDiagonalFork.E Tm.base0 Tm.base0) :=
  localConfluence_fails_at_diagonal comparatorDiagonalFork Tm.base0
    comparator_diagonalVerdicts_not_join

/-- **Concrete non-vacuity / diverging-peak witness.**

The diagonal source `cmp base0 base0` genuinely has the two distinct one-step
successors `eq` (reflexive rule) and `diff` (totalized difference rule at
`y := base0`), and local confluence fails there. This exhibits a real, populated
peak (Gate R5), not a vacuous claim: the existential content is two concrete
constructor applications plus the failure of joinability. -/
theorem comparator_divergence_witness :
    Rel (Tm.cmp Tm.base0 Tm.base0) Tm.eq
      ∧ Rel (Tm.cmp Tm.base0 Tm.base0) Tm.diff
      ∧ ¬ LocalJoinAt comparatorDiagonalFork (Tm.cmp Tm.base0 Tm.base0) :=
  ⟨Rel.cmpRefl Tm.base0, Rel.cmpDiff Tm.base0 Tm.base0, localConfluence_fails_comparator⟩

-- Statement-adequacy (Gate R2) and non-vacuity (Gate R5): exact types.
#check @comparatorDiagonalFork
#check @localConfluence_fails_comparator
#check @comparator_divergence_witness
#check @eq_diff_unjoinable
#check @cmp_varies
#check @diff_rule_total

-- The instance carrier is genuinely distinct from the kernel: `Tm`, not `Trace`.
example : DiagonalForkSchema Tm := comparatorDiagonalFork

-- `E` is the varying binary constructor `cmp`, not a constant function.
example : comparatorDiagonalFork.E = Tm.cmp := rfl

#print axioms eq_diff_unjoinable
#print axioms cmp_varies
#print axioms diff_rule_total
#print axioms localConfluence_fails_comparator
#print axioms comparator_divergence_witness

end OperatorKO7.Meta.SafeStep.DiagonalForkClassicInstance
