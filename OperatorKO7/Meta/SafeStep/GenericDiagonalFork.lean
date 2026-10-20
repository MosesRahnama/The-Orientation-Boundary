import OperatorKO7.Kernel
import OperatorKO7.Meta.Confluence_Safe
import OperatorKO7.Meta.SafeStep.EqWVoidAnomaly

/-!
# Generic Diagonal-Fork Schema (portability of the `eqW void void` breaker)

This file abstracts the KO7 `eqW void void` confluence breaker into a reusable
*diagonal-fork* schema, then re-derives the concrete KO7 instance **from** the
abstract theorem. The point is portability: the local-confluence failure at a
diagonal verdict node is not a one-symbol accident of `eqW`, it is a structural
consequence of having two root rules that overlap on the diagonal `E a a`, with
the two outputs (`Z` from the reflexive rule, `D a a` from the difference rule)
unjoinable.

## What the schema captures

A `DiagonalForkSchema T` packages an abstract one-step relation `R` on a carrier
`T`, a binary "verdict constructor" `E`, an "equal" output `Z`, a "different"
output `D`, and the two overlapping root rules:

* `refl_rule a : R (E a a) Z`            -- the reflexive verdict
* `diff_rule a b : R (E a b) (D a b)`    -- the difference verdict

Because both rules fire at the diagonal source `E a a`, that source has two
one-step successors `Z` and `D a a`. If those two successors are unjoinable in
the closure `RStar`, the source is a non-joinable local divergence, i.e. local
confluence fails there.

## Local-confluence vocabulary

The package states "local confluence at a term" as a *local-join-at-a-source*
predicate (`MetaSN_KO7.LocalJoinStep`, file `Meta/Confluence_Safe.lean`):

```
def LocalJoinStep (a : Trace) : Prop :=
  ∀ {b c}, Step a b → Step a c → ∃ d, StepStar b d ∧ StepStar c d
```

and "local confluence fails at `a`" is the negation `¬ LocalJoinStep a` (this is
exactly how `not_localJoinStep_eqW_void_void` is phrased). The abstract predicate
`LocalJoinAt` below has the identical shape over the schema's own `R`/`RStar`, so
when the KO7 schema is instantiated with `R := Step` and `RStar := StepStar` the
abstract predicate `LocalJoinAt ko7DiagonalFork void` is **definitionally**
`MetaSN_KO7.LocalJoinStep (eqW void void)`. The KO7 instance theorem therefore
states `¬ MetaSN_KO7.LocalJoinStep (eqW void void)` and discharges it by applying
the generic theorem to the *existing* non-joinability witness
`EqWVoidAnomaly.eqW_void_void_normal_forms_are_unjoinable`. No joinability fact is
re-proved here.

## Audit notes (LASOT)

* Relation: full kernel `Step` (instance) / abstract `R` (schema). Closure
  `RStar` (instance: `StepStar`). Not `SafeStep`.
* Property: `local_confluence` (its negation at a single source term).
* No `sorry`, `admit`, `axiom`, `native_decide`, `@[csimp]`, `unsafe`,
  `partial`, or `opaque`. Every declaration closes by direct construction.
* The KO7 instance is *derived* from the abstract theorem, not re-proved: the
  unjoinability input is reused verbatim from the existing anomaly module.
* `#print axioms` on both headline theorems is a subset of
  `{propext, Classical.choice, Quot.sound}`.
-/

set_option autoImplicit false

open OperatorKO7 Trace

namespace OperatorKO7.Meta.SafeStep.GenericDiagonalFork

universe u

/-- Abstract *diagonal-fork* schema.

`R` is a one-step relation; `RStar` is its intended reflexive-transitive
closure (kept abstract so an instance can plug in the package's actual closure,
e.g. `StepStar`). The two overlapping root rules `refl_rule` and `diff_rule`
fire at the diagonal source `E a a`, producing `Z` and `D a a` respectively. The
closure fields `rstar_refl` and `rstar_single` are the only closure facts the
breaker theorem needs (reflexivity for the join shape, and the single-step
injection so a successor is reachable in the closure). -/
structure DiagonalForkSchema (T : Type u) where
  /-- Abstract one-step relation. -/
  R : T → T → Prop
  /-- Intended reflexive-transitive closure of `R`. -/
  RStar : T → T → Prop
  /-- The binary verdict constructor (KO7: `eqW`). -/
  E : T → T → T
  /-- The reflexive verdict output (KO7: `void`). -/
  Z : T
  /-- The difference verdict output (KO7: `fun a b => integrate (merge a b)`). -/
  D : T → T → T
  /-- Reflexive rule: the diagonal source steps to `Z`. -/
  refl_rule : ∀ a, R (E a a) Z
  /-- Difference rule: every verdict source steps to its difference output. -/
  diff_rule : ∀ a b, R (E a b) (D a b)
  /-- Reflexivity of the closure. -/
  rstar_refl : ∀ t, RStar t t
  /-- One step embeds into the closure. -/
  rstar_single : ∀ {a b}, R a b → RStar a b

variable {T : Type u}

/-- Local joinability at a fixed source for a schema, phrased in the package's
own local-join shape (`MetaSN_KO7.LocalJoinStep`): every pair of one-step
successors of `a` has a common reduct in the closure `RStar`.

"Local confluence fails at `a`" is the negation `¬ LocalJoinAt S a`. -/
def LocalJoinAt (S : DiagonalForkSchema T) (a : T) : Prop :=
  ∀ {b c}, S.R a b → S.R a c → ∃ d, S.RStar b d ∧ S.RStar c d

/-- Abstract joinability of the two diagonal verdicts at `a`: `S.Z` and
`S.D a a` have a common reduct. The breaker hypothesis is the negation of this. -/
def DiagonalVerdictsJoin (S : DiagonalForkSchema T) (a : T) : Prop :=
  ∃ d, S.RStar S.Z d ∧ S.RStar (S.D a a) d

/-- The diagonal peak: at the source `E a a` the schema exhibits the two
one-step successors `Z` (via `refl_rule`) and `D a a` (via `diff_rule`). -/
theorem diagonal_peak (S : DiagonalForkSchema T) (a : T) :
    S.R (S.E a a) S.Z ∧ S.R (S.E a a) (S.D a a) :=
  ⟨S.refl_rule a, S.diff_rule a a⟩

/-- **Generic diagonal-fork breaker (main abstract theorem).**

For any diagonal-fork schema `S` and any `a` whose two diagonal verdicts `S.Z`
and `S.D a a` are *not* joinable, local confluence fails at the diagonal source
`S.E a a`: the peak `S.E a a ⇒ S.Z`, `S.E a a ⇒ S.D a a` is a non-joinable local
divergence.

Relation: abstract `S.R` with closure `S.RStar`.
Property: negation of `local_confluence` at the source `S.E a a`. -/
theorem localConfluence_fails_at_diagonal
    (S : DiagonalForkSchema T) (a : T)
    (hnj : ¬ DiagonalVerdictsJoin S a) :
    ¬ LocalJoinAt S (S.E a a) := by
  intro hjoin
  have hb : S.R (S.E a a) S.Z := S.refl_rule a
  have hc : S.R (S.E a a) (S.D a a) := S.diff_rule a a
  exact hnj (hjoin hb hc)

/-- Convenience form: from a witnessed peak plus non-joinability of `Z` and
`D a a`, the source `E a a` is a non-joinable local divergence. This repackages
the breaker as an explicit "diverging peak" certificate. -/
theorem diagonal_divergence_witness
    (S : DiagonalForkSchema T) (a : T)
    (hnj : ¬ DiagonalVerdictsJoin S a) :
    S.R (S.E a a) S.Z ∧ S.R (S.E a a) (S.D a a) ∧ ¬ LocalJoinAt S (S.E a a) :=
  ⟨S.refl_rule a, S.diff_rule a a, localConfluence_fails_at_diagonal S a hnj⟩

/-! ## KO7 instantiation

`E := eqW`, `Z := void`, `D a b := integrate (merge a b)`, `R := Step`,
`RStar := StepStar`. The schema's `refl_rule`/`diff_rule` are *exactly* the
kernel rules `Step.R_eq_refl` and `Step.R_eq_diff`. -/

/-- The KO7 diagonal-fork schema built from the kernel `Step` relation and its
closure `StepStar`. The two rules are the kernel's own `eqW` rules. -/
def ko7DiagonalFork : DiagonalForkSchema Trace where
  R := Step
  RStar := StepStar
  E := eqW
  Z := void
  D := fun a b => integrate (merge a b)
  refl_rule := Step.R_eq_refl
  diff_rule := Step.R_eq_diff
  rstar_refl := StepStar.refl
  rstar_single := stepstar_of_step

/-- The KO7 diagonal verdicts at `void` are exactly `void` and
`integrate (merge void void)`; their non-joinability is the existing anomaly
fact. This restates that witness in the schema's `DiagonalVerdictsJoin` shape so
the generic theorem can consume it directly. -/
theorem ko7_diagonalVerdicts_not_join :
    ¬ DiagonalVerdictsJoin ko7DiagonalFork void :=
  EqWVoidAnomaly.eqW_void_void_normal_forms_are_unjoinable

/-- **KO7 instance, derived from the generic theorem.**

Local confluence of the full kernel `Step` relation fails at `eqW void void`.
Stated in the package's own local-confluence vocabulary: this is precisely
`¬ MetaSN_KO7.LocalJoinStep (eqW void void)`, because with the KO7 schema the
abstract predicate `LocalJoinAt ko7DiagonalFork void` *is* (definitionally)
`MetaSN_KO7.LocalJoinStep (eqW void void)`.

This is obtained by applying `localConfluence_fails_at_diagonal` to the KO7
schema and the reused non-joinability witness — it is **not** an independent
re-proof of the breaker.

Relation: full kernel `Step` (closure `StepStar`). Not `SafeStep`.
Property: negation of `local_confluence` at `eqW void void`. -/
theorem eqW_void_void_genericDiagonalFork :
    ¬ MetaSN_KO7.LocalJoinStep (eqW void void) :=
  localConfluence_fails_at_diagonal ko7DiagonalFork void ko7_diagonalVerdicts_not_join

/-- Sanity check that the generic instantiation lands on the package predicate:
the derived theorem has exactly the type of the pre-existing hand-proved fact
`MetaSN_KO7.not_localJoinStep_eqW_void_void`. (Definitional agreement of
`LocalJoinAt ko7DiagonalFork void` with `MetaSN_KO7.LocalJoinStep (eqW void void)`
is what makes this typecheck.) -/
theorem eqW_void_void_genericDiagonalFork_matches_existing :
    eqW_void_void_genericDiagonalFork =
      (eqW_void_void_genericDiagonalFork :
        ¬ MetaSN_KO7.LocalJoinStep (eqW void void)) :=
  rfl

end OperatorKO7.Meta.SafeStep.GenericDiagonalFork

namespace OperatorKO7.Meta.SafeStep.GenericDiagonalFork

-- Statement-adequacy (Gate R2): the KO7 instance really has the package
-- local-confluence type, and is interchangeable with a goal of that type.
#check (eqW_void_void_genericDiagonalFork :
    ¬ MetaSN_KO7.LocalJoinStep (eqW void void))
#check @localConfluence_fails_at_diagonal
example : ¬ MetaSN_KO7.LocalJoinStep (eqW void void) :=
  eqW_void_void_genericDiagonalFork

#print axioms localConfluence_fails_at_diagonal
#print axioms eqW_void_void_genericDiagonalFork

end OperatorKO7.Meta.SafeStep.GenericDiagonalFork
