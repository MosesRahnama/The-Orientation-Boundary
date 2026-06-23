import OperatorKO7.Meta.SafeStep.GenericDiagonalFork

/-!
# The Distinction-Witness Boundary Theorem (schema-level, KO7-stripped)

This file sharpens the one-directional diagonal-fork breaker of
`OperatorKO7.Meta.SafeStep.GenericDiagonalFork` into a *boundary characterization*
plus its *recovery routes*, then ties both ends back to the concrete KO7 kernel.

The slogan: a system that internalizes distinction through a **reflexive equality
rule** (`E a a ⇒ Z`) together with a **totalized difference rule**
(`E a b ⇒ D a b` for *all* `a, b`, in particular at the diagonal `a = b`) must
either accept non-confluence at the diagonal source `E a a`, or license an
external guard that suppresses one of the two overlapping diagonal reducts.

## What is new here over `GenericDiagonalFork`

`GenericDiagonalFork.localConfluence_fails_at_diagonal` proves only the forward
obstruction: *non-joinable verdicts ⇒ local confluence fails*. This file adds:

* **Part 1 — characterization.** Under the (mild, always-true-for-the-fork)
  determinacy hypothesis that the diagonal source has *only* the two verdict
  reducts, local confluence at the diagonal holds **iff** the two verdicts join
  (`diagonal_localConfluence_iff_verdictsJoin`). This is a genuine biconditional:
  it upgrades the breaker from a sufficient condition to an exact boundary.

* **Part 2 — recovery routes.** A *guarded* schema
  (`GuardedDiagonalForkSchema`) restricts the difference rule to the off-diagonal
  (`a ≠ b`) and records, as a structural field, that the only diagonal reduct of
  `E a a` is `Z`. Then local confluence at the diagonal is **recovered**
  (`guarded_diagonal_localJoin`): the guard collapses the peak. Two further short
  corollaries cover the *delete* route (`D a a = Z`) and the *quotient* route
  (`Z = D a a`).

* **Part 3 — non-vacuity + KO7 tie.** One concrete guarded instance over the real
  KO7 carrier `Trace`, with `E := eqW`, `Z := void`,
  `D a b := integrate (merge a b)`, and a hand-rolled guarded one-step relation
  `GuardedStep` whose diagonal reduct is provably unique. The existing *unguarded*
  obstruction is re-exported (not re-proved) so obstruction and recovery sit in
  one file.

* **Part 4 — bundled headline.** `distinction_witness_boundary` packages
  obstruction (unguarded: non-join ⇒ failure) and recovery (guarded: join holds)
  as a single named anchor.

## Audit notes (LASOT)

* Relation: abstract `S.R` (Part 1, schema) / abstract guarded `Sg.R` (Part 2,
  guarded schema) / concrete `GuardedStep` over the kernel carrier `Trace`
  (Part 3). Closure: abstract `RStar` / concrete `StepStar`. **Not** `SafeStep`;
  the re-exported obstruction is about the full kernel `Step`.
* Property: `local_confluence` at the single diagonal source `E a a` — its
  characterization (Part 1), its recovery under the guard (Part 2/4), and its
  documented failure for the unguarded kernel (re-export, Part 3/4).
* No `sorry`, `admit`, `axiom`, `native_decide`, `bv_decide`, `@[csimp]`,
  `unsafe`, `partial`, or `opaque`. Every declaration closes by direct
  construction / inversion. `GuardedStep` is a plain `inductive Prop`.
* `#print axioms` on every headline is a subset of
  `{propext, Classical.choice, Quot.sound}`.
-/

set_option autoImplicit false
set_option linter.dupNamespace false

open OperatorKO7 Trace
open OperatorKO7.Meta.SafeStep.GenericDiagonalFork

namespace OperatorKO7.Meta.SafeStep.DistinctionWitnessBoundary

universe u

variable {T : Type u}

/-! ## Part 1 — the boundary characterization

We sharpen the one-directional breaker into a biconditional. The forward
direction (1a) holds unconditionally for any `DiagonalForkSchema`. The converse
needs only the determinacy hypothesis (1b) that the diagonal source reduces in
one step to *nothing but* the two verdicts. -/

/-- **(1a) Forward direction.** Local joinability at the diagonal source `E a a`
forces the two diagonal verdicts `Z` and `D a a` to join: feed `LocalJoinAt` the
two overlapping peak steps `refl_rule a` and `diff_rule a a`.

This is the easy half of the boundary and holds for *every* diagonal-fork schema,
with no side hypothesis. -/
theorem localJoinAt_diagonal_imp_verdictsJoin
    (S : DiagonalForkSchema T) (a : T)
    (h : LocalJoinAt S (S.E a a)) :
    DiagonalVerdictsJoin S a :=
  h (S.refl_rule a) (S.diff_rule a a)

/-- **(1b) Diagonal determinacy.** The only one-step reducts of the diagonal
source `E a a` are the two verdicts `Z` and `D a a`. This is the structural fact
that turns the forward implication into a biconditional: it says the diagonal
peak has no *third* escape route to confuse the join analysis. -/
def DiagonalDetermined (S : DiagonalForkSchema T) (a : T) : Prop :=
  ∀ b, S.R (S.E a a) b → b = S.Z ∨ b = S.D a a

/-- **(1c) Boundary characterization (headline).**

For a diagonal-fork schema whose diagonal source is *determined* (its only
one-step reducts are the two verdicts), local confluence at the diagonal source
`E a a` holds **exactly when** the two diagonal verdicts join:

```
LocalJoinAt S (E a a)  ↔  DiagonalVerdictsJoin S a
```

Forward is (1a). Converse: given the join witness `d` (with `Z ⇒* d` and
`D a a ⇒* d`) and determinacy, an arbitrary pair of reducts `b, c` of `E a a` is
each either `Z` or `D a a`; the four cases all join — at `d` when the side is a
verdict (rewriting the join witness), or reflexively when both sides coincide.
This biconditional is the sharp boundary: confluence at the diagonal is *equivalent*
to verdict joinability, not merely implied by it. -/
theorem diagonal_localConfluence_iff_verdictsJoin
    (S : DiagonalForkSchema T) (a : T)
    (hdet : DiagonalDetermined S a) :
    LocalJoinAt S (S.E a a) ↔ DiagonalVerdictsJoin S a := by
  constructor
  · intro h
    exact localJoinAt_diagonal_imp_verdictsJoin S a h
  · intro hVJ
    rcases hVJ with ⟨d, hZd, hDd⟩
    intro b c hb hc
    -- Each of `b`, `c` is one of the two verdicts, by determinacy.
    rcases hdet b hb with hbZ | hbD <;> rcases hdet c hc with hcZ | hcD
    · -- b = Z, c = Z : join reflexively at Z.
      subst hbZ; subst hcZ
      exact ⟨S.Z, S.rstar_refl S.Z, S.rstar_refl S.Z⟩
    · -- b = Z, c = D a a : join at the witness d.
      subst hbZ; subst hcD
      exact ⟨d, hZd, hDd⟩
    · -- b = D a a, c = Z : join at the witness d (swapped).
      subst hbD; subst hcZ
      exact ⟨d, hDd, hZd⟩
    · -- b = D a a, c = D a a : join reflexively at D a a.
      subst hbD; subst hcD
      exact ⟨S.D a a, S.rstar_refl (S.D a a), S.rstar_refl (S.D a a)⟩

/-! ## Part 2 — the recovery routes (generalization of SafeStep, KO7-free)

### Route (i): the guard.

A `GuardedDiagonalForkSchema` keeps the reflexive rule but fires the difference
rule **only off the diagonal** (`a ≠ b`), and records as a structural field that
this guard leaves `Z` as the *unique* one-step reduct of the diagonal source.
That single field is what lets the diagonal peak collapse. -/

/-- A diagonal-fork schema with the difference rule **guarded** to the
off-diagonal. The field `diag_determined_guarded` is the structural promise that
the guard works: at the diagonal source `E a a`, the only one-step reduct is `Z`.

Compare `DiagonalForkSchema`: there the difference rule `diff_rule a b` is total,
so the diagonal source `E a a` carries the extra reduct `D a a`; here
`diff_rule a b` requires `a ≠ b`, so the diagonal is left with `Z` alone. -/
structure GuardedDiagonalForkSchema (T : Type u) where
  /-- Abstract one-step relation. -/
  R : T → T → Prop
  /-- Intended reflexive-transitive closure of `R`. -/
  RStar : T → T → Prop
  /-- The binary verdict constructor. -/
  E : T → T → T
  /-- The reflexive verdict output. -/
  Z : T
  /-- The difference verdict output. -/
  D : T → T → T
  /-- Reflexive rule: the diagonal source steps to `Z` (unguarded). -/
  refl_rule : ∀ a, R (E a a) Z
  /-- **Guarded** difference rule: only *distinct* arguments produce a difference
  verdict. This is the recovery move — the diagonal `a = b` is excluded. -/
  diff_rule : ∀ a b, a ≠ b → R (E a b) (D a b)
  /-- Reflexivity of the closure. -/
  rstar_refl : ∀ t, RStar t t
  /-- One step embeds into the closure. -/
  rstar_single : ∀ {a b}, R a b → RStar a b
  /-- **The guard certificate.** With the difference rule guarded, the diagonal
  source `E a a` has `Z` as its *only* one-step reduct. -/
  diag_determined_guarded : ∀ a b, R (E a a) b → b = Z

/-- Local joinability at a fixed source for a *guarded* schema (same shape as
`GenericDiagonalFork.LocalJoinAt`, over the guarded schema's own `R`/`RStar`). -/
def LocalJoinAtG (Sg : GuardedDiagonalForkSchema T) (a : T) : Prop :=
  ∀ {b c}, Sg.R a b → Sg.R a c → ∃ d, Sg.RStar b d ∧ Sg.RStar c d

/-- **(2b) Guard recovery (headline, route i).**

For a *guarded* diagonal-fork schema, local confluence is **recovered** at the
diagonal source `E a a`: local join holds there. The proof genuinely uses the
guard. By the guard certificate `diag_determined_guarded`, *both* reducts `b` and
`c` of `E a a` are forced to equal `Z`, so the peak is not a real divergence and
the two sides join reflexively at `Z`.

Contrast with the unguarded schema, where `E a a ⇒ Z` and `E a a ⇒ D a a` is a
genuine two-target peak that breaks local confluence whenever the verdicts do not
join (`GenericDiagonalFork.localConfluence_fails_at_diagonal`). The guard removes
the second target, and confluence returns.

Relation: guarded `Sg.R` with closure `Sg.RStar`.
Property: `local_confluence` at the source `Sg.E a a` (recovered). -/
theorem guarded_diagonal_localJoin
    (Sg : GuardedDiagonalForkSchema T) (a : T) :
    LocalJoinAtG Sg (Sg.E a a) := by
  intro b c hb hc
  -- The guard forces both reducts to be `Z`.
  have hbZ : b = Sg.Z := Sg.diag_determined_guarded a b hb
  have hcZ : c = Sg.Z := Sg.diag_determined_guarded a c hc
  subst hbZ; subst hcZ
  exact ⟨Sg.Z, Sg.rstar_refl Sg.Z, Sg.rstar_refl Sg.Z⟩

/-- **(2c, route iii — delete).** If the difference output *collapses onto* the
reflexive output on the diagonal (`D a a = Z`), the two diagonal verdicts join
trivially (reflexively at `Z`), so the schema is **not** broken at the diagonal.
This is the "delete the offending difference verdict" recovery, stated as
joinability rather than as a guard on the rule. -/
theorem delete_recovers
    (S : DiagonalForkSchema T) (a : T)
    (hdel : S.D a a = S.Z) :
    DiagonalVerdictsJoin S a := by
  refine ⟨S.Z, S.rstar_refl S.Z, ?_⟩
  rw [hdel]
  exact S.rstar_refl S.Z

/-- **(2c, route ii — quotient).** If the reflexive and difference outputs are
*identified* on the diagonal (`Z = D a a`, e.g. after passing to a quotient that
equates the two verdicts), the two diagonal verdicts join trivially. This is the
"quotient the verdicts together" recovery. -/
theorem quotient_recovers
    (S : DiagonalForkSchema T) (a : T)
    (hquot : S.Z = S.D a a) :
    DiagonalVerdictsJoin S a := by
  refine ⟨S.Z, S.rstar_refl S.Z, ?_⟩
  rw [← hquot]
  exact S.rstar_refl S.Z

/-! ## Part 3 — non-vacuity + the KO7 tie

A concrete *guarded* schema over the real kernel carrier `Trace`, witnessing that
the guard recovery (2b) is not vacuous. We use the actual KO7 constructors:
`E := eqW`, `Z := void`, `D a b := integrate (merge a b)`. The guarded one-step
relation `GuardedStep` is the kernel's `eqW` rules with the difference rule
*restricted to distinct arguments*, so the diagonal `eqW a a` reduces only to
`void`. -/

/-- The **guarded** one-step relation over `Trace`: the reflexive `eqW` rule, and
the difference `eqW` rule *guarded* to distinct arguments. This is the concrete
recovery relation: unlike the full kernel `Step` (whose `R_eq_diff` fires
unconditionally, even at `eqW a a`), `GuardedStep` only emits the difference
verdict `integrate (merge a b)` when `a ≠ b`. Hence the diagonal source
`eqW a a` has the single reduct `void`. -/
inductive GuardedStep : Trace → Trace → Prop
  /-- Reflexive verdict (unguarded): `eqW a a` reduces to `void`. -/
  | g_eq_refl : ∀ a, GuardedStep (eqW a a) void
  /-- Difference verdict, **guarded** by `a ≠ b`. -/
  | g_eq_diff : ∀ a b, a ≠ b → GuardedStep (eqW a b) (integrate (merge a b))

/-- The diagonal source `eqW a a` has `void` as its *only* `GuardedStep`-reduct.
Inversion: the reflexive rule gives `void`; the guarded difference rule cannot
fire because it would require `a ≠ a`. This is the concrete discharge of the
`diag_determined_guarded` field. -/
theorem guardedStep_diag_unique (a b : Trace) :
    GuardedStep (eqW a a) b → b = void := by
  intro h
  cases h with
  | g_eq_refl _ => rfl
  | g_eq_diff _ _ hne => exact absurd rfl hne

/-- **The concrete KO7-flavoured guarded schema.** Carrier `Trace`; verdict
constructor `eqW`; reflexive output `void`; difference output
`fun a b => integrate (merge a b)`; relation the guarded `GuardedStep` with the
kernel closure `StepStar`. The reflexive/guarded rules are `GuardedStep`'s own
constructors, and the guard certificate is `guardedStep_diag_unique`. -/
def ko7GuardedDiagonalFork : GuardedDiagonalForkSchema Trace where
  R := GuardedStep
  RStar := StepStar
  E := eqW
  Z := void
  D := fun a b => integrate (merge a b)
  refl_rule := GuardedStep.g_eq_refl
  diff_rule := GuardedStep.g_eq_diff
  rstar_refl := StepStar.refl
  rstar_single := by
    intro a b h
    cases h with
    | g_eq_refl a => exact stepstar_of_step (Step.R_eq_refl a)
    | g_eq_diff a b _ => exact stepstar_of_step (Step.R_eq_diff a b)
  diag_determined_guarded := guardedStep_diag_unique

/-- **(Part 3 headline) Concrete guard recovery over `Trace`.**

The KO7-flavoured guarded schema recovers local confluence at the genuine
diagonal source `eqW a a`: local join holds there. This is
`guarded_diagonal_localJoin` discharged on the real `eqW` / `void` /
`integrate (merge ..)` constructors, confirming the recovery is not an abstract
artifact. -/
theorem ko7_guarded_diagonal_localJoin (a : Trace) :
    LocalJoinAtG ko7GuardedDiagonalFork (eqW a a) :=
  guarded_diagonal_localJoin ko7GuardedDiagonalFork a

/-- **Re-export of the existing unguarded obstruction** (not re-proved). The full
kernel `Step` is *not* locally confluent at `eqW void void`: this is exactly
`GenericDiagonalFork.eqW_void_void_genericDiagonalFork`, surfaced here so the
obstruction (unguarded) and the recovery (guarded) live in one file. -/
theorem ko7_unguarded_obstruction :
    ¬ MetaSN_KO7.LocalJoinStep (eqW void void) :=
  GenericDiagonalFork.eqW_void_void_genericDiagonalFork

/-! ## Part 4 — the bundled headline

`distinction_witness_boundary` is the named anchor the manuscript cites. It packs
the two faces of the boundary into one structure: the *obstruction* (an unguarded
diagonal-fork schema with non-joining verdicts is not locally confluent at the
diagonal — reusing `localConfluence_fails_at_diagonal`), and the *recovery* (the
corresponding guarded schema is locally confluent at the diagonal — `2b`). -/

/-- The two-sided Distinction-Witness Boundary, parameterized by an unguarded
schema `S`, a guarded schema `Sg`, and a point `a`. -/
structure DistinctionWitnessBoundary
    (S : DiagonalForkSchema T) (Sg : GuardedDiagonalForkSchema T) (a : T) : Prop where
  /-- **Obstruction.** If the unguarded schema's diagonal verdicts do not join,
  local confluence fails at the diagonal source `S.E a a`. -/
  obstruction : ¬ DiagonalVerdictsJoin S a → ¬ LocalJoinAt S (S.E a a)
  /-- **Recovery.** The guarded schema has local join at its diagonal source
  `Sg.E a a`. -/
  recovery : LocalJoinAtG Sg (Sg.E a a)

/-- **(Part 4 headline) The Distinction-Witness Boundary Theorem.**

For any unguarded diagonal-fork schema `S`, guarded diagonal-fork schema `Sg`,
and point `a`:

* **obstruction** — if `S`'s two diagonal verdicts `Z` and `D a a` do not join,
  then local confluence fails at the diagonal source `S.E a a` (the reflexive
  rule and the *totalized* difference rule create an unjoinable peak); this reuses
  `GenericDiagonalFork.localConfluence_fails_at_diagonal`;
* **recovery** — `Sg`, whose difference rule is *guarded* off the diagonal,
  recovers local join at its diagonal source `Sg.E a a` (`guarded_diagonal_localJoin`).

Together: internalizing distinction via a reflexive rule plus a totalized
difference rule forces non-confluence at the diagonal, *unless* the difference
rule is guarded (or the verdicts are otherwise identified, cf. `delete_recovers`
/ `quotient_recovers`). This is the named boundary anchor.

Relation: abstract `S.R` (obstruction) and guarded `Sg.R` (recovery).
Property: `local_confluence` at the diagonal source (its failure, resp. recovery). -/
theorem distinction_witness_boundary
    (S : DiagonalForkSchema T) (Sg : GuardedDiagonalForkSchema T) (a : T) :
    DistinctionWitnessBoundary S Sg a :=
  { obstruction := fun hnj => localConfluence_fails_at_diagonal S a hnj
    recovery := guarded_diagonal_localJoin Sg a }

/-! ## Statement-adequacy checks and axiom inventory (Gates R2, R1) -/

section AuditChecks

-- Part 1
#check @localJoinAt_diagonal_imp_verdictsJoin
#check @DiagonalDetermined
#check @diagonal_localConfluence_iff_verdictsJoin
-- Part 2
#check @GuardedDiagonalForkSchema
#check @LocalJoinAtG
#check @guarded_diagonal_localJoin
#check @delete_recovers
#check @quotient_recovers
-- Part 3
#check @GuardedStep
#check @guardedStep_diag_unique
#check @ko7GuardedDiagonalFork
#check @ko7_guarded_diagonal_localJoin
#check (ko7_unguarded_obstruction : ¬ MetaSN_KO7.LocalJoinStep (eqW void void))
-- Part 4
#check @DistinctionWitnessBoundary
#check @distinction_witness_boundary

-- Headline axiom inventories (each must be ⊆ {propext, Classical.choice, Quot.sound}).
#print axioms localJoinAt_diagonal_imp_verdictsJoin
#print axioms diagonal_localConfluence_iff_verdictsJoin
#print axioms guarded_diagonal_localJoin
#print axioms ko7_guarded_diagonal_localJoin
#print axioms distinction_witness_boundary

end AuditChecks

end OperatorKO7.Meta.SafeStep.DistinctionWitnessBoundary
