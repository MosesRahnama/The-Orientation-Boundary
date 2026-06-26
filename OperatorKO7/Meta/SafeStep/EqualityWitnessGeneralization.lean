import OperatorKO7.Meta.SafeStep.DistinctionWitnessBoundary
import OperatorKO7.Meta.ComparatorNecessity

/-!
# Equality-witness generalization: comparison, internalization, and diagonal instability

This module states the **scoped universality** of the Distinction Boundary, correcting
the naive over-claim "every distinction-generating system has an `eqW` and universally
fails on the diagonal" (which is false: relational, typed, structural, and guarded
equality all compare without forking). The defensible statement is a four-part stack:

1. **Comparison is necessary and universally available.** Every carrier has a
   relational comparison interface (`externalComparisonInterface`), and a *decidable*
   sound-and-complete comparison interface is exactly `DecidableEq` data
   (`ComparisonInterface.toDecidableEq`), routed through the already-proven
   `ComparatorNecessity.exactComparator_decidableEq`. So comparison is forced, and it
   is a meta-level resource, not internal Σ-expressibility.

2. **Sound comparison refuses the diagonal difference.** Any sound comparison
   interface has `¬ DiffVerdict (query a a)` (`comparison_diagonal_no_difference`):
   the difference branch is simply unavailable where there is no distinction. This is
   the *universal reason* every confluence-preserving equality mode avoids the fork.

3. **Internalized + unguarded + totalized = the fork.** Once comparison is
   internalized as a binary verdict constructor with a reflexive collapse rule and a
   *totalized* difference rule, the diagonal forks exactly when the two verdicts do
   not join (`fork_iff_verdicts_not_join`, the negation of the manuscript
   biconditional). KO7 `eqW` is the minimal closed instance of that mode.

4. **Avoidance.** Guarded, delete, and quotient routes each negate one fork conjunct
   and recover the diagonal (`guarded_/delete_/quotient_avoids_fork`); guarded
   interfaces are explicit counterexamples to the naive universal-failure claim.

Everything here re-exports already-proven baseline-clean anchors from
`GenericDiagonalFork`, `DistinctionWitnessBoundary`, and `ComparatorNecessity`, or
proves short new bridges. No KO7-specific machinery is required for parts 1-4; KO7
enters only as the concrete unguarded-internalized instance.

## Audit notes (LASOT)
* Relation: abstract schema `S.R` (parts 3-4) / none (parts 1-2, pure interface
  bookkeeping). The KO7 instance is `GenericDiagonalFork.ko7DiagonalFork`.
* Property: `local_confluence` at the diagonal (its failure characterization and its
  recovery), plus the comparison-resource necessity.
* No `sorry`, `admit`, `axiom`, `native_decide`, `bv_decide`, `@[csimp]`, `unsafe`,
  `partial`, or `opaque`. `toDecidableEq` uses `by_contra` (Classical, baseline).
* `#print axioms` on every headline is a subset of `{propext, Classical.choice, Quot.sound}`.
-/

set_option autoImplicit false

open OperatorKO7
open OperatorKO7.Meta.SafeStep.GenericDiagonalFork
open OperatorKO7.Meta.SafeStep.DistinctionWitnessBoundary
open OperatorKO7.Meta.ComparatorNecessity

namespace OperatorKO7.Meta.SafeStep.EqualityWitnessGeneralization

universe u
variable {A Q T : Type u}

/-! ## Part 1 — comparison is necessary and universally available -/

/-- A **comparison interface**: a query map into a verdict carrier `Q`, with an
equal-verdict and a difference-verdict predicate. The difference verdict is **sound**
(`DiffVerdict (query a b) → a ≠ b`) and **complete** (`a ≠ b → DiffVerdict ...`), and
the diagonal always carries the equal verdict. The interface is neutral over *how* the
comparison is realized: relational, typed, guarded, structural, or external. It is the
abstract content of "a system that registers distinctions has a comparison capability". -/
structure ComparisonInterface (A Q : Type u) where
  /-- The comparison query: present two values, get a verdict object. -/
  query : A → A → Q
  /-- The "equal" verdict predicate on verdict objects. -/
  EqVerdict : Q → Prop
  /-- The "different" verdict predicate on verdict objects. -/
  DiffVerdict : Q → Prop
  /-- The diagonal query always carries the equal verdict. -/
  eq_diag : ∀ a, EqVerdict (query a a)
  /-- **Soundness** of the difference verdict: a difference verdict forces distinctness. -/
  diff_sound : ∀ {a b}, DiffVerdict (query a b) → a ≠ b
  /-- **Completeness** of the difference verdict: distinct inputs force a difference verdict. -/
  diff_complete : ∀ {a b}, a ≠ b → DiffVerdict (query a b)

/-- **Comparison is universally available, externally.** Every carrier `A` carries a
relational comparison interface: the query returns the pair, and the equal/difference
verdicts are `=`/`≠`. This is a *meta-level* object (a function on `A`), not
Σ-expressibility inside any object signature — exactly the distinction the inexpressibility
theorem turns on. -/
def externalComparisonInterface (A : Type u) : ComparisonInterface A (A × A) where
  query a b := (a, b)
  EqVerdict q := q.1 = q.2
  DiffVerdict q := q.1 ≠ q.2
  eq_diag _ := rfl
  diff_sound h := h
  diff_complete h := h

/-- **Comparison resource necessity: a decidable sound-and-complete comparison
interface is `DecidableEq` data.** Decide `a = b` by the difference decision: a
difference verdict refutes equality (`diff_sound`); its absence forces equality
(`diff_complete`, contrapositive). This pins the resource an exact total distinction
decision must supply — not a weaker oracle, exactly `DecidableEq` — matching
`ComparatorNecessity.exactComparator_decidableEq`. -/
def ComparisonInterface.toDecidableEq (C : ComparisonInterface A Q)
    [inst : ∀ a b, Decidable (C.DiffVerdict (C.query a b))] : DecidableEq A :=
  fun a b =>
    match inst a b with
    | isTrue h  => isFalse (C.diff_sound h)
    | isFalse h => isTrue (by by_contra hab; exact h (C.diff_complete hab))

/-- The comparison resource packaged as an `ExactComparator` (via the necessity bridge
and the already-proven `ComparatorNecessity.decidableEq_exactComparator`). Witnesses
that the comparison interface and exact Boolean comparison are the same resource. -/
noncomputable def ComparisonInterface.toExactComparator (C : ComparisonInterface A Q)
    [∀ a b, Decidable (C.DiffVerdict (C.query a b))] : ExactComparator A :=
  letI := C.toDecidableEq
  decidableEq_exactComparator A

/-! ## Part 2 — sound comparison refuses the diagonal difference (the universal avoidance reason) -/

/-- **The universal avoidance reason.** Any **sound** comparison interface refuses the
difference verdict on the diagonal: `¬ DiffVerdict (query a a)`, because a difference
verdict would entail `a ≠ a`. Every confluence-preserving equality mode (relational,
typed, structural, guarded) inherits this: the difference branch is unavailable where
there is no distinction. The fork is precisely what happens when an *unguarded rewrite
rule* emits the difference verdict anyway, in violation of comparison soundness. -/
theorem comparison_diagonal_no_difference (C : ComparisonInterface A Q) (a : A) :
    ¬ C.DiffVerdict (C.query a a) :=
  fun h => (C.diff_sound h) rfl

/-! ## Part 3 — internalized + unguarded + totalized = the fork -/

/-- An **internalized unguarded** equality witness *is* a diagonal-fork schema: a
binary verdict constructor with a reflexive collapse rule and a totalized difference
rule. -/
abbrev UnguardedEqWLike (T : Type u) := DiagonalForkSchema T

/-- A **guarded** equality witness: the difference rule fires only off the diagonal. -/
abbrev GuardedEqWLike (T : Type u) := GuardedDiagonalForkSchema T

/-- **Universal instability.** Once comparison is internalized as a reflexive collapse
rule plus a totalized difference rule, the diagonal source `E a a` is a non-joinable
local divergence whenever the two verdicts `Z` and `D a a` do not join. (Re-export of
`localConfluence_fails_at_diagonal` in the generalization vocabulary.) -/
theorem unguarded_internalized_diagonal_fails
    (S : UnguardedEqWLike T) (a : T)
    (hnj : ¬ DiagonalVerdictsJoin S a) :
    ¬ LocalJoinAt S (S.E a a) :=
  localConfluence_fails_at_diagonal S a hnj

/-- **The classification (sharp boundary).** For a *determined* diagonal, local
confluence fails at `E a a` **exactly when** the two diagonal verdicts fail to join.
This is the negation of the manuscript biconditional
`diagonal_localConfluence_iff_verdictsJoin`, and it is what makes the universality
two-sided: a calculus carries the fork iff it keeps the verdicts unjoined. -/
theorem fork_iff_verdicts_not_join
    (S : UnguardedEqWLike T) (a : T) (hdet : DiagonalDetermined S a) :
    (¬ LocalJoinAt S (S.E a a)) ↔ (¬ DiagonalVerdictsJoin S a) :=
  not_congr (diagonal_localConfluence_iff_verdictsJoin S a hdet)

/-! ## Part 4 — avoidance: each mode negates one fork conjunct -/

/-- **Guarded mode avoids the fork** (negates "unguarded"). The guarded schema recovers
local join at the diagonal. -/
theorem guarded_avoids_fork (Sg : GuardedEqWLike T) (a : T) :
    LocalJoinAtG Sg (Sg.E a a) :=
  guarded_diagonal_localJoin Sg a

/-- **Delete mode avoids the fork** (negates "totalized difference": the diagonal
difference output collapses onto `Z`). -/
theorem delete_avoids_fork (S : UnguardedEqWLike T) (a : T) (hdel : S.D a a = S.Z) :
    DiagonalVerdictsJoin S a :=
  delete_recovers S a hdel

/-- **Quotient mode avoids the fork** (negates "verdicts don't join": `Z` and `D a a`
are identified). -/
theorem quotient_avoids_fork (S : UnguardedEqWLike T) (a : T) (hquot : S.Z = S.D a a) :
    DiagonalVerdictsJoin S a :=
  quotient_recovers S a hquot

/-! ## Part 5 — KO7 is the minimal internalized-unguarded instance; no overclaim -/

/-- **KO7 `eqW` is an internalized totalized comparison.** The KO7 kernel realizes the
unguarded-internalized mode on the carrier `Trace`: `eqW` is the verdict constructor and
the reflexive/totalized-difference rules are the kernel's own `Step` rules. -/
def ko7_eqW_is_internalized_totalized_comparison :
    UnguardedEqWLike Trace :=
  ko7DiagonalFork

/-- **No overclaim.** Guarded equality interfaces are explicit *counterexamples* to the
naive universal-failure claim: they carry an equality witness yet do not fork. This is
why the universality is scoped to the unguarded-internalized mode, never asserted for
every equality witness. -/
theorem guarded_interfaces_refute_universal_failure (Sg : GuardedEqWLike T) (a : T) :
    LocalJoinAtG Sg (Sg.E a a) :=
  guarded_diagonal_localJoin Sg a

/-! ## Part 6 — the necessity bridge: every distinction generator is a comparison interface

This part closes the necessity direction. A *distinction-generating system* is forced to
instantiate the eqW-like comparison structure (a sound and complete binary verdict), and a
decidable one carries `DecidableEq`. The structure is induced, not an added assumption; the
object-level reducing form remains a design choice, and only its unguarded totalized variant
carries the diagonal fork (Parts 3-5). -/

/-- A **distinction-generating system**: an abstract surface that registers a non-null
distinction for a pair exactly when the pair is distinct. `sound` is record-legality (a
registered distinction forces distinct inputs) and `generating` is productivity (every
distinct pair is registered). This is the structural content of a system that registers
distinctions, with no commitment to how the registration is realized. -/
structure DistinctionGenerator (A : Type u) where
  /-- A non-null distinction is registered for the pair `(a, b)`. -/
  emitsDistinction : A → A → Prop
  /-- Soundness: a registered distinction forces distinct inputs. -/
  sound : ∀ {a b}, emitsDistinction a b → a ≠ b
  /-- Productivity: every distinct pair is registered. -/
  generating : ∀ {a b}, a ≠ b → emitsDistinction a b

/-- **Structural necessity: every distinction generator is a comparison interface.**
The eqW-like comparison structure, a binary verdict with a sound and complete difference
verdict and an equal verdict on the diagonal, is forced by the act of registering
distinctions. The difference verdict is the registration of a distinction, the equal
verdict is its absence, and the diagonal carries the equal verdict because a registered
distinction there would force `a ≠ a`. The structure is induced from the generator, never
assumed. -/
def DistinctionGenerator.toComparisonInterface (G : DistinctionGenerator A) :
    ComparisonInterface A (A × A) where
  query a b := (a, b)
  EqVerdict q := ¬ G.emitsDistinction q.1 q.2
  DiffVerdict q := G.emitsDistinction q.1 q.2
  eq_diag a := fun h => (G.sound h) rfl
  diff_sound h := G.sound h
  diff_complete h := G.generating h

/-- **Resource necessity: a decidable distinction generator carries decidable equality.**
Once a distinction generator can decide whether it would register a distinction, it has
`DecidableEq A`. This pins the meta-level resource a distinction generator supplies, the
same resource the comparator-necessity equivalence `ComparatorNecessity.exactComparator_decidableEq`
identifies, which `SyntacticNonDerivability.disequality_not_sigma_expressible_unconditional`
shows the kernel signature cannot synthesise from inside. -/
def DistinctionGenerator.toDecidableEq (G : DistinctionGenerator A)
    [inst : ∀ a b, Decidable (G.emitsDistinction a b)] : DecidableEq A :=
  fun a b =>
    match inst a b with
    | isTrue h  => isFalse (G.sound h)
    | isFalse h => isTrue (by by_contra hab; exact h (G.generating hab))

/-- **The induced comparison is diagonal-inert.** A distinction generator registers no
distinction on the diagonal, since a registered distinction at `a = a` would force `a ≠ a`.
Registering a distinction is the off-diagonal event, which is the abstract form of the
record-legality face. -/
theorem distinctionGenerator_diagonal_inert (G : DistinctionGenerator A) (a : A) :
    ¬ G.emitsDistinction a a :=
  fun h => (G.sound h) rfl

/-- **Non-vacuity and round-trip.** Any carrier with decidable equality is a distinction
generator, registering a distinction exactly when the inputs differ. This inhabits the
`DistinctionGenerator` structure and closes the loop with the comparator resource: the
generator built from `DecidableEq A` decides its registrations by the ambient equality. -/
def decidableEq_distinctionGenerator (A : Type u) [DecidableEq A] : DistinctionGenerator A where
  emitsDistinction a b := a ≠ b
  sound h := h
  generating h := h

/-! ## Statement-adequacy checks and axiom inventory (Gates R2, R1) -/

section AuditChecks

#check @externalComparisonInterface
#check @ComparisonInterface.toDecidableEq
#check @ComparisonInterface.toExactComparator
#check @comparison_diagonal_no_difference
#check @unguarded_internalized_diagonal_fails
#check @fork_iff_verdicts_not_join
#check @guarded_avoids_fork
#check @delete_avoids_fork
#check @quotient_avoids_fork
#check (ko7_eqW_is_internalized_totalized_comparison : UnguardedEqWLike Trace)
#check @guarded_interfaces_refute_universal_failure

#print axioms comparison_diagonal_no_difference
#print axioms ComparisonInterface.toDecidableEq
#print axioms fork_iff_verdicts_not_join
#print axioms guarded_avoids_fork
#print axioms delete_avoids_fork
#print axioms quotient_avoids_fork
#print axioms ko7_eqW_is_internalized_totalized_comparison

#check @DistinctionGenerator.toComparisonInterface
#check @DistinctionGenerator.toDecidableEq
#check @distinctionGenerator_diagonal_inert
#check @decidableEq_distinctionGenerator
#print axioms distinctionGenerator_diagonal_inert
#print axioms DistinctionGenerator.toDecidableEq

end AuditChecks

end OperatorKO7.Meta.SafeStep.EqualityWitnessGeneralization
