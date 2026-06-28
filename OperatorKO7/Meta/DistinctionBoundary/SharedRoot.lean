import OperatorKO7.Meta.SafeStep.SyntacticNonDerivability
import OperatorKO7.Meta.SafeStep.SigmaFreeAlgebra
import OperatorKO7.Meta.Recursor.RecursorFreeAlgebra
import OperatorKO7.Meta.Recursor.DPConfessionLicenseUnconditional

set_option autoImplicit false

/-!
# The two non-derivabilities share one substitution-invariance root (WAVE5)

The Distinction paper (`thm:onefaces`, "one obstruction, two faces") states that
the orientation-axis non-derivability and the distinction-axis non-derivability are
two INSTANCES of ONE substitution-invariance obstruction on the KO7 signature. This
module mechanizes that claim as a single shared Lean object, not prose.

## The genuine shared shape (honesty fence G1/G8)

Both non-derivabilities live over a **free algebra on the seven KO7 constructors**
(`{void, delta, integrate, merge, app, recR/recΔ, eqW}`):

* distinction: `SigmaFreeAlgebra.SigmaTerm` with the homomorphic substitution
  evaluator `evalSigma`;
* orientation: `RecursorFreeAlgebra` `RecursorTerm` with the homomorphic fold
  `RecursorTerm.fold`.

In each, the obstruction is identical in shape: there is a **constant-collapse
Σ-homomorphism** (every constructor mapped to a single carrier value) that
identifies a witness pair `a ≠ b`, while an **external license** genuinely
separates `a` and `b`. The homomorphic evaluator therefore cannot distinguish what
the external license distinguishes; the license is not internal to the rewriting
layer. That single sentence is the abstract object `SubstitutionInvariantObstruction`
defined below, and BOTH axes are exhibited as inhabitants of it.

This is the substitution-invariance unification, NOT the degenerate collapse
isomorphism: `BoundaryDuality.collapseBoundaryOperator` / `verdictSwap` has a
collapse fixed by construction and is neither imported nor referenced here. The content
is the two genuine already-unconditional substitution-invariance facts:

* `SigmaFreeAlgebra.disequality_is_not_substitution_invariant`
  (`∃ a b, a ≠ b ∧ evalSigma a b void = void`), and
* `DPConfessionLicense.DP_projection_is_not_substitution_invariant`
  (`∃ a b, a ≠ b ∧ dpCollapseToVoid a = dpCollapseToVoid b`).

Neither non-derivability theorem is weakened: the headline records that each is an
instance of the shared obstruction, and both instances are exhibited
non-vacuously (a concrete distinct witness pair, collapsed by a genuine constant
Σ-homomorphism, on each axis).

## What is genuinely shared vs. what differs (honest scope)

GENUINELY SHARED (the substitution-invariance core): a constant Σ-homomorphism over
the seven KO7 constructors identifies a distinct witness pair on each axis. This is
the `evalSigma` / `fold` substitution-invariance content, abstracted to
`SubstitutionInvariantObstruction` and instantiated on both axes.

DIFFERS (the external-license target predicate): the distinction license is the
Boolean disequality `a ≠ b`; the orientation license is the DP counter-payload
projection (Arts-Giesl 2000 DP soundness). These are different target predicates on
the two axes, captured by the per-instance `license` field. The unification is at
the substitution-invariance level (the shared root), not at the level of a single
common target predicate. The headline states exactly this and no more.

Relation: not a rewriting relation; this is a metatheoretic statement about
signature-homomorphic evaluators over the two KO7 free algebras.
Closure: not applicable. Strategy: not applicable.
Property: substitution-invariance obstruction (inexpressibility), NOT a
normalization, SN, or confluence theorem.
Trust: kernel-only; allowed axioms only.
-/

namespace OperatorKO7.Meta.DistinctionBoundary.SharedRoot

open OperatorKO7.Meta.SafeStep.SigmaFreeAlgebra
open OperatorKO7.Meta.SafeStep.SyntacticNonDerivability
open OperatorKO7.Meta.Recursor.RecursorFreeAlgebra
open OperatorKO7.Meta.Recursor.DPConfessionLicense

/-! ## The abstract substitution-invariance obstruction -/

/-- **The one obstruction, abstractly.**

`SubstitutionInvariantObstruction Term Lic` captures the common shape of both KO7
non-derivabilities: a homomorphic *collapse* evaluator over the signature
identifies a witness pair that an external license genuinely separates.

Fields:

* `collapse : Term → Term` — the constant-collapse Σ-homomorphism (every
  constructor sent to one carrier value). Concretely this is `evalSigma a b ·` at a
  fixed term on the distinction axis, and `dpCollapseToVoid` / the fixed-void
  fold on the orientation axis.
* `license : Term → Lic` — the EXTERNAL license observable, i.e. the boundary
  decision that lives outside the rewriting layer (disequality for distinction, the
  DP counter projection for orientation).
* `a`, `b` — the witness pair.
* `distinct : a ≠ b` — the pair is genuinely distinct (non-vacuity guard: the
  collapse really does identify two different terms).
* `collapse_identifies : collapse a = collapse b` — the homomorphic evaluator
  cannot distinguish the pair (substitution-invariance: it reads only collapsed
  structure).
* `license_separates : license a ≠ license b` — the external license DOES
  distinguish the pair.

The conjunction is exactly "a homomorphic evaluator over the KO7 constructors
cannot distinguish what an external license distinguishes". -/
structure SubstitutionInvariantObstruction (Term : Type) (Lic : Type) where
  /-- The constant-collapse Σ-homomorphism over the signature. -/
  collapse : Term → Term
  /-- The external license observable (boundary decision outside the layer). -/
  license : Term → Lic
  /-- First witness term. -/
  a : Term
  /-- Second witness term. -/
  b : Term
  /-- The witness pair is genuinely distinct. -/
  distinct : a ≠ b
  /-- The collapse evaluator identifies the witness pair (substitution-invariance). -/
  collapse_identifies : collapse a = collapse b
  /-- The external license separates the witness pair. -/
  license_separates : license a ≠ license b

namespace SubstitutionInvariantObstruction

variable {Term : Type} {Lic : Type}

/-- **The core consequence of the obstruction.** The collapse evaluator and the
external license disagree on the witness pair: the collapse identifies `(a, b)`
while the license separates them. Hence no map that factors through `collapse`
(reads only the collapsed image) can reproduce the license's decision on this
pair — the license is not signature-internal.

Proves: `collapse a = collapse b ∧ license a ≠ license b` for the carried witness.
Does not prove: any statement about a specific rewriting relation.
Relation: not applicable (metatheoretic). Closure: not applicable.
Trust: kernel-only. -/
theorem collapse_blind_license_sighted
    (O : SubstitutionInvariantObstruction Term Lic) :
    O.collapse O.a = O.collapse O.b ∧ O.license O.a ≠ O.license O.b :=
  ⟨O.collapse_identifies, O.license_separates⟩

/-- **Non-vacuity of the obstruction.** Every inhabitant exhibits a genuinely
distinct witness pair that the collapse evaluator identifies; in particular the
collapse is not injective on the carrier, so the obstruction is not an empty shell.

Proves: `∃ a b, a ≠ b ∧ O.collapse a = O.collapse b`.
Does not prove: anything about a specific rewriting relation.
Trust: kernel-only. -/
theorem collapse_not_injective
    (O : SubstitutionInvariantObstruction Term Lic) :
    ∃ a b : Term, a ≠ b ∧ O.collapse a = O.collapse b :=
  ⟨O.a, O.b, O.distinct, O.collapse_identifies⟩

end SubstitutionInvariantObstruction

/-! ## Instance 1 — the distinction axis (eqW disequality)

The constant-collapse Σ-homomorphism is `evalSigma · · void`, which by
`evalSigma_void` returns `void` on every input (a genuine homomorphic evaluator
specialized at the constant term `void`). The witness pair is `(void, delta void)`,
distinct closed terms collapsed to the same image. The external license is the
disequality decision: the identity license `id`, whose separation on the pair is
exactly `void ≠ delta void`. This is the substitution-invariance content of
`disequality_is_not_substitution_invariant` repackaged as a shared-root instance. -/

/-- The distinction-axis instance of the shared obstruction. `collapse` is the
fixed-void substitution evaluator `evalSigma · · void`; the witness pair is
`(void, delta void)`; the external license is the identity (the disequality
decision separates the two terms). Non-vacuous: every field is a genuine value and
`distinct` is the real disequality. -/
def distinctionObstruction :
    SubstitutionInvariantObstruction SigmaTerm SigmaTerm where
  collapse := fun t => evalSigma t t SigmaTerm.void
  license := fun t => t
  a := SigmaTerm.void
  b := SigmaTerm.delta SigmaTerm.void
  distinct := by intro h; cases h
  collapse_identifies := by
    -- both sides reduce to `void` by `evalSigma_void`.
    show evalSigma SigmaTerm.void SigmaTerm.void SigmaTerm.void
          = evalSigma (SigmaTerm.delta SigmaTerm.void)
              (SigmaTerm.delta SigmaTerm.void) SigmaTerm.void
    rw [evalSigma_void, evalSigma_void]
  license_separates := by intro h; cases h

/-- The distinction instance genuinely realizes the substitution-invariance content
of `disequality_is_not_substitution_invariant`: its collapse identifies a distinct
pair, exactly the `∃ a b, a ≠ b ∧ evalSigma a b void = void` witness.

Proves: the distinction obstruction's `collapse` identifies its distinct witness
pair, matching `disequality_is_not_substitution_invariant`.
Does not prove: a rewriting statement. Trust: kernel-only. -/
theorem distinctionObstruction_matches_sigma_witness :
    distinctionObstruction.a ≠ distinctionObstruction.b ∧
      evalSigma distinctionObstruction.a distinctionObstruction.a
        SigmaTerm.void = SigmaTerm.void := by
  refine ⟨distinctionObstruction.distinct, ?_⟩
  exact evalSigma_void distinctionObstruction.a distinctionObstruction.a

/-! ## Instance 2 — the orientation axis (DP counter projection)

The constant-collapse Σ-homomorphism is `dpCollapseToVoid` (= `fun _ => void`,
which is the canonical constant-void fold `RecursorTerm.fold DpCollapseToVoidSigma`
by `RecursorTerm.fold_DpCollapseToVoidSigma_eq_dpCollapseToVoid`). The witness pair
is `(recR void void void, recR void void (delta void))`, distinct closed terms
collapsed to the same image. The external license is the DP counter-payload
projection: a map separating the two terms by their recursor counter depth
(0 vs 1). This is the substitution-invariance content of
`DP_projection_is_not_substitution_invariant` repackaged as a shared-root instance. -/

/-- The DP counter-payload projection, as a concrete external license that
separates the orientation witness pair: it returns the counter depth of the third
argument of an outermost `recR`. On `recR void void void` it returns `0`; on
`recR void void (delta void)` it returns `1`. This is the orientation-axis
external license (Arts-Giesl 2000 DP soundness), made concrete only enough to
witness separation. -/
def dpCounterProjection : RecursorTerm → Nat
  | RecursorTerm.recR _ _ (RecursorTerm.delta _) => 1
  | _ => 0

/-- The orientation-axis instance of the shared obstruction. `collapse` is
`dpCollapseToVoid`; the witness pair is the W17.3 recursor pair; the external
license is `dpCounterProjection` (counter depth), which separates the pair `0 ≠ 1`.
Non-vacuous: every field is a genuine value and `distinct` is the real recursor-term
disequality. -/
def orientationObstruction :
    SubstitutionInvariantObstruction RecursorTerm Nat where
  collapse := dpCollapseToVoid
  license := dpCounterProjection
  a := RecursorTerm.recR RecursorTerm.void RecursorTerm.void RecursorTerm.void
  b := RecursorTerm.recR RecursorTerm.void RecursorTerm.void
        (RecursorTerm.delta RecursorTerm.void)
  distinct := by intro h; cases h
  collapse_identifies := rfl
  license_separates := by
    -- license a = 0, license b = 1.
    show dpCounterProjection
          (RecursorTerm.recR RecursorTerm.void RecursorTerm.void RecursorTerm.void)
        ≠ dpCounterProjection
          (RecursorTerm.recR RecursorTerm.void RecursorTerm.void
            (RecursorTerm.delta RecursorTerm.void))
    intro h; cases h

/-- The orientation instance genuinely realizes the substitution-invariance content
of `DP_projection_is_not_substitution_invariant`: its collapse identifies a
distinct pair, exactly the `∃ a b, a ≠ b ∧ dpCollapseToVoid a = dpCollapseToVoid b`
witness, and its collapse coincides with the canonical constant-void fold.

Proves: the orientation obstruction's `collapse` identifies its distinct witness
pair, and equals the canonical fold `RecursorTerm.fold DpCollapseToVoidSigma` on
both witnesses.
Does not prove: a rewriting statement. Trust: kernel-only. -/
theorem orientationObstruction_matches_fold_witness :
    orientationObstruction.a ≠ orientationObstruction.b ∧
      RecursorTerm.fold DpCollapseToVoidSigma orientationObstruction.a
        = RecursorTerm.fold DpCollapseToVoidSigma orientationObstruction.b := by
  refine ⟨orientationObstruction.distinct, ?_⟩
  rw [RecursorTerm.fold_DpCollapseToVoidSigma_eq_dpCollapseToVoid,
      RecursorTerm.fold_DpCollapseToVoidSigma_eq_dpCollapseToVoid]
  exact orientationObstruction.collapse_identifies

/-! ## The headline: both axes share one root -/

/-- **`two_nonderivabilities_share_one_root`** (Distinction paper `thm:onefaces`,
"one obstruction, two faces", mechanized).

A single theorem witnessing that both axes' inexpressibility is the SAME
substitution-invariance obstruction. It exhibits BOTH the distinction-axis
instance and the orientation-axis instance of the one abstract
`SubstitutionInvariantObstruction`, and certifies that each is non-vacuous (a
genuinely distinct witness pair identified by a constant Σ-homomorphism over the
KO7 constructors), and that each carries the GENUINE already-unconditional
substitution-invariance fact of its axis:

* distinction: `disequality_is_not_substitution_invariant`
  (`∃ a b, a ≠ b ∧ evalSigma a b void = void`), realized by `distinctionObstruction`;
* orientation: `DP_projection_is_not_substitution_invariant`
  (`∃ a b, a ≠ b ∧ dpCollapseToVoid a = dpCollapseToVoid b`), realized by
  `orientationObstruction`.

Both obstructions have the same abstract type up to the carriers, and both satisfy
`collapse_blind_license_sighted` (collapse identifies, license separates) and
`collapse_not_injective` (non-vacuity).

**Proves:** the existence of the two instances together with, for each, the
collapse-blind/license-sighted core, the non-vacuity of the collapse identification,
and the matching original substitution-invariance witness of that axis.
**Does not prove:** that the two external license predicates are the same predicate
(they are NOT — disequality vs DP counter projection); the unification is at the
substitution-invariance level (the shared collapse root), not at the target
predicate. It also proves no SN, confluence, or normalization statement.
**Relation:** metatheoretic (signature-homomorphic evaluators over the two KO7 free
algebras), not a rewriting relation. **Trust:** kernel-only. -/
theorem two_nonderivabilities_share_one_root :
    -- distinction-axis instance, non-vacuous, carrying its genuine witness
    ( (distinctionObstruction.collapse distinctionObstruction.a
          = distinctionObstruction.collapse distinctionObstruction.b
        ∧ distinctionObstruction.license distinctionObstruction.a
          ≠ distinctionObstruction.license distinctionObstruction.b)
      ∧ (∃ a b : SigmaTerm, a ≠ b ∧ distinctionObstruction.collapse a
            = distinctionObstruction.collapse b)
      ∧ (∃ a b : SigmaTerm, a ≠ b ∧ evalSigma a b SigmaTerm.void = SigmaTerm.void) )
    ∧
    -- orientation-axis instance, non-vacuous, carrying its genuine witness
    ( (orientationObstruction.collapse orientationObstruction.a
          = orientationObstruction.collapse orientationObstruction.b
        ∧ orientationObstruction.license orientationObstruction.a
          ≠ orientationObstruction.license orientationObstruction.b)
      ∧ (∃ a b : RecursorTerm, a ≠ b ∧ orientationObstruction.collapse a
            = orientationObstruction.collapse b)
      ∧ (∃ a b : RecursorTerm, a ≠ b ∧ dpCollapseToVoid a = dpCollapseToVoid b) ) :=
  ⟨⟨distinctionObstruction.collapse_blind_license_sighted,
    distinctionObstruction.collapse_not_injective,
    disequality_is_not_substitution_invariant⟩,
   ⟨orientationObstruction.collapse_blind_license_sighted,
    orientationObstruction.collapse_not_injective,
    DP_projection_is_not_substitution_invariant⟩⟩

/-- **Corollary: the shared root is genuinely shared, not a single relabeled object.**
The two instances sit over different carrier signatures (`SigmaTerm` vs
`RecursorTerm`) and carry different external license codomains (`SigmaTerm` for the
disequality decision, `Nat` for the DP counter depth). Yet both inhabit the one
abstract `SubstitutionInvariantObstruction`. This rules out the degenerate reading
in which "two faces" is a relabeling of one object: the shared content is the
abstract obstruction, while the two faces are genuinely distinct instances.

Proves: both instances satisfy the abstract obstruction's core consequence, with
distinct carrier and license types.
Does not prove: a rewriting statement. Trust: kernel-only. -/
theorem shared_root_has_two_genuine_faces :
    (distinctionObstruction.collapse distinctionObstruction.a
        = distinctionObstruction.collapse distinctionObstruction.b
      ∧ distinctionObstruction.license distinctionObstruction.a
        ≠ distinctionObstruction.license distinctionObstruction.b)
    ∧
    (orientationObstruction.collapse orientationObstruction.a
        = orientationObstruction.collapse orientationObstruction.b
      ∧ orientationObstruction.license orientationObstruction.a
        ≠ orientationObstruction.license orientationObstruction.b) :=
  ⟨distinctionObstruction.collapse_blind_license_sighted,
   orientationObstruction.collapse_blind_license_sighted⟩

#print axioms two_nonderivabilities_share_one_root
#print axioms shared_root_has_two_genuine_faces
#print axioms distinctionObstruction_matches_sigma_witness
#print axioms orientationObstruction_matches_fold_witness

end OperatorKO7.Meta.DistinctionBoundary.SharedRoot
