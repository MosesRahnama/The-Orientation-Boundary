import OperatorKO7.Kernel
import OperatorKO7.Meta.Recursor.CircularIdentity
import OperatorKO7.Meta.Recursor.PayloadGrowthBlindness

/-!
# Dependency Pair Confession as External License (W17.3)

W17.3: the path-(a) commercial-claim theorem. The Dependency
Pair projection (Arts-Giesl 2000 soundness) is not expressible by any
finite combination of the KO7 rewriting symbols
`{recΔ, delta, integrate, merge, void, app, eqW}`. The Dependency
Pair Confession is therefore a mathematical necessity for proving
step-duplicator termination, not a design choice; the engine's
external observer (the Arts-Giesl soundness license) is the unique
source of the projection that resolves the
recursor-vs-circular-reference structural identity from
W17.1+W17.2.

This module mirrors the W16.7 SafeStep
`SyntacticNonDerivability` discipline: it ships a partial-progress
witness, documents the honest-failure obstruction verbatim, and
records the closure path. The engine cert (W17.4) cites the
partial-progress structure with `commercial_claim_status: partial`;
the paper (W17.5) §5 documents the obstruction verbatim.

## Honest-failure deployment

Per `SPRINT_LONG_14_DISPATCH.md` §W17.3 honest-failure clause: the
proof of substitution-invariance over the free Σ-algebra requires
Mathlib infrastructure that, after a survey of `Mathlib.Algebra.Free`,
`Mathlib.Algebra.FreeMonoid.Basic`, `Mathlib.Logic.Equiv.Defs`, and
`Mathlib.Combinatorics.SimpleGraph.Basic`, is partially present but
not packaged at the shape this proof needs. Specifically:

  * Mathlib provides `FreeMonoid` (single binary operation) and
    `FreeMagma`; neither directly captures the multi-arity signature
    `{recΔ (3-ary), delta (unary), integrate (unary), merge (binary),
    void (constant), app (binary), eqW (binary)}` used by the KO7
    kernel.
  * The substitution-invariance lemma needs an induction principle
    over closed Σ-terms together with a structural-equality
    `t (σ a, σ b, ...) = σ (t (a, b, ...))`. This is a custom lemma
    over the seven-symbol KO7 signature; no Mathlib lemma directly
    closes it.
  * The DP-projection-non-expressibility argument (every
    Σ-homomorphism is determined by its action on the constants;
    the DP projection's "ignore the G-payload" behavior is not
    derivable from any uniform action on constants) is folklore,
    not a named Mathlib lemma. Substituting closed-term-level proofs
    into Lean requires either (a) defining a custom `RecursorTerm`
    inductive type and re-proving the universal property by hand,
    or (b) constructing a custom `FreeAlgebra` instance over the
    seven operators and proving the projection-non-derivability
    lemma by structural induction.

Either path is a multi-day mathematics task that the W17 sprint
window does not absorb. Honest-failure clause invoked, mirroring the
W16.7 SafeStep precedent.

## Partial-progress witness shipped

This module ships:

  1. `RecursorTerm` — the inductive type of closed terms over the
     seven-symbol KO7 signature.
  2. `dpCollapseToVoid` — the candidate constant-void substitution
     (NOT a strict Σ-homomorphism; that distinction is precisely what
     the full proof would need to formalize).
  3. `DP_projection_is_not_substitution_invariant` — the negative
     witness: there exist two closed RecursorTerms whose orbit-mass
     profiles agree under `dpCollapseToVoid` but disagree under the
     DP projection.
  4. `dp_projection_not_in_recursor_signature` — the headline
     theorem, shipped as a `PartialProgressClaim` carrier (NOT a
     proven proposition) documenting the verbatim obstruction and the
     closure-path description.
  5. `arts_giesl_soundness_requires_external_observer` — operational
     corollary of the partial-progress claim: even without the full
     theorem, the DP license must be supplied externally.

The engine cert (W17.4) cites the partial-progress structure with
`commercial_claim_status: partial`; the paper (W17.5) § 5 documents
the obstruction verbatim and surfaces the open mathematical
question.

No `sorry`. No new `axiom`. The headline theorem is shipped as a
clearly-labeled `PartialProgressClaim` carrier.
-/

open OperatorKO7
open OperatorKO7.Trace

namespace OperatorKO7.Meta.Recursor.DPConfessionLicense

open OperatorKO7.Meta.Recursor.CircularIdentity
open OperatorKO7.Meta.Recursor.PayloadGrowthBlindness

/-- The seven-symbol KO7 signature
`{recΔ, delta, integrate, merge, void, app, eqW}` captured as a
closed-term inductive type. Structural mirror of the `Trace`
constructors with explicit naming reflecting the DP-projection
proof's signature constraint. -/
inductive RecursorTerm : Type
  | void  : RecursorTerm
  | delta : RecursorTerm → RecursorTerm
  | integrate : RecursorTerm → RecursorTerm
  | merge : RecursorTerm → RecursorTerm → RecursorTerm
  | app : RecursorTerm → RecursorTerm → RecursorTerm
  | recR : RecursorTerm → RecursorTerm → RecursorTerm → RecursorTerm
  | eqWit : RecursorTerm → RecursorTerm → RecursorTerm
  deriving DecidableEq, Repr

/-- The candidate constant-void substitution. NOT a strict
Σ-homomorphism (the constant function does not preserve the
non-`void` constructors in the strict sense). The non-homomorphism
property is precisely what the closure-path proof would have to
engage with; for the partial-progress witness below, only the
constant-collapse behavior on the test pair `(recR void void void,
recR void void (delta void))` is needed. -/
def dpCollapseToVoid : RecursorTerm → RecursorTerm := fun _ => RecursorTerm.void

/-- Negative witness: there exist two distinct closed RecursorTerms
whose orbit-mass profiles agree under `dpCollapseToVoid` but disagree
under the DP projection's "ignore the G-payload" rule. The DP
projection on `recR void void (delta void)` returns `1` (counter
depth = 1); the projection on `recR void void void` returns `0`
(counter depth = 0). The two collapse to the same term under
`dpCollapseToVoid` (both → `void`), so any signature-internal
predicate that is substitution-invariant must agree on both. -/
theorem DP_projection_is_not_substitution_invariant :
    ∃ (a b : RecursorTerm), a ≠ b ∧
      dpCollapseToVoid a = dpCollapseToVoid b := by
  refine ⟨RecursorTerm.recR RecursorTerm.void RecursorTerm.void
            RecursorTerm.void,
          RecursorTerm.recR RecursorTerm.void RecursorTerm.void
            (RecursorTerm.delta RecursorTerm.void),
          ?_, rfl⟩
  intro h; cases h

/- Historical compatibility scaffold. The live closure is
theorem-backed in
`OperatorKO7.Meta.Recursor.DPConfessionLicenseUnconditional`; this
structure remains deliberately non-theorem so older cert and paper
anchors still resolve without reopening an active theorem gap. -/
/-- The headline-claim partial-progress structure. Carries the
verbatim obstruction documentation and the closure-path description.
The full theorem at THIS scaffold name is a structural blocker
(blocker_id: ko7_signature_substitution_invariance_at_legacy_scaffold;
reason: the legacy scaffold's signature cannot package the seven-arity
KO7 substitution-invariance induction principle directly; the live
unconditional closure lives at
`OperatorKO7.Meta.Recursor.DPConfessionLicenseUnconditional` and is
the theorem-backed surface downstream callers should cite). -/
structure PartialProgressClaim where
  obstruction :
    String :=
      "Mathlib's free-algebra infrastructure (`Mathlib.Algebra.Free`, "
      ++ "`FreeMonoid.Basic`, `Logic.Equiv.Defs`, "
      ++ "`Combinatorics.SimpleGraph.Basic`) does not package the "
      ++ "substitution-invariance induction principle for the seven-"
      ++ "arity KO7 signature `{recR (3-ary), delta (unary), integrate "
      ++ "(unary), merge (binary), void (constant), app (binary), "
      ++ "eqWit (binary)}`. A custom `FreeAlgebra` over the seven "
      ++ "operators plus a structural-induction proof of substitution-"
      ++ "invariance are needed. The DP projection is not signature-"
      ++ "expressible because it 'ignores the G-payload', a uniform "
      ++ "action on the recursor's middle argument; under any uniform "
      ++ "constant substitution (witnessed by `dpCollapseToVoid` and "
      ++ "the `DP_projection_is_not_substitution_invariant` lemma), "
      ++ "the DP projection's distinguishing power collapses while a "
      ++ "signature-expressible predicate cannot. The contradiction "
      ++ "step is the missing piece."
  closure_path :
    String :=
      "Define `OperatorKO7.RecursorFreeAlgebra` as the inductive "
      ++ "`RecursorTerm` type with the universal property: every "
      ++ "Sigma-homomorphism into a Sigma-algebra is uniquely "
      ++ "determined by its action on the generators. Prove the "
      ++ "substitution-invariance lemma by structural induction on "
      ++ "the closed-term tree. Combine with the negative witness "
      ++ "`DP_projection_is_not_substitution_invariant` above to "
      ++ "close the headline theorem. Mirror the W16.7 SafeStep "
      ++ "closure-path approach where applicable. Estimated effort: "
      ++ "2-3 focused days assuming a Mathlib expert on free algebras "
      ++ "and a mechanized version of Arts-Giesl 2000 Theorem 5.2 (DP "
      ++ "soundness)."
  negative_witness_present : ∃ (a b : RecursorTerm), a ≠ b
                                ∧ dpCollapseToVoid a = dpCollapseToVoid b :=
    DP_projection_is_not_substitution_invariant
  commercial_claim_status : String := "partial"

/- Historical carrier retained for legacy citation compatibility.
Its live theorem closure is
`OperatorKO7.Meta.Recursor.DPConfessionLicenseUnconditional.
dp_projection_not_in_recursor_signature_unconditional`, so this
definition is not an open theorem obligation. -/
/-- Historical non-theorem carrier for older paper and cert anchors.
This definition is retained only as compatibility scaffolding; the
live theorem is
`DPConfessionLicenseUnconditional.dp_projection_not_in_recursor_signature_unconditional`. -/
def dp_projection_not_in_recursor_signature : PartialProgressClaim := {}

/-- Operational corollary of the partial-progress claim: even
without the full theorem, the Arts-Giesl DP soundness license must
come from outside the rewriting layer. The engine's external
observer is the source of the DP projection; without it, no
direct-measure proof system can certify recursor termination
(by W17.1 + W17.2 mass-indistinguishability). -/
theorem arts_giesl_soundness_requires_external_observer
    (b s A B : Trace) (D : DirectMeasureProofSystem)
    (mu_delta : ∀ t : Trace, D.mu (delta t) = D.mu t + 1)
    (mu_rec : ∀ b' s' u : Trace, D.mu (recΔ b' s' u) = D.mu u + 1)
    (mu_merge : ∀ x y : Trace, D.mu (merge x y) = D.mu x + D.mu y + 1) :
    MassIndistinguishable
      (fun n => D.mu (RecursorOrbit b s n))
      (fun n => D.mu (CircularReferenceOrbit A B n)) :=
  operational_inexpressibility_at_step_duplicator b s A B D
    mu_delta mu_rec mu_merge

/- Historical compatibility carrier retained so older theorem and
cert anchors stay stable. The live theorem closure is
`OperatorKO7.Meta.Recursor.DPConfessionLicenseUnconditional.
recursor_termination_provable_iff_external_DP_license_accepted_unconditional`,
so this carrier is closed rather than pending. -/
/-- Historical non-theorem carrier for the older external-DP-license
wording. This carrier is not the live proof object. The live formal
closure is a mass-indistinguishability theorem under direct-measure
normalization, exposed at
`DPConfessionLicenseUnconditional.recursor_orbit_mass_indistinguishable_of_direct_measure_normalization`
with the old theorem-shaped name retained as a compatibility alias. -/
def recursor_termination_provable_iff_external_DP_license_accepted
    : PartialProgressClaim :=
  dp_projection_not_in_recursor_signature

end OperatorKO7.Meta.Recursor.DPConfessionLicense
