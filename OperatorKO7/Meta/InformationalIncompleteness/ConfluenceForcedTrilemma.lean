import OperatorKO7.Meta.SafeStep.GuardNecessity
import OperatorKO7.Meta.BoundaryGeneral.DistinctionRecord
import OperatorKO7.Meta.InformationalIncompleteness.DiagonalInert

/-!
# The confluence-axis forced-output trilemma and false formal legitimacy (T2)

The Informational-Incompleteness paper proves a *termination-axis* forced-output trilemma: an agent
denied witness-language ascent, forced to commit on the recursor, structurally emits one of
{divergence, unsupported definite output, typed abstention}, and the unique honest output is the typed
confession. The unsupported case is *false formal legitimacy* (proof-shaped output with no witness).

This module proves the exact **confluence-axis twin**. A rewrite engine required to give a unique verdict
at the diagonal `eqW a a` while denied the disequality license has three forced behaviors:

* **(I) non-confluence** — keep both verdicts; the source `eqW a a` is not locally joinable
  (`GuardNecessity.diagonal_emission_incompatible_with_local_confluence`). No unique normal form is
  produced (the confluence-axis analogue of divergence).
* **(II) unlicensed distinction record = false formal legitimacy** — commit the difference branch,
  emitting a non-null distinction record from a no-distinction input. On the distinction-complete `eqW`
  surface no non-null record is licensed at the diagonal (`diagonal_no_licensed_record`,
  `diagonal_emission_is_false_formal_legitimacy`): a forced definite "distinct" verdict at `eqW a a` is a
  record with no distinction witness, the confluence-axis instance of false formal legitimacy.
* **(III) typed confession** — import the disequality license; the SafeStep guard restores local
  confluence at the off-diagonal source (`GuardNecessity.guard_is_the_satisfier`). This is the only
  discharged repair (per `GuardNecessity.RepairRoute`, only the guard arm carries a witness), so the
  typed confession is the unique honest output: it neither loses unique normal forms (I) nor fabricates
  an unlicensed distinction (II).

`confluence_forced_trilemma` packages the three cases. This is the confluence-axis instance of
`thm:trilemma` / `thm:architectural-origin`, feeding the same META-HALT `T3_confession` typed output as
the termination axis (`GaugeFixingGuard.safestep_is_meta_halt`).

## Claim typing (binding)
* PROVEN: every theorem below. The case facts re-export the verified no-go, guard repair, and
  record-inertness anchors; the trilemma packaging and the false-formal-legitimacy framing are the new
  content.
* ANALOGY (docstring only): the identification of the rewrite engine with an autoregressive generator;
  the formal content is the three confluence-axis facts and their packaging.

## Audit slots
- Relation: `Step` (full unguarded kernel) for case I; `SafeStep` for case III; the record surface for
  case II. Closure: root critical pair at the diagonal `eqW a a`.
- Closure: `propext`, `Classical.choice`, `Quot.sound` (or a subset); verified by `#print axioms`.
- Trust: no `sorry`/`admit`/`axiom`/`opaque`/`partial`/`unsafe`/`native_decide`/`bv_decide`/`@[csimp]`.
- Non-vacuity (R5): `confluence_forced_trilemma_witness` instantiates the trilemma at the diagonal `void`.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.InformationalIncompleteness.ConfluenceForcedTrilemma

open OperatorKO7 Trace
open MetaSN_KO7
open OperatorKO7.Meta.SafeStep.GuardNecessity
open OperatorKO7.Meta.SafeStep.GaugeFixingGuard
open OperatorKO7.Meta.BoundaryGeneral.DistinctionRecord
open OperatorKO7.Meta.InformationalIncompleteness.DiagonalInert

/-- The three forced behaviors of a rewrite engine required to give a unique verdict at the diagonal
`eqW a a` while denied the disequality license. -/
inductive ConfluenceForcedCase
  | nonConfluence
  | unlicensedDistinction
  | typedConfession
  deriving DecidableEq, Repr

/-- **Exhaustiveness.** Every forced behavior is one of the three: non-confluence, unlicensed distinction
record, or typed confession. -/
theorem confluence_forced_trilemma_exhaustive (c : ConfluenceForcedCase) :
    c = ConfluenceForcedCase.nonConfluence
      ∨ c = ConfluenceForcedCase.unlicensedDistinction
      ∨ c = ConfluenceForcedCase.typedConfession := by
  cases c <;> decide

/-- **Confluence-axis false formal legitimacy (case II).** Committing a non-null distinction record at
the diagonal is unlicensed: on the distinction-complete `eqW` surface a reflexive input emits no non-null
record. A forced definite "distinct" verdict at `eqW a a` is therefore proof-shaped output (a record)
with no witness (no distinction), the confluence-axis instance of false formal legitimacy. -/
theorem diagonal_emission_is_false_formal_legitimacy {W : Type} (a : W) {r : Rec W}
    (he : (ko7RecordSurface W).emits a a r) : ¬ (ko7RecordSurface W).nonnull r :=
  equality_record_inert (ko7_distinctionComplete W) he

/-- No licensed non-null distinction record exists at the diagonal: the unlicensed-distinction case (II)
can never produce a witnessed record. Re-export of `DiagonalInert.diagonal_no_record`. -/
theorem diagonal_no_licensed_record {W : Type} (a : W) :
    ¬ ∃ r, (ko7RecordSurface W).emits a a r ∧ (ko7RecordSurface W).nonnull r :=
  diagonal_no_record a

/-- **The confluence-axis forced-output trilemma.** For the diagonal source `eqW a a`: (I) keeping both
verdicts is non-confluent; (II) no licensed non-null distinction record exists at the diagonal (a
committed one is false formal legitimacy); (III) the imported disequality guard restores local confluence
off the diagonal. The typed confession (III) is the unique honest output. -/
theorem confluence_forced_trilemma (a : Trace) :
    (¬ LocalJoinStep (eqW a a))
      ∧ (¬ ∃ r, (ko7RecordSurface Trace).emits a a r ∧ (ko7RecordSurface Trace).nonnull r)
      ∧ (∀ b, SafeStepGuard a b → LocalJoinSafe (eqW a b)) :=
  ⟨diagonal_emission_incompatible_with_local_confluence a,
    diagonal_no_licensed_record a,
    fun _ g => guard_is_the_satisfier g⟩

/-- **Non-vacuity (R5).** The trilemma holds at the concrete diagonal source `eqW void void`. -/
theorem confluence_forced_trilemma_witness :
    (¬ LocalJoinStep (eqW void void))
      ∧ (¬ ∃ r, (ko7RecordSurface Trace).emits void void r ∧ (ko7RecordSurface Trace).nonnull r)
      ∧ (∀ b, SafeStepGuard void b → LocalJoinSafe (eqW void b)) :=
  confluence_forced_trilemma void

#print axioms confluence_forced_trilemma_exhaustive
#print axioms diagonal_emission_is_false_formal_legitimacy
#print axioms diagonal_no_licensed_record
#print axioms confluence_forced_trilemma
#print axioms confluence_forced_trilemma_witness

end OperatorKO7.Meta.InformationalIncompleteness.ConfluenceForcedTrilemma
