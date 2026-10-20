import OperatorKO7.Meta.InformationalIncompleteness.DiagonalEntropy
import OperatorKO7.Meta.InformationalIncompleteness.MemoryDistinction
import OperatorKO7.Meta.BoundaryGeneral.DistinctionRecord

/-!
# Diagonal inertness, fused (T3): one degeneracy on three faces

The carrier diagonal is the no-distinction locus, and the Distinction-Boundary and
Informational-Incompleteness developments read that single fact on three different faces. This module
fuses them.

* **Record face.** A non-null record is emitted from a pair exactly when the pair is a genuine
  distinction (`record_emission_iff_distinction`, new biconditional over the concrete `eqW` record
  surface). On the diagonal the pair is reflexive, so no non-null record is emitted
  (`diagonal_no_record`); this is the record-legality face `equality_record_inert`.
* **Information face.** An `m`-fold diagonal copy of any payload carries no new Shannon information
  (`DiagonalEntropy.diagonal_entropy_eq`): identical copies add no independent information.
* **Rewrite face.** The kernel's attempt to manufacture a distinction at the no-distinction cell
  `eqW void void` forks to unjoinable normal forms (`MemoryDistinction.eqW_distinction_fork`): the
  diagonal is exactly the confluence-boundary site.

`diagonal_inert_trinity` packages the three faces as one statement: the same diagonal is record-inert,
information-inert, and the rewrite fracture site. The non-trivial new content is the record-face
biconditional and its diagonal corollary; the packaging then certifies that the record, information,
and rewrite degeneracies are three coordinates of one diagonal fact.

## Claim typing (binding)
* PROVEN: `record_emission_iff_distinction`, `diagonal_no_record`, `diagonal_inert_trinity`, and the R5
  witness, each a Lean theorem below.
* ANALOGY (docstring only): the reading that these three faces are "the same fact" in a stronger sense
  than the shared diagonal; the formal content is exactly the three conjuncts and the biconditional.

## Audit slots
- Relation: the kernel `Step` relation enters only through the re-exported `eqW void void` critical
  pair; the new content is the record-surface biconditional and finite-alphabet entropy invariance.
- Closure: `propext`, `Classical.choice`, `Quot.sound` (or a subset); verified by `#print axioms`.
- Trust: no `sorry`/`admit`/`axiom`/`opaque`/`partial`/`unsafe`/`native_decide`/`bv_decide`/`@[csimp]`.
- Non-vacuity (R5): `diagonal_inert_trinity_witness` instantiates the trinity at `W = Bool`, `a = true`,
  `α = Bool`, `m = 2`, `p = coinFlip`.
-/

set_option autoImplicit false

noncomputable section

namespace OperatorKO7.Meta.InformationalIncompleteness.DiagonalInert

open OperatorKO7 Trace
open OperatorKO7.Meta.SafeStep.EqWVoidAnomaly
open OperatorKO7.Meta.InformationalIncompleteness.ShannonFinite
open OperatorKO7.Meta.InformationalIncompleteness.DiagonalEntropy
open OperatorKO7.Meta.InformationalIncompleteness.MemoryDistinction
open OperatorKO7.Meta.BoundaryGeneral.DistinctionRecord

/-- **Record face (new).** On the concrete `eqW` record surface, a non-null record is emitted from a
pair `(a, b)` exactly when the pair is a genuine distinction `a ≠ b`. The reflexive rule
`eqW a a → void` emits the null record; the difference rule `eqW a b → integrate(merge a b)` fires
precisely on a distinction. -/
theorem record_emission_iff_distinction {W : Type} (a b : W) :
    (∃ r, (ko7RecordSurface W).emits a b r ∧ (ko7RecordSurface W).nonnull r) ↔ a ≠ b := by
  constructor
  · rintro ⟨r, he, hn⟩
    rcases he with ⟨_, hv⟩ | ⟨hne, _⟩
    · subst hv; exact (hn : False).elim
    · exact hne
  · intro hab
    exact ⟨Rec.diff a b, Or.inr ⟨hab, rfl⟩, trivial⟩

/-- **Record face on the diagonal.** A reflexive input emits no non-null record: at `a = a` there is no
distinction to record. Immediate corollary of `record_emission_iff_distinction` at the diagonal. -/
theorem diagonal_no_record {W : Type} (a : W) :
    ¬ ∃ r, (ko7RecordSurface W).emits a a r ∧ (ko7RecordSurface W).nonnull r := by
  rw [record_emission_iff_distinction]
  exact fun h => h rfl

/-- **Diagonal inertness, fused.** The carrier diagonal is degenerate on all three faces of the
distinction boundary, which are three coordinates of one fact (the diagonal carries no distinction):
the record face emits no non-null record, the information face adds no Shannon information under
`m`-fold diagonal copying, and the rewrite face forks at `eqW void void`. -/
theorem diagonal_inert_trinity {W : Type} (a : W) {α : Type} [Fintype α] [DecidableEq α]
    {m : ℕ} (hm : 0 < m) (p : α → ℝ) :
    (¬ ∃ r, (ko7RecordSurface W).emits a a r ∧ (ko7RecordSurface W).nonnull r)
      ∧ H (pushforward (diag α m) p) = H p
      ∧ CriticalPairAt (eqW void void) void (integrate (merge void void)) :=
  ⟨diagonal_no_record a, diagonal_entropy_eq hm p, eqW_distinction_fork⟩

/-- **Non-vacuity (R5).** The fused trinity holds at a concrete instance (`W = Bool`, `a = true`,
`α = Bool`, `m = 2`, `p = coinFlip`): the reflexive emission is record-inert, the 2-copy diagonal of the
fair register carries no new information, and the kernel forks. -/
theorem diagonal_inert_trinity_witness :
    (¬ ∃ r, (ko7RecordSurface Bool).emits true true r ∧ (ko7RecordSurface Bool).nonnull r)
      ∧ H (pushforward (diag Bool 2) coinFlip) = H coinFlip
      ∧ CriticalPairAt (eqW void void) void (integrate (merge void void)) :=
  diagonal_inert_trinity (W := Bool) true (by norm_num) coinFlip

#print axioms record_emission_iff_distinction
#print axioms diagonal_no_record
#print axioms diagonal_inert_trinity
#print axioms diagonal_inert_trinity_witness

end OperatorKO7.Meta.InformationalIncompleteness.DiagonalInert
