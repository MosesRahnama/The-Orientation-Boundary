import OperatorKO7.Meta.DistinctionBoundary.GodelPartial

set_option autoImplicit false

/-!
# Escape trichotomy for the Goedel object: three doors, no fourth

The fixed-point obstruction of `GodelObject.lean` consumes three
hypotheses: totality of evaluation (`H_tot`), a shared argument/value
carrier (`H_car`), and membership of the diagonal composite in the
represented class (`H_rep`). This module packages the three clauses as
an `Ingredients` record, proves the De Morgan trichotomy
(`escape_complete` / `escape_sound` / `escape_iff_not_obstruction`),
and then ties each clause to the compiled KO7 structure that takes that
escape, so the trichotomy is about the live objects and each door has a
named inhabitant:

* `H_tot` at the partiality escape: totality of the fuelled interpreter
  `GodelPartial.step` fails (`fuelled_eval_not_total`, via the
  everywhere-divergent code; the diagonal composite
  `diagonal_successor_composite_diverges_at_own_code` diverges at its
  own encoding for the diagonal reason).
* `H_car` at the separate-value escape: the unit-valued evaluator
  admits no retraction onto the carrier
  (`unitValued_retraction_impossible`, re-exporting
  `Godel.unit_valued_has_no_retraction`).
* `H_rep` at the smaller-class escape: the schematic quote-represented
  class omits the diagonal-successor composite
  (`schematic_omits_delta_selfap`, from
  `Godel.quote_represented_are_constants`).

Scope fence: the trichotomy is exhaustive over the three named clauses
of one `Ingredients` record (De Morgan on a three-clause conjunction);
the mathematical weight is the identification of the clauses in
`GodelObject.lean`/`GodelPartial.lean`. The concrete record
`ko7Ingredients` instantiates each clause at the KO7 structure that
takes that escape (partial interpreter, unit-valued evaluator,
schematic fragment); it does not assert the three clauses about a
single self-evaluation structure. Nothing here is an incompleteness
theorem.

Relation: not applicable (Prop-level classification).
Closure: not applicable. Strategy: not applicable.
Trust: kernel only, Mathlib baseline
(`escape_complete` uses classical case analysis).
-/

namespace OperatorKO7.Meta.DistinctionBoundary.GodelEscape

open OperatorKO7
open OperatorKO7.Meta.DistinctionBoundary.DiagonalLevels
open OperatorKO7.Meta.DistinctionBoundary.Godel
open OperatorKO7.Meta.DistinctionBoundary.GodelPartial

/-! ## The abstract trichotomy -/

/-- The three ingredients the fixed-point obstruction consumes:
`H_tot` (evaluation total), `H_car` (shared argument/value carrier),
`H_rep` (the represented class contains the diagonal composite). -/
structure Ingredients where
  H_tot : Prop
  H_car : Prop
  H_rep : Prop

/-- The obstruction is the conjunction of the three clauses and nothing
else. -/
def Obstruction (I : Ingredients) : Prop := I.H_tot ∧ I.H_car ∧ I.H_rep

/-- The three escape doors: each is the failure of one clause. -/
inductive Escape (I : Ingredients) : Prop where
  | dropTotality    : ¬ I.H_tot → Escape I
  | separateCarrier : ¬ I.H_car → Escape I
  | restrictClass   : ¬ I.H_rep → Escape I

/-- Completeness (classical De Morgan): a structure that avoids the
obstruction inhabits one of the three escapes; there is no fourth
door. -/
theorem escape_complete (I : Ingredients)
    (hne : ¬ Obstruction I) : Escape I := by
  by_cases h1 : I.H_tot
  · by_cases h2 : I.H_car
    · by_cases h3 : I.H_rep
      · exact absurd ⟨h1, h2, h3⟩ hne
      · exact Escape.restrictClass h3
    · exact Escape.separateCarrier h2
  · exact Escape.dropTotality h1

/-- Soundness: any escape refutes the obstruction. -/
theorem escape_sound (I : Ingredients) : Escape I → ¬ Obstruction I := by
  intro e o
  cases e with
  | dropTotality h    => exact h o.1
  | separateCarrier h => exact h o.2.1
  | restrictClass h   => exact h o.2.2

/-- The equivalence: escaping is refuting the obstruction, and the only
refutations are the three doors. -/
theorem escape_iff_not_obstruction (I : Ingredients) :
    Escape I ↔ ¬ Obstruction I :=
  ⟨escape_sound I, escape_complete I⟩

/-! ## The three concrete clauses -/

/-- `H_tot` clause at the partiality escape: the fuelled interpreter of
`GodelPartial.lean` evaluates every code at every argument to a value. -/
def EvalTotal : Prop :=
  ∀ (c : PartialCode) (x : Trace), ∃ v : Trace, convergesTo c x v

/-- `H_car` clause at the separate-value escape: a decode map retracts
the unit-valued self-application onto the carrier, restoring a shared
argument/value type. -/
def UnitValuedRetraction : Prop :=
  ∃ decode : Unit → Trace, ∀ t : Trace, decode (valueSelfap unitValued t) = t

/-- `H_rep` clause at the smaller-class escape: the schematic
quote-represented class contains the diagonal-successor composite
`delta ∘ S_D`. -/
def SchematicRepresentsDeltaSelfap : Prop :=
  represents schematicSelfEvaluation
    (fun y => Trace.delta (selfap schematicSelfEvaluation y))

/-! ## The three named inhabitants -/

/-- Door 1 inhabitant (partiality): the fuelled interpreter is partial;
the everywhere-divergent code refutes totality. -/
theorem fuelled_eval_not_total : ¬ EvalTotal := by
  intro h
  obtain ⟨v, n, hn⟩ := h .diverge Trace.void
  exact Option.noConfusion ((diverges_diverge Trace.void n).symm.trans hn)

/-- Door 2 inhabitant (carrier separation): no retraction restores the
carrier from the unit-valued evaluator. Re-export of
`Godel.unit_valued_has_no_retraction` at the clause. -/
theorem unitValued_retraction_impossible : ¬ UnitValuedRetraction :=
  unit_valued_has_no_retraction

/-- Door 3 inhabitant (smaller class): every schematic quote-represented
map is constant, so the class omits `delta ∘ S_D`. -/
theorem schematic_omits_delta_selfap : ¬ SchematicRepresentsDeltaSelfap := by
  intro h
  obtain ⟨t, ht⟩ := quote_represented_are_constants h
  have h0 : Trace.delta Trace.void = t := by
    have h0' := ht Trace.void
    rwa [const_quote_forces_identity_selfap] at h0'
  have h1 : Trace.delta (Trace.delta Trace.void) = t := by
    have h1' := ht (Trace.delta Trace.void)
    rwa [const_quote_forces_identity_selfap] at h1'
  have hdd : Trace.delta Trace.void = Trace.delta (Trace.delta Trace.void) :=
    h0.trans h1.symm
  injection hdd with hd
  exact carrier_r5 hd

/-! ## The KO7 record and its doors -/

/-- The concrete ingredients record: each clause instantiated at the
KO7 structure that takes that escape. -/
def ko7Ingredients : Ingredients :=
  ⟨EvalTotal, UnitValuedRetraction, SchematicRepresentsDeltaSelfap⟩

/-- KO7 escapes by the partiality door. -/
theorem ko7_escape_by_partiality : Escape ko7Ingredients :=
  Escape.dropTotality fuelled_eval_not_total

/-- KO7 escapes by the carrier-separation door. -/
theorem ko7_escape_by_carrier : Escape ko7Ingredients :=
  Escape.separateCarrier unitValued_retraction_impossible

/-- KO7 escapes by the smaller-class door. -/
theorem ko7_escape_by_class : Escape ko7Ingredients :=
  Escape.restrictClass schematic_omits_delta_selfap

/-- The KO7 record is unobstructed: the conjunction of the three
concrete clauses fails. -/
theorem ko7_not_obstructed : ¬ Obstruction ko7Ingredients :=
  escape_sound ko7Ingredients ko7_escape_by_partiality

end OperatorKO7.Meta.DistinctionBoundary.GodelEscape
