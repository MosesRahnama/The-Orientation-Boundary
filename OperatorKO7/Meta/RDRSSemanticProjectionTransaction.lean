import OperatorKO7.Meta.RDRSDescentLens
import OperatorKO7.Meta.RDRSSeedCollapse
import OperatorKO7.Meta.RDRSSemanticDirectMeasure

set_option autoImplicit false

/-!
# RDRS Semantic Projection Transaction

Semantic projection transactions.

A semantic projection transaction on an RDRS step `R` packages a projection
`pi : T → T'` that commutes with the left-hand and right-hand sides of the step
(the pi block) and a semantic measure on `T'` with a well-founded strict relation
(the sigma block). A semantic projection escape adds a proof that the projected
measure orients the projected step, and `lifted_orients` transports that
orientation back to `R` through `mu' ∘ pi`.

The record no longer carries the seed-collapse block (`PayloadCarrier`, `seedCollapse`,
`pi_factors_seedCollapse`). Every map factors through the identity seed collapse
(`factorsThroughSeedCollapse_of_identity`), so the block held for every projection,
and no theorem consumed it. The escape record is inhabited by every projection
that commutes with the step together with a semantic measure on its target that
orients the projected step (`semanticProjectionTransactionEscape_of_commuting_projection`),
the identity projection included; an escape on `R` exists if and only if some
semantic measure on `T` orients `R` (`semanticProjectionTransactionEscape_nonempty_iff`).
Payload forgetting is a property of a particular projection and is stated where it
holds: for `Prod.fst` on the counter-first-lex step, in
the semantic projection-transaction audit module.

## Module contract

```
Relation:  RDRSStep B S N T  (source) and RDRSStep B S N T' (projected).
Closure:   root (single-step orientation transport; no contextual
           closure, transitive closure, or SN claim).
Strategy:  N/A.
Trust:     kernel-only. No forbidden trust-surface tokens.
Scope:     semantic projection transactions. The sigma block is a
           `SemanticMeasureData T'`, which carries its own
           well-foundedness proof; the escape additionally requires a
           projected-orientation proof.
```

## Distinction from `ProjectionTransaction`

The static `ProjectionTransaction` (in the projection-transaction module)
carries `ltA' : A' -> A' -> Prop` as a bare strict relation and keeps a
seed-collapse block. This module strengthens the sigma block to a full
`SemanticMeasureData T'` with `wf_ltA : WellFounded ltA`, and the escape adds a
positive projected-orientation proof:

```
(T' + pi + Rproj + commutation)                          -- pi block
  + (A' + ltA' + wf_ltA + mu' = SemanticMeasureData T')  -- sigma block
                                                         -- => SemanticProjectionTransaction
  + projected_orientation                                -- => Escape
```

## Honesty boundary

`lifted_orients` proves single-step orientation transport on the
source step `R`. It is **not** an SN theorem and does **not** discharge
any full DP / MSPO / WPO soundness chain. Source-system termination
belongs to the separate termination layer.
-/

namespace OperatorKO7.RDRSSemanticProjectionTransaction

open OperatorKO7.RDRSDescentLens
open OperatorKO7.RDRSSeedCollapse
open OperatorKO7.RDRSSemanticDirectMeasure

/--
Proves: a semantic projection-transaction record on an RDRS step `R`,
  packaging the pi block (a projection `pi : T → T'` and a projected step
  `Rproj` with commutation on both sides of the step) and the sigma block
  (a `SemanticMeasureData T'`, whose strict relation is well-founded).
Does not prove: that the projected measure orients the projected step
  (that obligation lives on `SemanticProjectionTransactionEscape`), or that
  `pi` forgets the payload. Every commuting projection with any semantic
  measure on its target inhabits the record; the identity projection with
  `Rproj := R` is one.
Relation: source `R : RDRSStep B S N T` and projected `Rproj`.
Closure: root.
Strategy: not applicable.
Trust: kernel-only.
Scope: static data; no DP, MSPO, WPO/gWPO, arbitrary quotient, or
  rewrite oracle.
-/
structure SemanticProjectionTransaction
    {B S N T : Type} (R : RDRSStep B S N T) : Type 1 where
  /-- Projected term type (target of `pi`). -/
  T'              : Type
  /-- `pi`: projection on terms. -/
  pi              : T → T'
  /-- Projected step on `T'`. -/
  Rproj           : RDRSStep B S N T'
  /-- Soundness license (lhs): `pi` commutes with each step's LHS. -/
  pi_commutes_lhs : ∀ b s n, pi (R.lhs b s n) = Rproj.lhs b s n
  /-- Soundness license (rhs): `pi` commutes with each step's RHS. -/
  pi_commutes_rhs : ∀ b s n, pi (R.rhs b s n) = Rproj.rhs b s n
  /-- `sigma`: projected semantic-measure data with well-founded
  strict relation. -/
  semanticMeasure : SemanticMeasureData T'

/--
Proves: positive success certificate for a semantic projection
  transaction. Extends the transaction with a proof that the
  projected measure strictly orients the projected step in the
  (well-founded) projected strict relation.
Does not prove: source-system SN, source-system confluence, full
  DP / MSPO / WPO/gWPO soundness, or payload forgetting. `Orients` is the
  single-step orientation predicate.
Relation: source `R` and projected `Rproj`.
Closure: root.
Strategy: not applicable.
Trust: kernel-only.
Scope: the record is inhabited by every projection commuting with the
  step together with a semantic measure on its target that orients the
  projected step (`semanticProjectionTransactionEscape_of_commuting_projection`),
  the identity projection included; an escape on `R` exists if and only if
  some semantic measure on `T` orients `R`
  (`semanticProjectionTransactionEscape_nonempty_iff`). `lifted_orients`
  uses the commutation and orientation fields.
-/
structure SemanticProjectionTransactionEscape
    {B S N T : Type} (R : RDRSStep B S N T) : Type 1 where
  /-- The underlying semantic projection transaction `(pi, sigma)`. -/
  transaction          : SemanticProjectionTransaction R
  /-- **Positive transaction-success proof.** The projected measure
  strictly orients the projected step. -/
  projected_orientation :
    Orients transaction.Rproj
            transaction.semanticMeasure.μ
            transaction.semanticMeasure.ltA

namespace SemanticProjectionTransactionEscape

variable {B S N T : Type} {R : RDRSStep B S N T}

/--
Proves: the decisive descent measure on the source term type defined
  by factoring the projected measure through `pi`.
Does not prove: any orientation property (that is `lifted_orients`).
Relation: source `R`; not a closure relation.
Closure: not applicable at the definition level.
Strategy: not applicable.
Trust: kernel-only (record projection).
Scope: every escape inhabitant.
-/
def liftedMeasure (E : SemanticProjectionTransactionEscape R) :
    T → E.transaction.semanticMeasure.A :=
  fun t => E.transaction.semanticMeasure.μ (E.transaction.pi t)

/--
Proves: `Orients R (mu' ∘ pi) ltA'` on the source step, with `ltA'`
  the projected (well-founded) strict relation.
Does not prove: source-system SN. Single-step orientation transport is NOT a
  termination theorem.
Relation: `RDRSStep B S N T` at each `(b, s, n)`.
Closure: root.
Strategy: not applicable.
Trust: kernel-only (`rw` of two commutation equations).
Scope: depends on the supplied escape record.
-/
theorem lifted_orients (E : SemanticProjectionTransactionEscape R) :
    Orients R E.liftedMeasure E.transaction.semanticMeasure.ltA := by
  intro b s n
  show E.transaction.semanticMeasure.ltA
        (E.transaction.semanticMeasure.μ (E.transaction.pi (R.rhs b s n)))
        (E.transaction.semanticMeasure.μ (E.transaction.pi (R.lhs b s n)))
  rw [E.transaction.pi_commutes_lhs, E.transaction.pi_commutes_rhs]
  exact E.projected_orientation b s n

end SemanticProjectionTransactionEscape

/-! ## The removed seed-collapse field held for every map -/

/--
Proves: every map `pi : T → X` factors through the identity seed collapse
  `SeedCollapse.id T`, with factor map `pi` itself. This is the field
  `pi_factors_seedCollapse` that `SemanticProjectionTransaction` carried
  before 2026-10-13, at the identity seed collapse: every projection
  satisfied it, so the field carried no payload-forgetting content.
Does not prove: that `pi` forgets any payload; the identity seed collapse
  forgets nothing.
Relation: factorisation of a function on terms; not a rewriting relation.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: every map out of every `T : Type`.
-/
theorem factorsThroughSeedCollapse_of_identity {T X : Type} (pi : T → X) :
    Nonempty (FactorsThroughSeedCollapse (SeedCollapse.id T) pi) :=
  ⟨{ factor := pi, obs_eq := fun _ => rfl }⟩

/-! ## Inhabitation of the escape record -/

/--
Proves: every projection `pi : T → T'` that commutes with both sides of the
  step `R` into a projected step `Rproj`, together with a semantic measure on
  `T'` that orients `Rproj`, yields a semantic projection escape on `R`.
Does not prove: that `pi` forgets the payload; the identity projection with
  `Rproj := R` satisfies the hypotheses whenever a semantic measure on `T`
  orients `R`.
Relation: source `R : RDRSStep B S N T` and projected `Rproj`.
Closure: root.
Strategy: not applicable.
Trust: kernel-only (record construction).
Scope: every RDRS step and every commuting projection.
-/
theorem semanticProjectionTransactionEscape_of_commuting_projection
    {B S N T T' : Type} {R : RDRSStep B S N T}
    (pi : T → T') (Rproj : RDRSStep B S N T')
    (h_lhs : ∀ b s n, pi (R.lhs b s n) = Rproj.lhs b s n)
    (h_rhs : ∀ b s n, pi (R.rhs b s n) = Rproj.rhs b s n)
    (M : SemanticMeasureData T')
    (hOrient : Orients Rproj M.μ M.ltA) :
    Nonempty (SemanticProjectionTransactionEscape R) :=
  ⟨{ transaction :=
       { T' := T'
         pi := pi
         Rproj := Rproj
         pi_commutes_lhs := h_lhs
         pi_commutes_rhs := h_rhs
         semanticMeasure := M }
     projected_orientation := hOrient }⟩

/--
Proves: an RDRS step `R` has a semantic projection escape if and only if
  some semantic measure on `T` orients `R`. Forward: the lifted measure
  `mu' ∘ pi`, with the projected strict relation and its well-foundedness
  proof, orients `R` (`lifted_orients`). Backward: the identity projection
  with `Rproj := R` and the given measure is an escape.
Does not prove: source-system SN, or that the projection of a given escape
  forgets the payload. The equivalence shows that the escape record adds no
  condition beyond orientation of `R` by a well-founded semantic measure.
Relation: source `RDRSStep B S N T`.
Closure: root single-step.
Strategy: not applicable.
Trust: kernel-only.
Scope: every RDRS step.
-/
theorem semanticProjectionTransactionEscape_nonempty_iff
    {B S N T : Type} (R : RDRSStep B S N T) :
    Nonempty (SemanticProjectionTransactionEscape R) ↔
      ∃ M : SemanticMeasureData T, Orients R M.μ M.ltA := by
  constructor
  · rintro ⟨E⟩
    exact ⟨{ A := E.transaction.semanticMeasure.A
             ltA := E.transaction.semanticMeasure.ltA
             wf_ltA := E.transaction.semanticMeasure.wf_ltA
             μ := E.liftedMeasure }, E.lifted_orients⟩
  · rintro ⟨M, hM⟩
    exact semanticProjectionTransactionEscape_of_commuting_projection
      (fun t => t) R (fun _ _ _ => rfl) (fun _ _ _ => rfl) M hM

/-! ## Extraction theorems -/

/--
Proves: every `SemanticProjectionTransactionEscape` exhibits a
  semantic-measure record (the sigma block) on the projected term
  type.
Does not prove: that arbitrary sigma data lifts to an escape; the
  caller must also supply the commutation and projected-orientation
  evidence to inhabit the escape.
Relation: record extraction; not a rewriting theorem.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: every escape inhabitant.
-/
theorem semantic_projection_escape_requires_sigma
    {B S N T : Type} {R : RDRSStep B S N T}
    (E : SemanticProjectionTransactionEscape R) :
    Nonempty (SemanticMeasureData E.transaction.T') :=
  ⟨E.transaction.semanticMeasure⟩

/--
Proves: the projection of every `SemanticProjectionTransactionEscape`
  factors through some seed collapse on the source term type; the
  witness is the identity seed collapse `SeedCollapse.id T`
  (`factorsThroughSeedCollapse_of_identity`).
Does not prove: that the escape requires a payload-forgetting seed
  collapse. The conclusion holds for every map out of `T`, so the name
  records the former record field, not a condition on the escape.
Relation: record extraction; not a rewriting theorem.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: every escape inhabitant.
-/
theorem semantic_projection_escape_requires_seed_collapse
    {B S N T : Type} {R : RDRSStep B S N T}
    (E : SemanticProjectionTransactionEscape R) :
    ∃ (PayloadCarrier : Type) (sc : SeedCollapse PayloadCarrier T),
      Nonempty (FactorsThroughSeedCollapse sc E.transaction.pi) :=
  ⟨T, SeedCollapse.id T, factorsThroughSeedCollapse_of_identity E.transaction.pi⟩

/--
Proves: every `SemanticProjectionTransactionEscape` carries a
  positive projected-orientation proof on the projected step.
Does not prove: source-system SN. The orientation is single-step on
  the projected side; `lifted_orients` transports it back through
  `pi` at the source level.
Relation: `RDRSStep B S N T'` (projected) at every `(b, s, n)`.
Closure: root.
Strategy: not applicable.
Trust: kernel-only.
Scope: every escape inhabitant.
-/
theorem semantic_projection_escape_requires_projected_orientation
    {B S N T : Type} {R : RDRSStep B S N T}
    (E : SemanticProjectionTransactionEscape R) :
    Orients E.transaction.Rproj
            E.transaction.semanticMeasure.μ
            E.transaction.semanticMeasure.ltA :=
  E.projected_orientation

/--
Proves: every `SemanticProjectionTransactionEscape` has a
  well-founded projected strict relation.
Does not prove: well-foundedness of the source relation.
Relation: record extraction (the field is on the projected sigma
  block, not on the source `R`).
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: every escape inhabitant.
-/
theorem semantic_projection_escape_requires_wellFounded
    {B S N T : Type} {R : RDRSStep B S N T}
    (E : SemanticProjectionTransactionEscape R) :
    WellFounded E.transaction.semanticMeasure.ltA :=
  E.transaction.semanticMeasure.wf_ltA

/-! ## Non-vacuity witness

A concrete `SemanticProjectionTransactionEscape` over `Nat`. The
witness uses `Rproj.lhs := n+1`, `Rproj.rhs := n` so that the
projected orientation `n < n+1` discharges trivially; the projection is
the identity on `Nat`. The witness is concrete and **does not require
[Inhabited T]**: it inhabits the escape branch unconditionally for the
chosen `trivialNatStep`.
-/

/-- A concrete RDRS step on `Nat`. Used as the non-vacuity carrier
for the escape branch. The third positional argument (`N = Nat`) is
the natural-number index used to construct the step pair. -/
def trivialNatStep : RDRSStep Unit Unit Nat Nat where
  lhs := fun _ _ n => n + 1
  rhs := fun _ _ n => n

/-- A concrete `SemanticMeasureData Nat` with the standard well-founded
order. -/
def natSemanticMeasure : SemanticMeasureData Nat where
  A      := Nat
  ltA    := fun a b => a < b
  wf_ltA := Nat.lt_wfRel.wf
  μ      := fun n => n

/-- Concrete inhabitant of `SemanticProjectionTransaction trivialNatStep`. -/
def trivialSemanticTransaction :
    SemanticProjectionTransaction trivialNatStep where
  T'                       := Nat
  pi                       := fun n => n
  Rproj                    := trivialNatStep
  pi_commutes_lhs          := fun _ _ _ => rfl
  pi_commutes_rhs          := fun _ _ _ => rfl
  semanticMeasure          := natSemanticMeasure

/-- Concrete inhabitant of
`SemanticProjectionTransactionEscape trivialNatStep`. The projected
orientation is `n < n + 1`, discharged by `Nat.lt_succ_self`. -/
def trivialSemanticTransactionEscape :
    SemanticProjectionTransactionEscape trivialNatStep where
  transaction           := trivialSemanticTransaction
  projected_orientation := fun _ _ n => Nat.lt_succ_self n

/--
Proves: `SemanticProjectionTransaction trivialNatStep` is non-empty
  via the concrete `trivialSemanticTransaction` witness.
Does not prove: non-emptiness for an arbitrary RDRS step.
Relation: extraction on the concrete `Nat` carrier; not a rewriting
  property of arbitrary `R`.
Trust: kernel-only.
-/
theorem SemanticProjectionTransaction_nonempty :
    Nonempty (SemanticProjectionTransaction trivialNatStep) :=
  ⟨trivialSemanticTransaction⟩

/--
Proves: `SemanticProjectionTransactionEscape trivialNatStep` is
  non-empty via the concrete `trivialSemanticTransactionEscape`
  witness; the projected-orientation field is discharged by
  `Nat.lt_succ_self`.
Does not prove: non-emptiness for an arbitrary RDRS step; the escape
  branch is conditional on the supplied projected orientation.
Trust: kernel-only.
-/
theorem SemanticProjectionTransactionEscape_nonempty :
    Nonempty (SemanticProjectionTransactionEscape trivialNatStep) :=
  ⟨trivialSemanticTransactionEscape⟩

/-- Audit anchor for the semantic projection-transaction surface. -/
def rdrs_semantic_projection_transaction_anchor : String :=
  "OperatorKO7.RDRSSemanticProjectionTransaction.SemanticProjectionTransactionEscape"

end OperatorKO7.RDRSSemanticProjectionTransaction
