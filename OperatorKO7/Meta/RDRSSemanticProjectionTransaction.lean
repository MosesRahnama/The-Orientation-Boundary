import OperatorKO7.Meta.RDRSDescentLens
import OperatorKO7.Meta.RDRSSeedCollapse
import OperatorKO7.Meta.RDRSSemanticDirectMeasure

set_option autoImplicit false

/-!
# RDRS Semantic Projection Transaction (Milestone S4)

Roadmap source:
`OperatorKO7-private/Expansion/Universal_Payload_Sensitive_Direct_Measures_Roadmap.md`
Milestone S4 -- Semantic Projection Transactions.

S4 closes the semantic projection branch of the universal payload-
sensitive direct-measure barrier program. The branch must require
`pi` (retained coordinate), `sigma` (external soundness / witness
transport with **well-founded** projected relation), `phi`
(seed-collapse forgetting witness), and a **positive** projected-
orientation proof. Bare erasure syntax does not inhabit this branch.

## Audit slots (Lean Development Bible W8 / R4)

```
Relation:  RDRSStep B S N T  (source) and RDRSStep B S N T' (projected).
Closure:   root (single-step orientation transport; no contextual
           closure, transitive closure, or SN claim).
Strategy:  N/A.
Trust:     kernel-only. No forbidden trust-surface tokens from the
           Lean audit bible.
Scope:     semantic projection transactions only. No DP processor,
           MSPO, WPO/gWPO, arbitrary semantic quotient, transformed-
           relation, or rewrite-oracle escape route inhabits this branch. The
           sigma block uses `SemanticMeasureData T'` which carries its
           own well-foundedness proof; the escape additionally
           requires a projected-orientation proof. No plain erasure
           branch is admitted.
```

## Distinction from U1.5 `ProjectionTransaction`

U1.5's `ProjectionTransaction` (in `RDRSProjectionTransaction.lean`)
carries `ltA' : A' -> A' -> Prop` as a bare strict relation. S4
strengthens this: the sigma block is a full `SemanticMeasureData T'`
which includes `wf_ltA : WellFounded ltA`. The escape adds a positive
projected-orientation proof. Bare erasure thus cannot inhabit
`SemanticProjectionTransactionEscape`:

```
[bare erasure] (T' + pi + Rproj + commutation)        -- not enough
        + (A' + ltA' + wf_ltA + mu' = SemanticMeasureData T')   -- sigma
        + (PayloadCarrier + seedCollapse + pi_factors_seedCollapse) -- phi
                                                       -- => SemanticProjectionTransaction
        + projected_orientation                        -- => Escape
```

Removing any field falsifies inhabitation by Lean's structural
type-checking; this is the precise sense in which "bare erasure
syntax must not inhabit the escape branch."

## K-check 7 honesty

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
Proves: existence of a semantic projection-transaction record on an
  RDRS step `R`, packaging the pi block (retained coordinate with
  commutation), the sigma block (`SemanticMeasureData T'` carrying a
  well-founded projected relation), and the phi block (seed-collapse
  on the source plus `FactorsThroughSeedCollapse` for pi).
Does not prove: the projected measure orients the projected step.
  That obligation lives on `SemanticProjectionTransactionEscape`.
Relation: source `R : RDRSStep B S N T` and projected `Rproj`.
Closure: root.
Strategy: not applicable.
Trust: kernel-only.
Scope: static; no DP, MSPO, WPO/gWPO, arbitrary quotient, or rewrite-
  oracle inhabits this branch; the phi obligation is discharged by a concrete
  `SeedCollapse` + `FactorsThroughSeedCollapse`, never by an opaque
  quotient.
-/
structure SemanticProjectionTransaction
    {B S N T : Type} (R : RDRSStep B S N T) : Type 1 where
  /-- Projected term type (target of `pi`). -/
  T'              : Type
  /-- `pi`: payload-forgetting projection on terms. -/
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
  /-- Abstract payload-carrier type underlying the seed-collapse on `T`. -/
  PayloadCarrier  : Type
  /-- `phi`: seed-collapse data on the source term type. -/
  seedCollapse    : SeedCollapse PayloadCarrier T
  /-- Forgetting witness: `pi` factors through the seed-collapse. -/
  pi_factors_seedCollapse :
    FactorsThroughSeedCollapse seedCollapse pi

/--
Proves: positive success certificate for a semantic projection
  transaction. Extends the transaction with a proof that the
  projected measure strictly orients the projected step in the
  (well-founded) projected strict relation.
Does not prove: source-system SN, source-system confluence, or full
  DP / MSPO / WPO/gWPO soundness. `Orients` is the single-step
  orientation predicate.
Relation: source `R` and projected `Rproj`.
Closure: root.
Strategy: not applicable.
Trust: kernel-only.
Scope: bare erasure plus a well-founded relation is NOT enough; the
  caller must also supply seed-collapse + projected-orientation
  evidence. The structure has no inhabitant without all four fields.
-/
structure SemanticProjectionTransactionEscape
    {B S N T : Type} (R : RDRSStep B S N T) : Type 1 where
  /-- The underlying semantic projection transaction `(pi, sigma, phi, wf)`. -/
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
Does not prove: source-system SN. Per K-check 7 of the Lean
  Development Bible, single-step orientation transport is NOT a
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

/-! ## Required extraction theorems (S4 roadmap) -/

/--
Proves: every `SemanticProjectionTransactionEscape` exhibits a
  semantic-measure record (the sigma block) on the projected term
  type. Records that the escape branch cannot omit the sigma block.
Does not prove: that arbitrary sigma data lifts to an escape; the
  caller must also supply seed-collapse and projected-orientation
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
Proves: every `SemanticProjectionTransactionEscape` exhibits a
  seed-collapse on the source term type together with a
  `FactorsThroughSeedCollapse` witness for `pi`. Records that the
  phi obligation is non-optional on the escape branch.
Does not prove: arbitrary seed-collapse data lifts to an escape; the
  factorisation through `pi` is required.
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
  ⟨E.transaction.PayloadCarrier,
    E.transaction.seedCollapse,
    ⟨E.transaction.pi_factors_seedCollapse⟩⟩

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
  well-founded projected strict relation. Records that the escape
  branch is gated on well-foundedness, not on an arbitrary strict
  relation.
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

/-! ## Non-vacuity witness (Lean Development Bible R5 / S09)

A concrete `SemanticProjectionTransactionEscape` over `Nat`. The
witness uses `Rproj.lhs := n+1`, `Rproj.rhs := n` so that the
projected orientation `n < n+1` discharges trivially; the
seed-collapse is the identity on `Nat`. The witness is concrete and
**does not require [Inhabited T]**: it inhabits the escape branch
unconditionally for the chosen `trivialNatStep`.
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
  PayloadCarrier           := Nat
  seedCollapse             :=
    { carrier := fun n => n
      collapse := fun n => n
      collapse_carrier := fun _ => rfl }
  pi_factors_seedCollapse  :=
    { factor := fun n => n
      obs_eq := fun _ => rfl }

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

/-- Audit anchor for the S4 semantic projection-transaction surface. -/
def rdrs_semantic_projection_transaction_anchor : String :=
  "OperatorKO7.RDRSSemanticProjectionTransaction.SemanticProjectionTransactionEscape"

end OperatorKO7.RDRSSemanticProjectionTransaction
