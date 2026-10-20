import OperatorKO7.Meta.RDRSDescentLens
import OperatorKO7.Meta.RDRSSeedCollapse
import OperatorKO7.Meta.RDRSProjectionTransaction
import OperatorKO7.Meta.RDRSRetainedCoordinate
import OperatorKO7.Meta.RDRSWitnessTransport
import OperatorKO7.Meta.RDRSBoundaryBottleneck
import OperatorKO7.Meta.RDRSSearchBudgetInvariance
import OperatorKO7.Meta.RDRSSemanticDirectMeasure
import OperatorKO7.Meta.RDRSSemanticPayloadSensitivity
import OperatorKO7.Meta.RDRSSemanticProjectionTransaction

set_option autoImplicit false

/-!
# RDRS Semantic Projection-Transaction Hardening Audit

Projection-transaction hardening audit.

This module records four facts about every S4
`SemanticProjectionTransactionEscape` as named extractions and wires the
escape into the legacy bridge stack:

```
[S4 SemanticProjectionTransactionEscape]
        |
        +--> [sigma] sigma block is a SemanticMeasureData with WF strict relation
        +--> [phi]   pi factors through the identity seed collapse (every map does)
        +--> [wf]    the projected strict relation is well-founded
        +--> [+]     projected_orientation is a positive proof
        |
        +--> [legacy ProjectionTransactionEscape] via toLegacy
        |
        +--> [retainedCoordinate_factorsThrough_counter] factor-map-hypothesis form
        +--> [dpWitnessTransport_sound]                    via toLegacy
        +--> [BoundaryBottleneck.boundary_bottleneck]      via toLegacy
        +--> [search_budget_invariance]                    via toLegacy
```

The four extractions hold for every escape, the identity projection included
(`counterFirstLex_identityProjectionEscape` keeps the payload). They record the
shape of the record and exclude no projection. Payload forgetting is a property
of the canonical projection `Prod.fst` on `counterFirstLex_R`, stated by
`counterFirstLex_dpSemanticTransaction_forgets_payload` and
`counterFirstLex_pi_factors_seedCollapse`.

## Module contract

```
Relation:  source `RDRSStep B S N T` and projected `RDRSStep B S N T'`.
Closure:   root single-step (all transports are pointwise on steps; no
           transitive closure or SN is claimed).
Strategy:  N/A.
Trust:     kernel-only. No forbidden trust-surface tokens.
Scope:     the S4 semantic projection-transaction escape and its legacy
           bridges. Source-system SN is NOT in scope.
```

## Statements outside this module

- Source-system SN, source-system confluence, or full DP / MSPO /
  WPO / gWPO soundness.
- Payload forgetting of every escape; the identity projection is an escape
  that keeps the payload.
- An unconditional retained-coordinate factorisation through the counter;
  the theorem here takes static retained hypotheses and a factor map, and
  its type states both.

## Concrete witnesses

The DP-projection and argument-filtering audit rows of S6 use the
payload-forgetting projection of `counterFirstLex_R` on `T = Nat × Nat`:

```
pi (n, _) = n                       -- forget payload
Rproj    : RDRSStep Unit Nat Nat Nat
  lhs _ s n = n + 1
  rhs _ s n = n
projected order = Nat.lt           -- well-founded
seed-collapse  = forget payload    -- (carrier b = (b, 0); collapse (n, s) = n)
projected_orientation: Nat.lt_succ_self
```

This replaces the `trivialNatStep` placeholder previously used by the
S6 row evidence (in the placeholder, `pi = id` and the projection forgot
nothing).
-/

open OperatorKO7.RDRSDescentLens
open OperatorKO7.RDRSSeedCollapse
open OperatorKO7.RDRSProjectionTransaction
open OperatorKO7.RDRSRetainedCoordinate
open OperatorKO7.RDRSWitnessTransport
open OperatorKO7.RDRSBoundaryBottleneck
open OperatorKO7.RDRSSearchBudgetInvariance
open OperatorKO7.RDRSSemanticDirectMeasure
open OperatorKO7.RDRSSemanticPayloadSensitivity
open OperatorKO7.RDRSSemanticProjectionTransaction

/-! ## 1. Legacy bridge: semantic escape -> legacy projection-transaction escape

The bridge is placed in the original
`OperatorKO7.RDRSSemanticProjectionTransaction.SemanticProjectionTransactionEscape`
namespace so dot notation `E.toLegacy` resolves. The hardening theorems
below then call `E.toLegacy` directly.
-/

namespace OperatorKO7.RDRSSemanticProjectionTransaction.SemanticProjectionTransactionEscape

/--
Proves: every `SemanticProjectionTransactionEscape` translates to the
  legacy `ProjectionTransactionEscape` of `RDRSProjectionTransaction`,
  exposing the same pi and sigma data plus well-foundedness and projected
  orientation. The legacy seed-collapse block is filled by the identity
  seed collapse on the source type with factor map `pi`, which every map
  admits (`factorsThroughSeedCollapse_of_identity`). The translation
  supplies trivial counter data
  `(CounterIndex := semanticMeasure.A, counterFactor := id,
   retainedCoordinate := semanticMeasure.μ)` so that
  `mu'_factors_counter` reduces to `rfl`; canonicity of the retained
  coordinate as the recursion counter is a SEPARATE caller obligation
  expressed by `semantic_projection_escape_retained_factors_through_counter`.
Does not prove: that the trivial counter data is the canonical one, that
  `pi` forgets the payload, SN, or confluence.
Relation: source `R : RDRSStep B S N T` and projected `Rproj`.
Closure: root.
Strategy: not applicable.
Trust: kernel-only (record construction; `mu'_factors_counter` and the
  seed-collapse factorisation are `rfl`).
Scope: every `SemanticProjectionTransactionEscape R`.
-/
def toLegacy
    {B S N T : Type} {R : RDRSStep B S N T}
    (E : SemanticProjectionTransactionEscape R) :
    ProjectionTransactionEscape R :=
  let t : ProjectionTransaction R :=
    { T'                       := E.transaction.T'
      pi                       := E.transaction.pi
      Rproj                    := E.transaction.Rproj
      pi_commutes_lhs          := E.transaction.pi_commutes_lhs
      pi_commutes_rhs          := E.transaction.pi_commutes_rhs
      A'                       := E.transaction.semanticMeasure.A
      mu'                      := E.transaction.semanticMeasure.μ
      ltA'                     := E.transaction.semanticMeasure.ltA
      PayloadCarrier           := T
      seedCollapse             := SeedCollapse.id T
      pi_factors_seedCollapse  :=
        { factor := E.transaction.pi
          obs_eq := fun _ => rfl }
      CounterIndex             := E.transaction.semanticMeasure.A
      counterFactor            := fun a => a
      retainedCoordinate       := E.transaction.semanticMeasure.μ
      mu'_factors_counter      := fun _ => rfl }
  { transaction          := t
    projected_wellFounded := E.transaction.semanticMeasure.wf_ltA
    projected_orientation := E.projected_orientation }

end OperatorKO7.RDRSSemanticProjectionTransaction.SemanticProjectionTransactionEscape

namespace OperatorKO7.RDRSSemanticProjectionTransactionAudit

open OperatorKO7.RDRSDescentLens
open OperatorKO7.RDRSSeedCollapse
open OperatorKO7.RDRSProjectionTransaction
open OperatorKO7.RDRSRetainedCoordinate
open OperatorKO7.RDRSWitnessTransport
open OperatorKO7.RDRSBoundaryBottleneck
open OperatorKO7.RDRSSearchBudgetInvariance
open OperatorKO7.RDRSSemanticDirectMeasure
open OperatorKO7.RDRSSemanticPayloadSensitivity
open OperatorKO7.RDRSSemanticProjectionTransaction

/-! ## 2. The eight required S6.5 theorems -/

/--
Proves: the projection of every `SemanticProjectionTransactionEscape`
  factors through the identity seed collapse `SeedCollapse.id T`, with
  factor map `pi` itself. Exposed as a named `def` (a
  `FactorsThroughSeedCollapse` value is data, not a `Prop`) so the audit
  ledger can cite it. Statement change of 2026-10-13: the former type named
  the record's own `seedCollapse` field, which the record no longer carries.
Does not prove: that `pi` forgets the payload; the identity seed collapse
  forgets nothing, and every map factors through it.
Relation: not a rewriting theorem (factorisation of a function on
  terms).
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: every escape inhabitant.
-/
def semantic_projection_escape_factors_through_seed_collapse
    {B S N T : Type} {R : RDRSStep B S N T}
    (E : SemanticProjectionTransactionEscape R) :
    FactorsThroughSeedCollapse (SeedCollapse.id T) E.transaction.pi :=
  { factor := E.transaction.pi
    obs_eq := fun _ => rfl }

/--
Proves: **retained-coordinate factorisation (factor-map-hypothesis
  form; structural blocker `retained_coordinate_factor_map_required`
  on the unconditional version).** Under a static retained-hypothesis
  package `SH : StaticRetainedHypotheses R` and a caller-supplied
  factor map `factor : Nat -> semanticMeasure.A` exhibiting the lifted
  measure as a function of the recursion counter
  (`E.liftedMeasure t = factor (SH.counter t)`), the lifted measure
  factors through the recursion counter. The hypothesis is explicit
  in the theorem type. The unconditional
  version is mathematically false in general; the factor-map hypothesis
  is recorded at the retained-coordinate module's docstring.
Does not prove: an unconditional factorisation. The caller MUST supply
  the factor map; this module does not derive it from other data, and
  explicitly does not claim every projection escape's retained coordinate
  factors through the counter.
Relation: structural factorisation on the source side; not a rewriting
  theorem.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only (direct rewrite from the hypothesis equation).
Scope: every escape inhabitant with the supplied `(SH, factor, h)`
  hypothesis package.
-/
theorem semantic_projection_escape_retained_factors_through_counter
    {B S N T : Type} {R : RDRSStep B S N T}
    (E : SemanticProjectionTransactionEscape R)
    (SH : StaticRetainedHypotheses R)
    (factor : Nat → E.transaction.semanticMeasure.A)
    (h : ∀ t, E.liftedMeasure t = factor (SH.counter t)) :
    ∃ factorFromCounter : Nat → E.transaction.semanticMeasure.A,
      ∀ t, E.liftedMeasure t = factorFromCounter (SH.counter t) :=
  ⟨factor, h⟩

/--
Proves: every `SemanticProjectionTransactionEscape` carries the
  witness-transport content of DP-style escape: the lifted measure
  orients the source step in the projected (well-founded) strict
  relation. This is the `lifted_orients` content, recast through the
  legacy bridge so the `dpWitnessTransport_sound` theorem applies
  to a `DPProjectionEscape` built from the semantic escape.
Does not prove: source-system SN. `Orients` is single-step
  orientation transport, not an SN theorem; source SN belongs to
  the separate termination layer.
Relation: source `RDRSStep B S N T` at every `(b, s, n)`.
Closure: root single-step.
Strategy: not applicable.
Trust: kernel-only.
Scope: every escape inhabitant.
-/
theorem semantic_projection_escape_has_witness_transport
    {B S N T : Type} {R : RDRSStep B S N T}
    (E : SemanticProjectionTransactionEscape R) :
    Orients R E.liftedMeasure E.transaction.semanticMeasure.ltA :=
  E.lifted_orients

/-! ### Concrete payload-forgetting projection for `counterFirstLex_R` -/

/-- Seed-collapse on `Nat × Nat` that forgets the payload coordinate.
The diagonal lifts `n : Nat` to `(n, 0)`; the collapse forgets the
payload to recover the first coordinate. -/
def counterFirstLex_seedCollapse : SeedCollapse Nat (Nat × Nat) where
  carrier          := fun n => (n, 0)
  collapse         := fun p => p.fst
  collapse_carrier := fun _ => rfl

/-- Projected step on `Nat`: `lhs _ _ n = n + 1`, `rhs _ _ n = n`.
This is the counter-only projected step of `counterFirstLex_R`. -/
def counterFirstLex_Rproj : RDRSStep Unit Nat Nat Nat where
  lhs := fun _ _ n => n + 1
  rhs := fun _ _ n => n

/-- Projected semantic measure data on `Nat`: standard `<` order. -/
def counterFirstLex_semanticMeasure : SemanticMeasureData Nat where
  A      := Nat
  ltA    := fun a b => a < b
  wf_ltA := Nat.lt_wfRel.wf
  μ      := fun n => n

/-- Concrete `SemanticProjectionTransaction` on `counterFirstLex_R` with
projection `pi := Prod.fst`. Payload forgetting of this projection is
`counterFirstLex_dpSemanticTransaction_forgets_payload`; its factorisation
through the payload-forgetting seed collapse `counterFirstLex_seedCollapse`
is `counterFirstLex_pi_factors_seedCollapse`. -/
def counterFirstLex_dpSemanticTransaction :
    SemanticProjectionTransaction counterFirstLex_R where
  T'                       := Nat
  pi                       := fun p => p.fst
  Rproj                    := counterFirstLex_Rproj
  pi_commutes_lhs          := fun _ _ _ => rfl
  pi_commutes_rhs          := fun _ _ _ => rfl
  semanticMeasure          := counterFirstLex_semanticMeasure

/--
Proves: the projection `Prod.fst` of `counterFirstLex_dpSemanticTransaction`
  forgets the payload: two source terms with the same counter coordinate
  have the same projection.
Does not prove: payload forgetting for any other projection; the identity
  projection of `counterFirstLex_identityProjectionEscape` keeps the payload.
Relation: function on `Nat × Nat`; not a rewriting relation.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: the canonical `counterFirstLex_R` projection.
-/
theorem counterFirstLex_dpSemanticTransaction_forgets_payload (n p q : Nat) :
    counterFirstLex_dpSemanticTransaction.pi (n, p) =
      counterFirstLex_dpSemanticTransaction.pi (n, q) :=
  rfl

/--
Proves: the projection `Prod.fst` of `counterFirstLex_dpSemanticTransaction`
  factors through the payload-forgetting seed collapse
  `counterFirstLex_seedCollapse` (`collapse (n, s) = n`), with the identity
  on `Nat` as factor map.
Does not prove: anything about other projections or other steps.
Relation: factorisation of a function on terms; not a rewriting relation.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: the canonical `counterFirstLex_R` projection.
-/
theorem counterFirstLex_pi_factors_seedCollapse :
    Nonempty (FactorsThroughSeedCollapse counterFirstLex_seedCollapse
      counterFirstLex_dpSemanticTransaction.pi) :=
  ⟨{ factor := fun n => n
     obs_eq := fun _ => rfl }⟩

/-- Concrete `SemanticProjectionTransactionEscape` on `counterFirstLex_R`.
The projected orientation `n < n + 1` is discharged by
`Nat.lt_succ_self`. -/
def counterFirstLex_dpSemanticTransactionEscape :
    SemanticProjectionTransactionEscape counterFirstLex_R where
  transaction           := counterFirstLex_dpSemanticTransaction
  projected_orientation := fun _ _ n => Nat.lt_succ_self n

/-- DP-style packaging of the concrete escape: wraps it in
`DPProjectionEscape` via the legacy bridge. The DP-semantic side-
condition is the structural slot left at `True`, recording single-step
honesty only. -/
def counterFirstLex_dpProjectionEscape :
    DPProjectionEscape counterFirstLex_R :=
  DPProjectionEscape.ofProjectionTransactionEscape
    counterFirstLex_dpSemanticTransactionEscape.toLegacy

/--
Proves: **canonical DP projection transaction.** The concrete
  payload-forgetting projection of `counterFirstLex_R` inhabits the
  canonical chain
  `SemanticProjectionTransactionEscape -> ProjectionTransactionEscape
  -> DPProjectionEscape` and orients the source step under the
  well-founded projected order via the witness-transport content. The
  projection forgets the payload coordinate; `pi` is `Prod.fst`, not the
  identity.
Does not prove: that arbitrary DP projections fit this pattern; only
  the canonical `counterFirstLex_R` example does so via this module's
  concrete construction.
Relation: source `counterFirstLex_R : RDRSStep Unit Nat Nat (Nat × Nat)`.
Closure: root single-step orientation.
Strategy: not applicable.
Trust: kernel-only.
Scope: the named concrete instance only.
-/
theorem semantic_dp_projection_transaction_canonical :
    ∃ (E : SemanticProjectionTransactionEscape counterFirstLex_R)
      (D : DPProjectionEscape counterFirstLex_R),
      Orients counterFirstLex_R
        E.liftedMeasure E.transaction.semanticMeasure.ltA ∧
        Orients counterFirstLex_R
          D.toProjectionTransactionEscape.liftedMeasure
          D.toProjectionTransactionEscape.transaction.ltA' :=
  ⟨counterFirstLex_dpSemanticTransactionEscape,
    counterFirstLex_dpProjectionEscape,
    counterFirstLex_dpSemanticTransactionEscape.lifted_orients,
    dpWitnessTransport_sound counterFirstLex_dpProjectionEscape⟩

/-! ### Control: an escape whose projection keeps the payload -/

/--
Proves: an escape on `counterFirstLex_R` whose projection is the identity:
  `Rproj := counterFirstLex_R`, measure `counterFirstLex_M` (first
  coordinate, well-founded), projected orientation `n < n + 1`.
Does not prove: payload forgetting;
  `counterFirstLex_identityProjection_keeps_payload` shows that this
  projection keeps the payload.
Relation: `counterFirstLex_R : RDRSStep Unit Nat Nat (Nat × Nat)`.
Closure: root single-step.
Strategy: not applicable.
Trust: kernel-only.
Scope: the named concrete instance only.
-/
def counterFirstLex_identityProjectionEscape :
    SemanticProjectionTransactionEscape counterFirstLex_R where
  transaction :=
    { T'              := Nat × Nat
      pi              := fun p => p
      Rproj           := counterFirstLex_R
      pi_commutes_lhs := fun _ _ _ => rfl
      pi_commutes_rhs := fun _ _ _ => rfl
      semanticMeasure := counterFirstLex_M }
  projected_orientation := fun _ _ n => Nat.lt_succ_self n

/--
Proves: the identity projection of `counterFirstLex_identityProjectionEscape`
  keeps the payload: the sources `(1, 0)` and `(1, 1)` of the step at counter
  `0` and payloads `0` and `1` have different projections. The escape record
  therefore admits projections that forget no payload.
Does not prove: that payload-keeping projections fail to orient; this one
  orients through the first coordinate.
Relation: `counterFirstLex_R : RDRSStep Unit Nat Nat (Nat × Nat)`.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: the named concrete instance only.
-/
theorem counterFirstLex_identityProjection_keeps_payload :
    counterFirstLex_identityProjectionEscape.transaction.pi
        (counterFirstLex_R.lhs () 0 0) ≠
      counterFirstLex_identityProjectionEscape.transaction.pi
        (counterFirstLex_R.lhs () 1 0) := by
  intro h
  have h2 : (0 : Nat) = 1 := congrArg Prod.snd h
  exact absurd h2 (by decide)

/--
Proves: every `SemanticProjectionTransactionEscape R` yields four
  extractions: (1) a non-empty projected semantic-measure record (sigma),
  (2) a seed collapse on the source type through which `pi` factors (the
  identity seed collapse serves for every map), (3) a well-founded
  projected strict relation, and (4) a positive projected-orientation
  proof. Renamed on 2026-10-13 from
  `semantic_projection_escape_not_plain_erasure`; the type is unchanged.
Does not prove: that any projection fails to inhabit the escape. The
  identity projection with an orienting measure inhabits it
  (`counterFirstLex_identityProjection_keeps_payload`), and conjunct (2)
  holds for every map.
Relation: record extraction.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only (record projection).
Scope: every escape inhabitant.
-/
theorem semantic_projection_escape_extracts_sigma_seedCollapse_wf_orientation
    {B S N T : Type} {R : RDRSStep B S N T}
    (E : SemanticProjectionTransactionEscape R) :
    Nonempty (SemanticMeasureData E.transaction.T') ∧
    (∃ (PayloadCarrier : Type) (sc : SeedCollapse PayloadCarrier T),
        Nonempty (FactorsThroughSeedCollapse sc E.transaction.pi)) ∧
    WellFounded E.transaction.semanticMeasure.ltA ∧
    Orients E.transaction.Rproj
        E.transaction.semanticMeasure.μ
        E.transaction.semanticMeasure.ltA :=
  ⟨semantic_projection_escape_requires_sigma E,
    semantic_projection_escape_requires_seed_collapse E,
    semantic_projection_escape_requires_wellFounded E,
    semantic_projection_escape_requires_projected_orientation E⟩

/--
Proves: **hardened soundness of the semantic projection-transaction
  escape.** Bundles into one theorem (1) the four extractions of
  `semantic_projection_escape_extracts_sigma_seedCollapse_wf_orientation`
  and (2) the witness-transport content (`Orients R liftedMeasure ltA'`).
  This is the public capstone the S5 classifier's projection-escape
  soundness branch cites.
Does not prove: source-system SN, confluence, payload forgetting, or
  unconditional retained-coordinate factorisation through the counter.
  The retained-coordinate factorisation is the SEPARATE conditional
  theorem `semantic_projection_escape_retained_factors_through_counter`.
Relation: source `RDRSStep B S N T` at every `(b, s, n)`.
Closure: root single-step.
Strategy: not applicable.
Trust: kernel-only.
Scope: every escape inhabitant.
-/
theorem semantic_projection_transaction_escape_sound_hardened
    {B S N T : Type} {R : RDRSStep B S N T}
    (E : SemanticProjectionTransactionEscape R) :
    (Nonempty (SemanticMeasureData E.transaction.T') ∧
      (∃ (PayloadCarrier : Type) (sc : SeedCollapse PayloadCarrier T),
          Nonempty (FactorsThroughSeedCollapse sc E.transaction.pi)) ∧
      WellFounded E.transaction.semanticMeasure.ltA ∧
      Orients E.transaction.Rproj
          E.transaction.semanticMeasure.μ
          E.transaction.semanticMeasure.ltA)
    ∧ Orients R E.liftedMeasure E.transaction.semanticMeasure.ltA :=
  ⟨semantic_projection_escape_extracts_sigma_seedCollapse_wf_orientation E,
    semantic_projection_escape_has_witness_transport E⟩

/--
Proves: **semantic boundary-bottleneck split (W0 blocked, W2
  succeeds).** Given a semantic projection-transaction escape, the
  boundary bottleneck built from it (a `BoundaryBottleneck R` over
  the legacy bridge `E.toLegacy`) classifies a W0 witness as
  boundary-non-admissible and a W2 witness (the escape itself) as
  boundary-admissible. This is the bottleneck theorem lifted to
  the semantic surface; the layer divide is unchanged.
Does not prove: that the W0 layer is empty for the supplied `R`; it
  uses the canonical `abstain` certificate as a structural W0 tag.
  Does not prove SN or any rewriting-system property.
Relation: layered-witness tag (no rewriting relation at this layer).
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: every escape inhabitant.
-/
theorem semantic_boundary_bottleneck_w0_blocked_w2_succeeds
    {B S N T : Type} {R : RDRSStep B S N T}
    (E : SemanticProjectionTransactionEscape R) :
    let BB := BoundaryBottleneck.ofProjectionTransactionEscape E.toLegacy
    kappa_boundary BB.w0_witness = false ∧
      kappa_boundary BB.w2_witness = true :=
  boundary_bottleneck
    (BoundaryBottleneck.ofProjectionTransactionEscape E.toLegacy)

/--
Proves: **semantic search-budget invariance.** Combined with a
  semantic projection-transaction escape, the verdict split is
  uniform across budgets: any W0-bounded search procedure produces
  boundary-non-admissible witnesses at every budget (`κ_boundary =
  false`), while the W2 witness exhibited by the semantic escape
  remains boundary-admissible (`κ_boundary = true`). Increasing the
  search budget inside W0 cannot cross the boundary.
Does not prove: that the search procedure terminates; the budget
  parameter is the unspecified resource bound from `W0Search`. Does
  not prove SN.
Relation: search-budget tag (no rewriting relation).
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: every escape inhabitant plus any W0-bounded search.
-/
theorem semantic_search_budget_invariance
    {B S N T : Type} {R : RDRSStep B S N T}
    (E : SemanticProjectionTransactionEscape R)
    (search : W0Search R) (h : IsW0Bounded search) (budget : Nat) :
    kappa_boundary (search budget) = false ∧
      kappa_boundary
        (BoundaryBottleneck.ofProjectionTransactionEscape E.toLegacy).w2_witness
        = true :=
  W0_budget_invariance_does_not_block_W2 search h
    (BoundaryBottleneck.ofProjectionTransactionEscape E.toLegacy) budget

/-! ## 3. Audit anchor -/

/-- Audit anchor for the S6.5 projection-transaction hardening surface. -/
def rdrs_semantic_projection_transaction_audit_anchor : String :=
  "OperatorKO7.RDRSSemanticProjectionTransactionAudit.semantic_projection_transaction_escape_sound_hardened"

end OperatorKO7.RDRSSemanticProjectionTransactionAudit
