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
# RDRS Semantic Projection-Transaction Hardening Audit (Milestone S6.5)

Roadmap source:
`OperatorKO7/Expansion/Universal_Payload_Sensitive_Direct_Measures_Roadmap.md`
Milestone S6.5 -- Projection-Transaction Hardening.

This module hardens the S4 `SemanticProjectionTransactionEscape` surface
against the "bare erasure plus orientation" failure mode by wiring the
escape into the bridge stack:

```
[S4 SemanticProjectionTransactionEscape]
        |
        +--> [phi]  pi factors through a SeedCollapse  (S4 field)
        +--> [sigma] sigma block is a SemanticMeasureData with WF strict relation
        +--> [pi]   pi commutes with the step (S4 fields)
        +--> [+]    projected_orientation is a positive proof
        |
        +--> [legacy U1.5 ProjectionTransactionEscape] via toLegacy
        |
        +--> [U3 retainedCoordinate_factorsThrough_counter] factor-map-hypothesis form
                                                              (structural blocker:
                                                               retained_coordinate_factor_map_required)
        +--> [U3 dpWitnessTransport_sound]                    via toLegacy
        +--> [U5 BoundaryBottleneck.boundary_bottleneck]      via toLegacy
        +--> [U5 search_budget_invariance]                    via toLegacy
        |
        v
[licensed projection transaction; no plain erasure inhabitant]
```

## Audit slots (Lean Development Bible W8 / R4)

```
Relation:  source `RDRSStep B S N T` and projected `RDRSStep B S N T'`.
Closure:   root single-step (all transports are pointwise on steps; no
           transitive closure or SN is claimed).
Strategy:  N/A.
Trust:     kernel-only. No forbidden trust-surface tokens.
Scope:     hardens the S4 semantic projection-transaction escape against
           the bare-erasure failure mode. Source-system SN is NOT in
           scope (K-check 7 of the bible).
```

## What this module does NOT prove

- Source-system SN, source-system confluence, or full DP / MSPO /
  WPO / gWPO soundness.
- That arbitrary projection-style witnesses inhabit the escape branch;
  the escape branch is structurally gated on all four obligations.
- That the retained-coordinate factorisation through the counter is
  unconditional; it remains conditional on caller-supplied static
  retained hypotheses + a factor map, both of which are explicit in
  the theorem type per the S6.5 roadmap.

## Concrete witnesses

The DP-projection and argument-filtering audit rows of S6 use the
genuine payload-forgetting projection of `counterFirstLex_R` on
`T = Nat × Nat`:

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
S6 row evidence (in which `pi = id` and the projection did not actually
forget anything).
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
  exposing the same `pi / sigma / phi` data plus well-foundedness and
  projected orientation. The translation supplies trivial counter data
  `(CounterIndex := semanticMeasure.A, counterFactor := id,
   retainedCoordinate := semanticMeasure.μ)` so that
  `mu'_factors_counter` reduces to `rfl`; canonicity of the retained
  coordinate as the recursion counter is a SEPARATE caller obligation
  expressed by `semantic_projection_escape_retained_factors_through_counter`.
Does not prove: that the trivial counter data is the canonical one;
  does not prove SN or confluence.
Relation: source `R : RDRSStep B S N T` and projected `Rproj`.
Closure: root.
Strategy: not applicable.
Trust: kernel-only (record construction; `mu'_factors_counter` is `rfl`).
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
      PayloadCarrier           := E.transaction.PayloadCarrier
      seedCollapse             := E.transaction.seedCollapse
      pi_factors_seedCollapse  := E.transaction.pi_factors_seedCollapse
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
Proves: every `SemanticProjectionTransactionEscape` carries an explicit
  `FactorsThroughSeedCollapse` witness for `pi` through the supplied
  seed-collapse `seedCollapse`. This is the `phi` obligation, exposed
  as a named extraction (a `def`, since `FactorsThroughSeedCollapse`
  is data, not a `Prop`), so the audit ledger can cite it directly.
Does not prove: that `pi` is uniquely determined by the factor map on
  values outside the image of `seedCollapse.carrier`; only the
  pointwise factorisation equation.
Relation: not a rewriting theorem (factorisation of a function on
  terms).
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only (field accessor).
Scope: every escape inhabitant.
-/
def semantic_projection_escape_factors_through_seed_collapse
    {B S N T : Type} {R : RDRSStep B S N T}
    (E : SemanticProjectionTransactionEscape R) :
    FactorsThroughSeedCollapse
      E.transaction.seedCollapse E.transaction.pi :=
  E.transaction.pi_factors_seedCollapse

/--
Proves: **retained-coordinate factorisation (factor-map-hypothesis
  form; structural blocker `retained_coordinate_factor_map_required`
  on the unconditional version).** Under a static retained-hypothesis
  package `SH : StaticRetainedHypotheses R` and a caller-supplied
  factor map `factor : Nat -> semanticMeasure.A` exhibiting the lifted
  measure as a function of the recursion counter
  (`E.liftedMeasure t = factor (SH.counter t)`), the lifted measure
  factors through the recursion counter. The hypothesis is explicit
  in the theorem type per the S6.5 roadmap rule. The unconditional
  version is mathematically false in general; the structural blocker
  is recorded at the U3 retained-coordinate module's docstring.
Does not prove: an unconditional factorisation. The caller MUST supply
  the factor map; this module does not derive it from the seed-collapse
  data alone, and explicitly does not claim every projection escape's
  retained coordinate factors through the counter.
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
  legacy bridge so the U3 `dpWitnessTransport_sound` theorem applies
  to a `DPProjectionEscape` built from the semantic escape.
Does not prove: source-system SN. `Orients` is single-step
  orientation transport, not an SN theorem; per K-check 7 of the
  bible, source SN belongs to the separate termination layer.
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

/-- Concrete payload-forgetting `SemanticProjectionTransaction` on
`counterFirstLex_R`. The projection `pi := Prod.fst` forgets the
payload coordinate; the seed-collapse factorisation is honest
(factor map is the identity on `Nat`). -/
def counterFirstLex_dpSemanticTransaction :
    SemanticProjectionTransaction counterFirstLex_R where
  T'                       := Nat
  pi                       := fun p => p.fst
  Rproj                    := counterFirstLex_Rproj
  pi_commutes_lhs          := fun _ _ _ => rfl
  pi_commutes_rhs          := fun _ _ _ => rfl
  semanticMeasure          := counterFirstLex_semanticMeasure
  PayloadCarrier           := Nat
  seedCollapse             := counterFirstLex_seedCollapse
  pi_factors_seedCollapse  :=
    { factor := fun n => n
      obs_eq := fun _ => rfl }

/-- Concrete `SemanticProjectionTransactionEscape` on `counterFirstLex_R`.
The projected orientation `n < n + 1` is discharged by
`Nat.lt_succ_self`. -/
def counterFirstLex_dpSemanticTransactionEscape :
    SemanticProjectionTransactionEscape counterFirstLex_R where
  transaction           := counterFirstLex_dpSemanticTransaction
  projected_orientation := fun _ _ n => Nat.lt_succ_self n

/-- DP-style packaging of the concrete escape: wraps it in
`DPProjectionEscape` via the legacy bridge. The DP-semantic side-
condition is the structural slot left at `True` per the bible's
K-check 7 honesty discipline. -/
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
  projection genuinely forgets the payload coordinate; `pi` is
  `Prod.fst`, not the identity.
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

/--
Proves: **escape is not plain erasure.** Every
  `SemanticProjectionTransactionEscape R` exposes ALL four
  obligations: (1) a non-empty projected semantic-measure record
  (sigma), (2) a seed-collapse on the source type plus a factorisation
  of `pi` (phi), (3) a well-founded projected strict relation (wf),
  and (4) a positive projected-orientation proof. Removing any of the
  four extraction theorems strictly weakens the conclusion; bare
  erasure cannot inhabit the escape branch.

  This is the structural sense in which "no S6.5 close is allowed if
  a projection escape can be inhabited by erasure syntax alone": each
  of the four extraction theorems is independently witnessed on every
  inhabitant.
Does not prove: that arbitrary erasure syntax does NOT inhabit the
  escape; the structural argument is that Lean's record type-checking
  forbids inhabitation without all four fields, recorded here as
  separate named extractions.
Relation: record extraction.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only (record projection).
Scope: every escape inhabitant.
-/
theorem semantic_projection_escape_not_plain_erasure
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
  escape.** Bundles into one theorem (1) the four-obligation
  extraction shape (sigma + phi + wf + projected orientation) and
  (2) the witness-transport content (`Orients R liftedMeasure ltA'`).
  This is the public capstone the S5 classifier's projection-escape
  soundness branch cites; it strictly extends the S5 theorem with
  the explicit four-obligation shape.
Does not prove: source-system SN, confluence, or unconditional
  retained-coordinate factorisation through the counter. The
  retained-coordinate factorisation is the SEPARATE conditional
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
  ⟨semantic_projection_escape_not_plain_erasure E,
    semantic_projection_escape_has_witness_transport E⟩

/--
Proves: **semantic boundary-bottleneck split (W0 blocked, W2
  succeeds).** Given a semantic projection-transaction escape, the
  boundary bottleneck built from it (a `BoundaryBottleneck R` over
  the legacy bridge `E.toLegacy`) classifies a W0 witness as
  boundary-non-admissible and a W2 witness (the escape itself) as
  boundary-admissible. This is the U5 bottleneck theorem lifted to
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
