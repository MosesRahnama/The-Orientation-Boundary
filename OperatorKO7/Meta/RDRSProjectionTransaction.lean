import OperatorKO7.Meta.RDRSDescentLens
import OperatorKO7.Meta.RDRSSeedCollapse
import OperatorKO7.Meta.RDRSProjectionSyntax

set_option autoImplicit false

/-!
# RDRS Projection Transaction (Milestone U1, Sprint U1.5)

Roadmap source: `OperatorKO7/Expansion/Universal_Payload_Sensitive_Direct_Measures_Roadmap.md`
Milestone U1, file `Meta/RDRSProjectionTransaction.lean`.

The roadmap supersedes the plain payload-forgetting erasure surface of
`Meta/RDRSProjectionSyntax.lean` with the more demanding *static
projection transaction* surface `(pi, sigma, phi)`. The transaction is
the licensed-projection form a successful payload-sensitive direct
escape must take.

## Audit slots (Lean Development Bible W8 / R4)

```
Relation:  RDRSStep B S N T  (source) and RDRSStep B S N T' (projected).
Closure:   root (single-step orientation transport; no contextual
           closure or transitive closure is claimed at this layer).
Strategy:  N/A (no rewriting strategy is fixed; the transaction
           witnesses an orientation that lifts pointwise on steps).
Trust:     kernel-only. No `sorry`, `admit`, `axiom`, `opaque`,
           `unsafe`, `native_decide`, `bv_decide`, `csimp`, `extern`,
           `implemented_by`, or `addDeclWithoutChecking`.
Scope:     static projection transactions only. No DP processor, MSPO,
           full WPO/gWPO, or arbitrary semantic quotient is in scope.
           The compatibility bridge from the legacy `ProjectionEscape`
           is conditional on caller-supplied seed-collapse and counter
           data.
```

## Naming map

```
pi      = retained verdict-bearing coordinate
            (the payload-forgetting projection on terms together with
             the projected step)
sigma   = external soundness license / witness transport
            (the projected measure, the strict projected relation, and
             the commutation equations that transport descent back)
phi     = forgotten payload-multiplicity dimension
            (the seed-collapse data on the source type plus the
             factorization of pi through it)
```

Plus the roadmap's additional obligations:

* counter-factorisation: the projected measure factors through a
  retained counter coordinate;
* positive transaction-success proof: the projected measure strictly
  orients the projected step under a well-founded projected relation.

The split into two structures is deliberate. `ProjectionTransaction`
carries the three core pieces and the counter-factorisation obligation;
`ProjectionTransactionEscape` adds the positive-success proof. A
`ProjectionTransactionEscape` cannot inhabit the type without the
positive-success proof; bare erasure is therefore not enough.

The old `ProjectionEscape` from `RDRSProjectionSyntax.lean` is **not**
the final classifier surface. It remains available as a lower-level
building block. The compatibility bridge `ofProjectionEscape` produces
a `ProjectionTransactionEscape` only when the supplier discharges the
seed-collapse (phi) and counter-factorisation obligations that bare
erasure does not provide.

## Non-vacuity status

* `ProjectionTransaction R` is inhabited under `[Inhabited T]` (the
  diagonal `carrier` requires a `T`-value). This only witnesses the
  transaction data shape.
* `ProjectionTransactionEscape R` is not claimed non-empty for an
  arbitrary source step. It additionally requires a well-founded
  projected relation plus a projected-orientation proof.

## Scope discipline

* No `sorry`, `admit`, `axiom`, or production `example :`.
* No arbitrary-quotient surface: the phi obligation is discharged via a
  `SeedCollapse` factor, not an opaque quotient.
* No U2 imports: this module does not reference the raw direct-measure
  syntax of `Meta/RDRSRawDirectMeasure.lean` or the normalized method
  certificate of `Meta/RDRSMethodCertificate.lean`.
-/

namespace OperatorKO7.RDRSProjectionTransaction

open OperatorKO7.RDRSDescentLens
open OperatorKO7.RDRSSeedCollapse

/-- A static RDRS projection transaction on a step `R : RDRSStep B S N T`.

Fields are grouped by the `(pi, sigma, phi)` triple of the roadmap.

* `pi` block: `T'`, `pi`, `Rproj`, `pi_commutes_lhs`, `pi_commutes_rhs`.
* `sigma` block: `A'`, `mu'`, `ltA'`.
* `phi` block: `PayloadCarrier`, `seedCollapse`, `pi_factors_seedCollapse`.
* counter-factorisation block: `CounterIndex`, `counterFactor`,
  `retainedCoordinate`, `mu'_factors_counter`.

Note: this structure does *not* carry the positive transaction-success
proof. That is added by `ProjectionTransactionEscape` below.

**Audit slots.**

* **Proves:** existence of the `(pi, sigma, phi)` data with commutation
  and counter-factorisation equations.
* **Does not prove:** that the projected relation is well-founded or
  that the projected measure strictly orients the projected step (that
  is `ProjectionTransactionEscape`); does not prove source-system SN,
  confluence, or normalization.
* **Relation:** source `R : RDRSStep B S N T` and projected `Rproj`.
* **Closure:** root (pointwise on steps).
* **Strategy:** N/A.
* **Trust:** kernel-only.
* **Scope:** static; no DP processor, MSPO, WPO/gWPO, or arbitrary
  semantic quotient. -/
structure ProjectionTransaction
    {B S N T : Type} (R : RDRSStep B S N T) where
  -- pi block: retained verdict-bearing coordinate
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
  -- sigma block: external soundness license / witness transport
  /-- Projected measure codomain. -/
  A'              : Type
  /-- `sigma`: projected measure on the erased term type. -/
  mu'             : T' → A'
  /-- `sigma`: strict relation on the projected measure codomain. -/
  ltA'            : A' → A' → Prop
  -- phi block: forgotten payload-multiplicity dimension
  /-- Abstract payload-carrier type underlying the seed-collapse on `T`. -/
  PayloadCarrier  : Type
  /-- `phi`: seed-collapse data on the source term type. -/
  seedCollapse    : SeedCollapse PayloadCarrier T
  /-- Forgetting witness: `pi` factors through the seed-collapse. -/
  pi_factors_seedCollapse :
    FactorsThroughSeedCollapse seedCollapse pi
  -- counter-factorisation block
  /-- A retained "counter" index type. -/
  CounterIndex       : Type
  /-- Counter-only factor of the projected measure. -/
  counterFactor      : CounterIndex → A'
  /-- The retained coordinate the projected measure reads from. -/
  retainedCoordinate : T' → CounterIndex
  /-- Counter-factorisation equation: `mu'` depends only on the retained
  counter coordinate. -/
  mu'_factors_counter :
    ∀ t', mu' t' = counterFactor (retainedCoordinate t')

/-- Positive success certificate for a static RDRS projection transaction.

Extends a `ProjectionTransaction` with a proof that the projected
relation is well-founded and that the projected measure strictly
orients the projected step. Without both fields, no
`ProjectionTransactionEscape` inhabits the type.

**Audit slots.**

* **Proves:** existence of `(pi, sigma, phi)` data PLUS a
  well-founded projected relation and an orientation
  `Orients Rproj mu' ltA'` on the projected side.
* **Does not prove:** source-system SN, source-system confluence, or
  unconditional liftability to any other classifier. The
  source-orientation transport theorem `lifted_orients` below makes
  the precise structural claim that `mu' ∘ pi` orients the source
  step in `ltA'`; that is single-step orientation, not strong
  normalisation.
* **Relation:** source `R` and projected `Rproj`.
* **Closure:** root (lifted_orients is single-step / pointwise).
* **Strategy:** N/A.
* **Trust:** kernel-only.
* **Scope:** static. -/
structure ProjectionTransactionEscape
    {B S N T : Type} (R : RDRSStep B S N T) where
  /-- The underlying static projection transaction `(pi, sigma, phi)`
  with its counter-factorisation obligation. -/
  transaction          : ProjectionTransaction R
  /-- **Positive transaction-success proof.** The projected measure
  strictly orients the projected step. -/
  projected_wellFounded :
    WellFounded transaction.ltA'
  /-- **Positive transaction-success proof.** The projected measure
  strictly orients the projected step under the well-founded projected
  relation. -/
  projected_orientation :
    Orients transaction.Rproj transaction.mu' transaction.ltA'

namespace ProjectionTransactionEscape

variable {B S N T : Type} {R : RDRSStep B S N T}

/-- Decisive descent measure on the original term type: factor the
projected measure through `pi`. -/
def liftedMeasure (P : ProjectionTransactionEscape R) :
    T → P.transaction.A' :=
  fun t => P.transaction.mu' (P.transaction.pi t)

/-- **Factorisation theorem.** The lifted measure orients the original
RDRS step in the projected strict relation. The original-side descent
is exactly the projected-side descent transported back through `pi`.

**Audit slots.**

* **Proves:** `Orients R (mu' ∘ pi) ltA'`, i.e. pointwise on every
  step `(b, s, n)` the rhs measure is strictly less than the lhs
  measure under `ltA'`.
* **Does not prove:** that `R` is strongly normalising. `Orients` is a
  single-step orientation predicate, not an SN theorem; reflexive-transitive
  or contextual closure belongs to the separate SN layer.
* **Relation:** `RDRSStep B S N T`.
* **Closure:** root.
* **Strategy:** N/A.
* **Trust:** kernel-only (`rw` of two commutation equations).
* **Scope:** depends on the supplied PTE record. -/
theorem lifted_orients (P : ProjectionTransactionEscape R) :
    Orients R P.liftedMeasure P.transaction.ltA' := by
  intro b s n
  show P.transaction.ltA'
        (P.transaction.mu' (P.transaction.pi (R.rhs b s n)))
        (P.transaction.mu' (P.transaction.pi (R.lhs b s n)))
  rw [P.transaction.pi_commutes_lhs, P.transaction.pi_commutes_rhs]
  exact P.projected_orientation b s n

/-- **Positive-evidence witness.** Every `ProjectionTransactionEscape`
exhibits projected-orientation evidence. The structure cannot inhabit
the type without it; this is the structural content of the
"positive success certificate" discipline.

**Audit slots.**

* **Proves:** existence of the data
  `(T', A', Rproj, mu', ltA')` together with
  `WellFounded ltA'` and `Orients Rproj mu' ltA'`.
* **Does not prove:** that arbitrary erasure surfaces yield such
  evidence; bare erasure is rejected.
* **Trust:** kernel-only. -/
theorem requires_positive_evidence (P : ProjectionTransactionEscape R) :
    ∃ (T' A' : Type) (Rproj : RDRSStep B S N T')
      (mu' : T' → A') (ltA' : A' → A' → Prop),
      WellFounded ltA' ∧ Orients Rproj mu' ltA' :=
  ⟨P.transaction.T', P.transaction.A', P.transaction.Rproj,
   P.transaction.mu', P.transaction.ltA',
   P.projected_wellFounded, P.projected_orientation⟩

end ProjectionTransactionEscape

/-! ### Non-vacuity witnesses (Lean Development Bible R5 / S09)

The data-only structure `ProjectionTransaction R` is conditionally
inhabited under `[Inhabited T]`. The escape structure is stricter: a
caller must supply a well-founded projected relation and projected
orientation. This file deliberately avoids a generic
`ProjectionTransactionEscape R` non-vacuity lemma, because such a lemma
would turn the escape branch into a vacuous catch-all. -/

/-- Trivial projection transaction under `[Inhabited T]`. Uses the
unit-target projection and the unit payload-carrier diagonal. It is a
data-shape witness only, not an escape. -/
def ProjectionTransaction.trivial
    {B S N T : Type} [Inhabited T] (R : RDRSStep B S N T) :
    ProjectionTransaction R where
  T'                       := Unit
  pi                       := fun _ => ()
  Rproj                    :=
    { lhs := fun _ _ _ => (), rhs := fun _ _ _ => () }
  pi_commutes_lhs          := fun _ _ _ => rfl
  pi_commutes_rhs          := fun _ _ _ => rfl
  A'                       := Unit
  mu'                      := fun _ => ()
  ltA'                     := fun _ _ => False
  PayloadCarrier           := Unit
  seedCollapse             :=
    { carrier          := fun _ => (default : T)
      collapse         := fun _ => ()
      collapse_carrier := fun _ => rfl }
  pi_factors_seedCollapse  :=
    { factor := fun _ => ()
      obs_eq := fun _ => rfl }
  CounterIndex             := Unit
  counterFactor            := fun _ => ()
  retainedCoordinate       := fun _ => ()
  mu'_factors_counter      := fun _ => rfl

/-- **Non-vacuity (conditional on `[Inhabited T]`):**
`ProjectionTransaction R` is non-empty. -/
theorem ProjectionTransaction_nonempty_of_inhabited
    {B S N T : Type} [Inhabited T] (R : RDRSStep B S N T) :
    Nonempty (ProjectionTransaction R) :=
  ⟨ProjectionTransaction.trivial R⟩

/-! ### Compatibility bridge from the legacy `ProjectionEscape` -/

/-- Compatibility bridge from the legacy `ProjectionEscape` of
`Meta/RDRSProjectionSyntax.lean` to the projection-transaction surface.

The bridge is conditional. The legacy `ProjectionEscape` carries only
the erasure syntax (a `PayloadForgetErasure`) and a projected-orientation
proof. To lift it to a `ProjectionTransactionEscape`, the caller must
**also** supply:

* a payload-carrier type and a `SeedCollapse` on the source term type
  (the `phi` obligation), together with a `FactorsThroughSeedCollapse`
  witness for the erasure;
* a counter-index type, a counter factor `cFac : CounterIndex -> A'`,
  a retained-coordinate map `retained : T' -> CounterIndex`, and the
  counter-factorisation equation `mu' t' = cFac (retained t')`;
* a well-foundedness proof for the projected strict relation.

Bare erasure plus orientation no longer suffices. This is the precise
sense in which the plain projection syntax is "lower-level": one must
supply the additional roadmap obligations to be promoted to the final
classifier surface.

**Audit slots.**

* **Proves:** a function from `ProjectionEscape R` + the extra phi /
  counter data to `ProjectionTransactionEscape R`.
* **Does not prove:** that every legacy `ProjectionEscape` admits such
  a lift; the lift requires the caller to supply the seed-collapse
  and counter data.
* **Trust:** kernel-only. -/
def ofProjectionEscape
    {B S N T : Type} {R : RDRSStep B S N T}
    (P : OperatorKO7.RDRSProjectionSyntax.ProjectionEscape R)
    (PayloadCarrier : Type)
    (seedCollapse : SeedCollapse PayloadCarrier T)
    (piFactors :
      FactorsThroughSeedCollapse seedCollapse P.E.erase)
    (CounterIndex : Type)
    (counterFactor : CounterIndex → P.A')
    (retainedCoordinate : P.T' → CounterIndex)
    (mu'_factors_counter :
      ∀ t', P.mu' t' = counterFactor (retainedCoordinate t'))
    (projected_wellFounded : WellFounded P.ltA') :
    ProjectionTransactionEscape R :=
  let t : ProjectionTransaction R :=
    { T'                       := P.T'
      pi                       := P.E.erase
      Rproj                    := P.E.Rproj
      pi_commutes_lhs          := P.E.erase_commutes_lhs
      pi_commutes_rhs          := P.E.erase_commutes_rhs
      A'                       := P.A'
      mu'                      := P.mu'
      ltA'                     := P.ltA'
      PayloadCarrier           := PayloadCarrier
      seedCollapse             := seedCollapse
      pi_factors_seedCollapse  := piFactors
      CounterIndex             := CounterIndex
      counterFactor            := counterFactor
      retainedCoordinate       := retainedCoordinate
      mu'_factors_counter      := mu'_factors_counter }
  { transaction          := t
    projected_wellFounded := projected_wellFounded
    projected_orientation := P.projected_orientation }

/-- Audit anchor for the U1 projection-transaction surface. Downstream
registries cite this String when wiring the projection branch of the
final classifier; it supersedes the plain
`OperatorKO7.RDRSProjectionSyntax.ProjectionEscape.requires_positive_evidence`
anchor as the canonical classifier surface. -/
def rdrs_projection_transaction_positive_evidence_anchor : String :=
  "OperatorKO7.RDRSProjectionTransaction.ProjectionTransactionEscape.requires_positive_evidence"

end OperatorKO7.RDRSProjectionTransaction
