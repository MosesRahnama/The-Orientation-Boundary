import OperatorKO7.Meta.RDRSDescentLens
import OperatorKO7.Meta.RDRSProjectionTransaction

set_option autoImplicit false

/-!
# RDRS DP Witness Transport (Milestone U3)

Roadmap source: `OperatorKO7/Expansion/Universal_Payload_Sensitive_Direct_Measures_Roadmap.md`
Milestone U3 -- DP projection / projection-transaction reconciliation.

## Audit slots (Lean Development Bible W8 / R4)

```
Relation:  RDRSStep B S N T (source).
Closure:   root (witness transport is single-step).
Strategy:  N/A.
Trust:     kernel-only.
Scope:     "DP" here is restricted to the projection-transaction-escape
           shape `DPProjectionEscape` with an opaque caller-supplied
           DP-semantic side-condition. The full dependency-pair
           processor framework, full MSPO, full WPO/gWPO, arbitrary
           DP processor instances, and arbitrary semantic quotients
           are explicitly NOT formalised here.
```

## K-check 7 honesty (Lean Development Bible Section 7)

**This module does NOT claim**:

```
"The DP projection proves the source system terminates."
```

What it does claim, structurally:

```
A DPProjectionEscape gives a ProjectionTransactionEscape.
A ProjectionTransactionEscape orients the projected step.
By the U1.5 lifted_orients theorem, the projected orientation
  transports back to the source via pi-commutation, giving
  Orients R (mu' ∘ pi) ltA' on the source side.
```

`Orients` is a single-step orientation predicate. It is **not** a
strong-normalisation theorem, **not** a full DP-soundness chain, and
**not** a claim that arbitrary DP processors produce valid
projection-transaction escapes. The full chain `full Step termination
<- DP framework soundness <- complete DP extraction <- SCC
decomposition <- subterm/projection criterion <- all preconditions
discharged` belongs to the full DP-certification layer.

## Provided surfaces

* `DPProjectionEscape R` -- DP-style projection escape: a
  `ProjectionTransactionEscape R` together with an opaque
  DP-semantic side-condition.
* `dpProjection_is_projectionTransaction` -- every DP projection
  escape, in this sense, restricts to the underlying static
  projection-transaction escape on the same step.
* `dpWitnessTransport_sound` -- the witness-transport content of DP:
  the decisive descent measure on the original term type, obtained by
  transporting the projected measure back through `pi`, orients the
  original RDRS step in the projected strict relation (single-step
  orientation only; not SN).

## Non-vacuity status

* `DPProjectionEscape R` is inhabited once the caller supplies a
  `ProjectionTransactionEscape R`. There is no generic DP escape for
  an arbitrary source step.

Scope: no `sorry`, `admit`, `axiom`, or production `example :`. No U2
imports.
-/

namespace OperatorKO7.RDRSWitnessTransport

open OperatorKO7.RDRSDescentLens
open OperatorKO7.RDRSProjectionTransaction

/-- DP-style projection escape on top of the projection-transaction
surface.

A `DPProjectionEscape R` consists of:

* a `ProjectionTransactionEscape R` (the U1.5 final classifier surface);
* an opaque DP-semantic side-condition (a Prop the caller supplies and
  discharges).

The DP-semantic side-condition is **not** formalised at this layer.
It is the caller's responsibility to assert and prove that the
supplied projection transaction comes from a DP processor and respects
DP-side soundness in their formalisation. This module makes no claim
about which Propositions correspond to legitimate DP side-conditions:
the field is the structural slot for the caller's DP semantic content.

**Audit slots.**

* **Proves:** existence of a projection-transaction escape paired with
  an opaque DP-semantic side-condition `Prop` and its witness.
* **Does not prove:** that arbitrary DP processors produce this
  shape; does not prove the source system terminates; does not
  formalise the DP processor framework.
* **Relation:** source `R`.
* **Closure:** N/A at the structure level (witness transport happens
  via the underlying PTE).
* **Trust:** kernel-only.
* **Scope:** restricted to the structural shape above. -/
structure DPProjectionEscape {B S N T : Type} (R : RDRSStep B S N T) where
  /-- The underlying static projection-transaction escape. -/
  toProjectionTransactionEscape : ProjectionTransactionEscape R
  /-- DP-semantic side-condition. An opaque Prop supplied by the
  caller. Not formalised at this layer. -/
  dpSemanticConditions          : Prop
  /-- Witness that the DP-semantic side-condition holds. -/
  dpSemanticConditions_holds    : dpSemanticConditions

namespace DPProjectionEscape

variable {B S N T : Type} {R : RDRSStep B S N T}

/-- Extract the underlying static projection transaction. -/
def toProjectionTransaction (D : DPProjectionEscape R) :
    ProjectionTransaction R :=
  D.toProjectionTransactionEscape.transaction

end DPProjectionEscape

/-! ### Conditional non-vacuity witness (Lean Development Bible R5 / S09) -/

/-- Construct a `DPProjectionEscape` from supplied projection-
transaction evidence and the trivial DP-semantic side-condition.
Documents the wrapper shape only; no generic DP processor evidence is
encoded. -/
def DPProjectionEscape.ofProjectionTransactionEscape
    {B S N T : Type} {R : RDRSStep B S N T}
    (P : ProjectionTransactionEscape R) :
    DPProjectionEscape R where
  toProjectionTransactionEscape := P
  dpSemanticConditions          := True
  dpSemanticConditions_holds    := True.intro

/-- **Non-vacuity (conditional on supplied projection-transaction
evidence):** `DPProjectionEscape R` is non-empty whenever the caller
supplies a `ProjectionTransactionEscape R`. The DP side-condition is
the trivial `True`; this lemma documents wrapper inhabitation, not
substantive DP-processor evidence. -/
theorem DPProjectionEscape_nonempty_of_projectionTransactionEscape
    {B S N T : Type} {R : RDRSStep B S N T}
    (P : ProjectionTransactionEscape R) :
    Nonempty (DPProjectionEscape R) :=
  ⟨DPProjectionEscape.ofProjectionTransactionEscape P⟩

/-- **DP projection is a projection transaction (escape).**

Every DP-style projection escape, in the sense of `DPProjectionEscape`,
restricts to a static projection-transaction escape on the same RDRS
step. The DP-semantic side-condition does not enter the transaction
view; it is preserved as an opaque witness on the DP record.

This is the structural sense in which "DP projections are projection
transactions" at the level of generality this module commits to. We do
not claim that every DP processor produces a `DPProjectionEscape`; the
record must be supplied by the caller.

**Audit slots.**

* **Proves:** a `def` from `DPProjectionEscape R` to
  `ProjectionTransactionEscape R`.
* **Does not prove:** that this `def` is surjective; does not formalise
  the dependency-pair processor framework; does not prove source-system
  SN.
* **Relation:** RDRSStep at every step (lifted via `pi`).
* **Closure:** root (single-step shape).
* **Trust:** kernel-only (record projection).
* **Scope:** restricted to the structural shape of `DPProjectionEscape`. -/
def dpProjection_is_projectionTransaction
    {B S N T : Type} {R : RDRSStep B S N T}
    (D : DPProjectionEscape R) : ProjectionTransactionEscape R :=
  D.toProjectionTransactionEscape

/-- **DP witness transport is sound (single-step).**

The decisive descent measure on the original term type, obtained by
transporting the projected measure back through `pi`, orients the
original RDRS step in the projected strict relation.

This is the witness-transport content of DP at this layer: a descent
witness on the projected side transports to a descent witness on the
source side, via the projection's commutation with the step. The
underlying lemma is
`OperatorKO7.RDRSProjectionTransaction.ProjectionTransactionEscape.lifted_orients`.

**Audit slots.**

* **Proves:** `Orients R (D.toProjectionTransactionEscape.liftedMeasure)
              (D.toProjectionTransactionEscape.transaction.ltA')`,
              i.e. single-step orientation transport on the source RDRS
              step.
* **Does not prove:** source-system SN, source-system confluence, or
  any closure of `R` beyond single steps. **The name `_sound` here
  refers to single-step orientation soundness only, not to full DP
  framework soundness.** Per Lean Development Bible K-check 7, the
  source system's termination is **not** derived here.
* **Relation:** RDRSStep B S N T (source) at every `(b, s, n)`.
* **Closure:** root (single-step orientation).
* **Strategy:** N/A.
* **Trust:** kernel-only (delegates to `lifted_orients`).
* **Scope:** orientation-transport only; not an SN theorem. -/
theorem dpWitnessTransport_sound
    {B S N T : Type} {R : RDRSStep B S N T} (D : DPProjectionEscape R) :
    Orients R D.toProjectionTransactionEscape.liftedMeasure
              D.toProjectionTransactionEscape.transaction.ltA' :=
  D.toProjectionTransactionEscape.lifted_orients

/-- Audit anchor for the U3 DP witness-transport surface. Downstream
classifiers cite this String when wiring the DP branch through the
projection-transaction surface. -/
def rdrs_dp_witness_transport_anchor : String :=
  "OperatorKO7.RDRSWitnessTransport.dpWitnessTransport_sound"

end OperatorKO7.RDRSWitnessTransport
