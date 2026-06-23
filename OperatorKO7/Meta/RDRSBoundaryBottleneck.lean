import OperatorKO7.Meta.RDRSDescentLens
import OperatorKO7.Meta.RDRSMethodCertificate
import OperatorKO7.Meta.RDRSProjectionTransaction

set_option autoImplicit false

/-!
# RDRS Boundary-Relative Witness Order and Bottleneck Theorem (Milestone U5, file 1/2)

Roadmap source: `OperatorKO7/Expansion/Universal_Payload_Sensitive_Direct_Measures_Roadmap.md`
Milestone U5 -- boundary-relative bottleneck.

## Audit slots (Lean Development Bible W8 / R4)

```
Relation:  N/A. The bottleneck theorem is about layered witnesses and
           boundary admissibility tags, not about rewriting steps.
           The W2 layer carries a `ProjectionTransactionEscape` whose
           own orientation transport lives in
           `RDRSProjectionTransaction`; this module does not re-prove
           orientation transport.
Closure:   N/A.
Strategy:  N/A.
Trust:     kernel-only.
Scope:     three closed witness layers (W0 = direct payload-sensitive
           grammar, W1 = construction-import, W2 = projection-
           transaction escape). The W1 layer is an abstract slot with
           no payload; no formalisation of construction-style imported
           global witnesses is provided. No full DP processor, MSPO,
           or WPO/gWPO coverage claim.
```

The roadmap distinguishes three witness layers for an RDRS step and
imposes a *boundary-relative* ordering on them. The three layers are:

```
W0 = closed direct payload-sensitive grammar    (the U2 normalized
                                                  direct certificates)
W1 = construction-style imported global         (abstract slot at this
     witnesses                                    layer; no full DP /
                                                  MSPO / WPO)
W2 = transformed / DP / projection-transaction  (the U1.5 / U3
     witnesses                                    projection-
                                                  transaction escapes)
```

Truth-level and boundary-level orderings on these layers are
**explicitly distinct**:

```
κ_truth     : a Nat-valued order   (W0 ↦ 0,  W1 ↦ 1,  W2 ↦ 2)
κ_boundary  : a Bool admissibility (W0 ↦ false, W1 ↦ false, W2 ↦ true)
```

A truth-level construction witness may exist at W1 (κ_truth = 1) yet
not be boundary-admissible (κ_boundary = false). This is the precise
"boundary-relative" content the roadmap requires: the boundary admits
only the W2 projection-transaction layer.

## Theorem-name adequacy note (Lean Development Bible stop-the-line #9)

This module uses the words "boundary" and "sound"-adjacent terminology
in theorem names. The intended scope of each:

* `boundary_bottleneck` -- about the boundary-admissibility tag
  (W0/W1/W2 → Bool), **not** about any rewriting-system "boundary"
  in the TPDB / CeTA sense.
* `boundary_relative_not_truth_level` -- truth-level vs boundary-tag
  distinction, not a soundness claim.
* `W0_not_boundary_admissible`, `W1_not_boundary_admissible`,
  `W2_boundary_admissible` -- statements about the abstract layer
  tag, not about admissibility in any semantic / certification sense.

No theorem in this module asserts strong normalisation, confluence,
or external-certificate soundness.

## Non-vacuity status

* `RDRSLayeredWitness R` is unconditionally inhabited via the
  `W1_construction` constructor (it carries no payload).
* `BoundaryBottleneck R` is inhabited once the caller supplies a
  `ProjectionTransactionEscape R`. There is no generic W2 witness for
  an arbitrary step.

Scope: no `sorry`, `admit`, `axiom`, or production `example :`.
-/

namespace OperatorKO7.RDRSBoundaryBottleneck

open OperatorKO7.RDRSDescentLens
open OperatorKO7.RDRSMethodCertificate
open OperatorKO7.RDRSProjectionTransaction

/-! ### Witness layers and the two distinct orderings -/

/-- The three witness layers of the boundary-relative classification.

A closed inductive over three constants:

```
W0 = direct payload-sensitive grammar
W1 = construction-style imported global witnesses
W2 = transformed / DP / projection-transaction witnesses
```

**Audit slots.**

* **Proves:** an inductive type with three constructors and decidable
  equality.
* **Does not prove:** any property of the constructors beyond their
  identity.
* **Trust:** kernel-only. -/
inductive WitnessLayer
  | W0
  | W1
  | W2
  deriving DecidableEq, Repr

namespace WitnessLayer

/-- Truth-level ordering on witness layers: Nat-valued.

This captures the meta-level fact that a truth-level construction
witness may exist below W2, even though such a witness is not
boundary-admissible. Truth-level and boundary-level are explicitly
distinct orderings on the same three layers. -/
def truthLevel : WitnessLayer → Nat
  | W0 => 0
  | W1 => 1
  | W2 => 2

/-- Boundary-admissibility predicate on witness layers: Bool-valued.

Only W2 is boundary-admissible. The payload-sensitive boundary admits
the U1.5/U3 projection-transaction layer; the W0 direct grammar and
W1 construction-import layer are both blocked. -/
def boundaryAdmissible : WitnessLayer → Bool
  | W0 => false
  | W1 => false
  | W2 => true

end WitnessLayer

/-- κ_truth: truth-level order on witness layers. A truth-level
construction witness may exist at any layer; κ_truth records the layer
position in `Nat`. -/
def kappaTruth (ℓ : WitnessLayer) : Nat :=
  ℓ.truthLevel

/-- κ_boundary: boundary-admissibility on witness layers. The boundary
admits only W2; κ_boundary records the admissibility verdict in
`Bool`. -/
def kappaBoundary (ℓ : WitnessLayer) : Bool :=
  ℓ.boundaryAdmissible

/-- **Truth-level and boundary-level orderings are distinct.**

There is a layer (W1) with positive truth-level (`κ_truth = 1`) but
zero boundary-admissibility (`κ_boundary = false`). The boundary order
is **not** the same as the truth-level order on these layers; the
roadmap's "truth-level construction witness may exist below W2"
discipline is recorded structurally.

**Audit slots.**

* **Proves:** `∃ ℓ : WitnessLayer, 0 < kappaTruth ℓ ∧ kappaBoundary ℓ
  = false`. Witnessed by `W1`.
* **Does not prove:** that every truth-level positive layer is
  boundary-non-admissible (W2 is both positive and admissible).
* **Trust:** kernel-only (`decide`). -/
theorem kappa_truth_vs_boundary_distinct :
    ∃ ℓ : WitnessLayer, 0 < kappaTruth ℓ ∧ kappaBoundary ℓ = false := by
  refine ⟨WitnessLayer.W1, ?_, ?_⟩ <;> decide

/-! ### RDRS layered witnesses -/

/-- RDRS layered witnesses over a step `R`, indexed by witness layer.

Constructors:

* `W0_direct cert` -- a normalized direct method certificate from U2.
  Carries the closed-grammar direct payload-sensitive witness.
* `W1_construction` -- an abstract slot for construction-style
  imported global witnesses. We do not formalise their content at
  this layer (no full DP / MSPO / WPO). A `W1_construction` value is
  *just* a layer tag; it carries no payload.
* `W2_transformed pte` -- a projection-transaction escape from
  U1.5/U3. Carries the boundary-admissible witness.

**Audit slots.**

* **Proves:** an inductive type with three constructors and explicit
  payloads for the W0 and W2 layers.
* **Does not prove:** that the constructors correspond to any
  particular semantic class of witnesses; they are structural tags.
* **Trust:** kernel-only. -/
inductive RDRSLayeredWitness
    {B S N T : Type} (R : RDRSStep B S N T)
  | W0_direct (cert : NormalizedDescentCertificate)
  | W1_construction
  | W2_transformed (pte : ProjectionTransactionEscape R)

namespace RDRSLayeredWitness

/-- Project a layered RDRS witness to its witness-layer tag. -/
def layer {B S N T : Type} {R : RDRSStep B S N T} :
    RDRSLayeredWitness R → WitnessLayer
  | W0_direct _      => WitnessLayer.W0
  | W1_construction  => WitnessLayer.W1
  | W2_transformed _ => WitnessLayer.W2

end RDRSLayeredWitness

variable {B S N T : Type} {R : RDRSStep B S N T}

/-- κ_truth on layered RDRS witnesses. -/
def kappa_truth (w : RDRSLayeredWitness R) : Nat :=
  kappaTruth w.layer

/-- κ_boundary on layered RDRS witnesses. -/
def kappa_boundary (w : RDRSLayeredWitness R) : Bool :=
  kappaBoundary w.layer

/-- **Non-vacuity (unconditional):** `RDRSLayeredWitness R` is
non-empty via the `W1_construction` constructor, which carries no
payload. -/
theorem RDRSLayeredWitness_nonempty {B S N T : Type} (R : RDRSStep B S N T) :
    Nonempty (RDRSLayeredWitness R) :=
  ⟨RDRSLayeredWitness.W1_construction⟩

/-! ### Per-layer admissibility lemmas -/

/-- A W0-tagged witness is not boundary-admissible.

**Audit slots.**

* **Proves:** `kappa_boundary w = false` for any `w` with
  `w.layer = W0`.
* **Does not prove:** that `w` corresponds to a substantive direct
  payload-sensitive certificate; only its tag is examined.
* **Trust:** kernel-only. -/
theorem W0_not_boundary_admissible
    (w : RDRSLayeredWitness R) (h : w.layer = WitnessLayer.W0) :
    kappa_boundary w = false := by
  show kappaBoundary w.layer = false
  rw [h]
  rfl

/-- A W1-tagged witness is not boundary-admissible. -/
theorem W1_not_boundary_admissible
    (w : RDRSLayeredWitness R) (h : w.layer = WitnessLayer.W1) :
    kappa_boundary w = false := by
  show kappaBoundary w.layer = false
  rw [h]
  rfl

/-- A W2-tagged witness is boundary-admissible. -/
theorem W2_boundary_admissible
    (w : RDRSLayeredWitness R) (h : w.layer = WitnessLayer.W2) :
    kappa_boundary w = true := by
  show kappaBoundary w.layer = true
  rw [h]
  rfl

/-! ### Boundary-relative bottleneck premise and theorem -/

/-- Premise package for the boundary-relative bottleneck.

Records:

* A `w0_witness` tagged at layer W0 (the direct payload-sensitive
  grammar layer).
* A `w2_witness` tagged at layer W2 (the projection-transaction
  layer).

The W0 witness is blocked at the boundary by construction of
`kappaBoundary` on `W0`. The W2 witness succeeds at the boundary by
construction of `kappaBoundary` on `W2`. The bottleneck theorem
records both verdicts in one step. -/
structure BoundaryBottleneck
    {B S N T : Type} (R : RDRSStep B S N T) where
  /-- A witness tagged at layer W0 (direct payload-sensitive grammar). -/
  w0_witness : RDRSLayeredWitness R
  /-- Layer tag of the W0 witness. -/
  w0_at_W0   : w0_witness.layer = WitnessLayer.W0
  /-- A witness tagged at layer W2 (projection-transaction escape). -/
  w2_witness : RDRSLayeredWitness R
  /-- Layer tag of the W2 witness. -/
  w2_at_W2   : w2_witness.layer = WitnessLayer.W2

/-- Construct a `BoundaryBottleneck` from supplied projection-
transaction evidence. The W0 witness uses the `abstain` certificate;
the W2 witness uses the caller-provided escape. -/
def BoundaryBottleneck.ofProjectionTransactionEscape
    {B S N T : Type} {R : RDRSStep B S N T}
    (P : ProjectionTransactionEscape R) :
    BoundaryBottleneck R where
  w0_witness :=
    RDRSLayeredWitness.W0_direct NormalizedDescentCertificate.abstain
  w0_at_W0   := rfl
  w2_witness :=
    RDRSLayeredWitness.W2_transformed P
  w2_at_W2   := rfl

/-- **Non-vacuity (conditional on supplied W2 evidence):**
`BoundaryBottleneck R` is non-empty whenever the caller supplies a
`ProjectionTransactionEscape R`. -/
theorem BoundaryBottleneck_nonempty_of_projectionTransactionEscape
    {B S N T : Type} {R : RDRSStep B S N T}
    (P : ProjectionTransactionEscape R) :
    Nonempty (BoundaryBottleneck R) :=
  ⟨BoundaryBottleneck.ofProjectionTransactionEscape P⟩

/-- **Boundary-relative bottleneck theorem.**

Under the bottleneck premise (a W0 witness and a W2 witness both
exhibited), the W0 witness is blocked at the boundary
(`kappa_boundary = false`) and the W2 witness succeeds at the
boundary (`kappa_boundary = true`).

The boundary-admissibility split is along the W0 / W2 layer divide.
The roadmap's "W0 blocked, W2 succeeds under projection-transaction
witness" shape is recorded structurally: the W2 layer carries a
`ProjectionTransactionEscape` from U1.5/U3, which is the only way
`W2_transformed` can be inhabited.

**Audit slots.**

* **Proves:** `kappa_boundary BB.w0_witness = false`
  AND `kappa_boundary BB.w2_witness = true`.
* **Does not prove:** that any RDRS step admits a `BoundaryBottleneck`
  premise unconditionally; the structure must be supplied. Does not
  prove SN, confluence, or normalisation.
* **Trust:** kernel-only (extraction of per-layer admissibility
  lemmas). -/
theorem boundary_bottleneck (BB : BoundaryBottleneck R) :
    kappa_boundary BB.w0_witness = false ∧
    kappa_boundary BB.w2_witness = true := by
  refine ⟨?_, ?_⟩
  · exact W0_not_boundary_admissible BB.w0_witness BB.w0_at_W0
  · exact W2_boundary_admissible BB.w2_witness BB.w2_at_W2

/-- **The bottleneck is boundary-relative, not truth-level.**

Even at W1, the truth-level order assigns a positive value
(`κ_truth = 1`), while the boundary admissibility is `false`. The
bottleneck is therefore not a statement about truth-level existence
of witnesses; it is a statement about boundary admissibility, which
is a strictly coarser acceptance set on the same three layers. -/
theorem boundary_relative_not_truth_level :
    ∃ ℓ : WitnessLayer, 0 < kappaTruth ℓ ∧ kappaBoundary ℓ = false := by
  refine ⟨WitnessLayer.W1, ?_, ?_⟩ <;> decide

/-- Audit anchor for the U5 boundary-relative bottleneck surface. -/
def rdrs_boundary_bottleneck_anchor : String :=
  "OperatorKO7.RDRSBoundaryBottleneck.boundary_bottleneck"

end OperatorKO7.RDRSBoundaryBottleneck
