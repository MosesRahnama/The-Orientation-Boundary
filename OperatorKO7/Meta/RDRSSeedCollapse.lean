set_option autoImplicit false

/-!
# RDRS Seed-Collapse Carrier Factorization (Milestone U1, Sprint U1.5)

Roadmap source: `OperatorKO7-private/Expansion/Universal_Payload_Sensitive_Direct_Measures_Roadmap.md`
Milestone U1, file `Meta/RDRSSeedCollapse.lean`.

Syntactic seed-collapse carrier factorization interface. The roadmap's
non-negotiable replacement for vague "or arbitrary semantic quotient"
phrasing on the payload-forgetting side: a carrier-insensitive
observable on a term type is one that factors through a seed-collapse
map, not through an opaque quotient.

## Audit slots (Lean Development Bible W8 / R4)

```
Relation:  N/A (no rewriting at this layer; the module is parametric
           over abstract carrier and observable types and does not
           reference any RDRSStep).
Closure:   N/A.
Strategy:  N/A.
Trust:     kernel-only. No `sorry`, `admit`, `axiom`, `opaque`,
           `unsafe`, `native_decide`, `bv_decide`, `csimp`, `extern`,
           `implemented_by`, or `addDeclWithoutChecking` is used.
Scope:     Section equation `collapse (carrier b) = b` only.
           No claim that `carrier (collapse t) = t` (collapse is
           many-to-one).  No claim about arbitrary semantic quotients.
```

## Provided surfaces

* `SeedCollapse` -- structural seed-collapse data: a payload-carrier
  diagonal `carrier : PayloadCarrier -> T` and a collapse
  `collapse : T -> PayloadCarrier`, satisfying
  `collapse (carrier b) = b` (the diagonal is a section of the collapse).
* `FactorsThroughSeedCollapse` -- structural witness that an observable
  `obs : T -> X` factors through the seed-collapse: a factor map
  `factor : PayloadCarrier -> X` together with the pointwise equation
  `obs t = factor (SC.collapse t)`.
* `FactorsThroughSeedCollapse.factor_on_carrier` -- on the diagonal
  carrier, the factor is determined: `factor b = obs (SC.carrier b)`.
* `SeedCollapse.id` -- canonical unconditional witness when
  `PayloadCarrier = T`. Inhabits `SeedCollapse T T` via identity maps.
* `SeedCollapse_nonempty_diagonal` -- non-vacuity lemma exhibiting
  `Nonempty (SeedCollapse T T)` for every `T : Type`.
* `FactorsThroughSeedCollapse.const` and
  `FactorsThroughSeedCollapse_nonempty_of_const` -- conditional
  inhabitation for an observable that factors through the collapse via
  a caller-supplied factor map.

## Scope discipline

* No `sorry`, `admit`, `axiom`, or production `example :`.
* No semantic-quotient surface: every "forgetting" obligation is
  discharged by exhibiting a `SeedCollapse` + `FactorsThroughSeedCollapse`,
  not by an opaque quotient.
* No U2 imports: this module is parametric over abstract carrier and
  observable types; it does not reference the raw direct-measure syntax
  in `Meta/RDRSRawDirectMeasure.lean` or the normalized method-certificate
  syntax in `Meta/RDRSMethodCertificate.lean`.
-/

namespace OperatorKO7.RDRSSeedCollapse

/-- Structural seed-collapse data on a term type `T` over an abstract
payload carrier type `PayloadCarrier`.

The diagonal `carrier : PayloadCarrier -> T` selects, for each abstract
payload-carrier value `b`, the diagonal term whose payload coordinates
are all `b`. The collapse `collapse : T -> PayloadCarrier` forgets
payload multiplicity by extracting the canonical carrier value. The
defining equation `collapse_carrier` records that the diagonal is a
section of the collapse: collapsing a diagonal term recovers its
carrier value.

**Audit slots.**

* **Proves:** existence of a `(carrier, collapse)` pair with the
  section equation `collapse (carrier b) = b`.
* **Does not prove:** the converse `carrier (collapse t) = t`
  (collapse is many-to-one); does not prove `collapse` is unique or
  surjective beyond its image.
* **Relation:** N/A.
* **Closure:** N/A.
* **Strategy:** N/A.
* **Trust:** kernel-only.
* **Scope:** structural definition; non-vacuity witness shipped below
  for the diagonal case `PayloadCarrier = T`. -/
structure SeedCollapse (PayloadCarrier T : Type) where
  /-- Diagonal carrier: pick the term whose payload coordinates are all `b`. -/
  carrier          : PayloadCarrier → T
  /-- Forgetting collapse: extract the canonical carrier value from a term. -/
  collapse         : T → PayloadCarrier
  /-- Section equation: the collapse left-inverts the diagonal. -/
  collapse_carrier : ∀ b, collapse (carrier b) = b

/-- Structural witness that an observable `obs : T -> X` is carrier-
insensitive: it factors through the supplied seed-collapse via the
factor map `factor : PayloadCarrier -> X`. The defining equation
`obs_eq` records the factorization pointwise:
`obs t = factor (SC.collapse t)`.

**Audit slots.**

* **Proves:** existence of a factor map `factor : PayloadCarrier -> X`
  with `obs t = factor (SC.collapse t)` for every `t : T`.
* **Does not prove:** uniqueness of the factor map on values outside
  the image of `SC.carrier`; behaviour of `obs` outside the
  carrier-diagonal.
* **Relation:** N/A.
* **Closure:** N/A.
* **Strategy:** N/A.
* **Trust:** kernel-only.
* **Scope:** parametric over `PayloadCarrier T X`, fixed `SC` and
  `obs`. -/
structure FactorsThroughSeedCollapse
    {PayloadCarrier T X : Type}
    (SC : SeedCollapse PayloadCarrier T) (obs : T → X) where
  /-- The factor map on the carrier type. -/
  factor : PayloadCarrier → X
  /-- Pointwise factorization equation. -/
  obs_eq : ∀ t, obs t = factor (SC.collapse t)

namespace FactorsThroughSeedCollapse

variable {PayloadCarrier T X : Type}
variable {SC : SeedCollapse PayloadCarrier T} {obs : T → X}

/-- On the diagonal carrier, the factor map is forced:
`F.factor b = obs (SC.carrier b)`.

This is the uniqueness facet of the seed-collapse factorization: any
two `FactorsThroughSeedCollapse` records for the same observable and
seed-collapse agree on their factor maps when evaluated on the carrier
diagonal.

**Audit slots.**

* **Proves:** `F.factor b = obs (SC.carrier b)` for every
  `b : PayloadCarrier`.
* **Does not prove:** uniqueness of `F.factor` on
  `PayloadCarrier`-values outside the image of `SC.collapse`; does
  not prove two `FactorsThroughSeedCollapse` records share a factor
  map on arbitrary inputs.
* **Relation:** N/A.
* **Closure:** N/A.
* **Strategy:** N/A.
* **Trust:** kernel-only (`rw` + `Eq.symm`).
* **Scope:** parametric. -/
theorem factor_on_carrier
    (F : FactorsThroughSeedCollapse SC obs) (b : PayloadCarrier) :
    F.factor b = obs (SC.carrier b) := by
  have h := F.obs_eq (SC.carrier b)
  rw [SC.collapse_carrier] at h
  exact h.symm

end FactorsThroughSeedCollapse

/-! ### Non-vacuity witnesses (Lean Development Bible R5 / S09) -/

/-- Canonical seed-collapse on the diagonal case `PayloadCarrier = T`.
`carrier := id` and `collapse := id` satisfy the section equation
trivially.

**Audit slots.**

* **Proves:** `SeedCollapse T T` is inhabited for every `T : Type`.
* **Does not prove:** that this is the *only* `SeedCollapse T T`;
  does not lift to `SeedCollapse PayloadCarrier T` for arbitrary
  distinct `PayloadCarrier` and `T`.
* **Relation:** N/A.
* **Trust:** kernel-only. -/
def SeedCollapse.id (T : Type) : SeedCollapse T T where
  carrier          := fun b => b
  collapse         := fun t => t
  collapse_carrier := fun _ => rfl

/-- **Non-vacuity:** `SeedCollapse T T` is non-empty for every `T`. -/
theorem SeedCollapse_nonempty_diagonal (T : Type) :
    Nonempty (SeedCollapse T T) :=
  ⟨SeedCollapse.id T⟩

/-- Canonical `FactorsThroughSeedCollapse` for an observable that is
already known to factor through `SC.collapse` via a caller-supplied
factor map. This witness records the factorization explicitly so the
non-emptiness of `FactorsThroughSeedCollapse` is documented at this
layer.

**Audit slots.**

* **Proves:** `FactorsThroughSeedCollapse SC obs` is inhabited
  whenever the caller supplies `factor : PayloadCarrier -> X` with
  `obs t = factor (SC.collapse t)` pointwise.
* **Does not prove:** that an arbitrary `obs` factors through `SC`;
  the inhabitation is conditional on the factor data.
* **Relation:** N/A.
* **Trust:** kernel-only. -/
def FactorsThroughSeedCollapse.of_factor
    {PayloadCarrier T X : Type}
    (SC : SeedCollapse PayloadCarrier T) (obs : T → X)
    (factor : PayloadCarrier → X)
    (h : ∀ t, obs t = factor (SC.collapse t)) :
    FactorsThroughSeedCollapse SC obs :=
  { factor := factor
    obs_eq := h }

/-- **Non-vacuity (conditional):** `FactorsThroughSeedCollapse SC obs`
is non-empty whenever the caller supplies the factorization data. The
unconditional inhabitation of this structure is not provable -- not
every observable factors through every seed-collapse. -/
theorem FactorsThroughSeedCollapse_nonempty_of_factor
    {PayloadCarrier T X : Type}
    (SC : SeedCollapse PayloadCarrier T) (obs : T → X)
    (factor : PayloadCarrier → X)
    (h : ∀ t, obs t = factor (SC.collapse t)) :
    Nonempty (FactorsThroughSeedCollapse SC obs) :=
  ⟨FactorsThroughSeedCollapse.of_factor SC obs factor h⟩

/-- Constant observables factor through every seed-collapse via the
constant factor map. -/
theorem FactorsThroughSeedCollapse_nonempty_const
    {PayloadCarrier T X : Type}
    (SC : SeedCollapse PayloadCarrier T) (x : X) :
    Nonempty (FactorsThroughSeedCollapse SC (fun _ : T => x)) :=
  ⟨{ factor := fun _ => x, obs_eq := fun _ => rfl }⟩

/-- Audit anchor: this module supplies the seed-collapse carrier
factorization interface required by Milestone U1's projection
transaction. Downstream classifiers cite this String when discharging
the phi (forgotten payload-multiplicity dimension) obligation. -/
def rdrs_seed_collapse_anchor : String :=
  "OperatorKO7.RDRSSeedCollapse.SeedCollapse"

end OperatorKO7.RDRSSeedCollapse
