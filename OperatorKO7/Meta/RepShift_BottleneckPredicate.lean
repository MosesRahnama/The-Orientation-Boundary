import OperatorKO7.Meta.RepShift_LayeredSemanticsTower

/-!
# Representation-Shift Bottleneck Predicate

This module formalizes the central predicates of the
Representation-Shift Bottleneck paper:

- representation depth `kappa : Witness -> Nat`
- minimal representation order `kappaStar`
- the **single-layer bottleneck predicate**, instantiated against an
  abstract witness-language hierarchy
- the **interface bottleneck predicate**, instantiated against a
  two-layer tower from
  `Meta/RepShift_LayeredSemanticsTower.lean`

The bottleneck has *five* clauses in its abstract statement; the first
four are properties of the witness landscape and are formalized here
as a `Prop`-valued definition. The fifth (agent instability) is a
property of the *agent population* and is left as a parameter so that
downstream modules can supply it from empirical data without forcing
a particular formalization on the proof side.
-/

namespace OperatorKO7.RepShift

universe u v

/--
A **witness-language hierarchy** indexed by representation depth.
Each depth `k : Nat` carries a family of witnesses `W k P x`. Higher
`k` corresponds to more transformed proof objects (e.g., dependency
pairs, size-change matrices, accessibility-based termination
witnesses).
-/
structure WitnessHierarchy (S : Type u) where
  /-- Per-depth witness families. -/
  W : Nat → (S → Prop) → S → Type
  /-- A fixed verifier that says which witnesses (at any depth) are
  accepted. -/
  accepts : ∀ {k : Nat} {P : S → Prop} {x : S}, W k P x → Prop
  /-- The verifier is sound: an accepted witness at any depth proves
  the target property. -/
  sound :
    ∀ {k : Nat} {P : S → Prop} {x : S} (w : W k P x),
      accepts w → P x

namespace WitnessHierarchy

variable {S : Type u}

/-- The set of accepted witnesses at depth `k`. -/
def adequate (H : WitnessHierarchy S) (k : Nat) (P : S → Prop) (x : S)
    : Type _ :=
  { w : H.W k P x // H.accepts w }

/-- Existence of an accepted witness at depth `k`. -/
def hasAdequateAtDepth (H : WitnessHierarchy S) (k : Nat)
    (P : S → Prop) (x : S) : Prop :=
  Nonempty (H.adequate k P x)

/-- An *adequate* witness at *any* depth `< k`. -/
def hasAdequateBelow (H : WitnessHierarchy S) (k : Nat)
    (P : S → Prop) (x : S) : Prop :=
  ∃ j : Nat, j < k ∧ H.hasAdequateAtDepth j P x

/-- An *adequate* witness at depth `k` *exactly*. -/
def hasAdequateAt (H : WitnessHierarchy S) (k : Nat)
    (P : S → Prop) (x : S) : Prop :=
  H.hasAdequateAtDepth k P x

/-- An adequate witness exists at *some* depth `<= k`. -/
def hasAdequateAtMost (H : WitnessHierarchy S) (k : Nat)
    (P : S → Prop) (x : S) : Prop :=
  ∃ j : Nat, j ≤ k ∧ H.hasAdequateAtDepth j P x

/--
The **minimal representation order** of an instance `x` for property
`P` is the least depth `k` at which an adequate witness exists.
We model it as a relation `kappaStarLe H P x k`, true when an
adequate witness exists at some depth `j ≤ k`.
-/
def kappaStarLe (H : WitnessHierarchy S) (P : S → Prop) (x : S)
    (k : Nat) : Prop :=
  H.hasAdequateAtMost k P x

/-- `kappaStarGt H P x k`: every depth `≤ k` is empty of adequate
witnesses. -/
def kappaStarGt (H : WitnessHierarchy S) (P : S → Prop) (x : S)
    (k : Nat) : Prop :=
  ∀ j : Nat, j ≤ k → ¬ H.hasAdequateAtDepth j P x

end WitnessHierarchy

/--
**Single-layer representation-shift bottleneck predicate.**

An instance `x` exhibits a representation-shift bottleneck at depth
`k` (with respect to a witness hierarchy `H` and property `P`) when:

1. `P x` holds (the property is true);
2. no adequate witness exists at any depth strictly below `k`;
3. an adequate witness exists at depth `k`.

The fifth clause of the paper's abstract definition (agent
instability) is formalized separately in
`Meta/RepShift_PseudoWitnessMass.lean`.
-/
structure RepresentationShiftBottleneck {S : Type u}
    (H : WitnessHierarchy S) (P : S → Prop) (x : S) (k : Nat) : Prop where
  property_holds : P x
  no_witness_below : ∀ j : Nat, j < k → ¬ H.hasAdequateAtDepth j P x
  witness_at_k : H.hasAdequateAtDepth k P x

namespace RepresentationShiftBottleneck

variable {S : Type u} {H : WitnessHierarchy S} {P : S → Prop} {x : S} {k : Nat}

/-- A bottleneck at depth `k` rules out all adequate witnesses below `k`
in the form needed by the `kappaStarGt` relation. -/
theorem kappaStarGt_of_bottleneck (B : RepresentationShiftBottleneck H P x k)
    (hk : 0 < k) : H.kappaStarGt P x (k - 1) := by
  intro j hj hwit
  exact B.no_witness_below j (by omega) hwit

/-- A bottleneck at depth `k` realises the `kappaStarLe` upper bound at `k`. -/
theorem kappaStarLe_of_bottleneck (B : RepresentationShiftBottleneck H P x k) :
    H.kappaStarLe P x k :=
  ⟨k, le_refl k, B.witness_at_k⟩

/-- The bottleneck is *minimal* when `k` is exactly the minimal
representation order: no adequate witness at any strictly lower
depth. This is automatic from the no-witness-below clause but stated
as a corollary for downstream readability. -/
theorem minimal_iff_no_witness_below
    (B : RepresentationShiftBottleneck H P x k) (j : Nat) (hj : j < k) :
    ¬ H.hasAdequateAtDepth j P x :=
  B.no_witness_below j hj

end RepresentationShiftBottleneck

/-! ## Interface bottleneck across a two-layer tower

The single-layer bottleneck predicate above is parametrized by an
abstract depth `k`. The *interface* version below uses a two-layer
tower from `Meta/RepShift_LayeredSemanticsTower.lean`: there is a
lower layer with no adequate witness, an interface, and a higher
layer with an adequate witness. -/

/--
**Interface representation bottleneck.**

Given a two-layer tower `𝒯` with witness families `Wlo` at the lower
layer and `Whi` at the higher layer, plus a property `P` on the lower
layer and its abstracted form `Phi_P` on the higher layer, an
interface bottleneck at `x` consists of:

1. `P x` holds;
2. no `Llo`-adequate witness exists for `P` at `x`;
3. some `Lhi`-adequate witness exists for `Phi_P` at `α(x)`;
4. a sound transfer rule (witness transport) lifts the higher-layer
   witness back to a proof of `P x`.

Clauses (1)-(3) are *empirical* facts about the witness landscape;
clause (4) is the *transfer theorem*. Together they characterise
the interface where the proof must cross representation.
-/
structure InterfaceBottleneck
    {S T : Type u} (𝒯 : TwoLayerTower S T)
    (Vlo : Verifier 𝒯.lo) (Vhi : Verifier 𝒯.hi)
    (P : S → Prop) (Phi_P : T → Prop) (x : S) : Prop where
  property_holds : P x
  no_lo_witness : ¬ Nonempty (adequateWitnesses Vlo P x)
  has_hi_witness : Nonempty (adequateWitnesses Vhi Phi_P (𝒯.alpha x))
  transports : ∀ y : S,
      Nonempty (adequateWitnesses Vhi Phi_P (𝒯.alpha y)) → P y

namespace InterfaceBottleneck

variable {S T : Type u} {𝒯 : TwoLayerTower S T}
  {Vlo : Verifier 𝒯.lo} {Vhi : Verifier 𝒯.hi}
  {P : S → Prop} {Phi_P : T → Prop} {x : S}

/-- The transfer rule, applied to `x` itself, recovers the property. -/
theorem transports_to_property (B : InterfaceBottleneck 𝒯 Vlo Vhi P Phi_P x) :
    P x :=
  B.transports x B.has_hi_witness

/-- The lower layer is *empty* of adequate witnesses for `P` at `x`. -/
theorem lo_witness_empty (B : InterfaceBottleneck 𝒯 Vlo Vhi P Phi_P x) :
    ¬ Nonempty (adequateWitnesses Vlo P x) :=
  B.no_lo_witness

/-- The higher layer has an adequate witness for the abstracted
property at `α(x)`. -/
theorem hi_witness_at_alpha (B : InterfaceBottleneck 𝒯 Vlo Vhi P Phi_P x) :
    Nonempty (adequateWitnesses Vhi Phi_P (𝒯.alpha x)) :=
  B.has_hi_witness

end InterfaceBottleneck

/-! ## Pre-undecidability fracture

The pre-undecidability fracture is the special case of a bottleneck
where the property is decidable for `x`, the verifier accepts the
higher-layer witness in bounded time, and yet a population of
reasoning agents is unstable at the interface. The first three
ingredients are recorded structurally below; the fourth is a
parameter. -/

/--
**Pre-undecidability fracture predicate.**

The four clauses are:

1. `P x` is *decidable* for the specific instance `x`
   (modelled here by `Decidable (P x)`);
2. an adequate witness exists at depth `k > 0` (so the bottleneck
   is non-trivial);
3. the verifier `accepts` is decidable on the supplied witness
   (modelled by carrying a witness with an explicit acceptance proof);
4. yet the agent population is unstable at the interface (carried as
   an external `instability` proposition).

The fracture is *not* an undecidability theorem; on the contrary, it
holds *strictly below* undecidability — the truth is fixed, the
witness exists, the verifier is external. The agent instability is
the empirical content. The predicate packages all four conditions in
one record so downstream modules can cite them by name.
-/
structure PreUndecidabilityFracture {S : Type u}
    (H : WitnessHierarchy S) (P : S → Prop) (x : S) (k : Nat)
    (instability : Prop) where
  decidable_truth : Decidable (P x)
  witness_at_depth : H.hasAdequateAtDepth k P x
  k_positive : 0 < k
  agent_instability : instability

namespace PreUndecidabilityFracture

variable {S : Type u} {H : WitnessHierarchy S} {P : S → Prop} {x : S} {k : Nat}
  {instability : Prop}

/-- The fracture is genuinely *pre*-undecidability: the prop-valued
projections (the witness exists, `k > 0`, and the agent instability
holds) all follow from the fracture record. The decidability witness
is accessible as a separate field.

Stated as a conjunction over Props only; `Decidable (P x)` is data
and is exposed by `F.decidable_truth` directly. -/
theorem pre_undecidability_signature
    (F : PreUndecidabilityFracture H P x k instability) :
    H.hasAdequateAtDepth k P x ∧ 0 < k ∧ instability :=
  ⟨F.witness_at_depth, F.k_positive, F.agent_instability⟩

end PreUndecidabilityFracture

end OperatorKO7.RepShift
