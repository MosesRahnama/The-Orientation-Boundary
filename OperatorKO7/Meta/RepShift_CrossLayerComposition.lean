import OperatorKO7.Meta.RepShift_LayeredSemanticsTower
import OperatorKO7.Meta.RepShift_BottleneckPredicate

/-!
# Cross-Layer Composition

This module proves that two `LayerInterface`s compose into a single
`LayerInterface`, and that witness transports compose along the
composition. This packages the cross-layer transfer theorem of the
Representation-Shift Bottleneck paper.

The intuition is that a verification stack with three layers
`L_0 -> L_1 -> L_2` (e.g., source -> IR -> machine) can be analysed
by composing a source-to-IR interface with an IR-to-machine
interface. The bottleneck predicate is then *additive* under
composition in the sense that a bottleneck at any single interface
in the chain is a bottleneck at the composed interface.
-/

namespace OperatorKO7.RepShift

universe u v w

/-- **Composition of layer interfaces.** Given interfaces
`Φ : Llo ↝ Lmid` and `Ψ : Lmid ↝ Lhi`, their composition is the
interface `Llo ↝ Lhi` with abstraction `Ψ.alpha ∘ Φ.alpha` and
concretization `gamma_combined t = ⋃_{m ∈ Ψ.gamma t} Φ.gamma m`.

The Galois unit composes: if `x ∈ Φ.gamma (Φ.alpha x)` and
`Φ.alpha x ∈ Ψ.gamma (Ψ.alpha (Φ.alpha x))`, then
`x ∈ ⋃_{m ∈ Ψ.gamma ((Ψ ∘ Φ)(x))} Φ.gamma m`. -/
def LayerInterface.compose {S T U : Type u}
    {Llo : SemanticLayer S} {Lmid : SemanticLayer T} {Lhi : SemanticLayer U}
    (Φ : LayerInterface Llo Lmid) (Ψ : LayerInterface Lmid Lhi) :
    LayerInterface Llo Lhi where
  alpha := Ψ.alpha ∘ Φ.alpha
  gamma := fun u => { x : S | ∃ m ∈ Ψ.gamma u, x ∈ Φ.gamma m }
  galois_unit := by
    intro x
    refine ⟨Φ.alpha x, ?_, ?_⟩
    · exact Ψ.galois_unit (Φ.alpha x)
    · exact Φ.galois_unit x

/-- The composed interface's abstraction map is the function
composition. -/
@[simp] theorem LayerInterface.compose_alpha {S T U : Type u}
    {Llo : SemanticLayer S} {Lmid : SemanticLayer T} {Lhi : SemanticLayer U}
    (Φ : LayerInterface Llo Lmid) (Ψ : LayerInterface Lmid Lhi) (x : S) :
    (Φ.compose Ψ).alpha x = Ψ.alpha (Φ.alpha x) :=
  rfl

/-- The composed concretization at `u` is the union of `Φ.gamma m` over
`m ∈ Ψ.gamma u`. -/
theorem LayerInterface.compose_gamma_iff {S T U : Type u}
    {Llo : SemanticLayer S} {Lmid : SemanticLayer T} {Lhi : SemanticLayer U}
    (Φ : LayerInterface Llo Lmid) (Ψ : LayerInterface Lmid Lhi) (u : U) (x : S) :
    x ∈ (Φ.compose Ψ).gamma u ↔ ∃ m ∈ Ψ.gamma u, x ∈ Φ.gamma m :=
  Iff.rfl

/-! ## Composition of two-layer towers

We can build a composed `TwoLayerTower S U` from a chain
`L_0 ↝ L_1 ↝ L_2`. The intermediate layer is hidden inside the
composed interface.
-/

/-- Compose two two-layer towers into a single tower with the
intermediate layer projected out. -/
def TwoLayerTower.compose {S T U : Type u}
    (𝒯₁ : TwoLayerTower S T) (𝒯₂ : TwoLayerTower T U)
    (h : 𝒯₁.hi = 𝒯₂.lo) : TwoLayerTower S U := by
  -- We need to coerce the second tower's lower layer to match the
  -- first tower's higher layer. Since `h` says they are equal, this
  -- is a transport.
  refine ⟨𝒯₁.lo, 𝒯₂.hi, ?_⟩
  -- The composed interface lives over the composed pair `(Llo, Lhi)`.
  exact 𝒯₁.iface.compose (h ▸ 𝒯₂.iface)

/-! ## Cross-layer witness transport at the property level

The natural composition theorem in this framework is at the
*property* level: if there is a property-level transfer
`Phi_P (Φ.alpha y) → P y` along the lower interface, and a
property-level transfer
`Phi_Phi_P (Ψ.alpha m) → Phi_P m` along the upper interface, then
their composition is a property-level transfer
`Phi_Phi_P ((Ψ ∘ Φ)(x)) → P x` along the composed interface.

Property-level transfers are the right object for composition because
the data of a *specific witness* at the higher layer does not
generally lift to a specific witness at the lower layer; what does
lift is the truth of the property. `WitnessTransport` (as a record of
witness data) is preserved by composition only via the property-level
projection; we expose that projection below. -/

/-- The property-level projection of a witness transport: if any
adequate `Vhi`-witness for `Phi_P` exists at `Φ.alpha y`, then `P y`.
This follows from `WT.transfer` and `Nonempty`-elimination. -/
def WitnessTransport.propertyLevel {S T : Type u}
    {Llo : SemanticLayer S} {Lmid : SemanticLayer T}
    {Φ : LayerInterface Llo Lmid}
    {Vlo : Verifier Llo} {Vmid : Verifier Lmid}
    {P : S → Prop} {Phi_P : T → Prop}
    (WT : WitnessTransport Φ Vlo Vmid P Phi_P)
    (y : S) (h : Nonempty (adequateWitnesses Vmid Phi_P (Φ.alpha y))) :
    P y :=
  WT.transfer y h.some

/-- **Cross-layer transfer at the property level.** Given a
property-level transfer along each of two consecutive interfaces, we
get a property-level transfer along their composition. -/
theorem cross_layer_transfer {S T U : Type u}
    {Llo : SemanticLayer S} {Lmid : SemanticLayer T} {Lhi : SemanticLayer U}
    {Φ : LayerInterface Llo Lmid} {Ψ : LayerInterface Lmid Lhi}
    {P : S → Prop} {Phi_P : T → Prop} {Phi_Phi_P : U → Prop}
    (transfer₁ : ∀ y : S, Phi_P (Φ.alpha y) → P y)
    (transfer₂ : ∀ m : T, Phi_Phi_P (Ψ.alpha m) → Phi_P m)
    (x : S) (h : Phi_Phi_P (Ψ.alpha (Φ.alpha x))) : P x :=
  transfer₁ x (transfer₂ (Φ.alpha x) h)

/-- The composed transfer specialised to the composed interface. -/
theorem cross_layer_transfer_composed {S T U : Type u}
    {Llo : SemanticLayer S} {Lmid : SemanticLayer T} {Lhi : SemanticLayer U}
    {Φ : LayerInterface Llo Lmid} {Ψ : LayerInterface Lmid Lhi}
    {P : S → Prop} {Phi_P : T → Prop} {Phi_Phi_P : U → Prop}
    (transfer₁ : ∀ y : S, Phi_P (Φ.alpha y) → P y)
    (transfer₂ : ∀ m : T, Phi_Phi_P (Ψ.alpha m) → Phi_P m)
    (x : S) (h : Phi_Phi_P ((Φ.compose Ψ).alpha x)) : P x := by
  rw [LayerInterface.compose_alpha] at h
  exact cross_layer_transfer transfer₁ transfer₂ x h

/-! Through the property-level projection
`WitnessTransport.propertyLevel`, two `WitnessTransport`s compose to
a single property-level transfer along the composed interface. We do
not lift this back to a `WitnessTransport` because, in the abstract
framework, doing so would require choosing a canonical witness from
a `Nonempty` that is not generally available. The recursor instance
chooses the dependency-pair witness explicitly. -/

end OperatorKO7.RepShift
