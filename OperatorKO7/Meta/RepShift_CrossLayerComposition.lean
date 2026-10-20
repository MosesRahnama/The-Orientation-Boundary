import OperatorKO7.Meta.RepShift_LayeredSemanticsTower
import OperatorKO7.Meta.RepShift_BottleneckPredicate

/-!
# Composition of state interfaces and accepted certificates

State interfaces and backward property implications compose along finite
chains. Certificate transfer records compose when the intermediate verifier
realizes its property as accepted certificates. Forward maps between accepted
certificate types propagate existence through the actual prefix states;
together with backward property implications they give the endpoint
bottleneck theorem.
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

Property implications compose directly. The `composeRealized` construction
below also composes `WitnessTransport` records under the intermediate
verifier's realization premise. It supplies the accepted intermediate
certificate used by the lower transfer. -/

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

/-! ## Realization and finite accepted-witness chains

Semantic truth is converted
to an accepted witness only when realization is supplied explicitly.
-/

/-- Completeness for one chosen property, with no choice of canonical witness. -/
def Verifier.Realizes {S : Type u} {L : SemanticLayer S}
    (V : Verifier L) (P : S → Prop) : Prop :=
  ∀ x, P x → Nonempty (adequateWitnesses V P x)

/-- Higher realization turns accepted-witness transfer into semantic transfer. -/
theorem WitnessTransport.semanticTransfer {S T : Type u}
    {Llo : SemanticLayer S} {Lhi : SemanticLayer T}
    {Φ : LayerInterface Llo Lhi} {Vlo : Verifier Llo} {Vhi : Verifier Lhi}
    {P : S → Prop} {Q : T → Prop}
    (WT : WitnessTransport Φ Vlo Vhi P Q) (complete : Vhi.Realizes Q) :
    ∀ x, Q (Φ.alpha x) → P x :=
  fun x h => WT.propertyLevel x (complete (Φ.alpha x) h)

/-- Two transfers compose when the intermediate truth has accepted realizations. -/
def WitnessTransport.composeRealized {S T U : Type u}
    {Llo : SemanticLayer S} {Lmid : SemanticLayer T} {Lhi : SemanticLayer U}
    {Φ : LayerInterface Llo Lmid} {Ψ : LayerInterface Lmid Lhi}
    {Vlo : Verifier Llo} {Vmid : Verifier Lmid} {Vhi : Verifier Lhi}
    {P : S → Prop} {Q : T → Prop} {R : U → Prop}
    (Wlo : WitnessTransport Φ Vlo Vmid P Q)
    (Whi : WitnessTransport Ψ Vmid Vhi Q R) (complete : Vmid.Realizes Q) :
    WitnessTransport (Φ.compose Ψ) Vlo Vhi P R where
  transfer x w := Wlo.propertyLevel x (complete _ (Whi.transfer _ w))

/-- Identity abstraction and singleton concretization form an actual interface. -/
def LayerInterface.identity {S : Type u} (L : SemanticLayer S) : LayerInterface L L where
  alpha := id
  gamma := fun x => {x}
  galois_unit := fun _ => rfl

/-- The actual interfaces, including their concretizations, compose at every finite length. -/
def LayerInterface.prefix {S : ℕ → Type u} {L : ∀ n, SemanticLayer (S n)}
    (Φ : ∀ n, LayerInterface (L n) (L (n + 1))) :
    (n : ℕ) → LayerInterface (L 0) (L n)
  | 0 => LayerInterface.identity (L 0)
  | n + 1 => (LayerInterface.prefix Φ n).compose (Φ n)

@[simp] theorem LayerInterface.prefix_alpha_succ {S : ℕ → Type u}
    {L : ∀ n, SemanticLayer (S n)}
    (Φ : ∀ n, LayerInterface (L n) (L (n + 1))) (n : ℕ) (x : S 0) :
    (LayerInterface.prefix Φ (n + 1)).alpha x =
      (Φ n).alpha ((LayerInterface.prefix Φ n).alpha x) := rfl

/-- Actual witness functions compose between any two ordered finite levels. -/
def acceptedChainMap {W : ℕ → Type v} (next : ∀ n, W n → W (n + 1))
    {m n : ℕ} (h : m ≤ n) : W m → W n :=
  Nat.leRecOn h (fun {k} => next k)

/-- The empty chain preserves its witness. -/
theorem acceptedChainMap_refl {W : ℕ → Type v}
    (next : ∀ n, W n → W (n + 1)) (n : ℕ) (w : W n) :
    acceptedChainMap next (le_refl n) w = w :=
  Nat.leRecOn_self w

/-- Concatenating finite intervals composes their actual witness functions. -/
theorem acceptedChainMap_trans {W : ℕ → Type v}
    (next : ∀ n, W n → W (n + 1)) {i j k : ℕ}
    (hij : i ≤ j) (hjk : j ≤ k) (w : W i) :
    acceptedChainMap next (hij.trans hjk) w =
      acceptedChainMap next hjk (acceptedChainMap next hij w) :=
  Nat.leRecOn_trans hij hjk w

/-- Accepted existence moves forward under actual witness functions. -/
theorem acceptedChain_nonempty_mono {W : ℕ → Type v}
    (next : ∀ n, W n → W (n + 1)) {m n : ℕ} (h : m ≤ n) :
    Nonempty (W m) → Nonempty (W n) :=
  Nonempty.map (acceptedChainMap next h)

/-- Witness absence moves backward under the same functions. -/
theorem acceptedChain_empty_antitone {W : ℕ → Type v}
    (next : ∀ n, W n → W (n + 1)) {m n : ℕ} (h : m ≤ n) :
    ¬ Nonempty (W n) → ¬ Nonempty (W m) :=
  fun hn hm => hn (acceptedChain_nonempty_mono next h hm)

/-- Maps in both directions preserve existence; inverse equations are unnecessary. -/
theorem acceptedChain_nonempty_iff {W : ℕ → Type v}
    (next : ∀ n, W n → W (n + 1)) (back : ∀ n, W (n + 1) → W n)
    {m n : ℕ} (h : m ≤ n) : Nonempty (W m) ↔ Nonempty (W n) := by
  refine ⟨acceptedChain_nonempty_mono next h, ?_⟩
  let reverse : W n → W m :=
    Nat.leRecOn (C := fun k => W k → W m) h (fun {k} f => f ∘ back k) id
  exact Nonempty.map reverse

/-- Semantic backward laws compose on the states of the actual prefix interface. -/
theorem LayerInterface.prefix_property_transfer {S : ℕ → Type u}
    {L : ∀ n, SemanticLayer (S n)}
    (Φ : ∀ n, LayerInterface (L n) (L (n + 1))) (P : ∀ n, S n → Prop)
    (back : ∀ n x, P (n + 1) ((Φ n).alpha x) → P n x)
    (n : ℕ) (x : S 0) :
    P n ((LayerInterface.prefix Φ n).alpha x) → P 0 x := by
  induction n with
  | zero => exact id
  | succ n ih => exact fun h => ih (back n _ h)

/-- The supplied accepted-witness map at each state acts on the actual prefix states. -/
def LayerInterface.prefixAcceptedStep {S : ℕ → Type u}
    {L : ∀ n, SemanticLayer (S n)}
    (Φ : ∀ n, LayerInterface (L n) (L (n + 1)))
    (V : ∀ n, Verifier (L n)) (P : ∀ n, S n → Prop)
    (forward : ∀ n x, adequateWitnesses (V n) (P n) x →
      adequateWitnesses (V (n + 1)) (P (n + 1)) ((Φ n).alpha x))
    (x : S 0) (n : ℕ) :
    adequateWitnesses (V n) (P n) ((LayerInterface.prefix Φ n).alpha x) →
      adequateWitnesses (V (n + 1)) (P (n + 1))
        ((LayerInterface.prefix Φ (n + 1)).alpha x) :=
  forward n _

/-- An interior accepted-witness gap induces the endpoint bottleneck with all four fields. -/
theorem LayerInterface.prefix_endpoint_bottleneck {S : ℕ → Type u}
    {L : ∀ n, SemanticLayer (S n)}
    (Φ : ∀ n, LayerInterface (L n) (L (n + 1)))
    (V : ∀ n, Verifier (L n)) (P : ∀ n, S n → Prop)
    (forward : ∀ n x, adequateWitnesses (V n) (P n) x →
      adequateWitnesses (V (n + 1)) (P (n + 1)) ((Φ n).alpha x))
    (back : ∀ n x, P (n + 1) ((Φ n).alpha x) → P n x)
    (x : S 0) (k n : ℕ) (hkn : k + 1 ≤ n)
    (absent : ¬ Nonempty (adequateWitnesses (V k) (P k)
      ((LayerInterface.prefix Φ k).alpha x)))
    (present : Nonempty (adequateWitnesses (V (k + 1)) (P (k + 1))
      ((LayerInterface.prefix Φ (k + 1)).alpha x))) :
    InterfaceBottleneck
      (⟨L 0, L n, LayerInterface.prefix Φ n⟩ : TwoLayerTower (S 0) (S n))
      (V 0) (V n) (P 0) (P n) x := by
  have hi := acceptedChain_nonempty_mono
    (LayerInterface.prefixAcceptedStep Φ V P forward x) hkn present
  have hlo := acceptedChain_empty_antitone
    (LayerInterface.prefixAcceptedStep Φ V P forward x) (Nat.zero_le k) absent
  have transfer : ∀ y : S 0, Nonempty (adequateWitnesses (V n) (P n)
      ((LayerInterface.prefix Φ n).alpha y)) → P 0 y := by
    intro y hy
    rcases hy with ⟨w⟩
    exact LayerInterface.prefix_property_transfer Φ P back n y
      (adequate_implies_property w)
  exact ⟨transfer x hi, hlo, hi, transfer⟩

/-- A language with no candidate proof objects. -/
def emptySemanticLayer : SemanticLayer Unit where
  step := fun _ _ => False
  witnesses := fun _ _ => Empty

/-- The empty proof language has a sound verifier. -/
def emptySemanticVerifier : Verifier emptySemanticLayer where
  accepts := fun _ => False
  sound := fun w => Empty.elim w

/-- Soundness alone does not realize even the true property. -/
theorem sound_empty_not_realizing :
    ¬ emptySemanticVerifier.Realizes (fun _ : Unit => True) := by
  intro complete
  rcases complete () trivial with ⟨w⟩
  exact Empty.elim w.1

/-- Three consecutive candidate families with a missing middle family. -/
def witnessGapFamily (n : ℕ) : Type := if n = 1 then Empty else Unit

/-- Semantic implications alone do not supply a forward witness map. -/
theorem semantic_implication_not_witness_transport :
    (∀ _ : ℕ, True → True) ∧ Nonempty (witnessGapFamily 0) ∧
      ¬ Nonempty (witnessGapFamily 1) ∧ Nonempty (witnessGapFamily 2) ∧
      ¬ Nonempty (witnessGapFamily 0 → witnessGapFamily 1) := by
  refine ⟨fun _ h => h, ?_, ?_, ?_, ?_⟩
  · change Nonempty Unit
    exact ⟨()⟩
  · simp [witnessGapFamily]
  · change Nonempty Unit
    exact ⟨()⟩
  · rintro ⟨f⟩
    have w : witnessGapFamily 0 := by simpa [witnessGapFamily] using ()
    have bad : Empty := by simpa [witnessGapFamily] using f w
    exact Empty.elim bad

#check @Verifier.Realizes
#print axioms Verifier.Realizes
#check @WitnessTransport.semanticTransfer
#print axioms WitnessTransport.semanticTransfer
#check @WitnessTransport.composeRealized
#print axioms WitnessTransport.composeRealized
#check @LayerInterface.identity
#print axioms LayerInterface.identity
#check @LayerInterface.prefix
#print axioms LayerInterface.prefix
#check @LayerInterface.prefix_alpha_succ
#print axioms LayerInterface.prefix_alpha_succ
#check @acceptedChainMap
#print axioms acceptedChainMap
#check @acceptedChainMap_refl
#print axioms acceptedChainMap_refl
#check @acceptedChainMap_trans
#print axioms acceptedChainMap_trans
#check @acceptedChain_nonempty_mono
#print axioms acceptedChain_nonempty_mono
#check @acceptedChain_empty_antitone
#print axioms acceptedChain_empty_antitone
#check @acceptedChain_nonempty_iff
#print axioms acceptedChain_nonempty_iff
#check @LayerInterface.prefix_property_transfer
#print axioms LayerInterface.prefix_property_transfer
#check @LayerInterface.prefixAcceptedStep
#print axioms LayerInterface.prefixAcceptedStep
#check @LayerInterface.prefix_endpoint_bottleneck
#print axioms LayerInterface.prefix_endpoint_bottleneck
#check @emptySemanticLayer
#print axioms emptySemanticLayer
#check @emptySemanticVerifier
#print axioms emptySemanticVerifier
#check @sound_empty_not_realizing
#print axioms sound_empty_not_realizing
#check @witnessGapFamily
#print axioms witnessGapFamily
#check @semantic_implication_not_witness_transport
#print axioms semantic_implication_not_witness_transport

end OperatorKO7.RepShift
