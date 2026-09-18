import Mathlib.Order.GaloisConnection.Defs
import Mathlib.Data.Set.Basic

/-!
# Layered Semantics Tower

This module packages abstract semantic layers and a two-layer interface:

```
    L_0  --alpha_0-->  L_1  --alpha_1-->  L_2  --...-->  L_n
         <-gamma_0-          <-gamma_1-          <-...-
```

Each layer `L_i = (S_i, ->_i, W_i)` has a state space, a transition
relation, and a per-property witness family. The tower is connected
by abstraction maps `alpha_i : S_i -> S_{i+1}` and concretization
maps `gamma_i : S_{i+1} -> Set S_i`.

The central abstract objects packaged here are:

- `SemanticLayer S` for a state space `S`;
- `LayerInterface` between two consecutive layers, packaging an abstraction
  map, a concretization map, and the required unit condition
  `x ∈ gamma (alpha x)`;
- `WitnessTransport`: a sound transfer of witnesses from a higher
  layer back down to the property at a lower layer.

The unit condition is weaker than a full Galois connection because the
structures carry no orders and no adjunction equivalence.
-/

namespace OperatorKO7.RepShift

universe u v w

/--
A `SemanticLayer S` packages a state space `S`, a transition relation
`step : S -> S -> Prop`, and a per-property family of witnesses
`witnesses : (S -> Prop) -> S -> Type`. The witness family is
intentionally `Type`-valued so that downstream modules can speak about
*which* witness was chosen, not only whether one exists.
-/
structure SemanticLayer (S : Type u) where
  /-- Local one-step transition relation on `S`. -/
  step : S → S → Prop
  /-- For each property `P : S -> Prop` and instance `x : S`, the
  family of proof objects expressible at this layer that purport to
  establish `P x`. -/
  witnesses : (S → Prop) → S → Type

/--
A `Verifier L` for a layer `L : SemanticLayer S` is a decision
predicate that says which witnesses are accepted as actual proofs.
Externalising the verifier matches the paper's emphasis on a fixed
external acceptance criterion: the verifier is what supplies the
truth anchor, not the proposing agent.
-/
structure Verifier {S : Type u} (L : SemanticLayer S) where
  accepts : ∀ {P : S → Prop} {x : S}, L.witnesses P x → Prop
  sound :
    ∀ {P : S → Prop} {x : S} (w : L.witnesses P x),
      accepts w → P x

/--
The set of *adequate* witnesses: those accepted by the external
verifier.
-/
def adequateWitnesses {S : Type u} {L : SemanticLayer S}
    (V : Verifier L) (P : S → Prop) (x : S) : Type _ :=
  { w : L.witnesses P x // V.accepts w }

/--
Soundness corollary: if an adequate witness exists, the property
holds. Spelt out for downstream readability.
-/
theorem adequate_implies_property {S : Type u} {L : SemanticLayer S}
    {V : Verifier L} {P : S → Prop} {x : S}
    (w : adequateWitnesses V P x) : P x :=
  V.sound w.1 w.2

/-- **Abstraction map** lifting state from a lower layer `L_lo` to a
higher layer `L_hi`. -/
structure AbstractionMap {S T : Type u} (Llo : SemanticLayer S)
    (Lhi : SemanticLayer T) where
  alpha : S → T

/-- **Concretization map** sending a higher-layer state to the set of
lower-layer states it represents. -/
structure ConcretizationMap {S T : Type u} (Llo : SemanticLayer S)
    (Lhi : SemanticLayer T) where
  gamma : T → Set S

/--
A **layer interface** between two layers. It requires maps `alpha` and `gamma`
and the unit condition `x ∈ gamma (alpha x)`. This is a required field, not an
optional flag or a full Galois connection.
-/
structure LayerInterface {S T : Type u} (Llo : SemanticLayer S)
    (Lhi : SemanticLayer T) where
  /-- Abstraction map. -/
  alpha : S → T
  /-- Concretization map. -/
  gamma : T → Set S
  /-- Required unit condition: `x ∈ gamma (alpha x)` for every `x`. -/
  galois_unit : ∀ x : S, x ∈ gamma (alpha x)

namespace LayerInterface

/-- Restatement of the stored unit condition. -/
theorem mem_gamma_alpha {S T : Type u}
    {Llo : SemanticLayer S} {Lhi : SemanticLayer T}
    (Φ : LayerInterface Llo Lhi) (x : S) :
    x ∈ Φ.gamma (Φ.alpha x) :=
  Φ.galois_unit x

end LayerInterface

/--
**Witness transport** across a layer interface. Given an interface
`Φ : Llo ↝ Lhi` and a property `P` on the lower layer, a witness
transport says: every adequate `Lhi`-witness for the abstracted
property at `Φ.alpha x` already establishes `P x`.

This is the sound-transfer ingredient of the cross-layer theory.
Concrete instantiations supply this from a lower-layer simulation
proof or from an external soundness theorem (e.g., the
Arts–Giesl dependency-pair soundness theorem).
-/
structure WitnessTransport {S T : Type u}
    {Llo : SemanticLayer S} {Lhi : SemanticLayer T}
    (Φ : LayerInterface Llo Lhi)
    (Vlo : Verifier Llo) (Vhi : Verifier Lhi)
    (P : S → Prop) (Phi_P : T → Prop) where
  /-- Transfer rule: an adequate higher-layer witness for the
  abstracted property at `α(x)` yields a proof of the original
  property `P x`. -/
  transfer :
    ∀ x : S,
      adequateWitnesses Vhi Phi_P (Φ.alpha x) → P x

/--
The **canonical abstracted property**: when the higher layer's
property is `P ∘ ⋃γ`, i.e., it holds at `t` iff `P` holds on every
concretization, the witness transport degenerates to ordinary
property preservation. We do not require this canonical form;
downstream modules choose the abstracted property they need.
-/
def canonicalAbstractedProperty {S T : Type u}
    {Llo : SemanticLayer S} {Lhi : SemanticLayer T}
    (Φ : LayerInterface Llo Lhi) (P : S → Prop) : T → Prop :=
  fun t => ∀ x ∈ Φ.gamma t, P x

/-- If the canonical abstracted property is supplied at `alpha x`, the unit
condition specializes it to `P x`. -/
theorem canonicalAbstractedProperty_holds_at_alpha {S T : Type u}
    {Llo : SemanticLayer S} {Lhi : SemanticLayer T}
    (Φ : LayerInterface Llo Lhi) (P : S → Prop) (x : S)
    (h : canonicalAbstractedProperty Φ P (Φ.alpha x)) : P x :=
  h x (Φ.galois_unit x)

/--
A `TwoLayerTower` packages exactly two semantic layers and one interface.
-/
structure TwoLayerTower (S T : Type u) where
  /-- The lower layer. -/
  lo : SemanticLayer S
  /-- The higher layer. -/
  hi : SemanticLayer T
  /-- The interface between them. -/
  iface : LayerInterface lo hi

namespace TwoLayerTower

/-- Convenience extractor: the abstraction map of the tower. -/
def alpha {S T : Type u} (𝒯 : TwoLayerTower S T) : S → T :=
  𝒯.iface.alpha

/-- Convenience extractor: the concretization map of the tower. -/
def gamma {S T : Type u} (𝒯 : TwoLayerTower S T) : T → Set S :=
  𝒯.iface.gamma

end TwoLayerTower

end OperatorKO7.RepShift
