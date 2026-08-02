import OperatorKO7.Meta.InformationTheoreticConfession
import OperatorKO7.Meta.InformationalIncompleteness.CarrierBurden
import OperatorKO7.Meta.InformationalIncompleteness.RecursorPayloadErasure

/-!
# Carrier-Capacity Carrier (ENG-WCC sub-block 9-10, Brief A-073)

Carrier module for the carrier-capacity / tight-rate anchors cited by the
engine's witness-carrier certificate. NO new mathematical content: this
module is a thin definitional carrier that names existing substrate so the
engine can emit one stable theorem reference per cert.

Substrate citations (already mechanized; no new proofs):
- `OperatorKO7.Meta.InformationTheoreticConfession.confession_cost_floor`
  (Landauer-style per-bit thermodynamic floor on discarded-bit counts);
- `OperatorKO7.Meta.InformationTheoreticConfession.canonical_confession_minimizes_discarded_information`
  (canonical confession minimizes discarded information across the
  theorem-backed family).

The manuscript anchors are
- `Rahnama_Informational_Incompleteness.tex` Theorem `thm:carrier-capacity`,
- `Rahnama_Informational_Incompleteness.tex` Corollary `cor:tight-rate`.

Relation tag: NA (metadata / carrier module).
Property: definition.
Trust: kernel-only.
-/

namespace OperatorKO7.Meta.InformationalIncompleteness.CarrierCapacity

/-- Carrier-capacity anchor record cited by the engine. Three named
string fields keep the engine emission stable while pointing at upstream
theorems by exact name. -/
structure CarrierCapacityAnchor where
  /-- Module that owns the cost-floor and minimization theorems. -/
  informationTheoreticConfessionModule : String
  /-- Name of the per-bit confession cost-floor theorem. -/
  confessionCostFloorTheoremName : String
  /-- Name of the canonical-minimization theorem. -/
  canonicalMinimizationTheoremName : String
  /-- Manuscript anchor for the carrier-capacity bound. -/
  manuscriptCarrierCapacityAnchor : String
  /-- Manuscript anchor for the tight-rate corollary. -/
  manuscriptTightRateAnchor : String

/-- Canonical anchor used by the engine on every T3 / T4 emission whose
payload requires a carrier-capacity citation. -/
def canonicalCarrierCapacityAnchor : CarrierCapacityAnchor where
  informationTheoreticConfessionModule :=
    "OperatorKO7.Meta.InformationTheoreticConfession"
  confessionCostFloorTheoremName :=
    "OperatorKO7.Meta.InformationTheoreticConfession.confession_cost_floor"
  canonicalMinimizationTheoremName :=
    "OperatorKO7.Meta.InformationTheoreticConfession.canonical_confession_minimizes_discarded_information"
  manuscriptCarrierCapacityAnchor :=
    "Rahnama_Informational_Incompleteness.thm:carrier-capacity"
  manuscriptTightRateAnchor :=
    "Rahnama_Informational_Incompleteness.cor:tight-rate"

/-- The canonical carrier-capacity anchor names a non-empty
carrier-capacity manuscript reference. -/
theorem canonicalCarrierCapacityAnchor_manuscriptCarrierCapacityAnchor_nonempty :
    canonicalCarrierCapacityAnchor.manuscriptCarrierCapacityAnchor ≠ "" := by
  intro h
  have hlen :
      canonicalCarrierCapacityAnchor.manuscriptCarrierCapacityAnchor.length = 0 := by
    rw [h]; rfl
  have :
      canonicalCarrierCapacityAnchor.manuscriptCarrierCapacityAnchor.length =
      "Rahnama_Informational_Incompleteness.thm:carrier-capacity".length := by rfl
  rw [this] at hlen
  exact absurd hlen (by decide)

/-- The canonical carrier-capacity anchor names a non-empty tight-rate
manuscript reference. -/
theorem canonicalCarrierCapacityAnchor_manuscriptTightRateAnchor_nonempty :
    canonicalCarrierCapacityAnchor.manuscriptTightRateAnchor ≠ "" := by
  intro h
  have hlen :
      canonicalCarrierCapacityAnchor.manuscriptTightRateAnchor.length = 0 := by
    rw [h]; rfl
  have :
      canonicalCarrierCapacityAnchor.manuscriptTightRateAnchor.length =
      "Rahnama_Informational_Incompleteness.cor:tight-rate".length := by rfl
  rw [this] at hlen
  exact absurd hlen (by decide)

/-! ## Real theorems (anchor upgraded from anchor-only to anchor + theorem) -/

open OperatorKO7.RDRSDescentLens
open OperatorKO7.RDRSSemanticDirectMeasure
open OperatorKO7.RDRSSemanticPayloadSensitivity

/--
Proves: the operative content of the carrier-capacity bound `thm:carrier-capacity`,
  TOTAL over arbitrary semantic measures: every semantic measure that orients the
  recursor is counter-dominated, hence cannot encode the duplicating step through a
  payload-sensitive direct certificate. Re-export of the recursor counter-domination.
Does not prove: a numeric code-length budget model; the budget-vs-burden comparison
  is carried by `carrier_capacity_asymptotic_shortfall` (carrier lengths) below.
Relation: the canonical II recursor `iiRecursor` (root single-step orientation).
Closure: root single-step.
Strategy: not applicable.
Trust: kernel-only.
Scope: every `SemanticMeasureData (Nat × Nat)` that orients the recursor.
-/
theorem carrier_capacity_orienting_counter_dominated
    (M : SemanticMeasureData (Nat × Nat))
    (hOrient : Orients RecursorPayloadErasure.iiRecursor M.μ M.ltA) :
    CounterDominated RecursorPayloadErasure.iiRecursor M :=
  RecursorPayloadErasure.iiRecursor_orienting_measure_counter_dominated M hOrient

/--
Proves: a linear lower bound on the raw carrier burden: for positive payload code
  length `L`, the burden through depth `K` is at least `K + 1`.
Does not prove: the exact closed form (see `CarrierBurden.carrierRaw_two_mul`).
Relation: not applicable (pure Nat).
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only (induction on `K`).
Scope: every `L K : Nat` with `1 ≤ L`.
-/
theorem carrierRaw_succ_le (L : Nat) (hL : 1 ≤ L) (K : Nat) :
    K + 1 ≤ CarrierBurden.carrierRaw L K := by
  induction K with
  | zero =>
      have h : CarrierBurden.carrierRaw L 0 = L := rfl
      rw [h]; omega
  | succ k ih =>
      have h : CarrierBurden.carrierRaw L (k + 1)
          = CarrierBurden.carrierRaw L k + (k + 2) * L := rfl
      have hmul : k + 2 ≤ (k + 2) * L := by
        have h2 := Nat.mul_le_mul (Nat.le_refl (k + 2)) hL
        rwa [Nat.mul_one] at h2
      rw [h]; omega

/--
Proves: the asymptotic shortfall `cor:asymptotic-shortfall`: for any payload code
  length `L ≥ 1` and any fixed direct-interface carrier budget `C`, there is a trace
  depth at which the raw carrier burden strictly exceeds `C`. The direct interface
  therefore cannot stay within any fixed carrier budget as depth grows.
Does not prove: the sharp threshold constant `K_* ~ sqrt(2C/L)`; this is the
  existence (shortfall) form.
Relation: not applicable (pure Nat carrier-length comparison).
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: every `L : Nat` with `1 ≤ L` and every budget `C : Nat`.
-/
theorem carrier_capacity_asymptotic_shortfall
    (L : Nat) (hL : 1 ≤ L) (C : Nat) :
    ∃ K, C < CarrierBurden.carrierRaw L K :=
  ⟨C, by have h := carrierRaw_succ_le L hL C; omega⟩

end OperatorKO7.Meta.InformationalIncompleteness.CarrierCapacity
