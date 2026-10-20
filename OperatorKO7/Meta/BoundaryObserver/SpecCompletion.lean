import OperatorKO7.Meta.BoundaryObserver.SourceApexInstrument
import OperatorKO7.Meta.BoundaryObserver.DemandTransport

/-!
# Six goals of the universal-observation specification

Lean source: `UniversalObservationSpec.lean`, lines 513, 890, 989, 1006, 1010,
and 1057, together with `PrefixLawGoal` at line 429. No specification import.

Twelve theories are mechanized here. The carrier-burden result in Theory I is
in `PayloadStress`; its entropy result is in the information-theory development.
Theory XIII is empirical telemetry and has no Lean theorem. The modules contain
no `sorry`, `native_decide`, or user-added axioms; their axiom dependencies stay
within `{propext, Classical.choice, Quot.sound}`. Most use no axioms, and each
includes an example demonstrating non-vacuity.

| Theory | Module | Headline |
|---|---|---|
| II | `ProvenanceLicense` | origin capture does not license the verdict |
| III | `WholeTermIndistinguishability` | a mass observer cannot separate the recursor from the circular carrier; a step projection can |
| IV | `CostedConfession` | composition burden is at most the sum, with equality if and only if the supports are disjoint; the module proves a lower bound |
| V | `UniversalityGate` | a universal claim requires every declared row to be complete; one missing row invalidates the claim |
| VI | `PayloadStress` | carrier burden is linear in payload, quadratic in depth, and diverges at fixed entropy |
| VII | `C4Classifier` | the total layer classifier identifies interface inexpressibility for the recursor, not undecidability |
| VIII | `WitnessFirst` | acceptance requires a licensed certificate; origin without a license and carrier-blind projection are rejected |
| IX | `EndogenousProvenance` | a non-vacuous query with an endogenous answer has zero exogenous information gain |
| X | `DiagonalMirror` | the mirror test recognizes `eqW a a`; misrecognition incurs burden without adding a distinction |
| XI | `DistinctionRecord` | distinction generates the record; equality leaves the record unchanged |
| XII | `DirectMeasureGrammarClosure` | orientation is equivalent to payload-blindness plus counter-strictness; the payload-blindness characterization is bidirectional on the counter-admissible class; effective-payload syntax and a Boolean decision theorem discharge the pump hypothesis |
| XIV | `Wavepacket` | the amplitude bridge is `|ψ|²=g`; a Born density alone does not determine phase or amplitude |

Each goal uses the corresponding Lean carrier and fields: `ProtocolResolution.FiniteProtocol`, `Operational.OperationalData`, `Operational.QuantumRealization`, `Operational.Density`, `Operational.Effect`, `Operational.CompletelyPositive`, `Operational.TraceNonIncreasing`, `UniversalObservation.Reconstruction.ThermalExperiment`, `UniversalObservation.Demand.Problem`, and `UniversalObservation.Transport.DemandIso`. The package `tr` is `Matrix.trace`; `BoundaryReconstruction.tr_entrywise` expresses it as the sum of diagonal entries. No goal is generalized, and no hypothesis is added.

Relation: finite probability laws, operational sources, and their matrix representations.
External trust: none.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace OperatorKO7.Meta.BoundaryObserver.SpecCompletion

open OperatorKO7.Meta.BoundaryObserver.ProtocolResolution
  (FiniteProtocol prefixMass prefixMass_nil prefixMass_append)
open OperatorKO7.Meta.BoundaryObserver.BoundaryReconstruction (Mat tr)
open OperatorKO7.Meta.BoundaryObserver.BoundaryReconstruction.Operational

/-! ## S1: the protocol adapter (specification line 513) -/

section ProtocolAdapter

variable {Z A Y : Type} [Fintype Z] [Fintype A] [Fintype Y]

/-- Specification line 429: the source recursion of a mass function on retained histories. The
empty history carries the prior; one more event multiplies the mass by the policy and the
observation kernel, and gives zero after a stop. -/
def PrefixLawGoal (p : FiniteProtocol Z A Y) (mass : Z → List (A × Y) → ℝ) : Prop :=
  (∀ z, mass z [] = p.prior.mass z) ∧
  ∀ z h a y, mass z (h ++ [(a, y)]) =
    if p.stop h then 0 else mass z h * (p.policy h).mass a * (p.observation h a z).mass y

/-- Specification line 513: an adapter bundles a mass function on retained histories with its
proof of the source recursion. -/
structure ProtocolAdapter (p : FiniteProtocol Z A Y) where
  activeMass : Z → List (A × Y) → ℝ
  source_recursion : PrefixLawGoal p activeMass

/-- The package fold `prefixMass` obeys the source recursion, by `prefixMass_nil` and
`prefixMass_append`. -/
theorem prefixLawGoal_prefixMass (p : FiniteProtocol Z A Y) :
    PrefixLawGoal p (prefixMass p) :=
  ⟨prefixMass_nil p, prefixMass_append p⟩

/-- The adapter of a finite protocol, with the package fold as its active mass. -/
def protocolAdapter (p : FiniteProtocol Z A Y) : ProtocolAdapter p where
  activeMass := prefixMass p
  source_recursion := prefixLawGoal_prefixMass p

theorem protocolAdapter_activeMass (p : FiniteProtocol Z A Y) :
    (protocolAdapter p).activeMass = prefixMass p := rfl

/-- The source recursion determines the mass function: it holds for `mass` iff `mass` is the
package fold `prefixMass p`. The proof is an induction on histories from the right. -/
theorem prefixLawGoal_iff (p : FiniteProtocol Z A Y) (mass : Z → List (A × Y) → ℝ) :
    PrefixLawGoal p mass ↔ mass = prefixMass p := by
  constructor
  · rintro ⟨hnil, hstep⟩
    funext z h
    induction h using List.reverseRecOn with
    | nil => rw [hnil z, prefixMass_nil]
    | append_singleton h ay ih =>
      obtain ⟨a, y⟩ := ay
      rw [hstep z h a y, prefixMass_append, ih]
  · rintro rfl
    exact prefixLawGoal_prefixMass p

/-- Every adapter of `p` carries the package fold as its active mass. -/
theorem ProtocolAdapter.activeMass_eq (p : FiniteProtocol Z A Y) (q : ProtocolAdapter p) :
    q.activeMass = prefixMass p :=
  (prefixLawGoal_iff p q.activeMass).mp q.source_recursion

/-- A finite protocol has one adapter, the one built from `prefixMass`. -/
instance protocolAdapterUnique (p : FiniteProtocol Z A Y) : Unique (ProtocolAdapter p) where
  default := protocolAdapter p
  uniq q := by
    obtain ⟨mass, hmass⟩ := q
    obtain rfl : mass = prefixMass p := (prefixLawGoal_iff p mass).mp hmass
    rfl

end ProtocolAdapter

/-! ## S2: process realization (specification line 890) -/

section ProcessRealization

/-- Specification line 890: completely positive, trace-nonincreasing linear maps that act on the
represented states with the source weights and compose as the source processes compose. -/
def ProcessRealizationGoal (D : OperationalData) (dim : D.Obj → ℕ)
    (stateMap : (A : D.Obj) → D.State A → Mat (dim A)) : Prop :=
  ∃ maps : (A B : D.Obj) → D.Process A B → (Mat (dim A) →ₗ[ℂ] Mat (dim B)),
    (∀ A B f, CompletelyPositive (maps A B f) ∧ TraceNonIncreasing (maps A B f)) ∧
    (∀ A B f s, maps A B f (stateMap A s) = (D.weight f s : ℂ) • stateMap B (D.act f s)) ∧
    (∀ A B C f g, maps A C (D.compose g f) = (maps B C g).comp (maps A B f))

/-- Every quantum realization satisfies the predicate at its own dimensions and states: its
fields `positivity`, `trace_bound`, `source_action` and `composition` give the three clauses. -/
theorem processRealizationGoal_of_realization {D : OperationalData}
    (r : QuantumRealization D) :
    ProcessRealizationGoal D r.dim (fun A s => (r.states A s).val) :=
  ⟨r.maps, fun A B f => ⟨r.positivity A B f, r.trace_bound A B f⟩, r.source_action,
    r.composition⟩

/-- The finite quantum source satisfies the predicate at its identity representation. -/
theorem processRealizationGoal_quantumData :
    ProcessRealizationGoal quantumData (fun A => A.1) (fun _ s => s.val) :=
  processRealizationGoal_of_realization quantumData_realization

/-- At the zero state map every source satisfies the predicate through the zero maps, so the
predicate has content only at the state map of a representation. -/
theorem processRealizationGoal_zero (D : OperationalData) (dim : D.Obj → ℕ) :
    ProcessRealizationGoal D dim (fun _ _ => 0) :=
  ⟨fun _ _ _ => 0, fun _ _ _ => ⟨cp_zero, tni_zero⟩,
    fun _ _ _ _ => by simp only [LinearMap.zero_apply, smul_zero],
    fun _ _ _ _ _ => (LinearMap.zero_comp 0).symm⟩

/-- The finite quantum source with every process weight replaced by its square. The weights stay
in the unit interval and stay multiplicative along composition, so the minimal laws hold, and the
states and effects keep their Born probabilities. -/
def squaredWeightData : OperationalData :=
  { quantumData with weight := fun f s => (quantumData.weight f s) ^ 2 }

/-- The squared-weight source satisfies `OperationalLaws`: seven clauses are those of the quantum
source, and the two weight clauses follow from `0 ≤ w ≤ 1` and from `(w₁ w₂) ^ 2 = w₁ ^ 2 w₂ ^ 2`. -/
theorem squaredWeightData_operationalLaws : OperationalLaws squaredWeightData := by
  obtain ⟨hcond, hprob, hunit, hsep, hmix, hident, hcomp, hweight, hmul⟩ :=
    quantumData_operationalLaws
  refine ⟨hcond, hprob, hunit, hsep, hmix, hident, hcomp, ?_, ?_⟩
  · intro A B f s
    obtain ⟨h0, h1⟩ := hweight A B f s
    exact ⟨sq_nonneg _, pow_le_one₀ h0 h1⟩
  · intro A B C f g s
    show (quantumData.weight (quantumData.compose g f) s) ^ 2 =
      (quantumData.weight f s) ^ 2 * (quantumData.weight g (quantumData.act f s)) ^ 2
    rw [hmul A B C f g s, mul_pow]

/-- The squared-weight source has the identity state and effect representation. -/
theorem squaredWeightData_stateEffectRepresentation :
    StateEffectRepresentationGoal squaredWeightData :=
  ⟨fun A => A.1, fun A => A.2, fun _ => Equiv.refl _, fun _ => Equiv.refl _,
    fun _ _ _ => rfl⟩

/-- The squared-weight source fails the predicate at its representation. The compression `f` onto
the first coordinate of the qubit has weight `ρ₀₀` at a density `ρ`, so a realizing map `L` has
`(L ρ)₀₀ = ρ₀₀ ^ 2`; the basis densities give `1` and `0`, and their even mixture gives `1 / 4`
where linearity of `L` gives `1 / 2`. -/
theorem squaredWeightData_not_processRealization :
    ¬ ProcessRealizationGoal squaredWeightData (fun A => A.1) (fun _ s => s.val) := by
  rintro ⟨maps, -, hact, -⟩
  let f : QProc qubit.1 qubit.1 :=
    UniversalObservation.Reconstruction.sourceCoordinateProc qubit qubitZero
  have hmap : ∀ a : Mat qubit.1,
      f.map a = UniversalObservation.Reconstruction.sourceCoordinateMap qubitZero a :=
    fun _ => rfl
  have key : ∀ ρ : Density qubit.1, maps qubit qubit f ρ.val qubitZero qubitZero =
      ((ρ.val qubitZero qubitZero).re : ℂ) * ρ.val qubitZero qubitZero := by
    intro ρ
    have h1 : maps qubit qubit f ρ.val =
        (((tr (f.map ρ.val)).re ^ 2 : ℝ) : ℂ) • (f.out ρ).val := hact qubit qubit f ρ
    have h2 : f.map ρ.val = (((tr (f.map ρ.val)).re : ℝ) : ℂ) • (f.out ρ).val := f.out_spec ρ
    have h3 : maps qubit qubit f ρ.val = (((tr (f.map ρ.val)).re : ℝ) : ℂ) • f.map ρ.val := by
      rw [h1, pow_two, Complex.ofReal_mul, mul_smul, ← h2]
    rw [h3, Matrix.smul_apply, hmap,
      UniversalObservation.Reconstruction.sourceCoordinateMap_trace,
      UniversalObservation.Reconstruction.sourceCoordinateMap_apply, if_pos rfl, one_mul,
      mul_one, smul_eq_mul]
  have hq : qubitOne ≠ qubitZero := by decide
  have e0 : (basisState qubit qubitZero).val qubitZero qubitZero = 1 := by
    rw [basisState_val, single_one_apply, if_pos ⟨rfl, rfl⟩]
  have e1 : (basisState qubit qubitOne).val qubitZero qubitZero = 0 := by
    rw [basisState_val, single_one_apply, if_neg fun h => hq h.1]
  have hmix := densityMix_val (p := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
    (basisState qubit qubitZero) (basisState qubit qubitOne)
  have hlin := congrArg (fun a : Mat qubit.1 => maps qubit qubit f a qubitZero qubitZero) hmix
  simp only [map_add, map_smul, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at hlin
  rw [key, key, key, hmix] at hlin
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, e0, e1] at hlin
  norm_num at hlin

/-- Specification docstring of line 890: process completeness does not follow from a state-only
representation. A source with the minimal laws and a state and effect representation fails the
predicate at the state map of that representation. -/
theorem processRealizationGoal_not_of_stateRepresentation :
    ∃ D : OperationalData, OperationalLaws D ∧
      ∃ (dim : D.Obj → ℕ) (states : (A : D.Obj) → D.State A ≃ Density (dim A))
        (effects : (A : D.Obj) → D.Test A ≃ Effect (dim A)),
        (∀ A, 0 < dim A) ∧
        (∀ A s e, D.prob e s = (tr ((states A s).val * (effects A e).val)).re) ∧
        ¬ ProcessRealizationGoal D dim (fun A s => (states A s).val) :=
  ⟨squaredWeightData, squaredWeightData_operationalLaws, fun A => A.1, fun _ => Equiv.refl _,
    fun _ => Equiv.refl _, fun A => A.2, fun _ _ _ => rfl,
    squaredWeightData_not_processRealization⟩

end ProcessRealization

/-! ## S3: the heat bound from the thermal balance (specification line 989) -/

/-- Specification line 989, the same statement: from `β * q = drop + corr + rel` with
`0 ≤ corr` and `0 ≤ rel`, `drop ≤ β * q`. -/
theorem heat_bound_from_balance {β q drop corr rel : ℝ}
    (h : β * q = drop + corr + rel) (hc : 0 ≤ corr) (hd : 0 ≤ rel) : drop ≤ β * q := by
  rw [h]
  exact le_add_of_le_of_nonneg (le_add_of_nonneg_right hc) hd

/-- The bound on every thermal experiment of the specification carrier: the entropy drop of the
system is at most `β` times the heat released into the reservoir. The balance and both signs are
`thermalIdentityGoal`. -/
theorem entropyDrop_le_beta_mul_heat {n m : ℕ}
    (e : UniversalObservation.Reconstruction.ThermalExperiment n m) :
    UniversalObservation.Reconstruction.entropyDrop e ≤
      e.β * UniversalObservation.Reconstruction.heat e := by
  obtain ⟨hbal, hcorr, hrel⟩ := UniversalObservation.Reconstruction.thermalIdentityGoal n m e
  exact heat_bound_from_balance hbal hcorr hrel

/-- The divided form at the positive inverse temperature of the experiment. -/
theorem entropyDrop_div_beta_le_heat {n m : ℕ}
    (e : UniversalObservation.Reconstruction.ThermalExperiment n m) :
    UniversalObservation.Reconstruction.entropyDrop e / e.β ≤
      UniversalObservation.Reconstruction.heat e := by
  rw [div_le_iff₀ e.β_positive, mul_comm]
  exact entropyDrop_le_beta_mul_heat e

/-! ## S4: the operational demand problem (specification line 1006) -/

/-- Specification line 1006: the source task of jointly prescribing the probabilities of
specified tests. A demand is a test with a prescribed value, a candidate is a state, and a state
satisfies a demand if its probability on the test equals the value. -/
def operationalDemand (D : OperationalData) (A : D.Obj) :
    UniversalObservation.Demand.Problem (D.Test A × ℝ) (D.State A) where
  sat s i := D.prob i.1 s = i.2

theorem operationalDemand_sat (D : OperationalData) (A : D.Obj) (s : D.State A)
    (i : D.Test A × ℝ) : (operationalDemand D A).sat s i ↔ D.prob i.1 s = i.2 := Iff.rfl

/-- The full statistics of a state, as a set of demands. -/
def stateStatistics (D : OperationalData) {A : D.Obj} (s : D.State A) :
    Set (D.Test A × ℝ) :=
  Set.range fun e => (e, D.prob e s)

/-- Every state satisfies its own full statistics. -/
theorem operationalDemand_statistics_good (D : OperationalData) {A : D.Obj} (s : D.State A) :
    UniversalObservation.Demand.Good (operationalDemand D A) (stateStatistics D s) :=
  ⟨s, by
    rintro _ ⟨e, rfl⟩
    rfl⟩

/-- Under the separation clause of `OperationalLaws`, the state is the only candidate that
satisfies its full statistics. -/
theorem operationalDemand_statistics_witnesses (D : OperationalData) (hD : OperationalLaws D)
    {A : D.Obj} (s : D.State A) :
    UniversalObservation.Demand.Witnesses (operationalDemand D A) (stateStatistics D s) =
      {s} := by
  ext t
  constructor
  · intro ht
    rw [Set.mem_singleton_iff]
    exact hD.2.2.2.1 A t s fun e => ht (e, D.prob e s) ⟨e, rfl⟩
  · intro ht
    rw [Set.mem_singleton_iff] at ht
    subst ht
    rintro _ ⟨e, rfl⟩
    rfl

/-! ## S5: the Born-rule demand problem (specification line 1010) -/

/-- Specification line 1010: the demand problem of the Born rule in dimension `n`. A demand is an
effect with a prescribed value, a candidate is a density, and a density satisfies a demand if the
real part of the trace of its product with the effect equals the value. -/
def quantumDemand (n : ℕ) : UniversalObservation.Demand.Problem (Effect n × ℝ) (Density n) where
  sat s i := (tr (s.val * i.1.val)).re = i.2

theorem quantumDemand_sat (n : ℕ) (s : Density n) (i : Effect n × ℝ) :
    (quantumDemand n).sat s i ↔ (tr (s.val * i.1.val)).re = i.2 := Iff.rfl

/-- The Born-rule problem is the operational demand problem of the finite quantum source at the
system of that dimension. -/
theorem quantumDemand_eq_operationalDemand (A : QSys) :
    quantumDemand A.1 = operationalDemand quantumData A := rfl

/-- The full Born statistics of a density, as a set of demands. -/
def bornStatistics {n : ℕ} (ρ : Density n) : Set (Effect n × ℝ) :=
  Set.range fun e => (e, (tr (ρ.val * e.val)).re)

/-- A density is the only candidate that satisfies its full Born statistics. -/
theorem quantumDemand_statistics_witnesses {n : ℕ} (ρ : Density n) :
    UniversalObservation.Demand.Witnesses (quantumDemand n) (bornStatistics ρ) = {ρ} := by
  ext σ
  constructor
  · intro hσ
    rw [Set.mem_singleton_iff]
    exact density_ext_of_effects σ ρ fun e => hσ (e, (tr (ρ.val * e.val)).re) ⟨e, rfl⟩
  · intro hσ
    rw [Set.mem_singleton_iff] at hσ
    subst hσ
    rintro _ ⟨e, rfl⟩
    rfl

/-! ## S6: transport of the demand task (specification line 1057) -/

/-- Specification line 1057: every quantum realization transports the operational demand problem
of each system onto the Born-rule problem of its dimension, with the realization's state and
effect bijections. -/
def QuantumDemandTransportGoal : Prop :=
  ∀ (D : OperationalData) (r : QuantumRealization D) (A : D.Obj),
    ∃ e : UniversalObservation.Transport.DemandIso (operationalDemand D A)
        (quantumDemand (r.dim A)),
      (∀ s, e.witnesses s = r.states A s) ∧
      ∀ i, e.demands i = (r.effects A i.1, i.2)

/-- The demand isomorphism of a realization at one system: states go through `r.states A`,
demands through `r.effects A` on the test and the identity on the value, and the field
`probabilities` of the realization gives the satisfaction law. -/
def realizationDemandIso {D : OperationalData} (r : QuantumRealization D) (A : D.Obj) :
    UniversalObservation.Transport.DemandIso (operationalDemand D A) (quantumDemand (r.dim A))
    where
  demands := (r.effects A).prodCongr (Equiv.refl ℝ)
  witnesses := r.states A
  satisfaction s i := by
    show (tr ((r.states A s).val * (r.effects A i.1).val)).re = i.2 ↔ D.prob i.1 s = i.2
    rw [r.probabilities A s i.1]

theorem quantumDemandTransportGoal : QuantumDemandTransportGoal :=
  fun _ r A => ⟨realizationDemandIso r A, fun _ => rfl, fun _ => rfl⟩

/-- A demand set of the source is good iff its image under the realization is good in the
Born-rule problem of the realized dimension. -/
theorem operationalDemand_good_iff_quantumDemand {D : OperationalData}
    (r : QuantumRealization D) (A : D.Obj) (S : Set (D.Test A × ℝ)) :
    UniversalObservation.Demand.Good (quantumDemand (r.dim A))
        ((realizationDemandIso r A).demands '' S) ↔
      UniversalObservation.Demand.Good (operationalDemand D A) S :=
  (realizationDemandIso r A).good_transport S

end OperatorKO7.Meta.BoundaryObserver.SpecCompletion
