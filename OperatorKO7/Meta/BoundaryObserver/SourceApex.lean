import OperatorKO7.Meta.BoundaryObserver.BoundaryReconstruction
import OperatorKO7.Meta.BoundaryObserver.ProtocolResolution
import OperatorKO7.Meta.BoundaryObserver.DemandCompletion

/-!
# Same-source operational and quantum apex

Graph: notes/universal-roadmap/UNIVERSAL-OBSERVATION-PROOF-GRAPH.md, M5_8.
Author: bt-m58. Compiler owner: claude-two-voids.
LASOT 2.3 was read in full at OperatorKO7/LEAN_AGENT_AUDIT_SOURCE_OF_TRUTH.md.
Status: source candidate; kernel validation belongs to the supervisor.

The native source contract evaluates the actual conditional retained-record statistics
of recorded operations. The quantum comparison retains the identical source,
candidate, preparation, record and output test.
-/

set_option autoImplicit false

noncomputable section
open Matrix
open scoped BigOperators Classical

namespace UniversalObservation.Protocol

/-! The protocol names preserve the native production declarations and their scopes. -/
export OperatorKO7.Meta.BoundaryObserver.ProtocolResolution
  (ConditionalProtocol HistoryBank stoppedMass conditionalJointInfo
   conditionalMI conditionalExpectedCost LocalCapacityBound
   conditionalJointInfo_eq_conditionalMI conditionalMI_le_expectedCost)

end UniversalObservation.Protocol

namespace UniversalObservation.Reconstruction

open OperatorKO7.Meta.BoundaryObserver.BoundaryReconstruction
open OperatorKO7.Meta.BoundaryObserver.BoundaryReconstruction.Operational

/-- One native operation with its retained outcome and conditional post-state. -/
structure RecordedProcess (D : OperationalData) (A : D.Obj) (R : Type) [Fintype R] where
  total : D.Process A A
  branch : R → D.Process A A
  total_weight : ∀ s, D.weight total s = 1
  normalized : ∀ s, ∑ y, D.weight (branch y) s = 1
  forget_record : ∀ s e, (∑ y, D.weight (branch y) s * D.prob e (D.act (branch y) s)) =
    D.prob e (D.act total s)

def recordedStat {D : OperationalData} {A : D.Obj} {R : Type} [Fintype R]
    (p : RecordedProcess D A R) (i : D.State A × R × D.Test A) : ℝ :=
  D.weight (p.branch i.2.1) i.1 * D.prob i.2.2 (D.act (p.branch i.2.1) i.1)

/-- The contract's source, every candidate and every demand use these same maps. -/
structure SourceBinding (D : OperationalData) (A : D.Obj) (R : Type) [Fintype R]
    (p : RecordedProcess D A R) (C : Completion.SourceContract) where
  native : C.Process ≃ RecordedProcess D A R
  input : C.Input ≃ (D.State A × R × D.Test A)
  record : C.Output ≃ ℝ
  source : native C.source = p
  evaluation : ∀ f i, record (C.evaluate f i) = recordedStat (native f) (input i)

/-- Constant selectors provide one genuine native candidate on all selected demands.
The source evaluator remains the weighted branch probability for every input.
Resource coordinates remain attached to the native process and are supplied separately. -/
def recordedSourceContract {D : OperationalData} {A : D.Obj} {R : Type} [Fintype R]
    (p : RecordedProcess D A R) (cost : RecordedProcess D A R → ℕ → ℝ) :
    Completion.SourceContract where
  Process := RecordedProcess D A R
  Input := D.State A × R × D.Test A
  Output := ℝ
  Witness := RecordedProcess D A R
  source := p
  evaluate := recordedStat
  interpret := id
  allowed := fun _ => {s | ∀ i j, s i = s j}
  combines := fun _ _ _ => True
  assemble := fun _ s ws =>
    if h : Nonempty (D.State A × R × D.Test A) then
      ws (s (Classical.choice h))
    else p
  cost := cost

/-- Constant-source selections assemble an actual candidate and preserve each
licensed weighted outcome statistic, including all inputs outside the initial ensemble. -/
theorem recordedSourceContract_combinerLaw {D : OperationalData} {A : D.Obj}
    {R : Type} [Fintype R] (p : RecordedProcess D A R)
    (cost : RecordedProcess D A R → ℕ → ℝ) :
    (recordedSourceContract p cost).combinerLaw := by
  intro demands k s ws hallowed _ hw i hi
  change ∀ u v, s u = s v at hallowed
  change recordedStat
    (if h : Nonempty (D.State A × R × D.Test A) then
      ws (s (Classical.choice h)) else p) i = recordedStat p i
  have hInput : Nonempty (D.State A × R × D.Test A) := ⟨i⟩
  rw [dif_pos hInput, hallowed (Classical.choice hInput) i]
  exact hw i hi

/-- The native process and evaluator are tied to the same retained-outcome source
by identity equivalences, rather than by an endpoint-state comparison. -/
def recordedSourceBinding {D : OperationalData} {A : D.Obj} {R : Type} [Fintype R]
    (p : RecordedProcess D A R) (cost : RecordedProcess D A R → ℕ → ℝ) :
    SourceBinding D A R p (recordedSourceContract p cost) where
  native := Equiv.refl _
  input := Equiv.refl _
  record := Equiv.refl _
  source := rfl
  evaluation := by
    intro f i
    rfl

noncomputable def quantumRecordedStat {D : OperationalData} {A : D.Obj} {R : Type} [Fintype R]
    (r : QuantumRealization D) (p : RecordedProcess D A R) (i : D.State A × R × D.Test A) : ℝ :=
  (tr (r.maps A A (p.branch i.2.1) (r.states A i.1).val * (r.effects A i.2.2).val)).re

def SourceDemandQuantumGoal (D : OperationalData) (A : D.Obj) (R : Type) [Fintype R]
    (p : RecordedProcess D A R) (C : Completion.SourceContract)
    (b : SourceBinding D A R p C) (r : QuantumRealization D) : Prop :=
  ∀ w i, C.problem.sat w i ↔
    quantumRecordedStat r (b.native (C.interpret w)) (b.input i) =
      quantumRecordedStat r p (b.input i)

/-- Full source-action equality determines the weighted outcome and post-state test
for every input, even for zero-weight branches. -/
theorem quantumRecordedStat_eq_recordedStat {D : OperationalData} {A : D.Obj}
    {R : Type} [Fintype R] (r : QuantumRealization D)
    (p : RecordedProcess D A R) (i : D.State A × R × D.Test A) :
    quantumRecordedStat r p i = recordedStat p i := by
  rcases i with ⟨s, y, e⟩
  change (tr (r.maps A A (p.branch y) (r.states A s).val *
    (r.effects A e).val)).re =
    D.weight (p.branch y) s * D.prob e (D.act (p.branch y) s)
  rw [r.source_action A A (p.branch y) s]
  simp only [Matrix.smul_mul, tr, Matrix.trace_smul, smul_eq_mul,
    Complex.re_ofReal_mul, ← r.probabilities]

/-- Quantum satisfaction is exactly the original source-demand equation, without
any premise equating a target protocol or a separate process to the source. -/
theorem sourceDemandQuantumGoal (D : OperationalData) (A : D.Obj)
    (R : Type) [Fintype R] (p : RecordedProcess D A R)
    (C : Completion.SourceContract) (b : SourceBinding D A R p C)
    (r : QuantumRealization D) :
    SourceDemandQuantumGoal D A R p C b r := by
  intro w i
  change C.evaluate (C.interpret w) i = C.evaluate C.source i ↔
    quantumRecordedStat r (b.native (C.interpret w)) (b.input i) =
      quantumRecordedStat r p (b.input i)
  constructor
  · intro h
    have hc : b.record (C.evaluate (C.interpret w) i) =
        b.record (C.evaluate C.source i) := congrArg b.record h
    rw [b.evaluation (C.interpret w) i, b.evaluation C.source i,
      b.source] at hc
    simpa only [quantumRecordedStat_eq_recordedStat] using hc
  · intro h
    apply b.record.injective
    rw [b.evaluation (C.interpret w) i, b.evaluation C.source i, b.source]
    simpa only [quantumRecordedStat_eq_recordedStat] using h


/-- A spectral presentation defines matrix entropy without an invented library API. -/
structure SpectralState (I : Type) [Fintype I] [DecidableEq I] where
  eigen : I → ℝ
  eigen_nonnegative : ∀ i, 0 ≤ eigen i
  eigen_total : ∑ i, eigen i = 1
  basis : Matrix I I ℂ
  basis_left : basis.conjTranspose * basis = 1
  basis_right : basis * basis.conjTranspose = 1

noncomputable def spectralMatrix {I : Type} [Fintype I] [DecidableEq I]
    (s : SpectralState I) : Matrix I I ℂ :=
  s.basis * Matrix.diagonal (fun i => (s.eigen i : ℂ)) * s.basis.conjTranspose

noncomputable def spectralEntropy {I : Type} [Fintype I] [DecidableEq I]
    (s : SpectralState I) : ℝ :=
  - ∑ i, if s.eigen i = 0 then 0 else s.eigen i * Real.log (s.eigen i)

noncomputable def partition (β : ℝ) {m : ℕ} (energy : Fin m → ℝ) : ℝ :=
  ∑ r, Real.exp (-β * energy r)
noncomputable def bathWeight (β : ℝ) {m : ℕ} (energy : Fin m → ℝ) (r : Fin m) : ℝ :=
  Real.exp (-β * energy r) / partition β energy

/-- Physical premises concern states and a unitary, not the desired heat inequality. -/
structure ThermalExperiment (n m : ℕ) where
  system_positive : 0 < n
  bath_positive : 0 < m
  β : ℝ
  β_positive : 0 < β
  energy : Fin m → ℝ
  initialSystem : SpectralState (Fin n)
  initialBath : SpectralState (Fin m)
  thermal_matrix : spectralMatrix initialBath =
    Matrix.diagonal (fun r => (bathWeight β energy r : ℂ))
  unitary : Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ
  unitary_left : unitary.conjTranspose * unitary = 1
  unitary_right : unitary * unitary.conjTranspose = 1
  finalSystem : SpectralState (Fin n)
  finalBath : SpectralState (Fin m)
  finalJoint : SpectralState (Fin n × Fin m)
  joint_rule : ∀ (i j : Fin n × Fin m), spectralMatrix finalJoint i j =
    ∑ a : Fin n × Fin m, ∑ b : Fin n × Fin m,
      unitary i a * (spectralMatrix initialSystem a.1 b.1 *
        spectralMatrix initialBath a.2 b.2) * star (unitary j b)
  marginal_system : ∀ i j, spectralMatrix finalSystem i j =
    ∑ r, spectralMatrix finalJoint (i,r) (j,r)
  marginal_bath : ∀ r s, spectralMatrix finalBath r s =
    ∑ i, spectralMatrix finalJoint (i,r) (i,s)

noncomputable def heat {n m : ℕ} (e : ThermalExperiment n m) : ℝ :=
  ∑ r, e.energy r * ((spectralMatrix e.finalBath r r).re -
    (spectralMatrix e.initialBath r r).re)
noncomputable def entropyDrop {n m : ℕ} (e : ThermalExperiment n m) : ℝ :=
  spectralEntropy e.initialSystem - spectralEntropy e.finalSystem
noncomputable def correlation {n m : ℕ} (e : ThermalExperiment n m) : ℝ :=
  spectralEntropy e.finalSystem + spectralEntropy e.finalBath - spectralEntropy e.finalJoint
noncomputable def bathRelativeEntropy {n m : ℕ} (e : ThermalExperiment n m) : ℝ :=
  -spectralEntropy e.finalBath -
    ∑ r, (spectralMatrix e.finalBath r r).re * Real.log (bathWeight e.β e.energy r)

/-- The actual initial ensemble, stopped histories, final states and retained record. -/
structure SourceProtocolData (D : OperationalData) (A : D.Obj) (R H0 Z Act Y : Type)
    [Fintype H0] [Fintype Z] [Fintype Act] [Fintype Y] where
  protocol : Protocol.ConditionalProtocol H0 Z Act Y
  rounds : ℕ
  bank : List (List (Act × Y))
  bank_complete : Protocol.HistoryBank rounds bank
  initial : H0 → Z → D.State A
  final : H0 → List (Act × Y) → Z → D.State A
  record : List (Act × Y) → R

/-- This law identifies the complete source operation on every supported preparation,
including outcome records and all post-state tests. It must be proved from the native run. -/
def SourceProtocolLink {D : OperationalData} {A : D.Obj} {R H0 Z Act Y : Type}
    [Fintype R] [DecidableEq R] [Fintype H0] [Fintype Z] [Fintype Act] [Fintype Y]
    (p : RecordedProcess D A R) (d : SourceProtocolData D A R H0 Z Act Y) : Prop :=
  ∀ h0, 0 < d.protocol.initialRecord.mass h0 → ∀ z y e,
    (d.protocol.given h0).prior.mass z * recordedStat p (d.initial h0 z, y, e) =
      (d.bank.map (fun h => if d.record h = y then
        Protocol.stoppedMass (d.protocol.given h0) d.rounds z h * D.prob e (d.final h0 h z)
        else 0)).sum

/-- One unitary and the actual initial reservoir define this entire input-output map. -/
noncomputable def thermalChannel {n m : ℕ} (e : ThermalExperiment n m) (a : Mat n) : Mat n :=
  fun i j => ∑ r : Fin m, ∑ x : Fin n × Fin m, ∑ y : Fin n × Fin m,
    e.unitary (i,r) x * (a x.1 y.1 * spectralMatrix e.initialBath x.2 y.2) *
      star (e.unitary (j,r) y)

/-- Equality of full maps and outcome operations is stronger than equality at one state.
The projectors read records already retained in the output; no extra disturbance is omitted. -/
def ImplementsInstrument (D : OperationalData) (A : D.Obj) (R : Type) [Fintype R]
    (p : RecordedProcess D A R) (r : QuantumRealization D) {m : ℕ}
    (e : ThermalExperiment (r.dim A) m) (recordProjector : R → Mat (r.dim A)) : Prop :=
  (∀ y, dagger (recordProjector y) = recordProjector y ∧
    recordProjector y * recordProjector y = recordProjector y) ∧
  (∀ y z, y ≠ z → recordProjector y * recordProjector z = 0) ∧
  (∑ y, recordProjector y) = 1 ∧
  (∀ a, thermalChannel e a = r.maps A A p.total a) ∧
  (∀ y a, recordProjector y * thermalChannel e a * dagger (recordProjector y) =
    r.maps A A (p.branch y) a) ∧
  ∀ a, (∑ y, recordProjector y * thermalChannel e a * dagger (recordProjector y)) =
    thermalChannel e a

/-- Same-source instance target. Existence is not asserted for arbitrary processes or baths.
Cost coordinate 0 is heat in the declared energy unit; coordinate 1 is protocol cost.
The output system includes the retained record; M5.5 supplies any required enlargement. -/
def ApexInstanceGoal (D : OperationalData) (A : D.Obj) (R H0 Z Act Y : Type)
    [Fintype R] [DecidableEq R] [Fintype H0] [Fintype Z] [Fintype Act] [Fintype Y]
    (C : Completion.SourceContract) (p : RecordedProcess D A R)
    (b : SourceBinding D A R p C) (d : SourceProtocolData D A R H0 Z Act Y) (m : ℕ) : Prop :=
  OperationalLaws D ∧ Completion.CoreGoal C ∧ C.combinerLaw ∧ SourceProtocolLink p d ∧
  (Protocol.conditionalJointInfo d.protocol d.rounds d.bank =
    Protocol.conditionalMI d.protocol d.rounds d.bank) ∧
  (∀ κ : ℝ, 0 ≤ κ →
    (∀ h0, 0 < d.protocol.initialRecord.mass h0 → Protocol.LocalCapacityBound (d.protocol.given h0) κ) →
    Protocol.conditionalMI d.protocol d.rounds d.bank ≤
      κ * Protocol.conditionalExpectedCost d.protocol d.rounds d.bank) ∧
  ∃ r : QuantumRealization D, ∃ e : ThermalExperiment (r.dim A) m,
    ∃ recordProjector : R → Mat (r.dim A),
    ImplementsInstrument D A R p r e recordProjector ∧
    SourceDemandQuantumGoal D A R p C b r ∧
    (∀ i j, spectralMatrix e.initialSystem i j =
      ∑ h0, ∑ z, (d.protocol.initialJoint.mass (h0,z) : ℂ) * (r.states A (d.initial h0 z)).val i j) ∧
    (∀ i j, spectralMatrix e.finalSystem i j =
      ∑ h0, ∑ z, (d.protocol.initialJoint.mass (h0,z) : ℂ) *
        (r.states A (D.act p.total (d.initial h0 z))).val i j) ∧
    (∀ y, (tr (recordProjector y * spectralMatrix e.finalSystem)).re =
      ∑ h0, ∑ z, d.protocol.initialJoint.mass (h0,z) * D.weight (p.branch y) (d.initial h0 z)) ∧
    C.cost C.source 0 = heat e ∧
    C.cost C.source 1 = Protocol.conditionalExpectedCost d.protocol d.rounds d.bank ∧
    e.β * heat e = entropyDrop e + correlation e + bathRelativeEntropy e ∧
    0 ≤ correlation e ∧ 0 ≤ bathRelativeEntropy e

/-- The recorded native source, conditional entropy telescope and finite
capacity bound retain their original hypotheses and the same protocol data.
An actual source-to-protocol operation law and physical realization are separate obligations. -/
theorem sourceApex_prephysical
    (D : OperationalData) (A : D.Obj) (R H0 Z Act Y : Type)
    [Fintype R] [Fintype H0] [Fintype Z] [Fintype Act] [Fintype Y]
    (p : RecordedProcess D A R) (cost : RecordedProcess D A R → ℕ → ℝ)
    (d : SourceProtocolData D A R H0 Z Act Y) :
    Completion.CoreGoal (recordedSourceContract p cost) ∧
    (recordedSourceContract p cost).combinerLaw ∧
    (Protocol.conditionalJointInfo d.protocol d.rounds d.bank =
      Protocol.conditionalMI d.protocol d.rounds d.bank) ∧
    (∀ κ : ℝ, 0 ≤ κ →
      (∀ h0, 0 < d.protocol.initialRecord.mass h0 →
        Protocol.LocalCapacityBound (d.protocol.given h0) κ) →
      Protocol.conditionalMI d.protocol d.rounds d.bank ≤
        κ * Protocol.conditionalExpectedCost d.protocol d.rounds d.bank) := by
  refine ⟨Completion.source_observation_repair_core _,
    recordedSourceContract_combinerLaw p cost,
    Protocol.conditionalJointInfo_eq_conditionalMI
      d.protocol d.rounds d.bank d.bank_complete, ?_⟩
  intro κ _ hcapacity
  exact Protocol.conditionalMI_le_expectedCost
    d.protocol d.rounds d.bank d.bank_complete κ hcapacity



/-! ## M5.8: Native one-round retained-outcome protocol

The initial record retains preparation metadata. The one-round channel samples
the actual branch weights. Every output test reads the conditional post-state.
The empty history has zero stopped mass and a total record derived from laws.
-/

section OneRoundNative

open OperatorKO7.Meta.BoundaryObserver.ProtocolResolution

/-- Every normalized finite law has an inhabited carrier. -/
theorem finiteLaw_carrier_nonempty {X : Type} [Fintype X] (q : FiniteLaw X) :
    Nonempty X := by
  classical
  by_contra hn
  have hz : (∑ x : X, q.mass x) = (0 : ℝ) := by
    apply Finset.sum_eq_zero
    intro x _
    exact False.elim (hn ⟨x⟩)
  exact zero_ne_one (hz.symm.trans q.total)

/-- Native conditional branch probabilities retain every zero-weight outcome. -/
noncomputable def sourceOneRoundOutcomeLaw
    {D : OperationalData} {A : D.Obj} {R : Type} [Fintype R]
    (hL : OperationalLaws D) (p : RecordedProcess D A R)
    (s : D.State A) : FiniteLaw R where
  mass y := D.weight (p.branch y) s
  nonnegative y := (hL.2.2.2.2.2.2.2.1 A A (p.branch y) s).1
  total := p.normalized s

/-- A zero-weight branch has zero retained probability for every final test. -/
theorem sourceOneRound_zero_weight
    {D : OperationalData} {A : D.Obj} {R : Type} [Fintype R]
    (hL : OperationalLaws D) (p : RecordedProcess D A R)
    (s : D.State A) (y : R)
    (hy : D.weight (p.branch y) s = 0) :
    (sourceOneRoundOutcomeLaw hL p s).mass y = 0 ∧
      ∀ e : D.Test A, recordedStat p (s, y, e) = 0 := by
  constructor
  · exact hy
  · intro e
    change D.weight (p.branch y) s *
      D.prob e (D.act (p.branch y) s) = 0
    rw [hy, zero_mul]

/-- A single unit action samples the true source outcome law at each preparation.
The explicit nonnegative cost input is not identified with physical heat. -/
noncomputable def sourceOneRoundGiven
    {D : OperationalData} {A : D.Obj} {R H0 Z : Type}
    [Fintype R] [Fintype H0] [Fintype Z]
    (hL : OperationalLaws D) (p : RecordedProcess D A R)
    (prior : H0 → FiniteLaw Z) (prepare : H0 → Z → D.State A)
    (charge : H0 → List (Unit × R) → ℝ)
    (hcharge : ∀ h0 h, 0 ≤ charge h0 h)
    (h0 : H0) : FiniteProtocol Z Unit R where
  prior := prior h0
  policy _ := unitLaw
  observation _ _ z := sourceOneRoundOutcomeLaw hL p (prepare h0 z)
  stop := fun h => !h.isEmpty
  cost := fun h _ => charge h0 h
  cost_nonnegative := fun h _ => hcharge h0 h

/-- Initial joint mass is the product of initial record mass and its own
conditional target prior, including zero-mass initial records. -/
noncomputable def sourceOneRoundConditional
    {D : OperationalData} {A : D.Obj} {R H0 Z : Type}
    [Fintype R] [Fintype H0] [Fintype Z]
    (hL : OperationalLaws D) (p : RecordedProcess D A R)
    (recordLaw : FiniteLaw H0) (prior : H0 → FiniteLaw Z)
    (prepare : H0 → Z → D.State A)
    (charge : H0 → List (Unit × R) → ℝ)
    (hcharge : ∀ h0 h, 0 ≤ charge h0 h) :
    ConditionalProtocol H0 Z Unit R where
  initialRecord := recordLaw
  initialJoint :=
    { mass := fun hz => recordLaw.mass hz.1 * (prior hz.1).mass hz.2
      nonnegative := fun hz =>
        mul_nonneg (recordLaw.nonnegative hz.1) ((prior hz.1).nonnegative hz.2)
      total := by
        rw [Fintype.sum_prod_type]
        calc
          (∑ h0, ∑ z, recordLaw.mass h0 * (prior h0).mass z) =
              ∑ h0, recordLaw.mass h0 := by
            apply Finset.sum_congr rfl
            intro h0 _
            rw [← Finset.mul_sum, (prior h0).total, mul_one]
          _ = 1 := recordLaw.total }
  given := fun h0 => sourceOneRoundGiven hL p prior prepare charge hcharge h0
  initial_joint := by
    intro h0 z
    rfl

/-- The empty record is selected from the normalized initial and outcome laws. -/
noncomputable def sourceOneRoundEmptyRecord
    {D : OperationalData} {A : D.Obj} {R H0 Z : Type}
    [Fintype R] [Fintype H0] [Fintype Z]
    (hL : OperationalLaws D) (p : RecordedProcess D A R)
    (recordLaw : FiniteLaw H0) (prior : H0 → FiniteLaw Z)
    (prepare : H0 → Z → D.State A) : R := by
  let h0 : H0 := Classical.choice (finiteLaw_carrier_nonempty recordLaw)
  let z : Z := Classical.choice (finiteLaw_carrier_nonempty (prior h0))
  exact Classical.choice
    (finiteLaw_carrier_nonempty (sourceOneRoundOutcomeLaw hL p (prepare h0 z)))

/-- All source histories have defined records and final states. Singleton
histories contain the true branch label and its conditional post-state. -/
noncomputable def sourceOneRoundData
    {D : OperationalData} {A : D.Obj} {R H0 Z : Type}
    [Fintype R] [Fintype H0] [Fintype Z]
    (hL : OperationalLaws D) (p : RecordedProcess D A R)
    (recordLaw : FiniteLaw H0) (prior : H0 → FiniteLaw Z)
    (prepare : H0 → Z → D.State A)
    (charge : H0 → List (Unit × R) → ℝ)
    (hcharge : ∀ h0 h, 0 ≤ charge h0 h) :
    SourceProtocolData D A R H0 Z Unit R where
  protocol := sourceOneRoundConditional hL p recordLaw prior prepare charge hcharge
  rounds := 1
  bank := historyBank Unit R 1
  bank_complete := historyBank_complete Unit R 1
  initial := prepare
  final := fun h0 hist z =>
    match hist with
    | [] => prepare h0 z
    | (_, y) :: _ => D.act (p.branch y) (prepare h0 z)
  record := fun hist =>
    match hist with
    | [] => sourceOneRoundEmptyRecord hL p recordLaw prior prepare
    | (_, y) :: _ => y

/-- The empty-history record is total without an extra inhabitance premise. -/
theorem sourceOneRoundData_record_nil
    {D : OperationalData} {A : D.Obj} {R H0 Z : Type}
    [Fintype R] [Fintype H0] [Fintype Z]
    (hL : OperationalLaws D) (p : RecordedProcess D A R)
    (recordLaw : FiniteLaw H0) (prior : H0 → FiniteLaw Z)
    (prepare : H0 → Z → D.State A)
    (charge : H0 → List (Unit × R) → ℝ)
    (hcharge : ∀ h0 h, 0 ≤ charge h0 h) :
    (sourceOneRoundData hL p recordLaw prior prepare charge hcharge).record [] =
      sourceOneRoundEmptyRecord hL p recordLaw prior prepare := rfl

/-- Every singleton history carries its true outcome and final source action. -/
theorem sourceOneRoundData_singleton
    {D : OperationalData} {A : D.Obj} {R H0 Z : Type}
    [Fintype R] [Fintype H0] [Fintype Z]
    (hL : OperationalLaws D) (p : RecordedProcess D A R)
    (recordLaw : FiniteLaw H0) (prior : H0 → FiniteLaw Z)
    (prepare : H0 → Z → D.State A)
    (charge : H0 → List (Unit × R) → ℝ)
    (hcharge : ∀ h0 h, 0 ≤ charge h0 h)
    (h0 : H0) (z : Z) (y : R) :
    (sourceOneRoundData hL p recordLaw prior prepare charge hcharge).record
        [((), y)] = y ∧
      (sourceOneRoundData hL p recordLaw prior prepare charge hcharge).final
        h0 [((), y)] z = D.act (p.branch y) (prepare h0 z) := by
  exact ⟨rfl, rfl⟩

/-- The empty history has zero stopped mass at the one-round boundary. -/
theorem sourceOneRoundStoppedMass_nil
    {D : OperationalData} {A : D.Obj} {R H0 Z : Type}
    [Fintype R] [Fintype H0] [Fintype Z]
    (hL : OperationalLaws D) (p : RecordedProcess D A R)
    (prior : H0 → FiniteLaw Z) (prepare : H0 → Z → D.State A)
    (charge : H0 → List (Unit × R) → ℝ)
    (hcharge : ∀ h0 h, 0 ≤ charge h0 h)
    (h0 : H0) (z : Z) :
    stoppedMass (sourceOneRoundGiven hL p prior prepare charge hcharge h0)
      1 z [] = 0 := by
  rfl

/-- Singleton stopped mass equals the prior times its native branch weight. -/
theorem sourceOneRoundStoppedMass_singleton
    {D : OperationalData} {A : D.Obj} {R H0 Z : Type}
    [Fintype R] [Fintype H0] [Fintype Z]
    (hL : OperationalLaws D) (p : RecordedProcess D A R)
    (prior : H0 → FiniteLaw Z) (prepare : H0 → Z → D.State A)
    (charge : H0 → List (Unit × R) → ℝ)
    (hcharge : ∀ h0 h, 0 ≤ charge h0 h)
    (h0 : H0) (z : Z) (y : R) :
    stoppedMass (sourceOneRoundGiven hL p prior prepare charge hcharge h0)
      1 z [((), y)] =
      (prior h0).mass z * D.weight (p.branch y) (prepare h0 z) := by
  change prefixMass (sourceOneRoundGiven hL p prior prepare charge hcharge h0)
    z [((), y)] = _
  have h := prefixMass_append
    (sourceOneRoundGiven hL p prior prepare charge hcharge h0) z [] () y
  change prefixMass (sourceOneRoundGiven hL p prior prepare charge hcharge h0)
    z [((), y)] =
      (if false then (0 : ℝ) else
        (prior h0).mass z * 1 * D.weight (p.branch y) (prepare h0 z)) at h
  simpa only [if_false, mul_one] using h

/-- The complete bank contains the empty history and one singleton per label. -/
theorem sourceOneRound_history_sum {R : Type} [Fintype R]
    (f : List (Unit × R) → ℝ) :
    (∑ hist ∈ historySet (Unit × R) 1, f hist) =
      f [] + ∑ y : R, f [((), y)] := by
  rw [historySet_sum_succ]
  simp only [historySet, Finset.sum_singleton, List.nil_append,
    Fintype.sum_prod_type, Fintype.sum_unique]

/-- The complete native stopped law equals the recorded operation for each
preparation, outcome and final test, without excluding zero-weight branches. -/
theorem sourceOneRound_sourceProtocolLink
    {D : OperationalData} {A : D.Obj} {R H0 Z : Type}
    [Fintype R] [DecidableEq R] [Fintype H0] [Fintype Z]
    (hL : OperationalLaws D) (p : RecordedProcess D A R)
    (recordLaw : FiniteLaw H0) (prior : H0 → FiniteLaw Z)
    (prepare : H0 → Z → D.State A)
    (charge : H0 → List (Unit × R) → ℝ)
    (hcharge : ∀ h0 h, 0 ≤ charge h0 h) :
    SourceProtocolLink p
      (sourceOneRoundData hL p recordLaw prior prepare charge hcharge) := by
  intro h0 _ z y e
  let d := sourceOneRoundData hL p recordLaw prior prepare charge hcharge
  let q := sourceOneRoundGiven hL p prior prepare charge hcharge h0
  change (prior h0).mass z *
      (D.weight (p.branch y) (prepare h0 z) *
        D.prob e (D.act (p.branch y) (prepare h0 z))) =
    ((historyBank Unit R 1).map (fun hist =>
      if d.record hist = y then
        stoppedMass q 1 z hist * D.prob e (d.final h0 hist z)
      else 0)).sum
  rw [(historyBank_complete Unit R 1).sum_eq, sourceOneRound_history_sum]
  have hnil :
      (if d.record [] = y then stoppedMass q 1 z [] *
        D.prob e (d.final h0 [] z) else 0) = 0 := by
    by_cases hy : d.record [] = y
    · rw [if_pos hy, sourceOneRoundStoppedMass_nil, zero_mul]
    · rw [if_neg hy]
  rw [hnil, zero_add]
  have hsingle (v : R) :
      (if d.record [((), v)] = y then
        stoppedMass q 1 z [((), v)] * D.prob e (d.final h0 [((), v)] z)
      else 0) =
      (if v = y then
        ((prior h0).mass z * D.weight (p.branch v) (prepare h0 z)) *
          D.prob e (D.act (p.branch v) (prepare h0 z))
      else 0) := by
    change (if v = y then
      stoppedMass q 1 z [((), v)] *
        D.prob e (D.act (p.branch v) (prepare h0 z))
      else 0) = _
    rw [sourceOneRoundStoppedMass_singleton]
  simp_rw [hsingle]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

end OneRoundNative


/-! ## M5.8-N4: finite quantum projective source

Every coordinate operation below is a linear map on the whole matrix algebra.
The positive-dimensional native quantum source supplies normalized zero-weight
outputs. No endpoint-only operation identification is used.
-/

section SourceProjective

open scoped ComplexOrder

/-- The exact coordinate-record projector in the given finite system. -/
def sourceCoordinateProjector {n : ℕ} (y : Fin n) : Mat n :=
  Matrix.diagonal (fun i => if i = y then 1 else 0)

/-- Coordinate projectors are Hermitian, including the one-dimensional case. -/
theorem sourceCoordinateProjector_dagger {n : ℕ} (y : Fin n) :
    dagger (sourceCoordinateProjector y) = sourceCoordinateProjector y := by
  change (Matrix.diagonal (fun i : Fin n =>
    if i = y then (1 : ℂ) else 0)).conjTranspose =
      Matrix.diagonal (fun i : Fin n => if i = y then (1 : ℂ) else 0)
  rw [Matrix.diagonal_conjTranspose]
  apply congrArg Matrix.diagonal
  funext i
  change star (if i = y then (1 : ℂ) else 0) =
    (if i = y then (1 : ℂ) else 0)
  by_cases h : i = y
  · rw [if_pos h, star_one]
  · rw [if_neg h, star_zero]

/-- Every coordinate projector is idempotent. -/
theorem sourceCoordinateProjector_idempotent {n : ℕ} (y : Fin n) :
    sourceCoordinateProjector y * sourceCoordinateProjector y =
      sourceCoordinateProjector y := by
  unfold sourceCoordinateProjector
  rw [Matrix.diagonal_mul_diagonal]
  apply congrArg Matrix.diagonal
  funext i
  change (if i = y then (1 : ℂ) else 0) *
    (if i = y then (1 : ℂ) else 0) = (if i = y then (1 : ℂ) else 0)
  by_cases h : i = y
  · rw [if_pos h, one_mul]
  · rw [if_neg h, zero_mul]

/-- Distinct source outcomes occupy orthogonal matrix blocks. -/
theorem sourceCoordinateProjector_orthogonal {n : ℕ} {y z : Fin n} (hyz : y ≠ z) :
    sourceCoordinateProjector y * sourceCoordinateProjector z = 0 := by
  unfold sourceCoordinateProjector
  rw [Matrix.diagonal_mul_diagonal]
  have hz : (fun i : Fin n =>
      (if i = y then (1 : ℂ) else 0) * (if i = z then 1 else 0)) =
      (fun _ => (0 : ℂ)) := by
    funext i
    by_cases hi : i = y
    · subst i
      simp only [if_neg hyz, mul_zero]
    · simp only [if_neg hi, zero_mul]
  rw [hz, Matrix.diagonal_zero]

/-- The native record projectors resolve the identity on every finite dimension. -/
theorem sourceCoordinateProjector_sum {n : ℕ} :
    (∑ y : Fin n, sourceCoordinateProjector y) = 1 := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.sum_apply, sourceCoordinateProjector,
      Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_univ, if_true]
  · simp only [Matrix.sum_apply, sourceCoordinateProjector,
      Matrix.diagonal_apply_ne _ hij, Finset.sum_const_zero,
      Matrix.one_apply_ne hij]

/-- Compression to one record coordinate is defined for every input matrix. -/
def sourceCoordinateMap {n : ℕ} (y : Fin n) : Mat n →ₗ[ℂ] Mat n where
  toFun a := sourceCoordinateProjector y * a * sourceCoordinateProjector y
  map_add' a b := by
    simp only [Matrix.mul_add, Matrix.add_mul]
  map_smul' c a := by
    simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]

/-- The branch acts on all coherent and incoherent matrix entries. -/
theorem sourceCoordinateMap_apply {n : ℕ} (y : Fin n) (a : Mat n) (i j : Fin n) :
    sourceCoordinateMap y a i j =
      (if i = y then (1 : ℂ) else 0) * a i j *
        (if j = y then (1 : ℂ) else 0) := by
  change (sourceCoordinateProjector y * a * sourceCoordinateProjector y) i j = _
  simp only [sourceCoordinateProjector, Matrix.diagonal_mul, Matrix.mul_diagonal]

/-- The coordinate-record output has exactly the corresponding input diagonal trace. -/
theorem sourceCoordinateMap_trace {n : ℕ} (y : Fin n) (a : Mat n) :
    tr (sourceCoordinateMap y a) = a y y := by
  rw [tr_entrywise]
  simp only [sourceCoordinateMap_apply]
  have heq (i : Fin n) :
      (if i = y then (1 : ℂ) else 0) * a i i *
        (if i = y then (1 : ℂ) else 0) =
          if i = y then a i i else 0 := by
    by_cases h : i = y
    · simp only [if_pos h, one_mul, mul_one]
    · simp only [if_neg h, zero_mul]
  simp only [heq, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- Each record-compression map is completely positive on every finite ancilla. -/
theorem sourceCoordinateMap_cp {n : ℕ} (y : Fin n) :
    CompletelyPositive (sourceCoordinateMap y) := by
  intro r X hX
  let Q : Matrix (Fin r × Fin n) (Fin r × Fin n) ℂ :=
    Matrix.diagonal (fun t => if t.2 = y then 1 else 0)
  have hQ : Q.conjTranspose = Q := by
    change (Matrix.diagonal (fun t : Fin r × Fin n =>
      if t.2 = y then (1 : ℂ) else 0)).conjTranspose =
        Matrix.diagonal (fun t : Fin r × Fin n => if t.2 = y then (1 : ℂ) else 0)
    rw [Matrix.diagonal_conjTranspose]
    apply congrArg Matrix.diagonal
    funext i
    change star (if i.2 = y then (1 : ℂ) else 0) =
      (if i.2 = y then (1 : ℂ) else 0)
    by_cases h : i.2 = y
    · rw [if_pos h, star_one]
    · rw [if_neg h, star_zero]
  have heq : amplify (sourceCoordinateMap y) r X =
      Q * X * Q.conjTranspose := by
    rw [hQ]
    ext i j
    change (sourceCoordinateMap y
        (fun x z => X (i.1, x) (j.1, z))) i.2 j.2 = (Q * X * Q) i j
    rw [sourceCoordinateMap_apply]
    simp only [Q, Matrix.diagonal_mul, Matrix.mul_diagonal]
  rw [heq]
  exact (generalPSD_iff_posSemidef _).mpr
    (((generalPSD_iff_posSemidef _).mp hX).mul_mul_conjTranspose_same Q)

/-- Each record-compression map is trace-nonincreasing on all positive inputs. -/
theorem sourceCoordinateMap_tni {n : ℕ} (y : Fin n) :
    TraceNonIncreasing (sourceCoordinateMap y) := by
  intro a ha
  rw [sourceCoordinateMap_trace]
  have ha' : a.PosSemidef := (psd_iff_posSemidef _).mp ha
  calc
    (a y y).re ≤ ∑ i : Fin n, (a i i).re := by
      exact Finset.single_le_sum
        (fun i _ => (Complex.nonneg_iff.mp (posSemidef_diag_nonneg ha' i)).1)
        (Finset.mem_univ y)
    _ = (tr a).re := by rw [tr_entrywise, Complex.re_sum]


/-! ### The total nonselective projective quantum channel -/

/-- The native dephasing operation preserves exactly the diagonal entries. -/
def sourceDephaseMap (n : ℕ) : Mat n →ₗ[ℂ] Mat n where
  toFun a := Matrix.diagonal (fun i => a i i)
  map_add' a b := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [Matrix.diagonal_apply_eq, Matrix.add_apply]
    · simp only [Matrix.diagonal_apply_ne _ hij, Matrix.add_apply, add_zero]
  map_smul' c a := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [Matrix.diagonal_apply_eq, Matrix.smul_apply,
        smul_eq_mul, RingHom.id_apply]
    · simp only [Matrix.diagonal_apply_ne _ hij, Matrix.smul_apply,
        smul_eq_mul, RingHom.id_apply, mul_zero]

/-- Every matrix entry of the total map agrees with its defined diagonal channel. -/
theorem sourceDephaseMap_apply (n : ℕ) (a : Mat n) :
    sourceDephaseMap n a = Matrix.diagonal (fun i => a i i) := rfl

/-- The nonselective map is the sum of all actual selective maps on every matrix. -/
theorem sourceDephaseMap_eq_sum (n : ℕ) (a : Mat n) :
    sourceDephaseMap n a = ∑ y : Fin n, sourceCoordinateMap y a := by
  ext i j
  by_cases hij : i = j
  · subst j
    rw [sourceDephaseMap_apply, Matrix.diagonal_apply_eq, Matrix.sum_apply]
    have hcell (y : Fin n) :
        sourceCoordinateMap y a i i =
          if y = i then a i i else 0 := by
      rw [sourceCoordinateMap_apply]
      by_cases hy : i = y
      · subst y
        norm_num
      · have hyi : y ≠ i := Ne.symm hy
        simp only [if_neg hy, if_neg hyi, zero_mul]
    simp only [hcell, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · change (Matrix.diagonal (fun k => a k k)) i j =
        (∑ y : Fin n, sourceCoordinateMap y a) i j
    rw [Matrix.diagonal_apply_ne _ hij, Matrix.sum_apply]
    symm
    apply Finset.sum_eq_zero
    intro y _
    rw [sourceCoordinateMap_apply]
    by_cases hi : i = y
    · have hj : j ≠ y := by
        intro h
        exact hij (hi.trans h.symm)
      simp only [if_neg hj, mul_zero]
    · simp only [if_neg hi, zero_mul]

/-- The full dephasing map is completely positive for arbitrary finite ancillas.
Each positive summand is the actual record-compression channel. -/
theorem sourceDephaseMap_cp (n : ℕ) :
    CompletelyPositive (sourceDephaseMap n) := by
  intro r X hX
  have heq : amplify (sourceDephaseMap n) r X =
      ∑ y : Fin n, amplify (sourceCoordinateMap y) r X := by
    ext i j
    change (sourceDephaseMap n
        (fun u v => X (i.1, u) (j.1, v))) i.2 j.2 =
      (∑ y : Fin n, amplify (sourceCoordinateMap y) r X) i j
    rw [sourceDephaseMap_eq_sum]
    simp only [Matrix.sum_apply, amplify]
  rw [heq]
  exact (generalPSD_iff_posSemidef _).mpr
    (Thermal.psd_sum Finset.univ
      (fun y => amplify (sourceCoordinateMap y) r X)
      (fun y _ => (generalPSD_iff_posSemidef _).mp
        (sourceCoordinateMap_cp y r X hX)))

/-- Dephasing preserves the trace of every matrix, not merely every density. -/
theorem sourceDephaseMap_trace (n : ℕ) (a : Mat n) :
    tr (sourceDephaseMap n a) = tr a := by
  rw [tr_entrywise, tr_entrywise]
  apply Finset.sum_congr rfl
  intro i _
  exact Matrix.diagonal_apply_eq (fun j => a j j) i

/-- A trace-preserving map satisfies the required trace bound. -/
theorem sourceDephaseMap_tni (n : ℕ) :
    TraceNonIncreasing (sourceDephaseMap n) := by
  intro a _
  rw [sourceDephaseMap_trace]

/-- Testing each projective output inside the same dephasing channel gives
the coordinate map on every matrix input, including off-diagonal matrices. -/
theorem sourceCoordinateProjector_dephase (n : ℕ) (y : Fin n) (a : Mat n) :
    sourceCoordinateProjector y * sourceDephaseMap n a *
      dagger (sourceCoordinateProjector y) = sourceCoordinateMap y a := by
  rw [sourceCoordinateProjector_dagger]
  change sourceCoordinateMap y (sourceDephaseMap n a) = sourceCoordinateMap y a
  ext i j
  simp only [sourceCoordinateMap_apply, sourceDephaseMap_apply]
  by_cases hi : i = y
  · by_cases hj : j = y
    · subst i
      subst j
      rw [Matrix.diagonal_apply_eq]
    · simp only [if_neg hj, mul_zero]
  · simp only [if_neg hi, zero_mul]


/-! ### The same source process and retained-record quantum instrument -/

/-- Each native branch uses its full completely positive coordinate map.
The canonical normalized output handles zero-weight states without extra premises. -/
noncomputable def sourceCoordinateProc (A : QSys) (y : Fin A.val) :
    QProc A.val A.val :=
  QProc.ofMap (sourceCoordinateMap y) (sourceCoordinateMap_cp y)
    (sourceCoordinateMap_tni y) A.property

/-- The nonselective native process preserves the entire diagonal state. -/
noncomputable def sourceDephaseProc (A : QSys) : QProc A.val A.val :=
  QProc.ofMap (sourceDephaseMap A.val) (sourceDephaseMap_cp A.val)
    (sourceDephaseMap_tni A.val) A.property

/-- The one finite quantum source carries the total dephasing operation and
every selected coordinate operation, with source probabilities and post-states
derived from those same maps on every density. -/
noncomputable def sourceProjectiveRecordedProcess (A : QSys) :
    RecordedProcess quantumData A (Fin A.val) where
  total := sourceDephaseProc A
  branch y := sourceCoordinateProc A y
  total_weight := by
    intro s
    change (tr (sourceDephaseMap A.val s.val)).re = 1
    rw [sourceDephaseMap_trace, density_tr, Complex.one_re]
  normalized := by
    intro s
    change (∑ y : Fin A.val, (tr (sourceCoordinateMap y s.val)).re) = 1
    simp only [sourceCoordinateMap_trace]
    rw [← Complex.re_sum, ← tr_entrywise, density_tr, Complex.one_re]
  forget_record := by
    intro s e
    change (∑ y : Fin A.val,
      (tr ((sourceCoordinateProc A y).map s.val)).re *
        (tr (((sourceCoordinateProc A y).out s).val * e.val)).re) =
      (tr (((sourceDephaseProc A).out s).val * e.val)).re
    have hb (y : Fin A.val) :
        (tr ((sourceCoordinateProc A y).map s.val)).re *
          (tr (((sourceCoordinateProc A y).out s).val * e.val)).re =
        (tr (sourceCoordinateMap y s.val * e.val)).re :=
      QProc.weight_mul_prob (sourceCoordinateProc A y) s e.val
    calc
      (∑ y : Fin A.val,
          (tr ((sourceCoordinateProc A y).map s.val)).re *
            (tr (((sourceCoordinateProc A y).out s).val * e.val)).re) =
          ∑ y : Fin A.val, (tr (sourceCoordinateMap y s.val * e.val)).re := by
            apply Finset.sum_congr rfl
            intro y _
            exact hb y
      _ = (tr ((∑ y : Fin A.val, sourceCoordinateMap y s.val) * e.val)).re := by
            simp only [Matrix.sum_mul, Matrix.trace_sum, Complex.re_sum]
      _ = (tr (sourceDephaseMap A.val s.val * e.val)).re := by
            rw [sourceDephaseMap_eq_sum]
      _ = (tr (((sourceDephaseProc A).out s).val * e.val)).re := by
            have hw : (tr ((sourceDephaseProc A).map s.val)).re = 1 := by
              change (tr (sourceDephaseMap A.val s.val)).re = 1
              rw [sourceDephaseMap_trace, density_tr, Complex.one_re]
            have hprob := QProc.weight_mul_prob (sourceDephaseProc A) s e.val
            rw [hw, one_mul] at hprob
            exact hprob.symm

/-- All record operations are identified on every matrix input. Equality of
the physical channel with the explicitly defined nonselective map is the only
additional channel premise; it is not an assumed instrument theorem. -/
theorem sourceProjective_implementsInstrument_of_channel
    (A : QSys) {m : ℕ} (e : ThermalExperiment A.val m)
    (hchannel : ∀ a : Mat A.val, thermalChannel e a = sourceDephaseMap A.val a) :
    ImplementsInstrument quantumData A (Fin A.val)
      (sourceProjectiveRecordedProcess A) quantumData_realization e
      (sourceCoordinateProjector) := by
  unfold ImplementsInstrument
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro y
    exact ⟨sourceCoordinateProjector_dagger y,
      sourceCoordinateProjector_idempotent y⟩
  · intro y z hyz
    exact sourceCoordinateProjector_orthogonal hyz
  · exact sourceCoordinateProjector_sum
  · intro a
    exact hchannel a
  · intro y a
    rw [hchannel a]
    exact sourceCoordinateProjector_dephase A.val y a
  · intro a
    rw [hchannel a]
    calc
      (∑ y : Fin A.val, sourceCoordinateProjector y *
          sourceDephaseMap A.val a * dagger (sourceCoordinateProjector y)) =
        ∑ y : Fin A.val, sourceCoordinateMap y a := by
          apply Finset.sum_congr rfl
          intro y _
          exact sourceCoordinateProjector_dephase A.val y a
      _ = sourceDephaseMap A.val a := (sourceDephaseMap_eq_sum A.val a).symm

end SourceProjective



/-! ## Exact cost of the native one-round protocol -/

/-- A unit action carrier contributes exactly its single action value. -/
theorem source_sum_unit {W : Type*} [AddCommMonoid W] (f : Unit → W) :
    (∑ u : Unit, f u) = f () := by
  apply Fintype.sum_eq_single ()
  intro u hu
  cases u
  exact False.elim (hu rfl)

section OneRoundCost

open OperatorKO7.Meta.BoundaryObserver.ProtocolResolution

variable {D : OperationalData} {A : D.Obj} {R H0 Z : Type}
variable [Fintype R] [Fintype H0] [Fintype Z]
variable (hL : OperationalLaws D) (p : RecordedProcess D A R)
variable (prior : H0 → FiniteLaw Z) (prepare : H0 → Z → D.State A)
variable (charge : H0 → List (Unit × R) → ℝ)
variable (hcharge : ∀ h0 h, 0 ≤ charge h0 h)

/-- The one-round run pays its actual root charge once, for every source outcome law. -/
theorem sourceOneRound_expectedCost (h0 : H0) :
    expectedCost (sourceOneRoundGiven hL p prior prepare charge hcharge h0)
      1 (historyBank Unit R 1) = charge h0 [] := by
  let q := sourceOneRoundGiven hL p prior prepare charge hcharge h0
  have hroot : historyMass q [] = 1 := by
    change (∑ z, (prior h0).mass z) = 1
    exact (prior h0).total
  have hz : (0 : ℕ) < 1 ∧ false = false := by decide
  have ho : ¬ ((1 : ℕ) < 1 ∧ true = false) := by decide
  change expectedCost q 1 (historyBank Unit R 1) = charge h0 []
  unfold expectedCost
  rw [(historyBank_complete Unit R 1).sum_eq, sourceOneRound_history_sum]
  change
    (if (0 : ℕ) < 1 ∧ false = false then
      historyMass q [] * (∑ _a : Unit, (1 : ℝ) * charge h0 []) else 0) +
    (∑ y : R, if (1 : ℕ) < 1 ∧ true = false then
      historyMass q [((), y)] *
        (∑ _a : Unit, (1 : ℝ) * charge h0 [((), y)]) else 0) = charge h0 []
  rw [if_pos hz]
  simp only [if_neg ho, Finset.sum_const_zero, add_zero,
    hroot, source_sum_unit, one_mul]

/-- The retained initial record averages those same root charges with its actual law. -/
theorem sourceOneRound_conditionalExpectedCost (recordLaw : FiniteLaw H0) :
    conditionalExpectedCost
      (sourceOneRoundConditional hL p recordLaw prior prepare charge hcharge)
      1 (historyBank Unit R 1) =
        ∑ h0, recordLaw.mass h0 * charge h0 [] := by
  change
    (∑ h0, recordLaw.mass h0 *
      expectedCost (sourceOneRoundGiven hL p prior prepare charge hcharge h0)
        1 (historyBank Unit R 1)) =
      ∑ h0, recordLaw.mass h0 * charge h0 []
  simp only [sourceOneRound_expectedCost]

end OneRoundCost

end UniversalObservation.Reconstruction
