import OperatorKO7.Meta.BoundaryObserver.InstrumentDivision
import OperatorKO7.Meta.BoundaryObserver.ReconstructionCodeSpan
import OperatorKO7.Meta.BoundaryObserver.BoundaryInfiniteCostConditional
import OperatorKO7.Meta.BoundaryObserver.ReconstructionGNSDynamics
import OperatorKO7.Meta.BoundaryObserver.ReconstructionEntropyTail
import OperatorKO7.Meta.BoundaryObserver.ThermalSourceCompletion
import OperatorKO7.Meta.BoundaryObserver.BoundaryTheoremFull
import OperatorKO7.Meta.BoundaryObserver.BoundaryTheoremQuantum
import OperatorKO7.Meta.BoundaryObserver.ReconstructionKnillLaflamme
import OperatorKO7.Meta.BoundaryObserver.SourceApexInstrument
import OperatorKO7.Meta.BoundaryObserver.PairQuaternion

set_option autoImplicit false

/-!
# Full mathematical and conditional quantum package

The finite complex matrix carrier is explicit in each quantum statement.
Observer premises alone do not construct this carrier.
-/

namespace OperatorKO7.Meta.BoundaryObserver.BoundaryObservationSingularity

open Matrix
open scoped BigOperators Kronecker ComplexOrder Classical
open OperatorKO7.Meta.BoundaryObserver

universe u v w r s

noncomputable section

/-- Finite complex tomography, positive-functional density, star-algebra blocks,
Pauli tests, field controls and both pure- and mixed-state Bell results. -/
def FiniteComplexGoal : Prop :=
  (∀ (n : ℕ) (ρ : BoundaryReconstruction.Density n),
    QuantumReconstruction.reconstruct
      (QuantumReconstruction.population ρ.val)
      (QuantumReconstruction.plusReport ρ.val)
      (QuantumReconstruction.phaseReport ρ.val) = ρ.val) ∧
  (∀ (n : ℕ) (f : BoundaryReconstruction.PositiveFunctional n),
    ∃! ρ : BoundaryReconstruction.Density n,
      ∀ a : BoundaryReconstruction.Mat n,
        f.value a = BoundaryReconstruction.tr (ρ.val * a)) ∧
  (∀ (n : ℕ) (Q : Type u) (q : Fin n → Q) (a : BoundaryReconstruction.Mat n),
    BoundaryReconstruction.Generated q a ↔ BoundaryReconstruction.FiberClosed q a) ∧
  (∀ (n : ℕ) (Q : Type u) (q : Fin n → Q),
    StarAlgebra.adjoin ℂ (BoundaryReconstruction.fiberGenerators q) =
      BoundaryReconstruction.fiberAlgebra q) ∧
  (∀ (n : ℕ) (Q : Type u) (q : Fin n → Q),
    ∃ e : {a : BoundaryReconstruction.Mat n // BoundaryReconstruction.FiberClosed q a} ≃
        BoundaryReconstruction.BlockFamily q,
      ∀ (a : {a : BoundaryReconstruction.Mat n //
          BoundaryReconstruction.FiberClosed q a}) (y : Q)
          (i j : BoundaryReconstruction.Fiber q y),
        e a y i j = a.val i.val j.val) ∧
  PairQubit.PauliRelationsGoal ∧ PairQubit.PairSpanGoal ∧
  PairQubit.PairFiberAlgebraGoal ∧ PairField.FieldSelectionGoal ∧
  PairQuaternion.PairQuaternionGoal ∧ PairBell.BellTableGoal ∧
  PairBell.PureExcessGoal ∧ PairBell.MixedExcessGoal

/-- Q1 preserves every imported hypothesis and original result. -/
theorem finiteComplexGoal : FiniteComplexGoal := by
  refine ⟨?_, ?_, ?_, ?_, ?_, PairQubit.pauli_relations,
    PairQubit.pair_span, PairQubit.pair_fiber_algebra,
    PairField.fieldSelectionGoal, PairQuaternion.pairQuaternionGoal,
    PairBell.bellTable, PairBell.pureExcess, PairBell.mixedExcess⟩
  · intro n ρ
    exact BoundaryReconstruction.density_reconstruct_reports ρ
  · intro n f
    exact BoundaryReconstruction.density_representation f
  · intro n Q q a
    exact BoundaryReconstruction.generated_iff_fiberClosed q a
  · intro n Q q
    exact BoundaryReconstruction.star_adjoin_fiberGenerators q
  · intro n Q q
    exact BoundaryReconstruction.block_decomposition q

/-- A single named finite instrument supplies a common Kraus family, a
record-bearing isometry and a square unitary. Every branch is preserved on
every complex matrix, and the zero-weight branch is the zero matrix. -/
def LinkedInstrumentGoal : Prop :=
  ∀ (n m : ℕ) (Y : Type u) [Fintype Y]
      (branch : Y → ReconstructionRecovery.Mat n →ₗ[ℂ] ReconstructionRecovery.Mat m)
      (hCP : ∀ y : Y, ReconstructionRecovery.CompletelyPositive (branch y))
      (_ : ∀ a : ReconstructionRecovery.Mat n,
        ReconstructionRecovery.tr (∑ y : Y, branch y a) = ReconstructionRecovery.tr a),
    ∃ (K : (Y × (Fin n × Fin m)) → Matrix (Fin m) (Fin n) ℂ)
      (V : Matrix (Fin m × (Y × (Fin n × Fin m))) (Fin n) ℂ)
      (U : Matrix
        (Fin n ⊕ (Fin m × (Y × (Fin n × Fin m))))
        (Fin n ⊕ (Fin m × (Y × (Fin n × Fin m)))) ℂ),
      K = ReconstructionRecovery.instrumentJointKraus branch hCP ∧
      V = OperatorKO7.Meta.ReverseBridge.QMLaw_FiniteDilation.stinespringV K ∧
      U = ReconstructionRecovery.halmosSquareUnitary V ∧
      (∀ (a : ReconstructionRecovery.Mat n) (y : Y),
        (∑ z : Fin n × Fin m, K (y,z) * a * (K (y,z))ᴴ) = branch y a) ∧
      (∑ e : Y × (Fin n × Fin m), (K e)ᴴ * K e : ReconstructionRecovery.Mat n) = 1 ∧
      Vᴴ * V = 1 ∧
      (∀ (a : ReconstructionRecovery.Mat n) (y : Y),
        (∑ z : Fin n × Fin m,
          ReconstructionRecovery.recordedOutcome (y,z) (V * a * Vᴴ)) = branch y a) ∧
      (∀ a : ReconstructionRecovery.Mat n,
        (∑ e : Y × (Fin n × Fin m),
          ReconstructionRecovery.recordedOutcome e (V * a * Vᴴ)) =
          ∑ y : Y, branch y a) ∧
      Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧
      (∀ (a : ReconstructionRecovery.Mat n) (y : Y),
        (∑ z : Fin n × Fin m,
          ReconstructionRecovery.recordedOutcome (y,z)
            (U * ReconstructionRecovery.squareUnitaryInputBlock a * Uᴴ).toBlocks₂₂) =
          branch y a) ∧
      (∀ a : ReconstructionRecovery.Mat n,
        (∑ e : Y × (Fin n × Fin m),
          ReconstructionRecovery.recordedOutcome e
            (U * ReconstructionRecovery.squareUnitaryInputBlock a * Uᴴ).toBlocks₂₂) =
          ∑ y : Y, branch y a) ∧
      (∀ (ρ : ReconstructionRecovery.InstrumentDensity n) (y : Y),
        (ReconstructionRecovery.tr
          (∑ z : Fin n × Fin m,
            ReconstructionRecovery.recordedOutcome (y,z)
              (U * ReconstructionRecovery.squareUnitaryInputBlock ρ.val * Uᴴ).toBlocks₂₂)).re =
          ReconstructionRecovery.instrumentWeight branch ρ y) ∧
      (∀ (ρ : ReconstructionRecovery.InstrumentDensity n) (y : Y)
          (hp : 0 < ReconstructionRecovery.instrumentWeight branch ρ y),
        (ReconstructionRecovery.instrumentWeight branch ρ y : ℂ) •
            (ReconstructionRecovery.instrumentConditionalState branch hCP ρ y hp).val =
          ∑ z : Fin n × Fin m,
            ReconstructionRecovery.recordedOutcome (y,z)
              (U * ReconstructionRecovery.squareUnitaryInputBlock ρ.val * Uᴴ).toBlocks₂₂) ∧
      (∀ (ρ : ReconstructionRecovery.InstrumentDensity n) (y : Y)
          (_ : ReconstructionRecovery.instrumentWeight branch ρ y = 0),
        (∑ z : Fin n × Fin m,
          ReconstructionRecovery.recordedOutcome (y,z)
            (U * ReconstructionRecovery.squareUnitaryInputBlock ρ.val * Uᴴ).toBlocks₂₂) =
          (0 : ReconstructionRecovery.Mat m))

/-- The Kraus, isometry and unitary witnesses all come from the same CP
instrument. No independent realization or branch-equality premise is inserted. -/
theorem linkedInstrumentGoal : LinkedInstrumentGoal := by
  intro n m Y inst branch hCP hTP
  let K := ReconstructionRecovery.instrumentJointKraus branch hCP
  let V := OperatorKO7.Meta.ReverseBridge.QMLaw_FiniteDilation.stinespringV K
  let U := ReconstructionRecovery.instrumentSquareUnitary branch hCP
  have hcomplete :
      (∑ e : Y × (Fin n × Fin m),
        (K e)ᴴ * K e : ReconstructionRecovery.Mat n) = 1 :=
    ReconstructionRecovery.instrumentJointKraus_complete branch hCP hTP
  have hV : Vᴴ * V = 1 :=
    ReconstructionRecovery.instrumentJointKraus_isometry branch hCP hTP
  have hU : Uᴴ * U = 1 ∧ U * Uᴴ = 1 :=
    ReconstructionRecovery.instrumentSquareUnitary_unitary branch hCP hTP
  have hbranch (a : ReconstructionRecovery.Mat n) (y : Y) :
      (∑ z : Fin n × Fin m,
        ReconstructionRecovery.recordedOutcome (y,z) (V * a * Vᴴ)) =
        branch y a :=
    ReconstructionRecovery.instrumentJointKraus_branch branch hCP a y
  have htotal (a : ReconstructionRecovery.Mat n) :
      (∑ e : Y × (Fin n × Fin m),
        ReconstructionRecovery.recordedOutcome e (V * a * Vᴴ)) =
        ∑ y : Y, branch y a := by
    calc
      (∑ e : Y × (Fin n × Fin m),
        ReconstructionRecovery.recordedOutcome e (V * a * Vᴴ)) =
          OperatorKO7.Meta.ReverseBridge.QMLaw_FiniteDilation.partialTraceAncilla
            (V * a * Vᴴ) :=
        ReconstructionRecovery.recordedOutcome_sum _
      _ = OperatorKO7.Meta.ReverseBridge.QMLaw_FiniteDilation.cpMapKraus K a :=
        (OperatorKO7.Meta.ReverseBridge.QMLaw_FiniteDilation.stinespring_dilates K a).symm
      _ = ∑ y : Y, branch y a :=
        ReconstructionRecovery.instrumentJointKraus_total branch hCP a
  refine ⟨K, V, U, rfl, rfl, rfl, ?_, hcomplete, hV, hbranch, htotal, hU.1, hU.2,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro a y
    change OperatorKO7.Meta.ReverseBridge.QMLaw_FiniteDilation.cpMapKraus
      (ReconstructionRecovery.instrumentKraus branch hCP y) a = branch y a
    exact (ReconstructionRecovery.instrumentKraus_realizes branch hCP y a).symm
  · intro a y
    dsimp only [U, ReconstructionRecovery.instrumentSquareUnitary]
    rw [ReconstructionRecovery.halmosSquareUnitary_outputBlock]
    exact hbranch a y
  · intro a
    dsimp only [U, ReconstructionRecovery.instrumentSquareUnitary]
    rw [ReconstructionRecovery.halmosSquareUnitary_outputBlock]
    exact htotal a
  · intro ρ y
    exact ReconstructionRecovery.instrumentSquareUnitary_record_weight branch hCP ρ y
  · intro ρ y hp
    exact ReconstructionRecovery.instrumentSquareUnitary_record_postState branch hCP ρ y hp
  · intro ρ y hz
    exact ReconstructionRecovery.instrumentSquareUnitary_zeroWeight branch hCP ρ y hz

/-- The finite Knill-Laflamme overlaps are equivalent to one CPTP recovery
of all supported density matrices on the full complex matrix space. Empty
matrix sizes, empty Kraus index types and the zero projector are included. -/
def RecoveryCriterionGoal : Prop :=
  (∀ (n : ℕ) (E : Type) [Fintype E]
      (errors : E → ReconstructionRecovery.Mat n)
      (p : ReconstructionRecovery.Mat n)
      (_ : p = ReconstructionRecovery.dagger p)
      (_ : p * p = p)
      (_ : (∑ e : E,
        ReconstructionRecovery.dagger (errors e) * errors e) = 1),
    (∃ c : E → E → ℂ, ∀ a b,
      p * ReconstructionRecovery.dagger (errors a) * errors b * p = c a b • p) ↔
      ∃ recovery : ReconstructionRecovery.Mat n →ₗ[ℂ] ReconstructionRecovery.Mat n,
        ReconstructionRecovery.CompletelyPositive recovery ∧
        ReconstructionKnillLaflamme.TracePreserving recovery ∧
        ∀ ρ : ReconstructionKnillLaflamme.Density n,
          p * ρ.val * p = ρ.val →
          recovery (ReconstructionKnillLaflamme.krausOutput errors ρ.val) = ρ.val) ∧
  (∀ (n : ℕ) (E : Type) [Fintype E]
      (errors : E → ReconstructionRecovery.Mat n),
    (∃ c : E → E → ℂ, ∀ a b,
      (0 : ReconstructionRecovery.Mat n) *
        ReconstructionRecovery.dagger (errors a) * errors b * 0 =
          c a b • (0 : ReconstructionRecovery.Mat n)) ∧
    (∃ recovery : ReconstructionRecovery.Mat n →ₗ[ℂ] ReconstructionRecovery.Mat n,
      ReconstructionRecovery.CompletelyPositive recovery ∧
      ReconstructionKnillLaflamme.TracePreserving recovery ∧
      ∀ ρ : ReconstructionKnillLaflamme.Density n,
        (0 : ReconstructionRecovery.Mat n) * ρ.val * 0 = ρ.val →
          recovery (ReconstructionKnillLaflamme.krausOutput errors ρ.val) = ρ.val))

/-- Reuses both proved directions and explicit zero-projector constructions. -/
theorem recoveryCriterionGoal : RecoveryCriterionGoal := by
  refine ⟨?_, ?_⟩
  · intro n E inst errors p hstar hidem hcomplete
    exact ReconstructionKnillLaflamme.knillLaflamme_equivalence
      errors p hstar hidem hcomplete
  · intro n E inst errors
    exact ⟨ReconstructionKnillLaflamme.zero_projector_overlap errors,
      ReconstructionKnillLaflamme.zero_projector_recovery errors⟩


/-- The same error family realizes every recorded operation by one square
unitary and has the exact Knill-Laflamme recovery equivalence on that family.
No independent recovery channel or measurement source is substituted. -/
def SameSourceRecoveryInstrumentGoal : Prop :=
  ∀ (n : ℕ) (E : Type) [Fintype E]
      (errors : E → ReconstructionRecovery.Mat n)
      (p : ReconstructionRecovery.Mat n)
      (_ : p = ReconstructionRecovery.dagger p)
      (_ : p * p = p)
      (_ : (∑ e : E,
        ReconstructionRecovery.dagger (errors e) * errors e :
          ReconstructionRecovery.Mat n) = 1),
    ∃ (V : Matrix (Fin n × E) (Fin n) ℂ)
      (U : Matrix (Fin n ⊕ (Fin n × E)) (Fin n ⊕ (Fin n × E)) ℂ),
      V = OperatorKO7.Meta.ReverseBridge.QMLaw_FiniteDilation.stinespringV errors ∧
      U = ReconstructionRecovery.halmosSquareUnitary V ∧
      Vᴴ * V = 1 ∧ Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧
      (∀ (a : ReconstructionRecovery.Mat n) (e : E),
        ReconstructionRecovery.recordedOutcome e
          (U * ReconstructionRecovery.squareUnitaryInputBlock a * Uᴴ).toBlocks₂₂ =
            errors e * a * (errors e)ᴴ) ∧
      (∀ a : ReconstructionRecovery.Mat n,
        (∑ e : E,
          ReconstructionRecovery.recordedOutcome e
            (U * ReconstructionRecovery.squareUnitaryInputBlock a * Uᴴ).toBlocks₂₂) =
          ReconstructionKnillLaflamme.krausOutput errors a) ∧
      ((∃ c : E → E → ℂ, ∀ i j,
        p * ReconstructionRecovery.dagger (errors i) * errors j * p = c i j • p) ↔
        ∃ recovery : ReconstructionRecovery.Mat n →ₗ[ℂ] ReconstructionRecovery.Mat n,
          ReconstructionRecovery.CompletelyPositive recovery ∧
          ReconstructionKnillLaflamme.TracePreserving recovery ∧
          ∀ ρ : ReconstructionKnillLaflamme.Density n,
            p * ρ.val * p = ρ.val →
              recovery (ReconstructionKnillLaflamme.krausOutput errors ρ.val) = ρ.val)


/-- One set of Kraus errors realizes the record and square unitary and the
same errors enter both exact directions of the recovery criterion. -/
theorem sameSourceRecoveryInstrumentGoal : SameSourceRecoveryInstrumentGoal := by
  intro n E inst errors p hstar hidem hcomplete
  let V := OperatorKO7.Meta.ReverseBridge.QMLaw_FiniteDilation.stinespringV errors
  let U := ReconstructionRecovery.halmosSquareUnitary V
  have hV : Vᴴ * V = 1 :=
    OperatorKO7.Meta.ReverseBridge.QMLaw_FiniteDilation.stinespring_isometry
      errors hcomplete
  have hU : Uᴴ * U = 1 ∧ U * Uᴴ = 1 := by
    have hu := ReconstructionRecovery.halmosSquareUnitary_unitary V hV
    constructor
    · ext i j
      have he := congrFun (congrFun hu.1 i) j
      by_cases hij : i = j
      · simpa only [U, Matrix.one_apply, if_pos hij] using he
      · simpa only [U, Matrix.one_apply, if_neg hij] using he
    · ext i j
      have he := congrFun (congrFun hu.2 i) j
      by_cases hij : i = j
      · simpa only [U, Matrix.one_apply, if_pos hij] using he
      · simpa only [U, Matrix.one_apply, if_neg hij] using he
  have hblock (a : ReconstructionRecovery.Mat n) :
      (U * ReconstructionRecovery.squareUnitaryInputBlock a * Uᴴ).toBlocks₂₂ =
        V * a * Vᴴ :=
    ReconstructionRecovery.halmosSquareUnitary_outputBlock V a
  refine ⟨V, U, rfl, rfl, hV, hU.1, hU.2, ?_, ?_, ?_⟩
  · intro a e
    rw [hblock a]
    exact ReconstructionRecovery.recordedOutcome_stinespring errors a e
  · intro a
    rw [hblock a]
    calc
      (∑ e : E, ReconstructionRecovery.recordedOutcome e (V * a * Vᴴ)) =
          OperatorKO7.Meta.ReverseBridge.QMLaw_FiniteDilation.partialTraceAncilla
            (V * a * Vᴴ) :=
        ReconstructionRecovery.recordedOutcome_sum _
      _ = OperatorKO7.Meta.ReverseBridge.QMLaw_FiniteDilation.cpMapKraus errors a :=
        (OperatorKO7.Meta.ReverseBridge.QMLaw_FiniteDilation.stinespring_dilates
          errors a).symm
      _ = ReconstructionKnillLaflamme.krausOutput errors a := rfl
  · exact ReconstructionKnillLaflamme.knillLaflamme_equivalence
      errors p hstar hidem hcomplete

open BoundaryReconstruction.Operational

/-- The operational data alone do not select complex matrices: two lawful
countermodels refute both candidate frameworks. A supplied quantum realization
does yield state/effect representation, tomography and process consequences,
and the finite quantum source realizes the stronger premises nonvacuously. -/
def OperationalClassificationGoal : Prop :=
  (¬ ReconstructionFromFrameworkGoal
    (fun D => OperationalLaws D ∧ SelectionConditions D)) ∧
  (¬ ReconstructionFromFrameworkGoal StrengthenedFramework) ∧
  (∃ D : OperationalData,
    OperationalLaws D ∧ SelectionConditions D ∧
      ¬ Nonempty (QuantumRealization D)) ∧
  (∃ D : OperationalData,
    StrengthenedFramework D ∧ ¬ Nonempty (QuantumRealization D)) ∧
  (StrengthenedFramework quantumData ∧ Nonempty (QuantumRealization quantumData)) ∧
  (∀ (D : OperationalData) (_ : QuantumRealization D),
    StateEffectRepresentationGoal D ∧ LocalTomography D ∧
      FiniteTomography D ∧ TestExtensionality D ∧ ParallelProductLaws D) ∧
  (∀ (D : OperationalData), OperationalLaws D → ∀ _ : QuantumRealization D,
    AffineEffectFullness D ∧ StateFullness D)

/-- Q4 keeps constructive representation conditional and records both
independent negative witnesses rather than assuming the desired realization. -/
theorem operationalClassificationGoal : OperationalClassificationGoal := by
  refine ⟨minimalFramework_not_reconstruction,
    strengthenedFramework_not_reconstruction,
    ⟨trivialData, trivialData_operationalLaws, trivialData_selectionConditions,
      trivialData_no_realization⟩,
    ⟨tpData, tpData_strengthenedFramework, ?_⟩,
    ⟨quantumData_strengthenedFramework, quantumData_has_realization⟩,
    ?_, ?_⟩
  · rintro ⟨r⟩
    exact tpData_no_realization r
  · intro D r
    have hRep : StateEffectRepresentationGoal D :=
      ⟨r.dim, r.dimension_positive, r.states, r.effects, r.probabilities⟩
    exact ⟨hRep, realization_localTomography r,
      realization_finiteTomography r, realization_testExtensionality r,
      realization_parallelProductLaws r⟩
  · intro D hL r
    exact ⟨realization_affineEffectFullness hL r,
      realization_stateFullness hL r⟩

/-- The unchanged mathematical theorem package with its full universe scope. -/
def MathematicalPackageGoal : Prop :=
  BoundaryTheoremFull.BoundaryTheoremFullGoal.{u, v, w, r, s}

theorem mathematicalPackageGoal : MathematicalPackageGoal.{u, v, w, r, s} :=
  BoundaryTheoremFull.boundaryTheoremFullGoal.{u, v, w, r, s}

open UniversalObservation.Reconstruction

/-- The source apex preserves the recorded process, ensemble, explicit
quantum realization, instrument implementation, heat and cost premises.
A separate constructed two-level source witnesses nonvacuity. -/
def ConditionalApexGoal : Prop :=
  (∀ (D : OperationalData) (A : D.Obj) (R H0 Z : Type)
      [Fintype R] [DecidableEq R] [Fintype H0] [Fintype Z]
      (hL : OperationalLaws D)
      (p : RecordedProcess D A R)
      (recordLaw : ProtocolResolution.FiniteLaw H0)
      (prior : H0 → ProtocolResolution.FiniteLaw Z)
      (prepare : H0 → Z → D.State A)
      (charge : H0 → List (Unit × R) → ℝ)
      (hcharge : ∀ h0 h, 0 ≤ charge h0 h)
      (cost : RecordedProcess D A R → ℕ → ℝ)
      (r : QuantumRealization D) (m : ℕ)
      (e : ThermalExperiment (r.dim A) m)
      (P : R → BoundaryReconstruction.Mat (r.dim A))
      (_ : ImplementsInstrument D A R p r e P)
      (_ : spectralMatrix e.initialSystem =
        SourceApexInstrument.sourceEnsemble r
          (sourceOneRoundData hL p recordLaw prior prepare charge hcharge))
      (_ : cost p 0 = heat e)
      (_ : cost p 1 = UniversalObservation.Protocol.conditionalExpectedCost
        (sourceOneRoundData hL p recordLaw prior prepare charge hcharge).protocol
        (sourceOneRoundData hL p recordLaw prior prepare charge hcharge).rounds
        (sourceOneRoundData hL p recordLaw prior prepare charge hcharge).bank),
    ApexInstanceGoal D A R H0 Z Unit R (recordedSourceContract p cost) p
      (recordedSourceBinding p cost)
      (sourceOneRoundData hL p recordLaw prior prepare charge hcharge) m) ∧
  ApexInstanceGoal quantumData qubit (Fin 2) Unit (Fin 2) Unit (Fin 2)
    SourceApexInstrument.cnotSourceContract SourceApexInstrument.cnotSource
    SourceApexInstrument.cnotSourceBinding
    (SourceApexInstrument.cnotProtocolData SourceApexInstrument.cnotSource) 2

/-- The generic apex is conditional on the actual implementation, and
the nontrivial CNOT source satisfies the exact source specification. -/
theorem conditionalApexGoal : ConditionalApexGoal := by
  refine ⟨?_, apexInstanceGoal⟩
  intro D A R H0 Z instR decR instH instZ
    hL p recordLaw prior prepare charge hcharge cost r m e P
    himplementation hinitial hheat hcost
  exact sourceOneRound_apex_of_implementation
    hL p recordLaw prior prepare charge hcharge cost r e P
    himplementation hinitial hheat hcost

/-- The quantum package retains the existing full quantum theorem and adds
finite complex reconstruction, one linked instrument, exact recovery,
operational countermodels and the conditional source-bound apex. -/
def QuantumPackageGoal : Prop :=
  BoundaryTheorem.BoundaryTheoremGoal.{u} ∧
    FiniteComplexGoal.{u} ∧ LinkedInstrumentGoal.{u} ∧ RecoveryCriterionGoal ∧ SameSourceRecoveryInstrumentGoal ∧
    OperationalClassificationGoal ∧ ConditionalApexGoal

theorem quantumPackageGoal : QuantumPackageGoal.{u} :=
  ⟨BoundaryTheorem.boundaryTheoremGoal.{u}, finiteComplexGoal.{u},
    linkedInstrumentGoal.{u}, recoveryCriterionGoal,
    sameSourceRecoveryInstrumentGoal,
    operationalClassificationGoal, conditionalApexGoal⟩

/-- The combined theorem is a conjunction of the exact mathematical and
quantum packages. No original goal is weakened or silently changed. -/
def BoundaryObservationSingularityGoal : Prop :=
  MathematicalPackageGoal.{u, v, w, r, s} ∧ QuantumPackageGoal.{u}

theorem boundaryObservationSingularityGoal :
    BoundaryObservationSingularityGoal.{u, v, w, r, s} :=
  ⟨mathematicalPackageGoal.{u, v, w, r, s}, quantumPackageGoal.{u}⟩

/-- Projection to the unchanged complete mathematical Boundary Theorem. -/
theorem mathematicalProjection
    (h : BoundaryObservationSingularityGoal.{u, v, w, r, s}) :
    BoundaryTheoremFull.BoundaryTheoremFullGoal.{u, v, w, r, s} :=
  h.1

/-- Projection to the unchanged quantum Boundary Theorem. -/
theorem quantumProjection
    (h : BoundaryObservationSingularityGoal.{u, v, w, r, s}) :
    BoundaryTheorem.BoundaryTheoremGoal.{u} :=
  h.2.1

/-- The complete quantum extension, including all source-bound conditions. -/
theorem quantumPackageProjection
    (h : BoundaryObservationSingularityGoal.{u, v, w, r, s}) :
    QuantumPackageGoal.{u} :=
  h.2

/-! ## S5: conditional readings, general states, dynamics and controlled limits -/

open ProtocolResolution

/-- A binary target contributes at most one bit to any single finite-output
reading, including when the output alphabet has more than two elements. -/
theorem binary_target_localGain_le_one {A Y : Type} [Fintype A] [Fintype Y]
    (p : FiniteProtocol Bool A Y) (h : List (A × Y)) (a : A) :
    localGain p h a ≤ 1 := by
  rcases (historyMass_nonnegative p h).eq_or_lt with hw | hw
  · rw [localGain_zero_of_historyMass_zero p h hw.symm a]
    exact zero_le_one
  · have hs := massUncertainty_kernel_sum (posterior p h)
      (fun z y => (p.observation h a z).mass y)
      (fun z => (p.observation h a z).total)
    have hn : 0 ≤ ∑ y, massUncertainty
        (fun z : Bool => posterior p h z * (p.observation h a z).mass y) :=
      Finset.sum_nonneg (fun y _ => InstrumentDivision.massUncertainty_bool_nonneg _
        (fun z => mul_nonneg (posterior_nonnegative p h z)
          ((p.observation h a z).nonnegative y)))
    have ht : posterior p h true + posterior p h false = 1 := by
      simpa only [Fintype.sum_bool] using posterior_total p h hw
    have he := SeedFrontier.entropy_bool_le_one (posterior p h) ht
    unfold localGain
    linarith

/-- Unit-cost readings of a binary target satisfy capacity one for every
finite output alphabet. -/
theorem binary_target_capacity {A Y : Type} [Fintype A] [Fintype Y]
    (p : FiniteProtocol Bool A Y) (hcost : ∀ h a, 1 ≤ p.cost h a) :
    LocalCapacityBound p 1 := by
  intro h a _ _ _
  simpa only [one_mul] using
    (binary_target_localGain_le_one p h a).trans (hcost h a)

/-- The binary-target bound holds conditionally at every finite horizon. -/
theorem conditional_binary_target_information_le_cost {H0 A Y : Type}
    [Fintype H0] [Fintype A] [Fintype Y]
    (p : ConditionalProtocol H0 Bool A Y)
    (hcost : ∀ u, 0 < p.initialRecord.mass u → ∀ h a, 1 ≤ (p.given u).cost h a)
    (n : ℕ) (bank : List (List (A × Y))) (hb : HistoryBank n bank) :
    conditionalMI p n bank ≤ conditionalExpectedCost p n bank := by
  simpa only [one_mul] using conditionalMI_le_expectedCost p n bank hb 1
    (fun u hu => binary_target_capacity (p.given u) (hcost u hu))

/-- The same bound holds for limiting information and actual extended cost. -/
theorem conditional_binary_target_limit_le_cost {H0 A Y : Type}
    [Fintype H0] [Fintype A] [Fintype Y]
    (p : ConditionalProtocol H0 Bool A Y)
    (hcost : ∀ u, 0 < p.initialRecord.mass u → ∀ h a, 1 ≤ (p.given u).cost h a) :
    ENNReal.ofReal (conditionalInformationLimit p) ≤ conditionalExtendedCost p := by
  simpa only [ENNReal.ofReal_one, one_mul] using
    conditionalInformationLimit_le_extendedCost p 1 zero_le_one
      (fun u hu => binary_target_capacity (p.given u) (hcost u hu))

/-- Disjoint finite rows attain the cost c with the original output alphabet;
the lower bound includes every binary-target protocol on that alphabet. -/
def DisjointReadingFrontierGoal : Prop :=
  (∀ (H0 A Y : Type) [Fintype H0] [Fintype A] [Fintype Y]
      (p : ConditionalProtocol H0 Bool A Y),
    (∀ u, 0 < p.initialRecord.mass u → ∀ h a, 1 ≤ (p.given u).cost h a) →
      (∀ (n : ℕ) (bank : List (List (A × Y))), HistoryBank n bank →
        conditionalMI p n bank ≤ conditionalExpectedCost p n bank) ∧
      ENNReal.ofReal (conditionalInformationLimit p) ≤ conditionalExtendedCost p) ∧
  (∀ (Y : Type) [Fintype Y] (P Q : FiniteLaw Y),
    (∀ y, P.mass y = 0 ∨ Q.mass y = 0) →
    ∀ (c : ℝ), 0 ≤ c → c ≤ 1 →
      ∃ p : ConditionalProtocol Bool Bool Unit Y,
        (∀ u z, p.initialJoint.mass (u, z) =
          p.initialRecord.mass u * ResolutionAttainment.fairLaw.mass z) ∧
        (∀ u h a z, (p.given u).observation h a z = PairResolution.row P Q z) ∧
        (∀ u h a, (p.given u).cost h a = 1) ∧
        conditionalMI p 1 (historyBank Unit Y 1) = c ∧
        conditionalExpectedCost p 1 (historyBank Unit Y 1) = c ∧
        conditionalInformationLimit p = c ∧
        conditionalExtendedCost p = ENNReal.ofReal c)

theorem disjointReadingFrontierGoal : DisjointReadingFrontierGoal := by
  constructor
  · intro H0 A Y _ _ _ p hc
    exact ⟨fun n bank hb => conditional_binary_target_information_le_cost p hc n bank hb,
      conditional_binary_target_limit_le_cost p hc⟩
  · intro Y _ P Q h c hc0 hc1
    exact BoundaryInfiniteCostConditional.seededDisjointReading_fair_frontier P Q h c hc0 hc1

/-- Both labels may have arbitrary positive prior mass; the fixed reading
admits zero-error recovery at finite expected cost exactly for incomparable supports. -/
def ArbitraryPriorRecoveryGoal : Prop :=
  ∀ (Y : Type) [Fintype Y] (μ : FiniteLaw Bool), (∀ z, 0 < μ.mass z) →
    ∀ P Q : FiniteLaw Y,
      (∃ (p : FiniteProtocol Bool Unit Y) (d : List (Unit × Y) → Bool),
        p.prior = μ ∧
        (∀ h a z, p.observation h a z = PairResolution.row P Q z) ∧
        (∀ h a, 1 ≤ p.cost h a) ∧ ErasureReading.ZeroError p d ∧ extendedCost p < ⊤) ↔
        (∃ y, 0 < P.mass y ∧ Q.mass y = 0) ∧
        (∃ y, 0 < Q.mass y ∧ P.mass y = 0)

theorem arbitraryPriorRecoveryGoal : ArbitraryPriorRecoveryGoal := by
  intro Y _ μ hμ P Q
  exact ErasurePriorCompletion.exists_zeroError_finite_cost_arbitrary_prior_iff μ hμ P Q

/-- The representation uses arbitrary normalized positive states on unital
complex C* algebras. Multiplicativity of the state is not a premise. -/
def StateRepresentationGoal : Prop :=
  ∀ (A : Type u) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (ω : A →ₚ[ℂ] ℂ), ω 1 = 1 → ReconstructionGeneralGNS.GeneralGNSGoal ω

theorem stateRepresentationGoal : StateRepresentationGoal.{u} := by
  intro A _ _ _ ω hω
  exact ReconstructionGeneralGNS.generalGNSGoal ω hω

/-- Pointwise norm-continuous invariant star flows induce strongly continuous
unitary groups on the full GNS Hilbert space with the same-source covariance law. -/
def InvariantStateDynamicsGoal : Prop :=
  ∀ (A : Type u) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (ω : A →ₚ[ℂ] ℂ) (hω : ω 1 = 1)
    (D : ReconstructionGNSDynamics.InvariantStarFlow ω),
      ReconstructionGNSDynamics.GeneralHilbertDynamicsGoal ω hω D

theorem invariantStateDynamicsGoal : InvariantStateDynamicsGoal.{u} := by
  intro A _ _ _ ω hω D
  exact ReconstructionGNSDynamics.generalHilbertDynamicsGoal ω hω D

/-- Compatible normalized states recover every stage in the constructed
completion, with a unit cyclic vector and uniqueness on the dense stage union. -/
def CompatibleStageRecoveryGoal : Prop :=
  ∀ (ι : Type u) [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (S : ReconstructionLimitCompletion.IsometricStarSystem.{u, v} ι)
    [∀ i, PartialOrder (S.Fiber i)] [∀ i, StarOrderedRing (S.Fiber i)]
    (Ω : ReconstructionLimitCompletion.CompatibleStateFamily S),
      ReconstructionGNSDynamics.CompatibleGeneralGNSRecoveryGoal Ω

theorem compatibleStageRecoveryGoal : CompatibleStageRecoveryGoal.{u, v} := by
  intro ι _ _ _ S _ _ Ω
  exact ReconstructionGNSDynamics.compatibleGeneralGNSRecoveryGoal Ω

/-- The completed theorem preserves the original mathematics and quantum
packages and adjoins the source-derived protocol, code, state and limit results.
The arbitrary state and the physical geometric family have distinct types. -/
def SingularityTheoryGoal : Prop :=
  BoundaryObservationSingularityGoal.{u, v, w, r, s} ∧
  DisjointReadingFrontierGoal ∧ ArbitraryPriorRecoveryGoal ∧
  ReconstructionCodeSpan.CodeSpanFullGoal ∧
  StateRepresentationGoal.{u} ∧ InvariantStateDynamicsGoal.{u} ∧
  CompatibleStageRecoveryGoal.{u, v} ∧
  UniversalObservation.Reconstruction.ThermalSourceCompletion.SameSourceCNOTGoal ∧
  ReconstructionEntropyTail.GuardedTailAndCountercontrolGoal

theorem singularityTheoryGoal : SingularityTheoryGoal.{u, v, w, r, s} :=
  ⟨boundaryObservationSingularityGoal.{u, v, w, r, s},
    disjointReadingFrontierGoal, arbitraryPriorRecoveryGoal,
    ReconstructionCodeSpan.codeSpanFullGoal,
    stateRepresentationGoal.{u}, invariantStateDynamicsGoal.{u},
    compatibleStageRecoveryGoal.{u, v},
    UniversalObservation.Reconstruction.ThermalSourceCompletion.sameSourceCNOTGoal,
    ReconstructionEntropyTail.guardedTailAndCountercontrolGoal⟩

/-- The completed theorem projects to the unchanged forty-clause mathematical package. -/
theorem theoryMathematicalProjection (h : SingularityTheoryGoal.{u, v, w, r, s}) :
    BoundaryTheoremFull.BoundaryTheoremFullGoal.{u, v, w, r, s} :=
  mathematicalProjection h.1

/-- The completed theorem projects to the unchanged forty-two quantum clauses. -/
theorem theoryQuantumProjection (h : SingularityTheoryGoal.{u, v, w, r, s}) :
    BoundaryTheorem.BoundaryTheoremGoal.{u} :=
  quantumProjection h.1

end

end OperatorKO7.Meta.BoundaryObserver.BoundaryObservationSingularity
