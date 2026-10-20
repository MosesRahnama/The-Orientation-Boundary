import OperatorKO7.Meta.BoundaryObserver.DemandCompletion
import OperatorKO7.Meta.BoundaryObserver.Instances.Recursor
import Mathlib.Computability.Halting

set_option autoImplicit false

/-!
M4.4 and M4.5 source results isolated from the DemandCompletion import chain.
Kernel status: direct check with 0 errors and 0 warnings, a fresh named build, and every
declaration within the axioms propext, Classical.choice and Quot.sound, 2026-10-18.
-/

namespace UniversalObservation.Completion

open Demand Transport Set

/-! ## M4.4: a source-instantiated limit on total boundary detection -/

namespace RepresentedDetector

/-- The source uses the pinned partial-recursive code evaluator at input zero.
The evaluator includes primitive recursion and unbounded minimization. -/
def representedSourceHalt (c : Nat.Partrec.Code) : Prop :=
  (Nat.Partrec.Code.eval c 0).Dom

/-- An absent result is the concrete obstruction for the same source evaluator. -/
def representedSourceBoundary (c : Nat.Partrec.Code) : Prop :=
  ¬ representedSourceHalt c

/-- Soundness and completeness refer to the exact source evaluator and input. -/
def RepresentedBoundaryDetectorCorrect (detect : Nat.Partrec.Code → Bool) : Prop :=
  (∀ c, detect c = true → representedSourceBoundary c) ∧
    (∀ c, representedSourceBoundary c → detect c = true)

/-- Both reductions from the detector to the boundary predicate are explicit. -/
theorem represented_boundary_detector_iff (detect : Nat.Partrec.Code → Bool)
    (h : RepresentedBoundaryDetectorCorrect detect) (c : Nat.Partrec.Code) :
    detect c = true ↔ representedSourceBoundary c :=
  ⟨h.1 c, h.2 c⟩

/-- The represented class contains a concrete terminating source program. -/
theorem represented_source_has_result :
    ∃ c : Nat.Partrec.Code, representedSourceHalt c := by
  refine ⟨Nat.Partrec.Code.zero, ?_⟩
  change (Part.some (0 : ℕ)).Dom
  trivial

/-- The represented class also contains a genuinely undefined source program. -/
theorem represented_source_has_missing_result :
    ∃ c : Nat.Partrec.Code, representedSourceBoundary c := by
  have hp : Nat.Partrec (fun _ : ℕ => (Part.none : Part ℕ)) := Nat.Partrec.none
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hp
  refine ⟨c, ?_⟩
  intro h
  have hf : (Part.none : Part ℕ).Dom := by
    simpa only [representedSourceHalt, hc] using h
  exact hf

/-- No computable Boolean function is sound and complete for all nonhalting
codes of the concrete partial-recursive evaluator. This does not restrict
finite incidence search or the separately proved counted-recursion decider. -/
theorem no_computable_represented_boundary_detector :
    ¬ ∃ detect : Nat.Partrec.Code → Bool,
      Computable detect ∧ RepresentedBoundaryDetectorCorrect detect := by
  rintro ⟨detect, hcomputable, hcorrect⟩
  have hdetect : ComputablePred (fun c : Nat.Partrec.Code => detect c = true) := by
    apply (ComputablePred.computable_iff).2
    refine ⟨detect, hcomputable, ?_⟩
    funext c
    cases h : detect c <;> rfl
  have hboundary : ComputablePred representedSourceBoundary :=
    ComputablePred.of_eq hdetect (represented_boundary_detector_iff detect hcorrect)
  exact ComputablePred.halting_problem_not_re 0 (ComputablePred.to_re hboundary)

end RepresentedDetector

/-- The exact specification-level core quantifies over every retained source contract. -/
def UniversalCoreGoal : Prop := ∀ C : SourceContract, CoreGoal C

/-- The universal schema follows from the source-indexed core for each contract. -/
theorem universalCoreGoal : UniversalCoreGoal :=
  fun C => source_observation_repair_core C

/-! ## M4.5: native source contracts for the five demand adapters -/

namespace RecursorSource

open OperatorKO7 (Trace)
open OperatorKO7.Meta.BoundaryObserver.RecursorDecidability (content counter observed)

/-- Only selectors invariant under a change of the pass counter are licensed. -/
def contentSelectors (k : ℕ) : Set ((Trace × ℕ) → Fin k) :=
  {s | ∀ (R : Trace) (n m : ℕ), s (R, n) = s (R, m)}

/-- A counted-recursion source with native content and observed-target readouts.
The zero cost coordinate is an unpriced logical fixture, not a runtime estimate. -/
def contract : SourceContract :=
  readoutSource (Trace × ℕ) Trace Bool content observed
    (Set.univ : Set (Trace → Bool)) contentSelectors
    (fun _ _ _ => True) (fun _ _ => 0)

/-- The incidence predicate is exactly the imported counted-recursion adapter. -/
theorem native_problem :
    contract.problem = Transport.RecursorAdapter.contentProblem := rfl

/-- Selecting an available content readout has the same pointwise native semantics. -/
theorem combinerLaw : contract.combinerLaw := by
  intro D k s ws _ _ hw
  exact hw

/-- Every component of the source-bound universal core refers to this same run. -/
theorem core : CoreGoal contract :=
  source_observation_repair_core contract

/-- Counter-dependent observation is feasible, but content-only observation fails. -/
theorem content_blindness_control :
    ¬ Good contract.problem Set.univ ∧
      Good (readoutProblem (counter (T := Trace)) (observed (T := Trace))
        (Set.univ : Set (ℕ → Bool))) Set.univ := by
  constructor
  · rw [native_problem]
    exact Transport.RecursorAdapter.content_zero_test_obstruction
  · exact Transport.RecursorAdapter.counter_zero_test_witness

end RecursorSource

namespace EvaluatorSource

/-- The process is an evaluated code row; the target is the changed old diagonal.
The logical cost coordinate remains unpriced. -/
def contract (C V : Type) (E : C → C → V) (j : V → V) : SourceContract where
  Process := C → V
  Input := C
  Output := V
  Witness := C
  source := fun x => j (E x x)
  evaluate := fun p x => p x
  interpret := fun c x => E c x
  allowed := fun _ => Set.univ
  combines := fun _ _ _ => True
  assemble := fun _ s ws x => E (ws (s x)) x
  cost := fun _ _ => 0

/-- The native source problem reuses the actual original evaluator table. -/
theorem native_problem (C V : Type) (E : C → C → V) (j : V → V) :
    (contract C V E j).problem = diagonalProblem E j := rfl

/-- Each assembled evaluated row satisfies the same original target equation. -/
theorem combinerLaw (C V : Type) (E : C → C → V) (j : V → V) :
    (contract C V E j).combinerLaw := by
  intro D k s ws _ _ hw
  exact hw

/-- The source-indexed theorem specializes to any actual evaluator and code table. -/
theorem core (C V : Type) (E : C → C → V) (j : V → V) :
    CoreGoal (contract C V E j) :=
  source_observation_repair_core _

/-- The pinned paired evaluator supplies a concrete two-coordinate code source. -/
def paired : SourceContract :=
  contract (ℕ × Bool) Bool
    OperatorKO7.Meta.BoundaryObserver.SelfEvaluationBounds.pairedEval Bool.not

/-- Every old row retains the same table under the one-code extension. -/
theorem paired_extension_preserves_table :
    ∀ c x : ℕ × Bool,
      extendEval OperatorKO7.Meta.BoundaryObserver.SelfEvaluationBounds.pairedEval
        Bool.not false (some c) (some x) =
      OperatorKO7.Meta.BoundaryObserver.SelfEvaluationBounds.pairedEval c x :=
  fun _ _ => rfl

/-- The added code represents the old complemented diagonal exactly. -/
theorem paired_extension_reads_old_diagonal :
    ∀ x : ℕ × Bool,
      extendEval OperatorKO7.Meta.BoundaryObserver.SelfEvaluationBounds.pairedEval
        Bool.not false none (some x) =
      !(OperatorKO7.Meta.BoundaryObserver.SelfEvaluationBounds.pairedEval x x) :=
  fun _ => rfl

/-- The original paired source excludes its complemented diagonal. -/
theorem paired_exclusion : ¬ Good paired.problem Set.univ := by
  apply source_diagonal_exclusion paired (Equiv.refl (ℕ × Bool)) Bool.not
  · intro v
    change Bool.not v ≠ v
    cases v <;> decide
  · intro w
    rfl

/-- The paired source is a full instance of the source-indexed core. -/
theorem paired_core : CoreGoal paired := source_observation_repair_core _

/-- The fixed-point-free premise cannot be dropped from a general exclusion claim. -/
theorem identity_change_control :
    Good (contract Unit Bool (fun _ _ => false) id).problem Set.univ ∧
      ¬ (∀ v : Bool, id v ≠ v) := by
  constructor
  · exact ⟨(), fun _ _ => rfl⟩
  · intro h
    exact h false rfl

end EvaluatorSource

namespace StochasticSource

/-- A source equation is retained for each positive-probability input/output pair.
The incidence contract records no information-theoretic cost by itself. -/
def contract {X Y V : Type} (K : X → Y → ℝ) (T : X → V) : SourceContract where
  Process := {xy : X × Y // 0 < K xy.1 xy.2} → V
  Input := {xy : X × Y // 0 < K xy.1 xy.2}
  Output := V
  Witness := Y → V
  source := fun xy => T xy.val.1
  evaluate := fun p xy => p xy
  interpret := fun d xy => d xy.val.2
  allowed := fun _ => Set.univ
  combines := fun _ _ _ => True
  assemble := fun _ s ws xy => ws (s xy) xy.val.2
  cost := fun _ _ => 0

/-- The incidence equation is definitionally the original positive-support adapter. -/
theorem native_problem {X Y V : Type} (K : X → Y → ℝ) (T : X → V) :
    (contract K T).problem = Transport.supportProblem K T := rfl

/-- Every selected support decoder respects the original input/output incidence. -/
theorem combinerLaw {X Y V : Type} (K : X → Y → ℝ) (T : X → V) :
    (contract K T).combinerLaw := by
  intro D k s ws _ _ hw
  exact hw

/-- The core applies to the unchanged positive-support incidence relation. -/
theorem core {X Y V : Type} (K : X → Y → ℝ) (T : X → V) :
    CoreGoal (contract K T) := source_observation_repair_core _

/-- The normalized instrument furnishes its native joint support.
Its numerical weights do not follow from support incidence alone. -/
noncomputable def instrument {X Y Z V : Type} [Fintype Y] [Fintype Z]
    (I : OperatorKO7.Meta.BoundaryObserver.InstrumentLoss.StochasticInstrument X Y Z)
    (T : X → V) : SourceContract :=
  contract (OperatorKO7.Meta.BoundaryObserver.InstrumentComposition.jointChannel I).prob T

/-- The instrument source uses the exact native stochastic-instrument adapter. -/
theorem instrument_native_problem {X Y Z V : Type} [Fintype Y] [Fintype Z]
    (I : OperatorKO7.Meta.BoundaryObserver.InstrumentLoss.StochasticInstrument X Y Z)
    (T : X → V) :
    (instrument I T).problem = Transport.InstrumentAdapter.instrumentProblem I T := rfl

/-- The retained instrument and its output supports share the same source contract. -/
theorem instrument_core {X Y Z V : Type} [Fintype Y] [Fintype Z]
    (I : OperatorKO7.Meta.BoundaryObserver.InstrumentLoss.StochasticInstrument X Y Z)
    (T : X → V) :
    CoreGoal (instrument I T) := source_observation_repair_core _

/-- Exact retained output permits restoration, while erased output does not. -/
theorem silent_keep_erase_control :
    Good (instrument
      (OperatorKO7.Meta.BoundaryObserver.InstrumentComposition.deterministic
        OperatorKO7.Meta.BoundaryObserver.InstrumentLoss.silentKeep)
      (id : Bool → Bool)).problem Set.univ ∧
    ¬ Good (instrument
      (OperatorKO7.Meta.BoundaryObserver.InstrumentComposition.deterministic
        OperatorKO7.Meta.BoundaryObserver.InstrumentLoss.silentErase)
      (id : Bool → Bool)).problem Set.univ :=
  Transport.InstrumentAdapter.silent_keep_erase_incidence_control

/-- A uniform binary observation law. -/
noncomputable def fair (_x _y : Bool) : ℝ := 1 / 2

/-- A normalized law that favors the outcome matching the input bit. -/
noncomputable def correlated (x y : Bool) : ℝ := if x = y then 3 / 4 else 1 / 4

/-- Equal full supports do not identify normalized stochastic probabilities. -/
theorem same_support_different_laws :
    (∀ x y : Bool, 0 < fair x y ∧ 0 < correlated x y) ∧
      fair true true ≠ correlated true true ∧
      (∀ x : Bool, fair x false + fair x true = 1) ∧
      (∀ x : Bool, correlated x false + correlated x true = 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y
    cases x <;> cases y <;> norm_num [fair, correlated]
  · norm_num [fair, correlated]
  · intro x
    norm_num [fair]
  · intro x
    cases x <;> norm_num [correlated]

/-- Under the same fair input prior, the output-true posterior separates the laws. -/
noncomputable def truePosterior (K : Bool → Bool → ℝ) : ℝ :=
  K true true / (K true true + K false true)

/-- Full-support laws can carry different conditional information. -/
theorem same_support_different_posteriors :
    truePosterior fair = 1 / 2 ∧ truePosterior correlated = 3 / 4 := by
  constructor
  · norm_num [truePosterior, fair]
  · norm_num [truePosterior, correlated]

end StochasticSource

namespace CommonLawSource

open scoped BigOperators

open OperatorKO7.Meta.BoundaryObserver.ObserverRealization (triangleReport triangle_optimal_repair realizable_vertex)

/-- The candidate is the original normalized assignment law over the entire source carrier.
The logical cost coordinate does not assert a physical expense. -/
def contract {A J : Type} [Fintype A] (v : A → J → ℝ) (p : J → ℝ) :
    SourceContract where
  Process := J → ℝ
  Input := J
  Output := ℝ
  Witness := Transport.AssignmentLaw A
  source := p
  evaluate := fun q j => q j
  interpret := fun w j => ∑ a, w.val a * v a j
  allowed := fun _ => Set.univ
  combines := fun _ _ _ => True
  assemble := fun _ s ws j => ∑ a, (ws (s j)).val a * v a j
  cost := fun _ _ => 0

/-- Demand satisfaction is the exact common marginal-law equation. -/
theorem native_problem {A J : Type} [Fintype A] (v : A → J → ℝ) (p : J → ℝ) :
    (contract v p).problem = Transport.commonLawProblem v p := rfl

/-- Local weighted assignments combine by preserving the source report equations. -/
theorem combinerLaw {A J : Type} [Fintype A] (v : A → J → ℝ) (p : J → ℝ) :
    (contract v p).combinerLaw := by
  intro D k s ws _ _ hw
  exact hw

/-- The finite common-law source receives its exact general core specialization. -/
theorem core {A J : Type} [Fintype A] (v : A → J → ℝ) (p : J → ℝ) :
    CoreGoal (contract v p) := source_observation_repair_core _

/-- The original three-context incompatibility uses its native assignment laws. -/
def triangle : SourceContract := contract triangleReport (fun _ => 1)

/-- Each original triangle demand can be solved by a deterministic assignment. -/
def edgeAssignment : Fin 3 → Bool × Bool × Bool :=
  ![(true, false, false), (false, true, false), (false, false, true)]

theorem edgeAssignment_satisfies (j : Fin 3) :
    triangleReport (edgeAssignment j) j = 1 := by
  fin_cases j <;> norm_num [edgeAssignment, triangleReport]

/-- Every single marginal demand is satisfied in the same source problem. -/
theorem triangle_singleton_good (j : Fin 3) :
    Good triangle.problem ({j} : Set (Fin 3)) := by
  have hvertex :
      Good (Transport.commonLawProblem triangleReport (triangleReport (edgeAssignment j)))
        Set.univ :=
    (Transport.common_law_good_iff _ _).mpr
      (realizable_vertex triangleReport (edgeAssignment j))
  obtain ⟨w, hw⟩ := hvertex
  change Good (Transport.commonLawProblem triangleReport (fun _ => 1))
    ({j} : Set (Fin 3))
  refine ⟨w, ?_⟩
  intro i hi
  have hij : i = j := Set.mem_singleton_iff.mp hi
  subst i
  exact (hw j (Set.mem_univ j)).trans (edgeAssignment_satisfies j)

/-- The three individually satisfiable demands have no joint assignment law. -/
theorem triangle_global_obstruction : ¬ Good triangle.problem Set.univ :=
  Transport.triangle_demand_obstruction

/-- The original assignments admit the exact explicit repaired target. -/
noncomputable def repairedTriangle : SourceContract := contract triangleReport (fun _ => (2 : ℝ) / 3)

/-- The repaired same-carrier source has a normalized common law. -/
theorem repaired_triangle_good : Good repairedTriangle.problem Set.univ := by
  change Good (Transport.commonLawProblem triangleReport
    (fun _ => (2 : ℝ) / 3)) Set.univ
  exact (Transport.common_law_good_iff _ _).mpr triangle_optimal_repair.1

/-- Both unrepaired and repaired targets use the same source-bound theorem schema. -/
theorem triangle_cores : CoreGoal triangle ∧ CoreGoal repairedTriangle :=
  ⟨source_observation_repair_core _, source_observation_repair_core _⟩

end CommonLawSource

namespace AffineSource

open OperatorKO7.Meta.BoundaryObserver.AffineSelfObservation (Bit affineRows affineRhs copy_kernel_vector negation_row_refutation)

/-- Source witnesses are the original vectors, not arbitrary row-value functions.
The equation indices and field coefficients remain native to the original system. -/
def contract {K V I : Type} [Field K] [AddCommGroup V] [Module K V]
    (rows : I → V →ₗ[K] K) (b : I → K) : SourceContract where
  Process := I → K
  Input := I
  Output := K
  Witness := V
  source := b
  evaluate := fun p i => p i
  interpret := fun x i => rows i x
  allowed := fun _ => Set.univ
  combines := fun _ _ _ => True
  assemble := fun _ s ws i => rows i (ws (s i))
  cost := fun _ _ => 0

/-- The native source equation matches the affine-equation demand adapter. -/
theorem native_problem {K V I : Type} [Field K] [AddCommGroup V] [Module K V]
    (rows : I → V →ₗ[K] K) (b : I → K) :
    (contract rows b).problem = Transport.affineEquationProblem rows b := rfl

/-- The source combiner enforces each selected native linear equation. -/
theorem combinerLaw {K V I : Type} [Field K] [AddCommGroup V] [Module K V]
    (rows : I → V →ₗ[K] K) (b : I → K) :
    (contract rows b).combinerLaw := by
  intro D k s ws _ _ hw
  exact hw

/-- The core is instantiated at the full unchanged native row family. -/
theorem core {K V I : Type} [Field K] [AddCommGroup V] [Module K V]
    (rows : I → V →ₗ[K] K) (b : I → K) :
    CoreGoal (contract rows b) := source_observation_repair_core _

/-- The pinned finite-field source preserves the actual equations for each mode. -/
def mode (m : Fin 3) : SourceContract :=
  contract (affineRows m) (affineRhs m)

/-- The unnegated source has the witnessed zero assignment. -/
theorem copy_mode_good : Good (mode 0).problem Set.univ := by
  refine ⟨(0, 0), ?_⟩
  intro i _
  exact copy_kernel_vector.1 i

/-- The negating source contradicts its own sum-of-rows certificate. -/
theorem negation_mode_bad : ¬ Good (mode 1).problem Set.univ := by
  rintro ⟨x, hx⟩
  have h0 : affineRows 1 0 x = affineRhs 1 0 := hx (0 : Fin 2) (Set.mem_univ (0 : Fin 2))
  have h1 : affineRows 1 1 x = affineRhs 1 1 := hx (1 : Fin 2) (Set.mem_univ (1 : Fin 2))
  have hzero : affineRows 1 0 x + affineRows 1 1 x = 0 := by
    have hrow := congrArg
      (fun f : (Bit × Bit) →ₗ[Bit] Bit => f x) negation_row_refutation.1
    exact hrow
  have hone : (1 : Bit) = 0 := by
    calc
      1 = affineRhs 1 0 + affineRhs 1 1 := negation_row_refutation.2.symm
      _ = affineRows 1 0 x + affineRows 1 1 x := by rw [← h0, ← h1]
      _ = 0 := hzero
  exact (by decide : (1 : Bit) ≠ 0) hone

/-- Native satisfiable and incompatible sources both instantiate the shared core. -/
theorem mode_cores : CoreGoal (mode 0) ∧ CoreGoal (mode 1) :=
  ⟨source_observation_repair_core _, source_observation_repair_core _⟩

/-- Invertible row mixing preserves the global solutions but can alter subproblems. -/
theorem row_mixing_scope_control :
    Good (Transport.equationProblem (fun x : ℝ => ![x, x])
      (![0, 1] : Fin 2 → ℝ)) ({1} : Set (Fin 2)) ∧
    ¬ Good (Transport.equationProblem
      (fun x : ℝ => Transport.rowShear ![x, x])
      (Transport.rowShear ![0, 1])) ({1} : Set (Fin 2)) ∧
    Witnesses (Transport.equationProblem
      (fun x : ℝ => Transport.rowShear ![x, x])
      (Transport.rowShear ![0, 1])) Set.univ =
    Witnesses (Transport.equationProblem (fun x : ℝ => ![x, x])
      (![0, 1] : Fin 2 → ℝ)) Set.univ :=
  Transport.row_mixing_changes_restrictions

/-- A noninjective row map is not licensed as an invertible row equivalence. -/
theorem collapsed_row_not_injective :
    ¬ Function.Injective (fun _ : ℝ => (0 : ℝ)) := by
  intro h
  have h01 : (0 : ℝ) = 1 := h rfl
  norm_num at h01

end AffineSource

/-! ## M4.5: source-level controls for omitted hypotheses -/

namespace PremiseControls

/-- A witness-free source remains witness-free even for an empty demand set. -/
def emptyWitness : SourceContract where
  Process := Unit
  Input := Unit
  Output := Unit
  Witness := Empty
  source := ()
  evaluate := fun _ _ => ()
  interpret := fun w => nomatch w
  allowed := fun _ => Set.univ
  combines := fun _ _ _ => True
  assemble := fun _ _ _ => ()
  cost := fun _ _ => 0

theorem emptyWitness_not_good (D : Set Unit) :
    ¬ Good emptyWitness.problem D := by
  rintro ⟨w, _⟩
  cases w

theorem emptyWitness_core : CoreGoal emptyWitness :=
  source_observation_repair_core _

/-- A source can have an admissible witness but refuse every combination license. -/
def deniedCombination : SourceContract where
  Process := Unit
  Input := Unit
  Output := Unit
  Witness := Unit
  source := ()
  evaluate := fun _ _ => ()
  interpret := fun _ => ()
  allowed := fun _ => Set.univ
  combines := fun _ _ _ => False
  assemble := fun _ _ _ => ()
  cost := fun _ _ => 0

theorem deniedCombination_combinerLaw : deniedCombination.combinerLaw := by
  intro D k s ws _ hfalse _
  cases hfalse

/-- Native witness success does not authorize an unlicensed assembly. -/
theorem deniedCombination_control :
    Good deniedCombination.problem Set.univ ∧
      ¬ RepairFeasible deniedCombination.problem deniedCombination.menu Set.univ 1 := by
  constructor
  · exact ⟨(), fun _ _ => rfl⟩
  · rintro ⟨s, _, hfalse, ws, _⟩
    exact hfalse

theorem deniedCombination_core : CoreGoal deniedCombination :=
  source_observation_repair_core _

/-- The original threshold instance is expressed as a source-indexed Boolean evaluator. -/
def threshold : SourceContract where
  Process := ℕ → Bool
  Input := ℕ
  Output := Bool
  Witness := ℕ
  source := fun _ => true
  evaluate := fun p i => p i
  interpret := fun w i => decide (i ≤ w)
  allowed := fun _ => Set.univ
  combines := fun _ _ _ => True
  assemble := fun _ s ws i => decide (i ≤ ws (s i))
  cost := fun _ _ => 0

theorem threshold_satisfaction (w i : ℕ) :
    threshold.problem.sat w i ↔ thresholdProblem.sat w i := by
  change decide (i ≤ w) = true ↔ i ≤ w
  simp only [decide_eq_true_eq]

/-- Every finite threshold demand succeeds, but the entire infinite family fails. -/
theorem threshold_finite_not_global :
    (∀ D : Finset ℕ, Good threshold.problem (D : Set ℕ)) ∧
      ¬ Good threshold.problem Set.univ := by
  constructor
  · intro D
    obtain ⟨w, hw⟩ := threshold_finite_good D
    exact ⟨w, fun i hi => (threshold_satisfaction w i).mpr (hw i hi)⟩
  · rintro ⟨w, hw⟩
    exact threshold_global_bad
      ⟨w, fun i hi => (threshold_satisfaction w i).mp (hw i hi)⟩

theorem threshold_core : CoreGoal threshold := source_observation_repair_core _

/-- Permitted threshold readouts are the actual finite-bound rows of the source evaluator. -/
def thresholdLanguage : Set (ℕ → Bool) :=
  Set.range (fun w : ℕ => fun i : ℕ => decide (i ≤ w))

/-- Finite agreement with the all-true readout does not make it a permitted readout. -/
theorem threshold_language_not_closed : ¬ IsClosed thresholdLanguage := by
  intro hclosed
  have hfin : ∀ D : Finset ℕ, ∃ f ∈ thresholdLanguage,
      ∀ i ∈ D, f i = true := by
    intro D
    obtain ⟨w, hw⟩ := threshold_finite_good D
    refine ⟨(fun i => decide (i ≤ w)), ⟨w, rfl⟩, ?_⟩
    intro i hi
    exact (decide_eq_true_eq).mpr (hw i hi)
  have hmem : (fun _ : ℕ => true) ∈ thresholdLanguage :=
    (closed_readouts_iff thresholdLanguage).mp hclosed (fun _ => true) hfin
  obtain ⟨w, hw⟩ := hmem
  have hle : w + 1 ≤ w :=
    (decide_eq_true_eq).mp (congrFun hw (w + 1))
  exact Nat.not_succ_le_self w hle

end PremiseControls

/-! ## M4.4: halting reduction through an actual source demand -/

/-- A candidate witness is a finite evaluator budget and an output obtained
within that budget. The source target is success of the partial-recursive program
on input zero. The declared zero cost is only an unpriced logical coordinate. -/
def boundedHaltingSource (c : Nat.Partrec.Code) : SourceContract where
  Process := Bool
  Input := Unit
  Output := Bool
  Witness := ℕ × ℕ
  source := true
  evaluate := fun p _ => p
  interpret := fun w => decide (w.2 ∈ Nat.Partrec.Code.evaln w.1 c 0)
  allowed := fun _ => Set.univ
  combines := fun _ _ _ => True
  assemble := fun _ s ws =>
    decide ((ws (s ())).2 ∈ Nat.Partrec.Code.evaln (ws (s ())).1 c 0)
  cost := fun _ _ => 0

/-- The source incidence is precisely the finite evaluation witness relation. -/
theorem boundedHaltingSource_sat_iff (c : Nat.Partrec.Code) (w : ℕ × ℕ) :
    (boundedHaltingSource c).problem.sat w () ↔
      w.2 ∈ Nat.Partrec.Code.evaln w.1 c 0 := by
  change decide (w.2 ∈ Nat.Partrec.Code.evaln w.1 c 0) = true ↔
    w.2 ∈ Nat.Partrec.Code.evaln w.1 c 0
  simp only [decide_eq_true_eq]

/-- Assembly uses the selected finite evaluator witness at the same input. -/
theorem boundedHaltingSource_combinerLaw (c : Nat.Partrec.Code) :
    (boundedHaltingSource c).combinerLaw := by
  intro D k s ws _ _ hw i hi
  cases i
  exact hw () hi

/-- Source feasibility is equivalent in both directions to semantic halting of
the represented program, by completeness and soundness of bounded evaluation. -/
theorem boundedHaltingSource_good_iff (c : Nat.Partrec.Code) :
    Good (boundedHaltingSource c).problem Set.univ ↔ RepresentedDetector.representedSourceHalt c := by
  constructor
  · rintro ⟨w, hw⟩
    have hf : w.2 ∈ Nat.Partrec.Code.evaln w.1 c 0 :=
      (boundedHaltingSource_sat_iff c w).mp (hw () (Set.mem_univ ()))
    have hv : w.2 ∈ Nat.Partrec.Code.eval c 0 :=
      (Nat.Partrec.Code.evaln_complete).mpr ⟨w.1, hf⟩
    exact Part.dom_iff_mem.mpr ⟨w.2, hv⟩
  · intro h
    obtain ⟨v, hv⟩ := Part.dom_iff_mem.mp h
    obtain ⟨k, hk⟩ := (Nat.Partrec.Code.evaln_complete).mp hv
    refine ⟨(k, v), ?_⟩
    intro i _
    cases i
    exact (boundedHaltingSource_sat_iff c (k, v)).mpr hk

/-- The represented source family has both solvable and obstructed instances. -/
theorem boundedHaltingSource_both_statuses :
    (∃ c : Nat.Partrec.Code, Good (boundedHaltingSource c).problem Set.univ) ∧
      (∃ c : Nat.Partrec.Code, ¬ Good (boundedHaltingSource c).problem Set.univ) := by
  constructor
  · obtain ⟨c, hc⟩ := RepresentedDetector.represented_source_has_result
    exact ⟨c, (boundedHaltingSource_good_iff c).mpr hc⟩
  · obtain ⟨c, hc⟩ := RepresentedDetector.represented_source_has_missing_result
    exact ⟨c, fun h => hc ((boundedHaltingSource_good_iff c).mp h)⟩

/-- A proposed source detector has both exact evaluation equations. The
positive answer is nonhalting; the negative answer is halting. -/
theorem boundedHaltingSource_detector_equations
    (detect : Nat.Partrec.Code → Bool)
    (hcorrect : ∀ c, detect c = true ↔
      ¬ Good (boundedHaltingSource c).problem Set.univ)
    (c : Nat.Partrec.Code) :
    (detect c = true ↔ ¬ RepresentedDetector.representedSourceHalt c) ∧
      (detect c = false ↔ RepresentedDetector.representedSourceHalt c) := by
  have hyes : detect c = true ↔ ¬ RepresentedDetector.representedSourceHalt c := by
    constructor
    · intro hd hh
      exact (hcorrect c).mp hd ((boundedHaltingSource_good_iff c).mpr hh)
    · intro hn
      exact (hcorrect c).mpr (fun hg => hn ((boundedHaltingSource_good_iff c).mp hg))
  refine ⟨hyes, ?_⟩
  constructor
  · intro hd
    by_contra hh
    have ht : detect c = true := hyes.mpr hh
    have hf : (false : Bool) = true := hd.symm.trans ht
    cases hf
  · intro hh
    cases hd : detect c with
    | false => rfl
    | true => exact False.elim ((hyes.mp hd) hh)

/-- There is no computable total detector sound and complete for obstruction
of every represented source in this explicit evaluator family. No failure of
finite incidence search or of the counted-recursion decider follows. -/
theorem no_computable_source_obstruction_detector :
    ¬ ∃ detect : Nat.Partrec.Code → Bool,
      Computable detect ∧
        ∀ c, detect c = true ↔
          ¬ Good (boundedHaltingSource c).problem Set.univ := by
  rintro ⟨detect, hcomputable, hcorrect⟩
  apply RepresentedDetector.no_computable_represented_boundary_detector
  refine ⟨detect, hcomputable, ?_⟩
  constructor
  · intro c hyes hh
    exact (hcorrect c).mp hyes ((boundedHaltingSource_good_iff c).mpr hh)
  · intro c hn
    apply (hcorrect c).mpr
    intro hgood
    exact hn ((boundedHaltingSource_good_iff c).mp hgood)

/-- The full conditional core also holds for every concrete halting source,
without treating its logical cost coordinate as a physical budget. -/
theorem boundedHaltingSource_core (c : Nat.Partrec.Code) :
    CoreGoal (boundedHaltingSource c) :=
  source_observation_repair_core _

/-! ## M4.4: exact false negatives of every fixed evaluator budget -/

/-- A bounded-evaluation source for an arbitrary original input. The original
zero-input source is its literal specialization. Every witness retains both the
finite evaluator budget and the returned program output. -/
def boundedHaltingSourceAt (c : Nat.Partrec.Code) (input : ℕ) : SourceContract where
  Process := Bool
  Input := Unit
  Output := Bool
  Witness := ℕ × ℕ
  source := true
  evaluate := fun p _ => p
  interpret := fun w => decide (w.2 ∈ Nat.Partrec.Code.evaln w.1 c input)
  allowed := fun _ => Set.univ
  combines := fun _ _ _ => True
  assemble := fun _ s ws =>
    decide ((ws (s ())).2 ∈ Nat.Partrec.Code.evaln (ws (s ())).1 c input)
  cost := fun _ _ => 0

/-- The generalized source has exactly the original zero-input interpretation. -/
theorem boundedHaltingSourceAt_zero (c : Nat.Partrec.Code) :
    boundedHaltingSourceAt c 0 = boundedHaltingSource c := rfl

/-- Its native demand is precisely a successful bounded evaluator execution. -/
theorem boundedHaltingSourceAt_sat_iff (c : Nat.Partrec.Code) (input : ℕ)
    (w : ℕ × ℕ) :
    (boundedHaltingSourceAt c input).problem.sat w () ↔
      w.2 ∈ Nat.Partrec.Code.evaln w.1 c input := by
  change decide (w.2 ∈ Nat.Partrec.Code.evaln w.1 c input) = true ↔
    w.2 ∈ Nat.Partrec.Code.evaln w.1 c input
  simp only [decide_eq_true_eq]

/-- The source combiner retains the very same evaluator result at the demand. -/
theorem boundedHaltingSourceAt_combinerLaw (c : Nat.Partrec.Code) (input : ℕ) :
    (boundedHaltingSourceAt c input).combinerLaw := by
  intro D k s ws _ _ hw i hi
  cases i
  exact hw () hi

/-- Source feasibility and semantic evaluation agree in both directions, at
every program and input, with no boundedness assumption on the witness budget. -/
theorem boundedHaltingSourceAt_good_iff (c : Nat.Partrec.Code) (input : ℕ) :
    Good (boundedHaltingSourceAt c input).problem Set.univ ↔
      (Nat.Partrec.Code.eval c input).Dom := by
  constructor
  · rintro ⟨w, hw⟩
    have hf : w.2 ∈ Nat.Partrec.Code.evaln w.1 c input :=
      (boundedHaltingSourceAt_sat_iff c input w).mp (hw () (Set.mem_univ ()))
    have hv : w.2 ∈ Nat.Partrec.Code.eval c input :=
      (Nat.Partrec.Code.evaln_complete).mpr ⟨w.1, hf⟩
    exact Part.dom_iff_mem.mpr ⟨w.2, hv⟩
  · intro h
    obtain ⟨v, hv⟩ := Part.dom_iff_mem.mp h
    obtain ⟨k, hk⟩ := (Nat.Partrec.Code.evaln_complete).mp hv
    refine ⟨(k, v), ?_⟩
    intro i _
    cases i
    exact (boundedHaltingSourceAt_sat_iff c input (k, v)).mpr hk

/-- The bounded evaluator returns no result on input equal to its budget,
independently of the program. This follows from the pinned evaluator guard. -/
theorem evaln_input_budget_none (budget : ℕ) (c : Nat.Partrec.Code) :
    Nat.Partrec.Code.evaln budget c budget = none := by
  cases h : Nat.Partrec.Code.evaln budget c budget with
  | none => rfl
  | some x =>
    have hx : x ∈ Nat.Partrec.Code.evaln budget c budget := by
      rw [h]
      rfl
    exact False.elim ((Nat.lt_irrefl budget) (Nat.Partrec.Code.evaln_bound hx))

/-- Every budget admits a satisfiable and an obstructed source on the same
input, with identical unresolved bounded evaluator records. The full semantic
statuses are checked against the unbounded evaluator, not inferred from none. -/
theorem finite_budget_same_record_opposite_statuses (budget : ℕ) :
    ∃ (cSuccess cFailure : Nat.Partrec.Code),
      Good (boundedHaltingSourceAt cSuccess budget).problem Set.univ ∧
      ¬ Good (boundedHaltingSourceAt cFailure budget).problem Set.univ ∧
      Nat.Partrec.Code.evaln budget cSuccess budget = none ∧
      Nat.Partrec.Code.evaln budget cFailure budget = none := by
  have hp : Nat.Partrec (fun _ : ℕ => (Part.none : Part ℕ)) :=
    Nat.Partrec.none
  obtain ⟨cFailure, hFailure⟩ := Nat.Partrec.Code.exists_code.mp hp
  refine ⟨Nat.Partrec.Code.zero, cFailure, ?_, ?_, ?_, ?_⟩
  · apply (boundedHaltingSourceAt_good_iff _ _).mpr
    change (Part.some (0 : ℕ)).Dom
    trivial
  · intro hGood
    have hDom := (boundedHaltingSourceAt_good_iff cFailure budget).mp hGood
    have hFalse : (Part.none : Part ℕ).Dom := by
      simpa only [hFailure] using hDom
    exact hFalse
  · exact evaln_input_budget_none budget Nat.Partrec.Code.zero
  · exact evaln_input_budget_none budget cFailure

/-- No Boolean classifier of only the budgeted evaluation record recognizes
all source successes, even with no computability restriction on the classifier.
The limitation is strictly about fixed-budget records, not all source algorithms. -/
theorem no_uniform_fixed_budget_record_classifier (budget : ℕ) :
    ¬ ∃ classify : Option ℕ → Bool,
      ∀ c : Nat.Partrec.Code,
        (classify (Nat.Partrec.Code.evaln budget c budget) = true ↔
          Good (boundedHaltingSourceAt c budget).problem Set.univ) := by
  rintro ⟨classify, hCorrect⟩
  obtain ⟨cSuccess, cFailure, hSuccess, hFailure, hRecordSuccess,
    hRecordFailure⟩ := finite_budget_same_record_opposite_statuses budget
  have hYes : classify (Nat.Partrec.Code.evaln budget cSuccess budget) = true :=
    (hCorrect cSuccess).mpr hSuccess
  have hNo : ¬ classify (Nat.Partrec.Code.evaln budget cFailure budget) = true :=
    fun h => hFailure ((hCorrect cFailure).mp h)
  rw [hRecordSuccess] at hYes
  rw [hRecordFailure] at hNo
  exact hNo hYes

/-- The general source also retains every clause of the unweakened conditional
core; resource exhaustion supplies no omitted kernel proof premise. -/
theorem boundedHaltingSourceAt_core (c : Nat.Partrec.Code) (input : ℕ) :
    CoreGoal (boundedHaltingSourceAt c input) :=
  source_observation_repair_core _

/-! ## M4.5: the counted-recursion selector license is nonvacuous -/

namespace RecursorSource

open OperatorKO7 (Trace)
open OperatorKO7.Meta.BoundaryObserver.RecursorDecidability (content observed)

/-- The finite restriction contains two passes of one actual recursor content.
The target changes when the counter reaches zero. -/
def twoCounterDemands (R : Trace) (n : ℕ) : Set (Trace × ℕ) :=
  {(R, 0), (R, n + 1)}

/-- The two demands have identical observed content and opposite native targets. -/
theorem twoCounter_observed_disagree (R : Trace) (n : ℕ) :
    content (R, 0) = content (R, n + 1) ∧
      observed (R, 0) = true ∧ observed (R, n + 1) = false :=
  ⟨rfl, rfl, rfl⟩

/-- No licensed repair can solve the two demands for any number of colors.
The obstruction is pointwise and holds for the full native readout language. -/
theorem no_licensed_twoCounter_repair (R : Trace) (n k : ℕ) :
    ¬ RepairFeasible contract.problem contract.menu (twoCounterDemands R n) k := by
  rintro ⟨s, hs, _hc, ws, hw⟩
  change s ∈ contentSelectors k at hs
  have hsamed : s (R, 0) = s (R, n + 1) := hs R 0 (n + 1)
  have hzero := hw (R, 0) (by simp [twoCounterDemands])
  have hsucc := hw (R, n + 1) (by simp [twoCounterDemands])
  change (ws (s (R, 0))).val R = true at hzero
  change (ws (s (R, n + 1))).val R = false at hsucc
  rw [← hsamed] at hsucc
  have hfalse : (true : Bool) = false := hzero.symm.trans hsucc
  cases hfalse

/-- Each individual counter demand admits a native content readout. -/
theorem each_counter_singleton_good (x : Trace × ℕ) :
    Good contract.problem ({x} : Set (Trace × ℕ)) := by
  refine ⟨⟨fun _ => observed x, Set.mem_univ _⟩, ?_⟩
  intro y hy
  have heq : y = x := by simpa using hy
  subst y
  rfl

/-- Removing the selector-license restriction preserves the same source
equations and combination requirement but admits arbitrary selectors. -/
def unrestrictedMenu : RepairMenu contract.Input contract.Witness contract.problem where
  allowed := fun _ => Set.univ
  combines := fun _ _ _ => True

/-- This selector distinguishes zero from positive counters without changing
the original recursor state or its content readout. -/
def counterSplitSelector (x : Trace × ℕ) : Fin 2 :=
  match x.2 with
  | Nat.zero => 0
  | Nat.succ _ => 1

/-- The two witnesses are genuine content readouts, selected by the counter. -/
def counterSplitReadouts (i : Fin 2) : contract.Witness :=
  ⟨fun _ => if i = 0 then true else false, Set.mem_univ _⟩

/-- Removing only the selector license admits a two-color repair for exactly
the two counter demands which the original license rejects. -/
theorem unrestricted_twoCounter_repair (R : Trace) (n : ℕ) :
    RepairFeasible contract.problem unrestrictedMenu (twoCounterDemands R n) 2 := by
  refine ⟨counterSplitSelector, Set.mem_univ _, trivial, counterSplitReadouts, ?_⟩
  intro x hx
  have hcases : x = (R, 0) ∨ x = (R, n + 1) := by
    simpa [twoCounterDemands] using hx
  rcases hcases with hzero | hsucc
  · subst x
    change (counterSplitReadouts (counterSplitSelector (R, 0))).val R = true
    rfl
  · subst x
    change (counterSplitReadouts (counterSplitSelector (R, n + 1))).val R = false
    rfl

/-- Local satisfiability, refusal of every licensed repair and success after
license deletion occur on the very same native two-pass demand set. -/
theorem selector_license_necessity_control (R : Trace) (n : ℕ) :
    (∀ x ∈ twoCounterDemands R n, Good contract.problem ({x} : Set (Trace × ℕ))) ∧
      (∀ k, ¬ RepairFeasible contract.problem contract.menu (twoCounterDemands R n) k) ∧
      RepairFeasible contract.problem unrestrictedMenu (twoCounterDemands R n) 2 := by
  refine ⟨?_, ?_, unrestricted_twoCounter_repair R n⟩
  · intro x _
    exact each_counter_singleton_good x
  · intro k
    exact no_licensed_twoCounter_repair R n k

end RecursorSource

/-! ## M4.5: deletion of the evaluator's diagonal-target premise -/

namespace EvaluatorSource

open OperatorKO7.Meta.BoundaryObserver.SelfEvaluationBounds (pairedEval)

/-- The original paired evaluator row at base is represented by its own code.
This source changes only the target from the complemented diagonal to that row.
All native codes, inputs, interpreter values and evaluation equations are retained. -/
def representedPairedRow (base : ℕ × Bool) : SourceContract where
  Process := (ℕ × Bool) → Bool
  Input := ℕ × Bool
  Output := Bool
  Witness := ℕ × Bool
  source := pairedEval base
  evaluate := fun p x => p x
  interpret := pairedEval
  allowed := fun _ => Set.univ
  combines := fun _ _ _ => True
  assemble := fun _ s ws x => pairedEval (ws (s x)) x
  cost := fun _ _ => 0

/-- The interpreted process is exactly the old paired evaluator code row. -/
theorem representedPairedRow_native_evaluation
    (base code x : ℕ × Bool) :
    (representedPairedRow base).evaluate
        ((representedPairedRow base).interpret code) x =
      pairedEval code x := rfl

/-- The one-code extension retains every row of this represented source. -/
theorem representedPairedRow_old_table_preserved
    (base code x : ℕ × Bool) :
    (representedPairedRow base).evaluate
        ((representedPairedRow base).interpret code) x =
      extendEval pairedEval Bool.not false (some code) (some x) := rfl

/-- The actual old code base globally realizes its represented source row. -/
theorem representedPairedRow_good (base : ℕ × Bool) :
    Good (representedPairedRow base).problem Set.univ :=
  ⟨base, fun _ _ => rfl⟩

/-- This represented source still satisfies the unchanged native combiner law. -/
theorem representedPairedRow_combinerLaw (base : ℕ × Bool) :
    (representedPairedRow base).combinerLaw := by
  intro D k s ws _ _ hw
  exact hw

/-- Every clause of the universal core also applies to the represented row. -/
theorem representedPairedRow_core (base : ℕ × Bool) :
    CoreGoal (representedPairedRow base) :=
  source_observation_repair_core _

/-- The diagonal exclusion fails after the target-relation premise alone is
deleted, although Boolean complementation is still fixed-point-free and the
same old evaluator admits a global witness. The premise being tested is the
exact source-target equation at every old code, not evaluator universality. -/
theorem representedPairedRow_target_premise_control (base : ℕ × Bool) :
    Good (representedPairedRow base).problem Set.univ ∧
      (∀ v : Bool, Bool.not v ≠ v) ∧
      ¬ (∀ w : ℕ × Bool,
        (representedPairedRow base).evaluate
          (representedPairedRow base).source ((Equiv.refl (ℕ × Bool)) w) =
          Bool.not ((representedPairedRow base).evaluate
            ((representedPairedRow base).interpret w)
            ((Equiv.refl (ℕ × Bool)) w))) := by
  have hGood := representedPairedRow_good base
  have hNoFix : ∀ v : Bool, Bool.not v ≠ v := by
    intro v
    cases v <;> decide
  refine ⟨hGood, hNoFix, ?_⟩
  intro hTarget
  exact (source_diagonal_exclusion (representedPairedRow base)
    (Equiv.refl (ℕ × Bool)) Bool.not hNoFix hTarget) hGood

end EvaluatorSource

/-! ## M4.5: actual binary output laws -/

namespace StochasticSource

/-- The original channel uses a fair binary input prior. -/
noncomputable def uniformOutputLaw (K : Bool → Bool → ℝ) (y : Bool) : ℝ :=
  (K false y + K true y) / 2

/-- The fair channel yields a fair output law. -/
theorem fair_output_uniform (y : Bool) :
    uniformOutputLaw fair y = (1 : ℝ) / 2 := by
  cases y <;> norm_num [uniformOutputLaw, fair]

/-- The correlated channel has the same fair output law. -/
theorem correlated_output_uniform (y : Bool) :
    uniformOutputLaw correlated y = (1 : ℝ) / 2 := by
  cases y <;> norm_num [uniformOutputLaw, correlated]

end StochasticSource

/-! ## M4.5: exact Shannon information of the fair binary source -/

namespace StochasticSource

/-- The Shannon row entropy uses the actual probabilities in nats. -/
noncomputable def binaryRowEntropy (K : Bool → Bool → ℝ) (x : Bool) : ℝ :=
  Real.negMulLog (K x false) + Real.negMulLog (K x true)

/-- Fair-input Shannon mutual information is output entropy less mean row entropy. -/
noncomputable def uniformShannonInformation (K : Bool → Bool → ℝ) : ℝ :=
  Real.negMulLog (uniformOutputLaw K false) +
    Real.negMulLog (uniformOutputLaw K true) -
      (binaryRowEntropy K false + binaryRowEntropy K true) / 2

/-- The input-independent source has uniform conditional row entropy. -/
theorem fair_row_entropy (x : Bool) :
    binaryRowEntropy fair x =
      Real.negMulLog (1 / 2 : ℝ) + Real.negMulLog (1 / 2 : ℝ) := by
  cases x <;> norm_num [binaryRowEntropy, fair]

/-- The fair channel contains exactly zero Shannon information about the input. -/
theorem fair_information_zero : uniformShannonInformation fair = 0 := by
  simp only [uniformShannonInformation, fair_output_uniform, fair_row_entropy]
  ring

end StochasticSource

/-! ## M4.5: actual correlated conditional entropy -/

namespace StochasticSource

/-- Both correlated channel rows have the same nonuniform Shannon entropy. -/
theorem correlated_row_entropy (x : Bool) :
    binaryRowEntropy correlated x =
      Real.negMulLog (1 / 4 : ℝ) + Real.negMulLog (3 / 4 : ℝ) := by
  cases x <;> norm_num [binaryRowEntropy, correlated]; ring

end StochasticSource

namespace StochasticSource

theorem strict_quarter_entropy_gap :
    Real.negMulLog (1 / 4 : ℝ) + Real.negMulLog (3 / 4 : ℝ) <
      Real.negMulLog (1 / 2 : ℝ) + Real.negMulLog (1 / 2 : ℝ) := by
  have h := Real.strictConcaveOn_negMulLog.2
    (show (1 / 4 : ℝ) ∈ Set.Ici 0 by norm_num)
    (show (3 / 4 : ℝ) ∈ Set.Ici 0 by norm_num)
    (show (1 / 4 : ℝ) ≠ 3 / 4 by norm_num)
    (show (0 : ℝ) < 1 / 2 by norm_num)
    (show (0 : ℝ) < 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  have heq : (1 / 2 : ℝ) • (1 / 4 : ℝ) +
      (1 / 2 : ℝ) • (3 / 4 : ℝ) = 1 / 2 := by
    norm_num [smul_eq_mul]
  rw [heq] at h
  simp only [smul_eq_mul] at h
  linarith

end StochasticSource

namespace StochasticSource

/-- Correlated outputs convey strictly positive Shannon information. -/
theorem correlated_information_pos :
    0 < uniformShannonInformation correlated := by
  have hgap := strict_quarter_entropy_gap
  simp only [uniformShannonInformation, correlated_output_uniform,
    correlated_row_entropy]
  linarith

end StochasticSource

namespace StochasticSource

/-- Both normalized channels have exactly the same positive support. -/
theorem fair_correlated_support_iff (x y : Bool) :
    0 < fair x y ↔ 0 < correlated x y := by
  have h := same_support_different_laws.1 x y
  exact ⟨fun _ => h.2, fun _ => h.1⟩

end StochasticSource

namespace StochasticSource

/-- The two actual positive-support source problems are incidence-isomorphic. -/
noncomputable def fair_correlated_incidence_iso :
    Transport.DemandIso (contract fair (id : Bool → Bool)).problem
      (contract correlated (id : Bool → Bool)).problem where
  demands := {
    toFun := fun xy =>
      ⟨xy.val, (fair_correlated_support_iff xy.val.1 xy.val.2).mp xy.property⟩
    invFun := fun xy =>
      ⟨xy.val, (fair_correlated_support_iff xy.val.1 xy.val.2).mpr xy.property⟩
    left_inv := by
      intro xy
      apply Subtype.ext
      rfl
    right_inv := by
      intro xy
      apply Subtype.ext
      rfl
  }
  witnesses := Equiv.refl (Bool → Bool)
  satisfaction := by
    intro w xy
    exact Iff.rfl

end StochasticSource

namespace StochasticSource

/-- Source isomorphism does not imply equality of Shannon information. -/
theorem incidence_iso_does_not_preserve_shannon_information :
    ∃ _e : Transport.DemandIso
        (contract fair (id : Bool → Bool)).problem
        (contract correlated (id : Bool → Bool)).problem,
      uniformShannonInformation fair ≠ uniformShannonInformation correlated := by
  refine ⟨fair_correlated_incidence_iso, ?_⟩
  rw [fair_information_zero]
  exact ne_of_lt correlated_information_pos

end StochasticSource

/-! ## M4.5: all proper triangle contexts share an assignment law -/

namespace CommonLawSource

open OperatorKO7.Meta.BoundaryObserver.ObserverRealization (triangleReport realizable_vertex)

/-- Each deterministic assignment leaves precisely one triangle demand unmet. -/
def omittedEdgeAssignment : Fin 3 → Bool × Bool × Bool :=
  ![(true, true, false), (true, false, false), (true, false, true)]

/-- The native report is one on every nonomitted edge and zero on that edge. -/
theorem omittedEdgeAssignment_report (omitted edge : Fin 3) :
    triangleReport (omittedEdgeAssignment omitted) edge =
      if edge = omitted then 0 else 1 := by
  fin_cases omitted <;> fin_cases edge <;>
    norm_num [omittedEdgeAssignment, triangleReport]

/-- Every source demand family excluding one edge admits a normalized
deterministic common assignment, with no added bound on the remaining edges. -/
theorem triangle_good_omitting (omitted : Fin 3) (D : Set (Fin 3))
    (hmiss : omitted ∉ D) : Good triangle.problem D := by
  have hvertex :
      Good (Transport.commonLawProblem triangleReport
        (triangleReport (omittedEdgeAssignment omitted))) Set.univ :=
    (Transport.common_law_good_iff _ _).mpr
      (realizable_vertex triangleReport (omittedEdgeAssignment omitted))
  obtain ⟨w, hw⟩ := hvertex
  change Good (Transport.commonLawProblem triangleReport (fun _ => 1)) D
  refine ⟨w, ?_⟩
  intro i hi
  have hne : i ≠ omitted := by
    intro h
    exact hmiss (h ▸ hi)
  change (∑ a, w.val a * triangleReport a i) = (1 : ℝ)
  calc
    (∑ a, w.val a * triangleReport a i) =
        triangleReport (omittedEdgeAssignment omitted) i := hw i (Set.mem_univ i)
    _ = 1 := by rw [omittedEdgeAssignment_report, if_neg hne]

/-- Every proper retained subset, including either two-edge context, is
satisfiable by one common native law. -/
theorem triangle_every_proper_subset_good (D : Set (Fin 3))
    (hproper : D ≠ Set.univ) : Good triangle.problem D := by
  by_contra hbad
  apply hproper
  ext i
  constructor
  · intro _
    exact Set.mem_univ i
  · intro _
    by_contra hi
    exact hbad (triangle_good_omitting i D hi)

/-- For this exact finite source, global feasibility is equivalent to
omitting at least one of the original three marginal demands. -/
theorem triangle_good_iff_proper (D : Set (Fin 3)) :
    Good triangle.problem D ↔ D ≠ Set.univ := by
  constructor
  · intro hgood heq
    exact triangle_global_obstruction (heq ▸ hgood)
  · exact triangle_every_proper_subset_good D

/-- The complete three-demand triangle is a minimal obstruction in the
original finite-demand structure, not merely a failed global instance. -/
theorem triangle_univ_minimal_bad :
    MinimalBad triangle.problem (Finset.univ : Finset (Fin 3)) := by
  constructor
  · have huniv : ((Finset.univ : Finset (Fin 3)) : Set (Fin 3)) = Set.univ :=
      Finset.coe_univ
    change ¬ Good triangle.problem ((Finset.univ : Finset (Fin 3)) : Set (Fin 3))
    rw [huniv]
    exact triangle_global_obstruction
  · intro A hA
    have hproper : (A : Set triangle.Input) ≠ Set.univ := by
      intro hs
      have heq : A = (Finset.univ : Finset (Fin 3)) := by
        ext i
        constructor
        · intro _
          exact Finset.mem_univ (α := Fin 3) i
        · intro _
          have hmem : i ∈ (A : Set triangle.Input) := by
            rw [hs]
            exact Set.mem_univ i
          exact hmem
      rw [heq] at hA
      exact (Finset.ssubset_iff_subset_ne.mp hA).2 rfl
    exact triangle_every_proper_subset_good (A : Set triangle.Input) hproper

end CommonLawSource


/-! ## M4.5: localized diagonal exclusion and exact separation -/

namespace BoundaryStrengthening

/-- Global failure is equivalent to one separating input for every original candidate. -/
theorem boundary_iff_separating_inputs (C : SourceContract) :
    ¬ Good C.problem Set.univ ↔
      ∃ pick : C.Witness → C.Input, ∀ w,
        C.evaluate (C.interpret w) (pick w) ≠ C.evaluate C.source (pick w) := by
  classical
  constructor
  · intro hbad
    have hsep (w : C.Witness) :
        ∃ i, C.evaluate (C.interpret w) i ≠ C.evaluate C.source i := by
      by_contra hnone
      apply hbad
      refine ⟨w, ?_⟩
      intro i _
      change C.evaluate (C.interpret w) i = C.evaluate C.source i
      by_contra hdiff
      exact hnone ⟨i, hdiff⟩
    exact ⟨fun w => Classical.choose (hsep w),
      fun w => Classical.choose_spec (hsep w)⟩
  · rintro ⟨pick, hsep⟩ ⟨w, hw⟩
    exact hsep w (hw (pick w) (Set.mem_univ _))

/-- The diagonal argument uses only its selected candidate values and a forward map. -/
theorem source_diagonal_exclusion_local (C : SourceContract)
    (pick : C.Witness → C.Input) (j : C.Output → C.Output)
    (hmove : ∀ w, j (C.evaluate (C.interpret w) (pick w)) ≠
      C.evaluate (C.interpret w) (pick w))
    (htarget : ∀ w, C.evaluate C.source (pick w) =
      j (C.evaluate (C.interpret w) (pick w))) :
    ¬ Good C.problem Set.univ := by
  rintro ⟨w, hw⟩
  have h : C.evaluate (C.interpret w) (pick w) = C.evaluate C.source (pick w) :=
    hw (pick w) (Set.mem_univ _)
  exact hmove w ((htarget w).symm.trans h.symm)

/-- A globally fixed-point-free change is sufficient with any candidate-to-input map. -/
theorem source_diagonal_exclusion_map (C : SourceContract)
    (pick : C.Witness → C.Input) (j : C.Output → C.Output)
    (noFix : ∀ v, j v ≠ v)
    (htarget : ∀ w, C.evaluate C.source (pick w) =
      j (C.evaluate (C.interpret w) (pick w))) :
    ¬ Good C.problem Set.univ :=
  source_diagonal_exclusion_local C pick j (fun _ => noFix _) htarget

/-- The source Goal localizes the change law without changing the original source equation. -/
def LocalDiagonalExclusionGoal (C : SourceContract) : Prop :=
  ∀ (pick : C.Witness → C.Input) (j : C.Output → C.Output),
    (∀ w, j (C.evaluate (C.interpret w) (pick w)) ≠
      C.evaluate (C.interpret w) (pick w)) →
    (∀ w, C.evaluate C.source (pick w) =
      j (C.evaluate (C.interpret w) (pick w))) →
    ¬ Good C.problem Set.univ

theorem localDiagonalExclusionGoal (C : SourceContract) : LocalDiagonalExclusionGoal C :=
  source_diagonal_exclusion_local C

/-- The candidate carrier has one element while the retained input carrier has two. -/
def unequalCarrierDiagonalSource : SourceContract where
  Process := Bool → Bool
  Input := Bool
  Output := Bool
  Witness := Unit
  source := fun _ => true
  evaluate := fun p i => p i
  interpret := fun _ _ => false
  allowed := fun _ => Set.univ
  combines := fun _ _ _ => True
  assemble := fun _ _ _ _ => false
  cost := fun _ _ => 0

/-- The localized theorem applies even when no candidate/input bijection exists. -/
theorem unequal_carrier_diagonal_control :
    ¬ Nonempty (unequalCarrierDiagonalSource.Witness ≃
      unequalCarrierDiagonalSource.Input) ∧
    (∀ w : unequalCarrierDiagonalSource.Witness,
      unequalCarrierDiagonalSource.evaluate unequalCarrierDiagonalSource.source false =
        Bool.not (unequalCarrierDiagonalSource.evaluate
          (unequalCarrierDiagonalSource.interpret w) false)) ∧
    ¬ Good unequalCarrierDiagonalSource.problem Set.univ := by
  refine ⟨?_, (fun _ => rfl), ?_⟩
  · rintro ⟨e⟩
    change Unit ≃ Bool at e
    obtain ⟨a, ha⟩ := e.surjective false
    obtain ⟨b, hb⟩ := e.surjective true
    cases a
    cases b
    have h : false = true := ha.symm.trans hb
    cases h
  · apply source_diagonal_exclusion_local unequalCarrierDiagonalSource
      (fun _ => false) Bool.not
    · intro _
      show (!false) ≠ false
      decide
    · intro _
      rfl

/-- The original candidate value moves although another output value is fixed. -/
def localChange (v : ℕ) : ℕ := if v = 0 then 1 else v

def localChangeSource : SourceContract where
  Process := ℕ
  Input := Unit
  Output := ℕ
  Witness := Unit
  source := 1
  evaluate := fun p _ => p
  interpret := fun _ => 0
  allowed := fun _ => Set.univ
  combines := fun _ _ _ => True
  assemble := fun _ _ _ => 0
  cost := fun _ _ => 0

/-- Global fixed-point-freedom is unnecessary outside the candidate values used by the proof. -/
theorem local_change_fixed_point_control :
    localChange 1 = 1 ∧
    ¬ (∀ v, localChange v ≠ v) ∧
    (∀ w : localChangeSource.Witness,
      localChangeSource.evaluate localChangeSource.source () =
        localChange (localChangeSource.evaluate (localChangeSource.interpret w) ())) ∧
    ¬ Good localChangeSource.problem Set.univ := by
  refine ⟨rfl, ?_, (fun _ => rfl), ?_⟩
  · intro h
    exact h 1 rfl
  · apply source_diagonal_exclusion_local localChangeSource (fun _ => ()) localChange
    · intro _
      show localChange 0 ≠ 0
      decide
    · intro _
      rfl

end BoundaryStrengthening

end UniversalObservation.Completion
