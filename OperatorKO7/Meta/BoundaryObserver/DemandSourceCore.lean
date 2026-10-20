import OperatorKO7.Meta.BoundaryObserver.ProtocolResolution
import OperatorKO7.Meta.BoundaryObserver.DemandDetector
import OperatorKO7.Meta.BoundaryObserver.Instances.Recursor

set_option autoImplicit false

/-!
# Source-bound operational completion

Kernel status: direct check with 0 errors and 0 warnings, a fresh named build, and every
declaration within the axioms propext, Classical.choice and Quot.sound, 2026-10-18.
The module transports licensed plans with their assembled processes and costs, admits the
actual assembly of the five native sources (counted recursion, the evaluator with its
conservative extension, the stochastic channel and the instrument, the common law, and the
affine rows), prices each plan on its own resource coordinates, and gives a separate
control for each omitted premise.
-/

namespace UniversalObservation.Completion.Operational

open Demand Transport

/-- A source plan retains its selector, witnesses and both native permissions. -/
abbrev SourcePlan (C : SourceContract) (D : Set C.Input) (k : ℕ) :=
  LicensedPlan C.problem C.menu D k

/-- The plan denotes the actual assembly selected by its stored data. -/
def planProcess (C : SourceContract) {D : Set C.Input} {k : ℕ}
    (r : SourcePlan C D k) : C.Process :=
  C.assemble k r.val.1 r.val.2

/-- Every resource coordinate is evaluated on that same assembled process. -/
def planCost (C : SourceContract) {D : Set C.Input} {k : ℕ}
    (r : SourcePlan C D k) : ℕ → ℝ :=
  C.cost (planProcess C r)

/-- Independent source equations specify the permitted change of representation. -/
structure SourceTransport (C B : SourceContract) where
  processes : C.Process ≃ B.Process
  inputs : C.Input ≃ B.Input
  outputs : C.Output ≃ B.Output
  witnesses : C.Witness ≃ B.Witness
  source_eq : processes C.source = B.source
  evaluation : ∀ p i, B.evaluate (processes p) (inputs i) =
    outputs (C.evaluate p i)
  interpretation : ∀ w, B.interpret (witnesses w) = processes (C.interpret w)
  allowed : ∀ k s, (fun i => s (inputs.symm i)) ∈ B.allowed k ↔ s ∈ C.allowed k
  combines : ∀ D k s,
    B.combines (inputs '' D) k (fun i => s (inputs.symm i)) ↔ C.combines D k s
  assembly : ∀ D k s ws, s ∈ C.allowed k → C.combines D k s →
    B.assemble k (fun i => s (inputs.symm i)) (fun j => witnesses (ws j)) =
      processes (C.assemble k s ws)
  resource : ∀ p j, B.cost (processes p) j = C.cost p j

namespace SourceTransport

variable {C B : SourceContract}

/-- Source and evaluation equations derive the candidate-incidence correspondence. -/
def demandIso (e : SourceTransport C B) : DemandIso C.problem B.problem where
  demands := e.inputs
  witnesses := e.witnesses
  satisfaction w i := by
    change B.evaluate (B.interpret (e.witnesses w)) (e.inputs i) =
      B.evaluate B.source (e.inputs i) ↔
        C.evaluate (C.interpret w) i = C.evaluate C.source i
    rw [e.interpretation, ← e.source_eq, e.evaluation, e.evaluation]
    constructor
    · intro h
      exact e.outputs.injective h
    · exact congrArg e.outputs

/-- Both permission laws refer to the same derived incidence transport. -/
def menuCorrespondence (e : SourceTransport C B) :
    e.demandIso.MenuCorrespondence C.menu B.menu where
  allowed := e.allowed
  combines := e.combines

/-- The equivalence maps the full licensed plan with its original component witnesses. -/
def planEquiv (e : SourceTransport C B) (D : Set C.Input) (k : ℕ) :
    SourcePlan C D k ≃ SourcePlan B (e.inputs '' D) k :=
  e.demandIso.licensedPlanEquiv C.menu B.menu e.menuCorrespondence D k

/-- The transported selector reads exactly the corresponding old input. -/
theorem plan_selector (e : SourceTransport C B) (D : Set C.Input) (k : ℕ)
    (r : SourcePlan C D k) (i : B.Input) :
    (e.planEquiv D k r).val.1 i = r.val.1 (e.inputs.symm i) := rfl

/-- The transported component is the image of the actual stored witness. -/
theorem plan_witness (e : SourceTransport C B) (D : Set C.Input) (k : ℕ)
    (r : SourcePlan C D k) (j : Fin k) :
    (e.planEquiv D k r).val.2 j = e.witnesses (r.val.2 j) := rfl

/-- The source assembly equation identifies the actual transported process. -/
theorem plan_process (e : SourceTransport C B) (D : Set C.Input) (k : ℕ)
    (r : SourcePlan C D k) :
    planProcess B (e.planEquiv D k r) = e.processes (planProcess C r) :=
  e.assembly D k r.val.1 r.val.2 r.property.1 r.property.2.1

/-- The cost law follows through actual assembly before applying resource preservation. -/
theorem plan_cost (e : SourceTransport C B) (D : Set C.Input) (k : ℕ)
    (r : SourcePlan C D k) (j : ℕ) :
    planCost B (e.planEquiv D k r) j = planCost C r j := by
  change B.cost (planProcess B (e.planEquiv D k r)) j =
    C.cost (planProcess C r) j
  rw [e.plan_process D k r]
  exact e.resource (planProcess C r) j

/-- Every whole-plan budget has exactly the same feasible native plans after transport. -/
theorem licensed_budget_iff (e : SourceTransport C B) (D : Set C.Input) (k : ℕ)
    (budget : ℕ → ℝ) :
    LicensedBudget C.problem C.menu D k (planCost C) budget ↔
      LicensedBudget B.problem B.menu (e.inputs '' D) k (planCost B) budget :=
  licensed_budget_transport_iff e.demandIso C.menu B.menu e.menuCorrespondence D k
    (planCost C) (planCost B) (e.plan_cost D k) budget

/-- Admission of the exact assembled process is preserved by the same process map. -/
theorem plan_admission_iff (e : SourceTransport C B)
    (native : Set C.Process) (D : Set C.Input) (k : ℕ)
    (r : SourcePlan C D k) :
    planProcess B (e.planEquiv D k r) ∈ e.processes '' native ↔
      planProcess C r ∈ native := by
  rw [e.plan_process D k r]
  constructor
  · rintro ⟨p, hp, he⟩
    have h : p = planProcess C r := e.processes.injective he
    exact h ▸ hp
  · intro h
    exact ⟨planProcess C r, h, rfl⟩

/-- Identity representation inhabits every source-transport law for any resource model. -/
def refl (C : SourceContract) : SourceTransport C C where
  processes := Equiv.refl C.Process
  inputs := Equiv.refl C.Input
  outputs := Equiv.refl C.Output
  witnesses := Equiv.refl C.Witness
  source_eq := rfl
  evaluation _ _ := rfl
  interpretation _ := rfl
  allowed _ _ := Iff.rfl
  combines D k s := by
    have h : (Equiv.refl C.Input) '' D = D := by
      ext i
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact hx
      · intro hi
        exact ⟨i, hi, rfl⟩
    change C.combines ((Equiv.refl C.Input) '' D) k s ↔ C.combines D k s
    rw [h]
  assembly _ _ _ _ _ _ := rfl
  resource _ _ := rfl

end SourceTransport

/-- The full plan, actual process, native-class image and budget all share the source map. -/
def SourcePlanTransportGoal (C B : SourceContract) (e : SourceTransport C B) : Prop :=
  ∀ (D : Set C.Input) (k : ℕ),
    (∀ r : SourcePlan C D k,
      (∀ i, (e.planEquiv D k r).val.1 i = r.val.1 (e.inputs.symm i)) ∧
      (∀ j, (e.planEquiv D k r).val.2 j = e.witnesses (r.val.2 j)) ∧
      planProcess B (e.planEquiv D k r) = e.processes (planProcess C r) ∧
      (∀ j, planCost B (e.planEquiv D k r) j = planCost C r j) ∧
      (∀ native : Set C.Process,
        planProcess B (e.planEquiv D k r) ∈ e.processes '' native ↔
          planProcess C r ∈ native)) ∧
    (∀ budget : ℕ → ℝ,
      LicensedBudget C.problem C.menu D k (planCost C) budget ↔
        LicensedBudget B.problem B.menu (e.inputs '' D) k (planCost B) budget)

/-- The source-indexed plan theorem derives every field from independent transport laws. -/
theorem sourcePlanTransportGoal (C B : SourceContract) (e : SourceTransport C B) :
    SourcePlanTransportGoal C B e := by
  intro D k
  constructor
  · intro r
    exact ⟨e.plan_selector D k r, e.plan_witness D k r, e.plan_process D k r,
      e.plan_cost D k r, fun native => e.plan_admission_iff native D k r⟩
  · exact e.licensed_budget_iff D k

/-- The unchanged logical goals and complete plan transport refer to their exact sources. -/
theorem core_with_plan_transport (C B : SourceContract) (e : SourceTransport C B) :
    CoreGoal C ∧ CoreGoal B ∧ SourcePlanTransportGoal C B e :=
  ⟨source_observation_repair_core C, source_observation_repair_core B,
    sourcePlanTransportGoal C B e⟩


/-- Closure applies to arbitrary permitted components before target satisfaction. -/
def SourceAssemblyClosed (C : SourceContract) (native : Set C.Process) : Prop :=
  ∀ D k s ws, s ∈ C.allowed k → C.combines D k s → C.assemble k s ws ∈ native

/-- The assembly preserves selected native evaluation before target satisfaction. -/
def SourceAssemblySelects (C : SourceContract) : Prop :=
  ∀ D k s ws, s ∈ C.allowed k → C.combines D k s →
    ∀ i ∈ D, C.evaluate (C.assemble k s ws) i = C.evaluate (C.interpret (ws (s i))) i

/-- The actual stored plan is admitted and satisfies its retained source. -/
def SourceNativeAssemblyGoal (C : SourceContract) (native : Set C.Process) : Prop :=
  ∀ D k (r : SourcePlan C D k), planProcess C r ∈ native ∧
    ∀ i ∈ D, C.evaluate (planProcess C r) i = C.evaluate C.source i

/-- The primitive evaluation law derives the original conditional combiner interface. -/
theorem sourceAssemblyCombinerLaw (C : SourceContract) (he : SourceAssemblySelects C) :
    C.combinerLaw := by
  intro D k s ws ha hc hw i hi
  exact (he D k s ws ha hc i hi).trans (hw i hi)

/-- Independent closure and evaluation laws derive admission and source correctness. -/
theorem sourceNativeAssemblyGoal (C : SourceContract) (native : Set C.Process)
    (hc : SourceAssemblyClosed C native) (he : SourceAssemblySelects C) :
    SourceNativeAssemblyGoal C native := by
  intro D k r
  refine ⟨hc D k r.val.1 r.val.2 r.property.1 r.property.2.1, ?_⟩
  intro i hi
  exact (he D k r.val.1 r.val.2 r.property.1 r.property.2.1 i hi).trans
    (r.property.2.2 i hi)

namespace NativeAssembly

open OperatorKO7 (Trace)
open OperatorKO7.Meta.BoundaryObserver.RecursorDecidability (content observed)
open scoped BigOperators

/-- The syntax retains the actual selector and each native component. -/
inductive SelectionProcess (I W : Type) where
  | target
  | direct (w : W)
  | selected (k : ℕ) (selector : I → Fin k) (components : Fin k → W)

/-- The resource counts selector and native evaluation calls as primitive operations. -/
def primitiveCalls {I W : Type} (targetCalls : ℕ) : SelectionProcess I W → ℕ
  | .target => targetCalls
  | .direct _ => 1
  | .selected _ _ _ => 2

/-- The anchored native class contains direct and selected witness syntax. -/
inductive AnchoredNative {I W : Type} : SelectionProcess I W → Prop where
  | direct (w : W) : AnchoredNative (.direct w)
  | selected (k : ℕ) (s : I → Fin k) (ws : Fin k → W) :
      AnchoredNative (.selected k s ws)

def anchoredEvaluate {I W V : Type} (eval : W → I → V)
    (target : I → V) (anchor : I) : SelectionProcess I W → I → V
  | .target => target
  | .direct w => eval w
  | .selected _ s ws => eval (ws (s anchor))

/-- Combination retains a single native component throughout the demand scope. -/
@[reducible]
noncomputable def anchoredContract (I W V : Type) (eval : W → I → V)
    (target : I → V) (anchor : I) (targetCalls : ℕ) : SourceContract where
  Process := SelectionProcess I W
  Input := I
  Output := V
  Witness := W
  source := .target
  evaluate := anchoredEvaluate eval target anchor
  interpret := SelectionProcess.direct
  allowed := fun _ => Set.univ
  combines := fun D _ s => ∀ i ∈ D, s i = s anchor
  assemble := SelectionProcess.selected
  cost := fun p j => if j = 0 then (primitiveCalls targetCalls p : ℝ) else 0

/-- Every admitted anchored process denotes one whole native witness. -/
theorem anchored_denotes {I W V : Type} (eval : W → I → V)
    (target : I → V) (anchor : I) (p : SelectionProcess I W) (hp : AnchoredNative p) :
    ∃ w : W, ∀ i, anchoredEvaluate eval target anchor p i = eval w i := by
  cases hp with
  | direct w => exact ⟨w, fun _ => rfl⟩
  | selected k s ws => exact ⟨ws (s anchor), fun _ => rfl⟩

theorem anchored_closed (I W V : Type) (eval : W → I → V)
    (target : I → V) (anchor : I) (n : ℕ) :
    SourceAssemblyClosed (anchoredContract I W V eval target anchor n) AnchoredNative := by
  intro D k s ws _ _
  exact .selected k s ws

theorem anchored_selects (I W V : Type) (eval : W → I → V)
    (target : I → V) (anchor : I) (n : ℕ) :
    SourceAssemblySelects (anchoredContract I W V eval target anchor n) := by
  intro D k s ws _ hc i hi
  change eval (ws (s anchor)) i = eval (ws (s i)) i
  exact congrArg (fun b => eval (ws b) i) (hc i hi).symm

theorem anchored_combinerLaw (I W V : Type) (eval : W → I → V)
    (target : I → V) (anchor : I) (n : ℕ) :
    (anchoredContract I W V eval target anchor n).combinerLaw :=
  sourceAssemblyCombinerLaw _ (anchored_selects I W V eval target anchor n)

theorem anchored_goal (I W V : Type) (eval : W → I → V)
    (target : I → V) (anchor : I) (n : ℕ) :
    SourceNativeAssemblyGoal (anchoredContract I W V eval target anchor n) AnchoredNative :=
  sourceNativeAssemblyGoal _ _ (anchored_closed I W V eval target anchor n)
    (anchored_selects I W V eval target anchor n)

theorem anchored_candidate_native (I W V : Type) (eval : W → I → V)
    (target : I → V) (anchor : I) (n : ℕ) (w : W) :
    AnchoredNative ((anchoredContract I W V eval target anchor n).interpret w) := .direct w

theorem anchored_plan_exists (I W V : Type) (eval : W → I → V)
    (target : I → V) (anchor : I) (n : ℕ) (D : Set I)
    (h : Good (anchoredContract I W V eval target anchor n).problem D) :
    Nonempty (SourcePlan (anchoredContract I W V eval target anchor n) D 1) := by
  obtain ⟨w, hw⟩ := h
  exact ⟨⟨((fun _ => 0), fun _ => w), Set.mem_univ _, fun _ _ => rfl, hw⟩⟩

theorem anchored_plan_cost (I W V : Type) (eval : W → I → V)
    (target : I → V) (anchor : I) (n : ℕ) (D : Set I) (k : ℕ)
    (r : SourcePlan (anchoredContract I W V eval target anchor n) D k) :
    planCost (anchoredContract I W V eval target anchor n) r 0 = 2 := rfl

abbrev CountedWitness := {f : Trace → Bool // f ∈ (Set.univ : Set (Trace → Bool))}

def countedEvaluate : SelectionProcess (Trace × ℕ) CountedWitness → (Trace × ℕ) → Bool
  | .target => observed
  | .direct f => fun x => f.val (content x)
  | .selected _ s ws => fun x => (ws (s x)).val (content x)

/-- Native selected readouts retain the original content-only selector permission. -/
inductive CountedNative : SelectionProcess (Trace × ℕ) CountedWitness → Prop where
  | direct (w : CountedWitness) : CountedNative (.direct w)
  | selected (k : ℕ) (s : Trace × ℕ → Fin k) (ws : Fin k → CountedWitness)
      (hs : s ∈ RecursorSource.contentSelectors k) : CountedNative (.selected k s ws)

@[reducible]
noncomputable def countedContract : SourceContract where
  Process := SelectionProcess (Trace × ℕ) CountedWitness
  Input := Trace × ℕ
  Output := Bool
  Witness := CountedWitness
  source := .target
  evaluate := countedEvaluate
  interpret := SelectionProcess.direct
  allowed := RecursorSource.contentSelectors
  combines := fun _ _ _ => True
  assemble := SelectionProcess.selected
  cost := fun p j => if j = 0 then (primitiveCalls 1 p : ℝ) else 0

theorem counted_problem :
    countedContract.problem = Transport.RecursorAdapter.contentProblem := rfl

theorem counted_denotes (p : countedContract.Process) (hp : CountedNative p) :
    ∃ f : Trace → Bool, ∀ x, countedEvaluate p x = f (content x) := by
  cases hp with
  | direct w => exact ⟨w.val, fun _ => rfl⟩
  | selected k s ws hs =>
    refine ⟨fun R => (ws (s (R, 0))).val R, ?_⟩
    rintro ⟨R, n⟩
    exact congrArg (fun j => (ws j).val R) (hs R n 0)

theorem counted_closed : SourceAssemblyClosed countedContract CountedNative := by
  intro D k s ws ha _
  exact .selected k s ws ha

theorem counted_selects : SourceAssemblySelects countedContract := by
  intro D k s ws _ _ i _
  rfl

theorem counted_combinerLaw : countedContract.combinerLaw :=
  sourceAssemblyCombinerLaw _ counted_selects

theorem counted_goal : SourceNativeAssemblyGoal countedContract CountedNative :=
  sourceNativeAssemblyGoal _ _ counted_closed counted_selects

theorem counted_candidate_native (w : CountedWitness) :
    CountedNative (countedContract.interpret w) := .direct w

theorem counted_singleton_plan (x : Trace × ℕ) :
    Nonempty (SourcePlan countedContract {x} 1) := by
  refine ⟨⟨((fun _ => 0), fun _ => ⟨fun _ => observed x, Set.mem_univ _⟩),
    (fun _ _ _ => rfl), trivial, ?_⟩⟩
  intro y hy
  have h : y = x := Set.mem_singleton_iff.mp hy
  subst y
  rfl

theorem counted_plan_cost (D : Set (Trace × ℕ)) (k : ℕ)
    (r : SourcePlan countedContract D k) : planCost countedContract r 0 = 2 := rfl

theorem counted_core : CoreGoal countedContract := source_observation_repair_core _

/-- The original pass relation retains its exact transition and endpoint scope. -/
theorem counted_pass_resource (f : ℕ → Trace × ℕ) (n k : ℕ) (R : Trace)
    (hp : ∀ i, i < n → OperatorKO7.Meta.BoundaryObserver.RecursorDecidability.Pass
      (f i) (f (i + 1))) (h0 : f 0 = (R, k)) (hn : f n = (R, 0)) : n = k :=
  OperatorKO7.Meta.BoundaryObserver.RecursorDecidability.run_length_eq_counter f n k R hp h0 hn

/-- The counted readout Goal retains native incidence, admission, a plan and its call price. -/
def CountedOperationalGoal : Prop :=
  countedContract.problem = Transport.RecursorAdapter.contentProblem ∧
  countedContract.combinerLaw ∧ CoreGoal countedContract ∧
  SourceNativeAssemblyGoal countedContract CountedNative ∧
  (∀ p : countedContract.Process, CountedNative p →
    ∃ f : Trace → Bool, ∀ x, countedEvaluate p x = f (content x)) ∧
  (∀ x : Trace × ℕ, Nonempty (SourcePlan countedContract {x} 1)) ∧
  (∀ D k (r : SourcePlan countedContract D k), planCost countedContract r 0 = 2)

theorem countedOperationalGoal : CountedOperationalGoal :=
  ⟨counted_problem, counted_combinerLaw, counted_core, counted_goal,
    counted_denotes, counted_singleton_plan, counted_plan_cost⟩

/-- The altered assembler returns the source request instead of native readout syntax. -/
@[reducible]
noncomputable def targetOnlyCounted : SourceContract :=
  { countedContract with assemble := fun _ _ _ => .target }

/-- Correct source output and a nonempty native class do not imply assembly admission. -/
theorem actual_native_closure_control (x : Trace × ℕ) :
    CoreGoal targetOnlyCounted ∧ targetOnlyCounted.combinerLaw ∧
    (∃ p : targetOnlyCounted.Process, CountedNative p) ∧
    Nonempty (SourcePlan targetOnlyCounted {x} 1) ∧
    ∀ r : SourcePlan targetOnlyCounted {x} 1,
      ¬ CountedNative (planProcess targetOnlyCounted r) := by
  refine ⟨source_observation_repair_core _, ?_, ?_, counted_singleton_plan x, ?_⟩
  · intro D k s ws _ _ _ i _
    rfl
  · let w : CountedWitness := ⟨fun _ => false, Set.mem_univ _⟩
    exact ⟨.direct w, .direct w⟩
  · intro r h
    change CountedNative (.target : SelectionProcess (Trace × ℕ) CountedWitness) at h
    cases h

end NativeAssembly


end UniversalObservation.Completion.Operational

namespace UniversalObservation.Completion

def ConservativeExtensionGoal : Prop :=
  ∀ (C V : Type) (E : C → C → V) (j : V → V) (v0 : V),
    (∀ v, j v ≠ v) →
    (∀ c x, extendEval E j v0 (some c) (some x) = E c x) ∧
    (∀ x, extendEval E j v0 none (some x) = j (E x x)) ∧
    ¬ ∃ c, ∀ x, extendEval E j v0 c x = j (extendEval E j v0 x x)

/-- The exact specification Goal follows from the conservative source construction. -/
theorem conservativeExtensionGoal : ConservativeExtensionGoal := by
  intro C V E j v0 h
  exact conservative_diagonal_extension E j v0 h

end UniversalObservation.Completion

namespace UniversalObservation.Completion.Operational
namespace NativeAssembly

/-- The evaluator source retains the original code table and its changed diagonal. -/
noncomputable def evaluatorContract (C V : Type) (E : C → C → V)
    (j : V → V) (a : C) : SourceContract :=
  anchoredContract C C V E (fun x => j (E x x)) a 2

theorem evaluator_problem (C V : Type) (E : C → C → V) (j : V → V) (a : C) :
    (evaluatorContract C V E j a).problem = diagonalProblem E j := rfl

theorem evaluator_combinerLaw (C V : Type) (E : C → C → V) (j : V → V) (a : C) :
    (evaluatorContract C V E j a).combinerLaw :=
  anchored_combinerLaw C C V E (fun x => j (E x x)) a 2

theorem evaluator_core (C V : Type) (E : C → C → V) (j : V → V) (a : C) :
    CoreGoal (evaluatorContract C V E j a) := source_observation_repair_core _

theorem evaluator_goal (C V : Type) (E : C → C → V) (j : V → V) (a : C) :
    SourceNativeAssemblyGoal (evaluatorContract C V E j a) AnchoredNative :=
  anchored_goal C C V E (fun x => j (E x x)) a 2

/-- The assembled evaluator denotes one actual original code on the whole input carrier. -/
theorem evaluator_assembled (C V : Type) (E : C → C → V) (j : V → V)
    (a : C) (D : Set C) (k : ℕ) (r : SourcePlan (evaluatorContract C V E j a) D k) :
    ∃ c : C, ∀ x, (evaluatorContract C V E j a).evaluate
      (planProcess (evaluatorContract C V E j a) r) x = E c x :=
  anchored_denotes E (fun x => j (E x x)) a _ ((evaluator_goal C V E j a D k r).1)

theorem evaluator_plan_cost (C V : Type) (E : C → C → V) (j : V → V)
    (a : C) (D : Set C) (k : ℕ) (r : SourcePlan (evaluatorContract C V E j a) D k) :
    planCost (evaluatorContract C V E j a) r 0 = 2 :=
  anchored_plan_cost C C V E (fun x => j (E x x)) a 2 D k r

/-- The code map identifies source requests and native evaluator syntax in the same extension. -/
def evaluatorCode {C : Type} (a : C) : SelectionProcess C C → Option C
  | .target => none
  | .direct c => some c
  | .selected _ s ws => some (ws (s a))

theorem evaluator_extension {C V : Type} (E : C → C → V) (j : V → V)
    (a : C) (v0 : V) (p : SelectionProcess C C) (x : C) :
    (evaluatorContract C V E j a).evaluate p x =
      extendEval E j v0 (evaluatorCode a p) (some x) := by
  cases p <;> rfl

theorem evaluator_conservative {C V : Type} (E : C → C → V) (j : V → V)
    (v0 : V) (h : ∀ v, j v ≠ v) :
    (∀ c x, extendEval E j v0 (some c) (some x) = E c x) ∧
    (∀ x, extendEval E j v0 none (some x) = j (E x x)) ∧
    ¬ ∃ c, ∀ x, extendEval E j v0 c x = j (extendEval E j v0 x x) :=
  conservativeExtensionGoal C V E j v0 h

/-- The fresh code gives a licensed native plan for the old changed diagonal. -/
theorem extended_evaluator_plan (C V : Type) (E : C → C → V) (j : V → V)
    (v0 : V) (a : C) :
    Nonempty (SourcePlan (anchoredContract C (Option C) V
      (fun c x => extendEval E j v0 c (some x)) (fun x => j (E x x)) a 2) Set.univ 1) :=
  anchored_plan_exists C (Option C) V (fun c x => extendEval E j v0 c (some x))
    (fun x => j (E x x)) a 2 Set.univ (old_diagonal_resolved E j v0)

/-- Native admission applies to the actual selected process using the fresh code. -/
theorem extended_evaluator_native (C V : Type) (E : C → C → V) (j : V → V)
    (v0 : V) (a : C) :
    SourceNativeAssemblyGoal (anchoredContract C (Option C) V
      (fun c x => extendEval E j v0 c (some x)) (fun x => j (E x x)) a 2) AnchoredNative :=
  anchored_goal C (Option C) V (fun c x => extendEval E j v0 c (some x))
    (fun x => j (E x x)) a 2

/-- A native old-code assembly cannot bypass the changed-diagonal obstruction. -/
theorem evaluator_no_global_plan (C V : Type) (E : C → C → V) (j : V → V)
    (a : C) (h : ∀ v, j v ≠ v) (k : ℕ) :
    ¬ Nonempty (SourcePlan (evaluatorContract C V E j a) Set.univ k) := by
  rintro ⟨r⟩
  obtain ⟨c, hc⟩ := evaluator_assembled C V E j a Set.univ k r
  apply h (E c c)
  exact ((evaluator_goal C V E j a Set.univ k r).2 c (Set.mem_univ c)).symm.trans (hc c)

/-- The evaluator Goal binds native code, permission, cost and conservative extension. -/
def EvaluatorNativeGoal (C V : Type) (E : C → C → V) (j : V → V) (a : C) : Prop :=
  (evaluatorContract C V E j a).problem = diagonalProblem E j ∧
  (evaluatorContract C V E j a).combinerLaw ∧
  CoreGoal (evaluatorContract C V E j a) ∧
  SourceNativeAssemblyGoal (evaluatorContract C V E j a) AnchoredNative ∧
  (∀ D k (r : SourcePlan (evaluatorContract C V E j a) D k),
    (∃ c : C, ∀ x, (evaluatorContract C V E j a).evaluate
      (planProcess (evaluatorContract C V E j a) r) x = E c x) ∧
    planCost (evaluatorContract C V E j a) r 0 = 2) ∧
  (∀ v0 (p : SelectionProcess C C) x,
    (evaluatorContract C V E j a).evaluate p x =
      extendEval E j v0 (evaluatorCode a p) (some x)) ∧
  (∀ v0, (∀ v, j v ≠ v) →
    (∀ c x, extendEval E j v0 (some c) (some x) = E c x) ∧
    (∀ x, extendEval E j v0 none (some x) = j (E x x)) ∧
    ¬ ∃ c, ∀ x, extendEval E j v0 c x = j (extendEval E j v0 x x)) ∧
  ((∀ v, j v ≠ v) → ∀ k,
    ¬ Nonempty (SourcePlan (evaluatorContract C V E j a) Set.univ k))

theorem evaluatorNativeGoal (C V : Type) (E : C → C → V) (j : V → V) (a : C) :
    EvaluatorNativeGoal C V E j a :=
  ⟨evaluator_problem C V E j a, evaluator_combinerLaw C V E j a, evaluator_core C V E j a,
    evaluator_goal C V E j a,
    fun D k r => ⟨evaluator_assembled C V E j a D k r, evaluator_plan_cost C V E j a D k r⟩,
    fun v0 p x => evaluator_extension E j a v0 p x,
    evaluator_conservative E j, evaluator_no_global_plan C V E j a⟩

open OperatorKO7.Meta.BoundaryObserver.SelfEvaluationBounds
  (pairedEval pairedEval_negation_closed)

/-- The paired original table supplies a concrete licensed old-code plan. -/
theorem paired_singleton_plan :
    Nonempty (SourcePlan (evaluatorContract (ℕ × Bool) Bool pairedEval Bool.not (0, false))
      {(0, false)} 1) := by
  apply anchored_plan_exists (ℕ × Bool) (ℕ × Bool) Bool pairedEval
    (fun x => !(pairedEval x x)) (0, false) 2 {(0, false)}
  refine ⟨(1, false), ?_⟩
  intro x hx
  have h : x = (0, false) := Set.mem_singleton_iff.mp hx
  subst x
  rfl

/-- The paired native instance retains the actual code transformation and a paid plan. -/
theorem paired_native_instance :
    EvaluatorNativeGoal (ℕ × Bool) Bool pairedEval Bool.not (0, false) ∧
    Nonempty (SourcePlan (evaluatorContract (ℕ × Bool) Bool pairedEval Bool.not (0, false))
      {(0, false)} 1) ∧
    (∀ (a : ℕ) (b : Bool) (x : ℕ × Bool),
      pairedEval (a, !b) x = !(pairedEval (a, b) x)) :=
  ⟨evaluatorNativeGoal (ℕ × Bool) Bool pairedEval Bool.not (0, false),
    paired_singleton_plan, pairedEval_negation_closed⟩

end NativeAssembly


namespace NativeAssembly

open Demand Transport
open scoped BigOperators

/-- Every original marginal is evaluated from one normalized assignment law. -/
noncomputable def lawEvaluate {A J : Type} [Fintype A] (v : A → J → ℝ)
    (w : AssignmentLaw A) (j : J) : ℝ := ∑ a, w.val a * v a j

/-- One original marginal evaluation uses one product for each complete assignment. -/
noncomputable def lawProducts {A J : Type} [Fintype A] :
    SelectionProcess J (AssignmentLaw A) → ℝ
  | .target => 0
  | .direct _ => ∑ _a : A, (1 : ℝ)
  | .selected _ _ _ => ∑ _a : A, (1 : ℝ)

/-- The native law process charges selection, evaluation and the original assignment products. -/
@[reducible]
noncomputable def commonLawContract {A J : Type} [Fintype A]
    (v : A → J → ℝ) (p : J → ℝ) (a : J) : SourceContract :=
  { anchoredContract J (AssignmentLaw A) ℝ (lawEvaluate v) p a 1 with
    cost := fun q n => if n = 0 then (primitiveCalls 1 q : ℝ)
      else if n = 1 then lawProducts q else 0 }

theorem common_law_problem {A J : Type} [Fintype A]
    (v : A → J → ℝ) (p : J → ℝ) (a : J) :
    (commonLawContract v p a).problem = Transport.commonLawProblem v p := rfl

theorem common_law_combinerLaw {A J : Type} [Fintype A]
    (v : A → J → ℝ) (p : J → ℝ) (a : J) :
    (commonLawContract v p a).combinerLaw :=
  anchored_combinerLaw J (AssignmentLaw A) ℝ (lawEvaluate v) p a 1

theorem common_law_core {A J : Type} [Fintype A]
    (v : A → J → ℝ) (p : J → ℝ) (a : J) : CoreGoal (commonLawContract v p a) :=
  source_observation_repair_core _

theorem common_law_goal {A J : Type} [Fintype A]
    (v : A → J → ℝ) (p : J → ℝ) (a : J) :
    SourceNativeAssemblyGoal (commonLawContract v p a) AnchoredNative :=
  anchored_goal J (AssignmentLaw A) ℝ (lawEvaluate v) p a 1

/-- The actual assembled syntax selects one normalized law for its entire report. -/
theorem common_law_selected {A J : Type} [Fintype A]
    (v : A → J → ℝ) (p : J → ℝ) (a : J) (D : Set J) (k : ℕ)
    (r : SourcePlan (commonLawContract v p a) D k) :
    let w := r.val.2 (r.val.1 a)
    (∀ b, 0 ≤ w.val b) ∧ (∑ b, w.val b) = 1 ∧
    ∀ i, (commonLawContract v p a).evaluate
      (planProcess (commonLawContract v p a) r) i = ∑ b, w.val b * v b i :=
  ⟨(r.val.2 (r.val.1 a)).property.1, (r.val.2 (r.val.1 a)).property.2, fun _ => rfl⟩

theorem common_law_assembled {A J : Type} [Fintype A]
    (v : A → J → ℝ) (p : J → ℝ) (a : J) (D : Set J) (k : ℕ)
    (r : SourcePlan (commonLawContract v p a) D k) :
    ∃ w : AssignmentLaw A, ∀ i, (commonLawContract v p a).evaluate
      (planProcess (commonLawContract v p a) r) i = ∑ b, w.val b * v b i :=
  ⟨r.val.2 (r.val.1 a), fun _ => rfl⟩

theorem common_law_plan_cost {A J : Type} [Fintype A]
    (v : A → J → ℝ) (p : J → ℝ) (a : J) (D : Set J) (k : ℕ)
    (r : SourcePlan (commonLawContract v p a) D k) :
    planCost (commonLawContract v p a) r 0 = 2 ∧
    planCost (commonLawContract v p a) r 1 = ∑ _b : A, (1 : ℝ) := ⟨rfl, rfl⟩

/-- The common-law Goal retains native assignments, marginal equations and actual costs. -/
def CommonLawNativeGoal {A J : Type} [Fintype A]
    (v : A → J → ℝ) (p : J → ℝ) (a : J) : Prop :=
  (commonLawContract v p a).problem = Transport.commonLawProblem v p ∧
  (commonLawContract v p a).combinerLaw ∧ CoreGoal (commonLawContract v p a) ∧
  SourceNativeAssemblyGoal (commonLawContract v p a) AnchoredNative ∧
  ∀ D k (r : SourcePlan (commonLawContract v p a) D k),
    (let w := r.val.2 (r.val.1 a);
      (∀ b, 0 ≤ w.val b) ∧ (∑ b, w.val b) = 1 ∧
      ∀ i, (commonLawContract v p a).evaluate
        (planProcess (commonLawContract v p a) r) i = ∑ b, w.val b * v b i) ∧
    planCost (commonLawContract v p a) r 0 = 2 ∧
    planCost (commonLawContract v p a) r 1 = ∑ _b : A, (1 : ℝ)

theorem commonLawNativeGoal {A J : Type} [Fintype A]
    (v : A → J → ℝ) (p : J → ℝ) (a : J) : CommonLawNativeGoal v p a :=
  ⟨common_law_problem v p a, common_law_combinerLaw v p a,
    common_law_core v p a, common_law_goal v p a,
    fun D k r => ⟨common_law_selected v p a D k r, common_law_plan_cost v p a D k r⟩⟩

open OperatorKO7.Meta.BoundaryObserver.ObserverRealization (triangleReport)

/-- Every original singleton marginal has an admitted paid common-law plan. -/
theorem common_triangle_singleton (j : Fin 3) :
    Nonempty (SourcePlan (commonLawContract triangleReport (fun _ => 1) 0) {j} 1) :=
  anchored_plan_exists (Fin 3) (AssignmentLaw (Bool × Bool × Bool)) ℝ
    (lawEvaluate triangleReport) (fun _ => 1) 0 1 {j}
    (CommonLawSource.triangle_singleton_good j)

/-- The original repaired triangle supplies one global original assignment law. -/
theorem common_triangle_repair :
    Nonempty (SourcePlan
      (commonLawContract triangleReport (fun _ => (2 : ℝ) / 3) 0) Set.univ 1) :=
  anchored_plan_exists (Fin 3) (AssignmentLaw (Bool × Bool × Bool)) ℝ
    (lawEvaluate triangleReport) (fun _ => (2 : ℝ) / 3) 0 1 Set.univ
    CommonLawSource.repaired_triangle_good

/-- The native triangle instance contains original local plans and a paid global repair. -/
theorem common_triangle_native_instance :
    CommonLawNativeGoal triangleReport (fun _ => 1) 0 ∧
    CommonLawNativeGoal triangleReport (fun _ => (2 : ℝ) / 3) 0 ∧
    (∀ j : Fin 3, Nonempty
      (SourcePlan (commonLawContract triangleReport (fun _ => 1) 0) {j} 1)) ∧
    ∃ r : SourcePlan
      (commonLawContract triangleReport (fun _ => (2 : ℝ) / 3) 0) Set.univ 1,
      AnchoredNative
        (planProcess (commonLawContract triangleReport (fun _ => (2 : ℝ) / 3) 0) r) ∧
      planCost (commonLawContract triangleReport (fun _ => (2 : ℝ) / 3) 0) r 0 = 2 := by
  obtain ⟨r⟩ := common_triangle_repair
  exact ⟨commonLawNativeGoal _ _ _, commonLawNativeGoal _ _ _, common_triangle_singleton,
    r, (common_law_goal _ _ _ Set.univ 1 r).1, (common_law_plan_cost _ _ _ Set.univ 1 r).1⟩

end NativeAssembly


namespace NativeAssembly

open Demand Transport
open OperatorKO7 (Trace)
open OperatorKO7.Meta.BoundaryObserver.RecursorDecidability (content observed)

/-- The run process retains its content, initial counter and complete readout syntax. -/
structure RetainedRunProcess (horizon : ℕ) where
  content : Trace
  initialCounter : ℕ
  readout : SelectionProcess (Fin (horizon + 1)) CountedWitness

def retainedTrace {k : ℕ} (p : RetainedRunProcess k) (n : ℕ) : Trace × ℕ :=
  (p.content, p.initialCounter - n)

def retainedReadout {k : ℕ} :
    SelectionProcess (Fin (k + 1)) CountedWitness → (Trace × ℕ) → Fin (k + 1) → Bool
  | .target, x, _ => observed x
  | .direct w, x, _ => w.val (content x)
  | .selected _ s ws, x, i => (ws (s i)).val (content x)

def retainedEvaluate {k : ℕ} (p : RetainedRunProcess k) (i : Fin (k + 1)) : Bool :=
  retainedReadout p.readout (retainedTrace p i.val) i

/-- The execution records native passes and readouts of the states in that same run. -/
def RetainedExecution {k : ℕ} (p : RetainedRunProcess k)
    (states : ℕ → Trace × ℕ) (n : ℕ) (outputs : Fin (k + 1) → Bool) : Prop :=
  states 0 = (p.content, p.initialCounter) ∧
  (∀ i, i < n → OperatorKO7.Meta.BoundaryObserver.RecursorDecidability.Pass
    (states i) (states (i + 1))) ∧
  states n = (p.content, 0) ∧
  ∀ i, outputs i = retainedReadout p.readout (states i.val) i

theorem retained_execution {k : ℕ} (p : RetainedRunProcess k) :
    RetainedExecution p (retainedTrace p) p.initialCounter (retainedEvaluate p) := by
  refine ⟨rfl, ?_, ?_, fun _ => rfl⟩
  · intro n hn
    refine ⟨rfl, ?_⟩
    change p.initialCounter - n = p.initialCounter - (n + 1) + 1
    omega
  · change (p.content, p.initialCounter - p.initialCounter) = (p.content, 0)
    have hz : p.initialCounter - p.initialCounter = 0 := by omega
    rw [hz]

theorem retained_execution_length {k : ℕ} (p : RetainedRunProcess k)
    (states : ℕ → Trace × ℕ) (n : ℕ) (outputs : Fin (k + 1) → Bool)
    (he : RetainedExecution p states n outputs) : n = p.initialCounter :=
  OperatorKO7.Meta.BoundaryObserver.RecursorDecidability.run_length_eq_counter
    states n p.initialCounter p.content he.2.1 he.1 he.2.2.1

/-- Every visited counter is an unchanged original counted-source input. -/
def retainedEmbedding (R : Trace) (k : ℕ) : Fin (k + 1) ↪ Trace × ℕ where
  toFun i := (R, k - i.val)
  inj' := by
    rintro ⟨i, hi⟩ ⟨j, hj⟩ h
    have hc := congrArg Prod.snd h
    change k - i = k - j at hc
    have hij : i = j := by omega
    cases hij
    rfl

inductive RetainedReadoutNative (k : ℕ) :
    SelectionProcess (Fin (k + 1)) CountedWitness → Prop where
  | direct (w : CountedWitness) : RetainedReadoutNative k (.direct w)
  | selected (m : ℕ) (s : Fin (k + 1) → Fin m) (ws : Fin m → CountedWitness)
      (hs : ∀ i j, s i = s j) : RetainedReadoutNative k (.selected m s ws)

def retainedNative (R : Trace) (k : ℕ) : Set (RetainedRunProcess k) :=
  {p | p.content = R ∧ p.initialCounter = k ∧ RetainedReadoutNative k p.readout}

/-- The resource coordinates count passes, all visited-state readouts and their sum. -/
noncomputable def retainedCost {k : ℕ} (p : RetainedRunProcess k) (j : ℕ) : ℝ :=
  if j = 0 then (p.initialCounter : ℝ)
  else if j = 1 then (((k + 1) * primitiveCalls 1 p.readout : ℕ) : ℝ)
  else if j = 2 then (p.initialCounter : ℝ) +
    (((k + 1) * primitiveCalls 1 p.readout : ℕ) : ℝ)
  else 0

noncomputable def retainedContract (R : Trace) (k : ℕ) : SourceContract where
  Process := RetainedRunProcess k
  Input := Fin (k + 1)
  Output := Bool
  Witness := CountedWitness
  source := ⟨R, k, .target⟩
  evaluate := retainedEvaluate
  interpret w := ⟨R, k, .direct w⟩
  allowed := fun _ => {s | ∀ i j, s i = s j}
  combines := fun _ _ _ => True
  assemble m s ws := ⟨R, k, .selected m s ws⟩
  cost := retainedCost

theorem retained_source_data (R : Trace) (k : ℕ) :
    (retainedContract R k).source.content = R ∧
      (retainedContract R k).source.initialCounter = k := ⟨rfl, rfl⟩

theorem retained_incidence (R : Trace) (k : ℕ) (w : CountedWitness) (i : Fin (k + 1)) :
    (retainedContract R k).problem.sat w i ↔
      countedContract.problem.sat w (retainedEmbedding R k i) := Iff.rfl

theorem retained_good_iff (R : Trace) (k : ℕ) (D : Set (Fin (k + 1))) :
    Good (retainedContract R k).problem D ↔
      Good countedContract.problem (retainedEmbedding R k '' D) := by
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨w, ?_⟩
    rintro x ⟨i, hi, rfl⟩
    exact hw i hi
  · rintro ⟨w, hw⟩
    exact ⟨w, fun i hi => hw _ ⟨i, hi, rfl⟩⟩

/-- A permitted finite selector extends to an original content selector. -/
theorem retained_selector_native (R : Trace) (k m : ℕ)
    (s : Fin (k + 1) → Fin m) (hs : ∀ i j, s i = s j) :
    ∃ g : Trace × ℕ → Fin m, g ∈ RecursorSource.contentSelectors m ∧
      ∀ i, g (retainedEmbedding R k i) = s i := by
  let z : Fin (k + 1) := ⟨0, by omega⟩
  exact ⟨fun _ => s z, fun _ _ _ => rfl, fun i => hs z i⟩

theorem retained_denotes {k : ℕ} (p : RetainedRunProcess k)
    (hp : RetainedReadoutNative k p.readout) :
    ∃ f : Trace → Bool, ∀ i, retainedEvaluate p i = f (content (retainedTrace p i.val)) := by
  cases p with
  | mk R n q =>
    cases hp with
    | direct w => exact ⟨w.val, fun _ => rfl⟩
    | selected m s ws hs =>
      let z : Fin (k + 1) := ⟨0, by omega⟩
      exact ⟨(ws (s z)).val, fun i => congrArg (fun j => (ws j).val R) (hs i z)⟩

theorem retained_closed (R : Trace) (k : ℕ) :
    SourceAssemblyClosed (retainedContract R k) (retainedNative R k) := by
  intro D m s ws ha _
  exact ⟨rfl, rfl, .selected m s ws ha⟩

theorem retained_selects (R : Trace) (k : ℕ) :
    SourceAssemblySelects (retainedContract R k) := by
  intro D m s ws _ _ i _
  rfl

theorem retained_candidate_native (R : Trace) (k : ℕ) (w : CountedWitness) :
    (retainedContract R k).interpret w ∈ retainedNative R k := ⟨rfl, rfl, .direct w⟩

theorem retained_native_goal (R : Trace) (k : ℕ) :
    SourceNativeAssemblyGoal (retainedContract R k) (retainedNative R k) :=
  sourceNativeAssemblyGoal _ _ (retained_closed R k) (retained_selects R k)

theorem retained_singleton_plan (R : Trace) (k : ℕ) (i : Fin (k + 1)) :
    Nonempty (SourcePlan (retainedContract R k) {i} 1) := by
  refine ⟨⟨((fun _ => 0),
    fun _ => ⟨fun _ => observed (retainedEmbedding R k i), Set.mem_univ _⟩),
    (fun _ _ => rfl), trivial, ?_⟩⟩
  intro j hj
  have h : j = i := Set.mem_singleton_iff.mp hj
  subst j
  rfl

/-- The same assembled run retains its source data, native execution and whole-plan charges. -/
def SourceRetainedRunGoal (R : Trace) (k : ℕ) : Prop :=
  CoreGoal (retainedContract R k) ∧
  SourceNativeAssemblyGoal (retainedContract R k) (retainedNative R k) ∧
  (∀ i : Fin (k + 1), Nonempty (SourcePlan (retainedContract R k) {i} 1)) ∧
  ∀ D m (r : SourcePlan (retainedContract R k) D m),
    let p := planProcess (retainedContract R k) r
    p.content = R ∧ p.initialCounter = k ∧
    p.readout = .selected m r.val.1 r.val.2 ∧
    RetainedExecution p (retainedTrace p) k (retainedEvaluate p) ∧
    planCost (retainedContract R k) r 1 = (((k + 1) * 2 : ℕ) : ℝ) ∧
    ∀ states n outputs, RetainedExecution p states n outputs →
      planCost (retainedContract R k) r 0 = (n : ℝ) ∧
      planCost (retainedContract R k) r 2 = (n : ℝ) + (((k + 1) * 2 : ℕ) : ℝ)

theorem sourceRetainedRunGoal (R : Trace) (k : ℕ) : SourceRetainedRunGoal R k := by
  refine ⟨source_observation_repair_core _, retained_native_goal R k,
    retained_singleton_plan R k, ?_⟩
  intro D m r
  refine ⟨rfl, rfl, rfl, retained_execution _, rfl, ?_⟩
  intro states n outputs he
  have hn := retained_execution_length (planProcess (retainedContract R k) r) states n outputs he
  rw [hn]
  exact ⟨rfl, rfl⟩

theorem retained_positive_plan (R : Trace) :
    ∃ r : SourcePlan (retainedContract R 1) {(0 : Fin 2)} 1,
      planCost (retainedContract R 1) r 0 = 1 ∧
      planCost (retainedContract R 1) r 1 = 4 ∧
      planCost (retainedContract R 1) r 2 = 5 := by
  obtain ⟨r⟩ := retained_singleton_plan R 1 (0 : Fin 2)
  refine ⟨r, ?_, rfl, ?_⟩
  · change ((1 : ℕ) : ℝ) = 1
    norm_num
  · change ((1 : ℕ) : ℝ) + ((4 : ℕ) : ℝ) = 5
    norm_num

end NativeAssembly


namespace NativeAssembly

open Demand Transport
open OperatorKO7 (Trace)
open OperatorKO7.Meta.BoundaryObserver.RecursorDecidability (Pass)

/-- The control retains a concrete native readout on the original content carrier. -/
def controlFalseReadout : CountedWitness := ⟨fun _ => false, Set.mem_univ _⟩

/-- Every direct candidate is admitted while assembled syntax is excluded. -/
inductive DirectOnlyCounted : countedContract.Process → Prop where
  | direct (w : CountedWitness) : DirectOnlyCounted (.direct w)

/-- The altered assembly returns a fixed admitted native readout. -/
@[reducible]
noncomputable def wrongReadoutCounted : SourceContract :=
  { countedContract with assemble := fun _ _ _ => .direct controlFalseReadout }

theorem wrong_readout_closed : SourceAssemblyClosed wrongReadoutCounted CountedNative := by
  intro D k s ws _ _
  exact .direct controlFalseReadout

/-- Each omitted primitive law has a nonempty native class and a concrete licensed plan. -/
def SourceAssemblyControlsGoal (R : Trace) : Prop :=
  SourceAssemblySelects countedContract ∧
  (∀ w : CountedWitness, DirectOnlyCounted (countedContract.interpret w)) ∧
  (∃ p : countedContract.Process, DirectOnlyCounted p) ∧
  ¬ SourceAssemblyClosed countedContract DirectOnlyCounted ∧
  (∃ r : SourcePlan countedContract {(R, 0)} 1,
    (∀ x ∈ ({(R, 0)} : Set (Trace × ℕ)),
      countedContract.evaluate (planProcess countedContract r) x =
        countedContract.evaluate countedContract.source x) ∧
    ¬ DirectOnlyCounted (planProcess countedContract r)) ∧
  SourceAssemblyClosed wrongReadoutCounted CountedNative ∧
  (∀ w : CountedWitness, CountedNative (wrongReadoutCounted.interpret w)) ∧
  (∃ p : wrongReadoutCounted.Process, CountedNative p) ∧
  ¬ SourceAssemblySelects wrongReadoutCounted ∧
  (∃ r : SourcePlan wrongReadoutCounted {(R, 0)} 1,
    CountedNative (planProcess wrongReadoutCounted r) ∧
    ¬ (∀ x ∈ ({(R, 0)} : Set (Trace × ℕ)),
      wrongReadoutCounted.evaluate (planProcess wrongReadoutCounted r) x =
        wrongReadoutCounted.evaluate wrongReadoutCounted.source x))

theorem sourceAssemblyControlsGoal (R : Trace) : SourceAssemblyControlsGoal R := by
  obtain ⟨r⟩ := counted_singleton_plan (R, 0)
  have hreject : ¬ DirectOnlyCounted (planProcess countedContract r) := by
    intro h
    change DirectOnlyCounted (.selected 1 r.val.1 r.val.2) at h
    cases h
  have hcorrect :
      ∀ x ∈ ({(R, 0)} : Set (Trace × ℕ)),
        countedContract.evaluate (planProcess countedContract r) x =
          countedContract.evaluate countedContract.source x :=
    sourceAssemblyCombinerLaw countedContract counted_selects
      {(R, 0)} 1 r.val.1 r.val.2 r.property.1 r.property.2.1 r.property.2.2
  have hwrong :
      ¬ (∀ x ∈ ({(R, 0)} : Set (Trace × ℕ)),
        wrongReadoutCounted.evaluate (planProcess wrongReadoutCounted r) x =
          wrongReadoutCounted.evaluate wrongReadoutCounted.source x) := by
    intro h
    have h0 := h (R, 0) (by rfl)
    change false = true at h0
    cases h0
  refine ⟨counted_selects, (fun w => .direct w),
    ⟨.direct controlFalseReadout, .direct controlFalseReadout⟩, ?_,
    ⟨r, hcorrect, hreject⟩, wrong_readout_closed, (fun w => .direct w),
    ⟨.direct controlFalseReadout, .direct controlFalseReadout⟩, ?_,
    ⟨r, .direct controlFalseReadout, hwrong⟩⟩
  · intro hc
    exact hreject (hc {(R, 0)} 1 r.val.1 r.val.2 r.property.1 r.property.2.1)
  · intro he
    exact hwrong (sourceAssemblyCombinerLaw wrongReadoutCounted he
      {(R, 0)} 1 r.val.1 r.val.2 r.property.1 r.property.2.1 r.property.2.2)

/-- Each inherited run premise has a separate failure on one admitted selected process. -/
def RetainedRunControlsGoal (R : Trace) : Prop :=
  ∃ r : SourcePlan (retainedContract R 2) {(0 : Fin 3)} 1,
    let p := planProcess (retainedContract R 2) r
    p ∈ retainedNative R 2 ∧
    planCost (retainedContract R 2) r 0 = 2 ∧
    planCost (retainedContract R 2) r 0 ≠ (1 : ℝ) ∧
    (∃ (states : ℕ → Trace × ℕ) (outputs : Fin 3 → Bool),
      states 0 = (p.content, p.initialCounter) ∧
      states 1 = (p.content, 0) ∧
      (∀ i, outputs i = retainedReadout p.readout (states i.val) i) ∧
      ¬ (∀ i, i < 1 → Pass (states i) (states (i + 1)))) ∧
    (∃ (states : ℕ → Trace × ℕ) (outputs : Fin 3 → Bool),
      (∀ i, i < 1 → Pass (states i) (states (i + 1))) ∧
      states 1 = (p.content, 0) ∧
      (∀ i, outputs i = retainedReadout p.readout (states i.val) i) ∧
      states 0 ≠ (p.content, p.initialCounter)) ∧
    (∃ (states : ℕ → Trace × ℕ) (outputs : Fin 3 → Bool),
      states 0 = (p.content, p.initialCounter) ∧
      (∀ i, i < 1 → Pass (states i) (states (i + 1))) ∧
      (∀ i, outputs i = retainedReadout p.readout (states i.val) i) ∧
      states 1 ≠ (p.content, 0))

theorem retainedRunControlsGoal (R : Trace) : RetainedRunControlsGoal R := by
  obtain ⟨r⟩ := retained_singleton_plan R 2 (0 : Fin 3)
  refine ⟨r, (retained_native_goal R 2 {(0 : Fin 3)} 1 r).1,
    rfl, ?_, ?_, ?_, ?_⟩
  · change (2 : ℝ) ≠ 1
    norm_num
  · let states : ℕ → Trace × ℕ := fun n => (R, if n = 0 then 2 else 0)
    refine ⟨states, (fun i => retainedReadout
      (planProcess (retainedContract R 2) r).readout (states i.val) i),
      rfl, rfl, (fun _ => rfl), ?_⟩
    intro h
    have hc : (2 : ℕ) = 1 := (h 0 (by omega)).2
    omega
  · let states : ℕ → Trace × ℕ := fun n => (R, 1 - n)
    refine ⟨states, (fun i => retainedReadout
      (planProcess (retainedContract R 2) r).readout (states i.val) i),
      ?_, rfl, (fun _ => rfl), ?_⟩
    · intro i hi
      have hz : i = 0 := by omega
      subst i
      exact ⟨rfl, rfl⟩
    · intro h
      have hc : (1 : ℕ) = 2 := congrArg Prod.snd h
      omega
  · refine ⟨retainedTrace (planProcess (retainedContract R 2) r),
      retainedEvaluate (planProcess (retainedContract R 2) r),
      rfl, ?_, (fun _ => rfl), ?_⟩
    · intro i hi
      have hz : i = 0 := by omega
      subst i
      exact ⟨rfl, rfl⟩
    · intro h
      have hc : (1 : ℕ) = 0 := congrArg Prod.snd h
      omega

end NativeAssembly


end UniversalObservation.Completion.Operational

namespace UniversalObservation.Demand

def DownsetRealizationGoal : Prop :=
  ∀ (I : Type) [Fintype I] (K : Set (Set I)),
    Downward K → (∅ : Set I) ∈ K →
    ∃ F : Set (I → Bool), F.Nonempty ∧ ∀ D : Set I,
      Good (readoutProblem id (fun _ => false) F) D ↔ D ∈ K

theorem downsetRealizationGoal : DownsetRealizationGoal := by
  intro I _ K hK h0
  exact boolean_downset_realization K hK h0

end UniversalObservation.Demand

namespace UniversalObservation.Completion

open Demand

def CompactCompletionGoal : Prop :=
  ∀ (I W : Type) [TopologicalSpace W] [CompactSpace W] (P : Problem I W),
    (∀ i, IsClosed {w | P.sat w i}) →
    ((∀ D : Finset I, Good P (D : Set I)) ↔ Good P Set.univ)

theorem compactCompletionGoal : CompactCompletionGoal := by
  intro I W _ _ P hclosed
  exact compact_completion_iff P hclosed

def ClosedReadoutsGoal : Prop :=
  ∀ (Y V : Type) [Fintype V] [Nonempty V] [TopologicalSpace V] [DiscreteTopology V]
    (F : Set (Y → V)),
    IsClosed F ↔ ∀ T : Y → V,
      (∀ D : Finset Y, ∃ f ∈ F, ∀ y ∈ D, f y = T y) → T ∈ F

theorem closedReadoutsGoal : ClosedReadoutsGoal := by
  intro Y V _ _ _ _ F
  exact closed_readouts_iff F

end UniversalObservation.Completion

namespace UniversalObservation.Completion.Operational


namespace SourceProtocol

open OperatorKO7.Meta.BoundaryObserver
open ProtocolResolution

/-- The capacity law concerns one invocation of the supplied native channel. -/
def Capacity {X O : Type} [Fintype X] [Fintype O]
    (K : StochasticGraph.Channel X O) (cap : ℝ) : Prop :=
  ∀ μ : FiniteLaw X,
    jointMI (fun xo : X × O => μ.mass xo.1 * K.prob xo.1 xo.2) ≤ cap

/-- Every active query invokes the same channel at its positive native charge. -/
noncomputable def acquisition {X A O : Type} [Fintype X] [Fintype A] [Fintype O]
    (K : StochasticGraph.Channel X O) (μ : FiniteLaw X)
    (policy : List (A × O) → FiniteLaw A) (stop : List (A × O) → Bool)
    (charge : ℝ) (hcharge : 0 < charge) : FiniteProtocol X A O where
  prior := μ
  policy := policy
  observation _ _ x := ⟨K.prob x, K.nonneg x, K.row_sum x⟩
  stop := stop
  cost _ _ := charge
  cost_nonnegative _ _ := hcharge.le

/-- Reachable posteriors supply the local capacity law at the same native charge. -/
theorem acquisition_capacity {X A O : Type}
    [Fintype X] [Fintype A] [Fintype O]
    (K : StochasticGraph.Channel X O) (μ : FiniteLaw X)
    (policy : List (A × O) → FiniteLaw A) (stop : List (A × O) → Bool)
    (charge : ℝ) (hcharge : 0 < charge) (cap : ℝ) (hcapacity : Capacity K cap) :
    LocalCapacityBound (acquisition K μ policy stop charge hcharge) (cap / charge) := by
  intro h a hh _ _
  let ν : FiniteLaw X :=
    ⟨posterior (acquisition K μ policy stop charge hcharge) h,
      posterior_nonnegative (acquisition K μ policy stop charge hcharge) h,
      posterior_total (acquisition K μ policy stop charge hcharge) h hh⟩
  change jointMI (fun xo : X × O =>
    posterior (acquisition K μ policy stop charge hcharge) h xo.1 *
      K.prob xo.1 xo.2) ≤ cap / charge * charge
  rw [div_mul_cancel₀ cap hcharge.ne']
  exact hcapacity ν

/-- The stopped bound uses the native channel and its actual paid history law. -/
theorem acquisition_information_bound {X A O : Type}
    [Fintype X] [Fintype A] [Fintype O]
    (K : StochasticGraph.Channel X O) (μ : FiniteLaw X)
    (policy : List (A × O) → FiniteLaw A) (stop : List (A × O) → Bool)
    (charge : ℝ) (hcharge : 0 < charge) (cap : ℝ) (hcapacity : Capacity K cap)
    (n : ℕ) (bank : List (List (A × O))) (hbank : HistoryBank n bank) :
    terminalMI (acquisition K μ policy stop charge hcharge) n bank ≤
      (cap / charge) * expectedCost (acquisition K μ policy stop charge hcharge) n bank :=
  terminalMI_le_expectedCost (acquisition K μ policy stop charge hcharge)
    (cap / charge) n bank hbank
    (acquisition_capacity K μ policy stop charge hcharge cap hcapacity)

/-- Required information imposes a lower bound at the native source rate. -/
theorem acquisition_cost_lower {X A O : Type}
    [Fintype X] [Fintype A] [Fintype O]
    (K : StochasticGraph.Channel X O) (μ : FiniteLaw X)
    (policy : List (A × O) → FiniteLaw A) (stop : List (A × O) → Bool)
    (charge : ℝ) (hcharge : 0 < charge) (cap : ℝ) (hcap : 0 < cap)
    (hcapacity : Capacity K cap) (n : ℕ) (bank : List (List (A × O)))
    (hbank : HistoryBank n bank) (required : ℝ)
    (htarget : required ≤ terminalMI (acquisition K μ policy stop charge hcharge) n bank) :
    required / (cap / charge) ≤
      expectedCost (acquisition K μ policy stop charge hcharge) n bank := by
  apply (div_le_iff₀ (div_pos hcap hcharge)).mpr
  calc
    required ≤ (cap / charge) *
        expectedCost (acquisition K μ policy stop charge hcharge) n bank :=
      htarget.trans
        (acquisition_information_bound K μ policy stop charge hcharge cap hcapacity
          n bank hbank)
    _ = expectedCost (acquisition K μ policy stop charge hcharge) n bank *
        (cap / charge) := mul_comm _ _

/-- An output equivalence transfers capacity through the exact native weights. -/
theorem capacity_reindex {X O U : Type} [Fintype X] [Fintype O] [Fintype U]
    (K : StochasticGraph.Channel X O) (L : StochasticGraph.Channel X U)
    (e : O ≃ U) (hkernel : ∀ x o, L.prob x (e o) = K.prob x o)
    (cap : ℝ) (hcapacity : Capacity K cap) : Capacity L cap := by
  intro μ
  have he := jointMI_reindex (Equiv.refl X) e
    (fun xo : X × O => μ.mass xo.1 * K.prob xo.1 xo.2)
    (fun xu : X × U => μ.mass xu.1 * L.prob xu.1 xu.2)
    (fun x o => congrArg (fun p => μ.mass x * p) (hkernel x o))
  rw [he]
  exact hcapacity μ

/-- The binary source supplies its capacity law for every normalized prior. -/
theorem binary_capacity (δ : ℝ) (hδ : |δ| ≤ 1 / 2) :
    Capacity (binaryChannel δ hδ) (4 * δ ^ 2) := by
  intro μ
  have htotal := μ.total
  simp only [Fintype.sum_bool] at htotal
  have hprior : μ.mass = binaryPrior (μ.mass true) := by
    funext b
    cases b
    · change μ.mass false = 1 - μ.mass true
      linarith
    · rfl
  change jointMI (fun xy : Bool × Bool =>
    μ.mass xy.1 * binaryKernel δ xy.1 xy.2) ≤ 4 * δ ^ 2
  rw [hprior]
  exact binaryJoint_information_le_quadratic (μ.mass true) δ hδ

end SourceProtocol

namespace SourceInstrument

open OperatorKO7.Meta.BoundaryObserver
open ProtocolResolution

abbrev Support {X O : Type} (K : X → O → ℝ) :=
  {xo : X × O // 0 < K xo.1 xo.2}

def liftSelector {X O : Type} (K : X → O → ℝ) {k : ℕ}
    (side : X → Fin k) : Support K → Fin k := fun xo => side xo.val.1

/-- The source retains positive support, admitted readouts and input-side permissions. -/
def contract {X O V : Type} [Fintype O] (K : StochasticGraph.Channel X O)
    (P : X → V) (F : Set (O → V)) (allowed : (k : ℕ) → Set (X → Fin k))
    (combines : Set (Support K.prob) → (k : ℕ) → (Support K.prob → Fin k) → Prop)
    (charge : ℝ) : SourceContract :=
  readoutSource (Support K.prob) O V (fun xo => xo.val.2)
    (fun xo => P xo.val.1) F
    (fun k => {s | ∃ side ∈ allowed k, s = liftSelector K.prob side})
    combines (fun _ _ => charge)

/-- The source constructor preserves the local selected readout equation. -/
theorem contract_combiner {X O V : Type} [Fintype O]
    (K : StochasticGraph.Channel X O) (P : X → V) (F : Set (O → V))
    (allowed : (k : ℕ) → Set (X → Fin k))
    (combines : Set (Support K.prob) → (k : ℕ) → (Support K.prob → Fin k) → Prop)
    (charge : ℝ) : (contract K P F allowed combines charge).combinerLaw := by
  intro D k s ws _ _ hw
  exact hw

/-- Native constructor closure contains neither a target nor its satisfaction equation. -/
def NativeClosure {X O V : Type} (K : X → O → ℝ) (F : Set (O → V))
    (allowed : (k : ℕ) → Set (X → Fin k))
    (combines : Set (Support K) → (k : ℕ) → (Support K → Fin k) → Prop)
    (native : Set (Support K → V)) : Prop :=
  ∀ D k side, side ∈ allowed k → combines D k (liftSelector K side) →
    ∀ ws : Fin k → F, (fun xo => (ws (side xo.val.1)).val xo.val.2) ∈ native

/-- The repeated native process evolves its state through the source transition. -/
noncomputable def traceWeight {X O : Type} [Fintype O]
    (K : StochasticGraph.Channel X O) (next : X → O → X) : X → List O → ℝ
  | _, [] => 1
  | x, o :: os => K.prob x o * traceWeight K next (next x o) os

/-- Retention gives the exact repeated-kernel law, including zero-weight traces. -/
theorem traceWeight_repeat {X O : Type} [Fintype O]
    (K : StochasticGraph.Channel X O) (next : X → O → X)
    (hretain : ∀ x o, 0 < K.prob x o → next x o = x) (x : X) (os : List O) :
    traceWeight K next x os = traceWeight K (fun x _ => x) x os := by
  induction os generalizing x with
  | nil => rfl
  | cons o os ih =>
    change K.prob x o * traceWeight K next (next x o) os =
      K.prob x o * traceWeight K (fun x _ => x) x os
    by_cases hz : K.prob x o = 0
    · simp only [hz, zero_mul]
    · have hp : 0 < K.prob x o := by
        by_contra hn
        have hnonnegative := K.nonneg x o
        apply hz
        linarith
      rw [hretain x o hp, ih x]

/-- Every operational clause uses the native kernel, transition, plan and source price. -/
def SourceOperationalGoal {X O V : Type} [Fintype X] [Fintype O]
    (K : StochasticGraph.Channel X O) (next : X → O → X)
    (P : X → V) (F : Set (O → V))
    (allowed : (k : ℕ) → Set (X → Fin k))
    (combines : Set (Support K.prob) → (k : ℕ) → (Support K.prob → Fin k) → Prop)
    (native : Set (Support K.prob → V))
    (charge : ℝ) (hcharge : 0 < charge) (cap : ℝ) : Prop :=
  let C := contract K P F allowed combines charge
  C.combinerLaw ∧ CoreGoal C ∧
  (∀ x os, traceWeight K next x os = traceWeight K (fun x _ => x) x os) ∧
  (∀ D k (r : SourcePlan C D k),
    planProcess C r ∈ native ∧
    (∀ xo ∈ D, planProcess C r xo = P xo.val.1) ∧ planCost C r 0 = charge) ∧
  (∀ (A : Type) [Fintype A] (μ : FiniteLaw X)
    (policy : List (A × O) → FiniteLaw A) (stop : List (A × O) → Bool),
    let p := SourceProtocol.acquisition K μ policy stop charge hcharge
    (∀ h a x o, (p.observation h a x).mass o = K.prob x o) ∧
    (∀ h a, p.cost h a = C.cost C.source 0) ∧
    ∀ n bank, HistoryBank n bank →
      (terminalMI p n bank ≤ (cap / C.cost C.source 0) * expectedCost p n bank) ∧
      (∀ required, 0 < cap → required ≤ terminalMI p n bank →
        required / (cap / C.cost C.source 0) ≤ expectedCost p n bank))

/-- Independent state retention, native closure and capacity derive the operational Goal. -/
theorem sourceOperationalGoal {X O V : Type} [Fintype X] [Fintype O]
    (K : StochasticGraph.Channel X O) (next : X → O → X)
    (P : X → V) (F : Set (O → V))
    (allowed : (k : ℕ) → Set (X → Fin k))
    (combines : Set (Support K.prob) → (k : ℕ) → (Support K.prob → Fin k) → Prop)
    (native : Set (Support K.prob → V))
    (charge : ℝ) (hcharge : 0 < charge) (cap : ℝ)
    (hretain : ∀ x o, 0 < K.prob x o → next x o = x)
    (hnative : NativeClosure K.prob F allowed combines native)
    (hcapacity : SourceProtocol.Capacity K cap) :
    SourceOperationalGoal K next P F allowed combines native charge hcharge cap := by
  refine ⟨contract_combiner K P F allowed combines charge,
    source_observation_repair_core _, traceWeight_repeat K next hretain, ?_, ?_⟩
  · intro D k r
    obtain ⟨side, hside, hs⟩ := r.property.1
    have hb : combines D k (liftSelector K.prob side) := by
      rw [← hs]
      exact r.property.2.1
    refine ⟨?_, ?_, rfl⟩
    · change (fun xo => (r.val.2 (r.val.1 xo)).val xo.val.2) ∈ native
      rw [hs]
      exact hnative D k side hside hb r.val.2
    · intro xo hxo
      exact r.property.2.2 xo hxo
  · intro A _ μ policy stop
    refine ⟨fun _ _ _ _ => rfl, fun _ _ => rfl, ?_⟩
    intro n bank hbank
    refine ⟨SourceProtocol.acquisition_information_bound K μ policy stop charge hcharge
      cap hcapacity n bank hbank, ?_⟩
    intro required hcap htarget
    exact SourceProtocol.acquisition_cost_lower K μ policy stop charge hcharge
      cap hcap hcapacity n bank hbank required htarget

end SourceInstrument


namespace SourceInstrument

open OperatorKO7.Meta.BoundaryObserver
open ProtocolResolution

/-- The source-native closure law supplies the common assembly interface. -/
theorem contract_closed {X O V : Type} [Fintype O]
    (K : StochasticGraph.Channel X O) (P : X → V) (F : Set (O → V))
    (allowed : (k : ℕ) → Set (X → Fin k))
    (combines : Set (Support K.prob) → (k : ℕ) → (Support K.prob → Fin k) → Prop)
    (native : Set (Support K.prob → V)) (charge : ℝ)
    (hnative : NativeClosure K.prob F allowed combines native) :
    SourceAssemblyClosed (contract K P F allowed combines charge) native := by
  intro D k s ws hs hc
  obtain ⟨side, hside, he⟩ := hs
  have hb : combines D k (liftSelector K.prob side) := by
    rw [← he]
    exact hc
  change (fun xo => (ws (s xo)).val xo.val.2) ∈ native
  rw [he]
  exact hnative D k side hside hb ws

/-- Selection preserves native readout evaluation before any target equation. -/
theorem contract_selects {X O V : Type} [Fintype O]
    (K : StochasticGraph.Channel X O) (P : X → V) (F : Set (O → V))
    (allowed : (k : ℕ) → Set (X → Fin k))
    (combines : Set (Support K.prob) → (k : ℕ) → (Support K.prob → Fin k) → Prop)
    (charge : ℝ) : SourceAssemblySelects (contract K P F allowed combines charge) := by
  intro D k s ws _ _ xo _
  rfl

/-- A primitive query retains its native channel and its invocation count. -/
structure NativeChannelProgram (X O : Type) [Fintype O] where
  channel : StochasticGraph.Channel X O
  calls : ℕ

def primitiveQuery {X O : Type} [Fintype O] (K : StochasticGraph.Channel X O) :
    NativeChannelProgram X O := ⟨K, 1⟩

theorem endpoint_bias_bound : |(1 / 2 : ℝ)| ≤ 1 / 2 := by
  exact le_of_eq (abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2))

noncomputable def endpointProgram : NativeChannelProgram Bool Bool :=
  primitiveQuery (binaryChannel (1 / 2) endpoint_bias_bound)

noncomputable def endpointKernel : StochasticGraph.Channel Bool Bool := endpointProgram.channel

noncomputable def endpointCharge : ℝ := endpointProgram.calls

theorem endpoint_original : endpointKernel = binaryChannel (1 / 2) endpoint_bias_bound := rfl

theorem endpointCharge_one : endpointCharge = 1 := by
  change (↑(1 : ℕ) : ℝ) = 1
  norm_num

theorem endpointCharge_pos : 0 < endpointCharge := by
  rw [endpointCharge_one]
  norm_num

/-- The admitted source readout returns the native reported bit. -/
def endpointReadouts : Set (Bool → Bool) := {f | ∀ o, f o = o}

/-- Constant input-side selectors incur no additional channel invocation. -/
def endpointAllowed (k : ℕ) : Set (Bool → Fin k) :=
  {side | ∃ j : Fin k, ∀ x, side x = j}

def endpointCombines : Set (Support endpointKernel.prob) → (k : ℕ) →
    (Support endpointKernel.prob → Fin k) → Prop := fun _ _ _ => True

def endpointNative : Set (Support endpointKernel.prob → Bool) :=
  {p | ∀ xo, p xo = xo.val.2}

noncomputable def endpointContract : SourceContract :=
  contract endpointKernel id endpointReadouts endpointAllowed endpointCombines endpointCharge

/-- Candidate satisfaction is the original native support incidence with admitted readouts. -/
theorem endpoint_problem_satisfaction (d : endpointReadouts) (xo : Support endpointKernel.prob) :
    endpointContract.problem.sat d xo ↔
      (Transport.supportProblem endpointKernel.prob (id : Bool → Bool)).sat d.val xo := Iff.rfl

/-- The endpoint report is the retained state on each positive native branch. -/
theorem endpoint_retains (x o : Bool) (hp : 0 < endpointKernel.prob x o) : o = x := by
  change (0 : ℝ) < (if o = x then 1 / 2 + 1 / 2 else 1 / 2 - 1 / 2) at hp
  by_contra hn
  rw [if_neg hn] at hp
  norm_num at hp

theorem endpoint_capacity : SourceProtocol.Capacity endpointKernel 1 := by
  have h := SourceProtocol.binary_capacity (1 / 2) endpoint_bias_bound
  have he : (4 : ℝ) * (1 / 2) ^ 2 = 1 := by norm_num
  rw [he] at h
  exact h

theorem endpoint_native_closure :
    NativeClosure endpointKernel.prob endpointReadouts endpointAllowed
      endpointCombines endpointNative := by
  intro D k side _ _ ws xo
  exact (ws (side xo.val.1)).property xo.val.2

/-- Every admitted assembled process denotes the same actual native readout on all support. -/
theorem endpoint_denotes (p : endpointContract.Process) (hp : p ∈ endpointNative) :
    ∃ d ∈ endpointReadouts, ∀ xo, p xo = d xo.val.2 :=
  ⟨id, fun _ => rfl, hp⟩

noncomputable def endpointPlan : SourcePlan endpointContract Set.univ 1 := by
  refine ⟨(liftSelector endpointKernel.prob (fun _ => (0 : Fin 1)),
    fun _ => ⟨id, fun _ => rfl⟩),
    ⟨(fun _ => (0 : Fin 1)), ⟨0, fun _ => rfl⟩, rfl⟩, trivial, ?_⟩
  intro xo _
  exact endpoint_retains xo.val.1 xo.val.2 xo.property

theorem endpoint_closed : SourceAssemblyClosed endpointContract endpointNative :=
  contract_closed endpointKernel id endpointReadouts endpointAllowed endpointCombines
    endpointNative endpointCharge endpoint_native_closure

theorem endpoint_selects : SourceAssemblySelects endpointContract :=
  contract_selects endpointKernel id endpointReadouts endpointAllowed endpointCombines endpointCharge

theorem endpoint_combiner : endpointContract.combinerLaw :=
  contract_combiner endpointKernel id endpointReadouts endpointAllowed endpointCombines endpointCharge

theorem endpoint_core : CoreGoal endpointContract := source_observation_repair_core _

/-- A required information amount costs at least that many primitive endpoint queries. -/
theorem endpoint_acquisition_lower {A : Type} [Fintype A] (μ : FiniteLaw Bool)
    (policy : List (A × Bool) → FiniteLaw A) (stop : List (A × Bool) → Bool)
    (n : ℕ) (bank : List (List (A × Bool))) (hbank : HistoryBank n bank) (required : ℝ)
    (htarget : required ≤ terminalMI
      (SourceProtocol.acquisition endpointKernel μ policy stop endpointCharge endpointCharge_pos)
      n bank) :
    required ≤ expectedCost
      (SourceProtocol.acquisition endpointKernel μ policy stop endpointCharge endpointCharge_pos)
      n bank := by
  have h := SourceProtocol.acquisition_cost_lower endpointKernel μ policy stop
    endpointCharge endpointCharge_pos 1 (by norm_num) endpoint_capacity n bank hbank required htarget
  have he : required / (1 / endpointCharge) = required := by
    rw [endpointCharge_one]
    ring
  rw [he] at h
  exact h

/-- The original channel, native plan, repeated queries and one-call price share one source. -/
def EndpointChannelOperationalGoal : Prop :=
  SourceOperationalGoal endpointKernel (fun _ o => o) id endpointReadouts
    endpointAllowed endpointCombines endpointNative endpointCharge endpointCharge_pos 1 ∧
  endpointKernel = binaryChannel (1 / 2) endpoint_bias_bound ∧ endpointProgram.calls = 1 ∧
  SourceAssemblyClosed endpointContract endpointNative ∧ SourceAssemblySelects endpointContract ∧
  (∀ p : endpointContract.Process, p ∈ endpointNative →
    ∃ d ∈ endpointReadouts, ∀ xo, p xo = d xo.val.2) ∧
  planProcess endpointContract endpointPlan ∈ endpointNative ∧
  planCost endpointContract endpointPlan 0 = 1 ∧
  (∀ xo, planProcess endpointContract endpointPlan xo = xo.val.2) ∧
  0 < endpointKernel.prob false false ∧ 0 < endpointKernel.prob true true ∧ (false : Bool) ≠ true

theorem endpointChannelOperationalGoal : EndpointChannelOperationalGoal := by
  refine ⟨sourceOperationalGoal endpointKernel (fun _ o => o) id endpointReadouts
    endpointAllowed endpointCombines endpointNative endpointCharge endpointCharge_pos 1
    endpoint_retains endpoint_native_closure endpoint_capacity,
    endpoint_original, rfl, endpoint_closed, endpoint_selects, endpoint_denotes,
    (fun _ => rfl), endpointCharge_one, (fun _ => rfl), ?_, ?_, by decide⟩
  · change (0 : ℝ) < binaryKernel (1 / 2) false false
    norm_num [binaryKernel]
  · change (0 : ℝ) < binaryKernel (1 / 2) true true
    norm_num [binaryKernel]

open scoped BigOperators

/-- The deletion fixture retains the endpoint data and sets its source price to zero. -/
noncomputable def zeroPricedSource : SourceContract :=
  contract endpointKernel id endpointReadouts endpointAllowed endpointCombines 0

/-- The deletion fixture queries the same normalized endpoint with zero paid cost. -/
noncomputable def zeroPricedEndpoint : FiniteProtocol Bool Unit Bool where
  prior := binaryPriorLaw (1 / 2) (by norm_num) (by norm_num)
  policy _ := unitLaw
  observation _ _ x :=
    { mass := endpointKernel.prob x
      nonnegative := endpointKernel.nonneg x
      total := endpointKernel.row_sum x }
  stop _ := false
  cost _ _ := 0
  cost_nonnegative _ _ := by norm_num

theorem zeroPricedEndpoint_historyMass_nil :
    historyMass zeroPricedEndpoint [] = 1 := by
  change (∑ x : Bool, zeroPricedEndpoint.prior.mass x) = 1
  exact zeroPricedEndpoint.prior.total

theorem zeroPricedEndpoint_posterior_nil :
    posterior zeroPricedEndpoint [] = binaryPrior (1 / 2) := by
  funext x
  unfold posterior
  rw [prefixMass_nil, zeroPricedEndpoint_historyMass_nil]
  change binaryPrior (1 / 2) x / 1 = binaryPrior (1 / 2) x
  norm_num

theorem zeroPricedEndpoint_gain_nil :
    localGain zeroPricedEndpoint [] () = 1 := by
  unfold localGain
  rw [zeroPricedEndpoint_posterior_nil]
  change jointMI (binaryJoint (1 / 2) (1 / 2)) = 1
  have h := binaryJoint_upper_only_control.2
  rw [binaryJoint_information_negative_endpoint] at h
  rw [binaryJoint_information_positive_endpoint]
  exact h

/-- The zero-price fixture preserves the other local source and protocol premises. -/
def QueryPricePremiseControlGoal : Prop :=
  SourceProtocol.Capacity endpointKernel 1 ∧
  (0 : ℝ) < 1 ∧
  SourceAssemblyClosed zeroPricedSource endpointNative ∧
  SourceAssemblySelects zeroPricedSource ∧
  (∀ h a x o, (zeroPricedEndpoint.observation h a x).mass o =
    endpointKernel.prob x o) ∧
  (∀ h a, zeroPricedEndpoint.cost h a =
    zeroPricedSource.cost zeroPricedSource.source 0) ∧
  (∀ x o, 0 < endpointKernel.prob x o → o = x) ∧
  HistoryBank 1 (historyBank Unit Bool 1) ∧
  localGain zeroPricedEndpoint [] () = 1 ∧
  ∀ rate : ℝ, ¬ LocalCapacityBound zeroPricedEndpoint rate

theorem queryPricePremiseControlGoal : QueryPricePremiseControlGoal := by
  refine ⟨endpoint_capacity, by norm_num, ?_, ?_,
    (fun _ _ _ _ => rfl), (fun _ _ => rfl), endpoint_retains,
    historyBank_complete Unit Bool 1, zeroPricedEndpoint_gain_nil, ?_⟩
  · intro D k s ws _ _
    change ∀ xo, (ws (s xo)).val xo.val.2 = xo.val.2
    intro xo
    exact (ws (s xo)).property xo.val.2
  · intro D k s ws _ _ i _
    rfl
  · intro rate h
    have hw : 0 < historyMass zeroPricedEndpoint [] := by
      rw [zeroPricedEndpoint_historyMass_nil]
      norm_num
    have ha : 0 < (zeroPricedEndpoint.policy []).mass () := by
      change (0 : ℝ) < 1
      norm_num
    have hbad := h [] () hw rfl ha
    rw [zeroPricedEndpoint_gain_nil] at hbad
    change (1 : ℝ) ≤ rate * 0 at hbad
    rw [mul_zero] at hbad
    norm_num at hbad

/-- The fair prior on the noiseless endpoint carries exactly one bit. -/
theorem fair_endpoint_information : jointMI (binaryJoint (1 / 2) (1 / 2)) = 1 := by
  rw [binaryJoint_information_positive_endpoint]
  have hh : Real.binEntropy (1 / 2 : ℝ) = Real.log 2 := by
    simpa only [one_div] using Real.binEntropy_two_inv
  rw [hh, div_self (Real.log_pos one_lt_two).ne']

/-- One query of the endpoint at its native price under the fair prior. -/
noncomputable def fairEndpointQuery : FiniteProtocol Bool Unit Bool :=
  SourceProtocol.acquisition endpointKernel (binaryPriorLaw (1 / 2) (by norm_num) (by norm_num))
    (fun _ => unitLaw) (fun _ => false) endpointCharge endpointCharge_pos

theorem fairEndpointQuery_historyMass_nil : historyMass fairEndpointQuery [] = 1 := by
  change (∑ x : Bool, fairEndpointQuery.prior.mass x) = 1
  exact fairEndpointQuery.prior.total

theorem fairEndpointQuery_posterior_nil :
    posterior fairEndpointQuery [] = binaryPrior (1 / 2) := by
  funext x
  unfold posterior
  rw [prefixMass_nil, fairEndpointQuery_historyMass_nil]
  change binaryPrior (1 / 2) x / 1 = binaryPrior (1 / 2) x
  norm_num

/-- The first fair query gains one bit. -/
theorem fairEndpointQuery_gain_nil : localGain fairEndpointQuery [] () = 1 := by
  unfold localGain
  rw [fairEndpointQuery_posterior_nil]
  change jointMI (binaryJoint (1 / 2) (1 / 2)) = 1
  exact fair_endpoint_information

/-- The capacity law is attained at one bit: no smaller capacity holds, and without it the
first fair query exceeds the local information bound at the rate it would supply. -/
def CapacityPremiseControlGoal : Prop :=
  SourceProtocol.Capacity endpointKernel 1 ∧
  (∀ cap : ℝ, cap < 1 → ¬ SourceProtocol.Capacity endpointKernel cap) ∧
  localGain fairEndpointQuery [] () = 1 ∧
  (∀ h a, fairEndpointQuery.cost h a = endpointCharge) ∧
  ∀ cap : ℝ, cap < 1 → ¬ LocalCapacityBound fairEndpointQuery (cap / endpointCharge)

theorem capacityPremiseControlGoal : CapacityPremiseControlGoal := by
  refine ⟨endpoint_capacity, ?_, fairEndpointQuery_gain_nil, (fun _ _ => rfl), ?_⟩
  · intro cap hcap h
    have hμ := h (binaryPriorLaw (1 / 2) (by norm_num) (by norm_num))
    change jointMI (binaryJoint (1 / 2) (1 / 2)) ≤ cap at hμ
    rw [fair_endpoint_information] at hμ
    linarith
  · intro cap hcap h
    have hw : 0 < historyMass fairEndpointQuery [] := by
      rw [fairEndpointQuery_historyMass_nil]
      norm_num
    have ha : 0 < (fairEndpointQuery.policy []).mass () := by
      change (0 : ℝ) < 1
      norm_num
    have hbad := h [] () hw rfl ha
    rw [fairEndpointQuery_gain_nil] at hbad
    have hc : fairEndpointQuery.cost [] () = 1 := endpointCharge_one
    rw [hc, endpointCharge_one, div_one, mul_one] at hbad
    linarith

end SourceInstrument


end UniversalObservation.Completion.Operational

namespace UniversalObservation.Demand

/-- Every finite color fiber has a witness exactly when it contains no obstruction. -/
theorem selectedOn_finset_iff_colorsOn {I W : Type*}
    (P : Problem I W) (D : Finset I) (k : ℕ) (s : I → Fin k) :
    SelectedOn P (D : Set I) k s ↔ ColorsOn P (D : Set I) k s := by
  classical
  constructor
  · rintro ⟨xs, hx⟩ B hBD hB ⟨j, hj⟩
    apply hB.1
    refine ⟨xs j, ?_⟩
    intro i hi
    rw [← hj i hi]
    exact hx i (hBD hi)
  · intro hc
    have hgood (j : Fin k) : Good P (↑(D.filter (fun i => s i = j)) : Set I) := by
      by_contra hn
      obtain ⟨B, hBE, hB⟩ :=
        (finite_obstruction_iff P (D.filter (fun i => s i = j))).mp hn
      have hb (i : I) (hi : i ∈ B) : i ∈ D ∧ s i = j :=
        Finset.mem_filter.mp (hBE hi)
      exact hc B (fun i hi => (hb i hi).1) hB ⟨j, fun i hi => (hb i hi).2⟩
    choose xs hx using hgood
    refine ⟨xs, ?_⟩
    intro i hi
    exact hx (s i) i (Finset.mem_filter.mpr ⟨hi, rfl⟩)

theorem licensed_coloring_finset_iff {I W : Type*}
    (P : Problem I W) (menu : RepairMenu I W P) (D : Finset I) (k : ℕ) :
    RepairFeasible P menu (D : Set I) k ↔
      ∃ s ∈ menu.allowed k, menu.combines (D : Set I) k s ∧
        ColorsOn P (D : Set I) k s := by
  constructor
  · rintro ⟨s, ha, hc, hs⟩
    exact ⟨s, ha, hc, (selectedOn_finset_iff_colorsOn P D k s).mp hs⟩
  · rintro ⟨s, ha, hc, hs⟩
    exact ⟨s, ha, hc, (selectedOn_finset_iff_colorsOn P D k s).mpr hs⟩

def FiniteLicensedColoringGoal : Prop :=
  ∀ (I W : Type) (P : Problem I W) (menu : RepairMenu I W P)
    (D : Finset I) (k : ℕ),
    RepairFeasible P menu (D : Set I) k ↔
      ∃ s ∈ menu.allowed k, menu.combines (D : Set I) k s ∧
        ColorsOn P (D : Set I) k s

theorem finiteLicensedColoringGoal : FiniteLicensedColoringGoal := by
  intro I W P menu D k
  exact licensed_coloring_finset_iff P menu D k

end UniversalObservation.Demand

namespace UniversalObservation.Completion.Operational


open Demand Transport

/-- The completion Goal retains the same native class and the same source evaluation. -/
def SourceNativeCompletionGoal (C : SourceContract) (native : Set C.Process) : Prop :=
  ∀ [TopologicalSpace C.Output] [DiscreteTopology C.Output],
    IsClosed (C.evaluate '' native) →
    (∀ D : Finset C.Input, ∃ k, Nonempty (SourcePlan C (D : Set C.Input) k)) →
    ∃ p ∈ native, ∀ i, C.evaluate p i = C.evaluate C.source i

theorem sourceNativeCompletionGoal (C : SourceContract) (native : Set C.Process)
    (hc : SourceAssemblyClosed C native) (he : SourceAssemblySelects C) :
    SourceNativeCompletionGoal C native := by
  intro _ _ hclosed hlocal
  have ht : C.evaluate C.source ∈ C.evaluate '' native := by
    apply (closed_readouts_iff (C.evaluate '' native)).mp hclosed (C.evaluate C.source)
    intro D
    obtain ⟨k, ⟨r⟩⟩ := hlocal D
    have hr := sourceNativeAssemblyGoal C native hc he (D : Set C.Input) k r
    refine ⟨C.evaluate (planProcess C r), ⟨planProcess C r, hr.1, rfl⟩, ?_⟩
    intro i hi
    exact hr.2 i hi
  obtain ⟨p, hp, hpEval⟩ := ht
  exact ⟨p, hp, fun i => congrFun hpEval i⟩

/-- The structural clauses retain one source and its actual admitted plan assemblies. -/
def SourceStructuralGoal (C : SourceContract) (native : Set C.Process) : Prop :=
  CoreGoal C ∧
  C.combinerLaw ∧
  SourceNativeAssemblyGoal C native ∧
  (∀ (B : SourceContract) (e : SourceTransport C B), SourcePlanTransportGoal C B e) ∧
  (∀ (D : Finset C.Input) (k : ℕ),
    (RepairFeasible C.problem C.menu (D : Set C.Input) k ↔
      ∃ s ∈ C.allowed k, C.combines (D : Set C.Input) k s ∧
        ColorsOn C.problem (D : Set C.Input) k s) ∧
    (Nonempty (SourcePlan C (D : Set C.Input) k) ↔
      RepairFeasible C.problem C.menu (D : Set C.Input) k)) ∧
  (∀ (E : Finset C.Input) (K : Set (Set {i : C.Input // i ∈ E})),
    Downward K → (∅ : Set {i : C.Input // i ∈ E}) ∈ K →
    ∃ F : Set ({i : C.Input // i ∈ E} → Bool), F.Nonempty ∧
      ∀ D : Set {i : C.Input // i ∈ E},
        Good (readoutProblem id (fun _ => false) F) D ↔ D ∈ K) ∧
  SourceNativeCompletionGoal C native

theorem sourceStructuralGoal (C : SourceContract) (native : Set C.Process)
    (hc : SourceAssemblyClosed C native) (he : SourceAssemblySelects C) :
    SourceStructuralGoal C native := by
  refine ⟨source_observation_repair_core C, sourceAssemblyCombinerLaw C he,
    sourceNativeAssemblyGoal C native hc he,
    fun B e => sourcePlanTransportGoal C B e, ?_, ?_,
    sourceNativeCompletionGoal C native hc he⟩
  · intro D k
    exact ⟨licensed_coloring_finset_iff C.problem C.menu D k,
      licensedPlan_nonempty_iff C.problem C.menu (D : Set C.Input) k⟩
  · intro E K hK h0
    exact boolean_downset_realization K hK h0


namespace NativeAssembly

open Demand

def thresholdReadout (n i : ℕ) : Bool := decide (i ≤ n)

@[reducible]
noncomputable def thresholdNativeContract : SourceContract :=
  anchoredContract ℕ ℕ Bool thresholdReadout (fun _ => true) 0 1

/-- The plan retains the finite demand maximum as its single native threshold. -/
noncomputable def thresholdNativePlan (D : Finset ℕ) :
    SourcePlan thresholdNativeContract (D : Set ℕ) 1 := by
  refine ⟨((fun _ => 0), fun _ => D.sup id), Set.mem_univ _, fun _ _ => rfl, ?_⟩
  intro i hi
  change decide (i ≤ D.sup id) = true
  exact (Bool.decide_iff (i ≤ D.sup id)).mpr (Finset.le_sup (f := id) hi)

theorem thresholdNative_closed :
    SourceAssemblyClosed thresholdNativeContract AnchoredNative :=
  anchored_closed ℕ ℕ Bool thresholdReadout (fun _ => true) 0 1

theorem thresholdNative_selects : SourceAssemblySelects thresholdNativeContract :=
  anchored_selects ℕ ℕ Bool thresholdReadout (fun _ => true) 0 1

/-- Every finite demand has an admitted process correct for its source with two primitive calls. -/
theorem thresholdNative_finite_operational (D : Finset ℕ) :
    ∃ r : SourcePlan thresholdNativeContract (D : Set ℕ) 1,
      AnchoredNative (planProcess thresholdNativeContract r) ∧
      (∀ i ∈ D, thresholdNativeContract.evaluate (planProcess thresholdNativeContract r) i =
        thresholdNativeContract.evaluate thresholdNativeContract.source i) ∧
      planCost thresholdNativeContract r 0 = 2 := by
  let r := thresholdNativePlan D
  have hr := sourceNativeAssemblyGoal thresholdNativeContract AnchoredNative
    thresholdNative_closed thresholdNative_selects (D : Set ℕ) 1 r
  exact ⟨r, hr.1, hr.2, rfl⟩

/-- Every native process misses the input immediately above its own threshold. -/
theorem thresholdNative_misses (p : thresholdNativeContract.Process) (hp : AnchoredNative p) :
    ∃ n : ℕ, (∀ i, thresholdNativeContract.evaluate p i = thresholdReadout n i) ∧
      thresholdNativeContract.evaluate p (n + 1) ≠
        thresholdNativeContract.evaluate thresholdNativeContract.source (n + 1) := by
  obtain ⟨n, hn⟩ := anchored_denotes thresholdReadout (fun _ => true) 0 p hp
  refine ⟨n, hn, ?_⟩
  intro h
  have hb : decide (n + 1 ≤ n) = true := (hn (n + 1)).symm.trans h
  have hle := (Bool.decide_iff (n + 1 ≤ n)).mp hb
  omega

theorem thresholdNative_no_global :
    ¬ ∃ p : thresholdNativeContract.Process, AnchoredNative p ∧
      ∀ i, thresholdNativeContract.evaluate p i =
        thresholdNativeContract.evaluate thresholdNativeContract.source i := by
  rintro ⟨p, hp, hcorrect⟩
  obtain ⟨n, _, hn⟩ := thresholdNative_misses p hp
  exact hn (hcorrect (n + 1))

/-- Closedness would place the missing source readout in the native evaluated image. -/
theorem thresholdNative_not_closed [TopologicalSpace Bool] [DiscreteTopology Bool] :
    ¬ IsClosed (thresholdNativeContract.evaluate '' AnchoredNative) := by
  intro hclosed
  have ht : thresholdNativeContract.evaluate thresholdNativeContract.source ∈
      thresholdNativeContract.evaluate '' AnchoredNative := by
    apply (closed_readouts_iff (thresholdNativeContract.evaluate '' AnchoredNative)).mp
      hclosed (thresholdNativeContract.evaluate thresholdNativeContract.source)
    intro D
    obtain ⟨r, hr, hcorrect, _⟩ := thresholdNative_finite_operational D
    exact ⟨thresholdNativeContract.evaluate (planProcess thresholdNativeContract r),
      ⟨planProcess thresholdNativeContract r, hr, rfl⟩, hcorrect⟩
  obtain ⟨p, hp, hpEval⟩ := ht
  exact thresholdNative_no_global ⟨p, hp, fun i => congrFun hpEval i⟩

theorem thresholdNative_omitted_closedness :
    ¬ ((∀ D : Finset ℕ,
      ∃ k, Nonempty (SourcePlan thresholdNativeContract (D : Set ℕ) k)) →
      ∃ p : thresholdNativeContract.Process, AnchoredNative p ∧
        ∀ i, thresholdNativeContract.evaluate p i =
          thresholdNativeContract.evaluate thresholdNativeContract.source i) := by
  intro h
  exact thresholdNative_no_global (h (fun D => ⟨1, ⟨thresholdNativePlan D⟩⟩))

def SourceNativeClosednessControlGoal : Prop :=
  CoreGoal thresholdNativeContract ∧
  SourceAssemblyClosed thresholdNativeContract AnchoredNative ∧
  SourceAssemblySelects thresholdNativeContract ∧
  (∃ p : thresholdNativeContract.Process, AnchoredNative p) ∧
  (∀ D : Finset ℕ, ∃ r : SourcePlan thresholdNativeContract (D : Set ℕ) 1,
    AnchoredNative (planProcess thresholdNativeContract r) ∧
    (∀ i ∈ D, thresholdNativeContract.evaluate (planProcess thresholdNativeContract r) i =
      thresholdNativeContract.evaluate thresholdNativeContract.source i) ∧
    planCost thresholdNativeContract r 0 = 2) ∧
  (∀ p : thresholdNativeContract.Process, AnchoredNative p →
    ∃ n : ℕ, (∀ i, thresholdNativeContract.evaluate p i = thresholdReadout n i) ∧
      thresholdNativeContract.evaluate p (n + 1) ≠
        thresholdNativeContract.evaluate thresholdNativeContract.source (n + 1)) ∧
  (¬ ∃ p : thresholdNativeContract.Process, AnchoredNative p ∧
    ∀ i, thresholdNativeContract.evaluate p i =
      thresholdNativeContract.evaluate thresholdNativeContract.source i) ∧
  (∀ [TopologicalSpace Bool] [DiscreteTopology Bool],
    ¬ IsClosed (thresholdNativeContract.evaluate '' AnchoredNative))

theorem sourceNativeClosednessControlGoal : SourceNativeClosednessControlGoal := by
  refine ⟨source_observation_repair_core thresholdNativeContract,
    thresholdNative_closed, thresholdNative_selects, ⟨.direct 0, .direct 0⟩,
    thresholdNative_finite_operational, thresholdNative_misses,
    thresholdNative_no_global, ?_⟩
  intro _ _
  exact thresholdNative_not_closed

end NativeAssembly


/-- The retained data contain exactly the transport laws before assembly and resources. -/
structure SourceTransportData (C B : SourceContract) where
  processes : C.Process ≃ B.Process
  inputs : C.Input ≃ B.Input
  outputs : C.Output ≃ B.Output
  witnesses : C.Witness ≃ B.Witness
  source_eq : processes C.source = B.source
  evaluation : ∀ p i, B.evaluate (processes p) (inputs i) = outputs (C.evaluate p i)
  interpretation : ∀ w, B.interpret (witnesses w) = processes (C.interpret w)
  allowed : ∀ k s, (fun i => s (inputs.symm i)) ∈ B.allowed k ↔ s ∈ C.allowed k
  combines : ∀ D k s,
    B.combines (inputs '' D) k (fun i => s (inputs.symm i)) ↔ C.combines D k s

namespace SourceTransportData

variable {C B : SourceContract}

def assemblyLaw (e : SourceTransportData C B) : Prop :=
  ∀ D k s ws, s ∈ C.allowed k → C.combines D k s →
    B.assemble k (fun i => s (e.inputs.symm i)) (fun j => e.witnesses (ws j)) =
      e.processes (C.assemble k s ws)

def resourceLaw (e : SourceTransportData C B) : Prop :=
  ∀ p j, B.cost (e.processes p) j = C.cost p j

def complete (e : SourceTransportData C B) (ha : e.assemblyLaw) (hr : e.resourceLaw) :
    SourceTransport C B where
  processes := e.processes
  inputs := e.inputs
  outputs := e.outputs
  witnesses := e.witnesses
  source_eq := e.source_eq
  evaluation := e.evaluation
  interpretation := e.interpretation
  allowed := e.allowed
  combines := e.combines
  assembly := ha
  resource := hr

def demandIso (e : SourceTransportData C B) : DemandIso C.problem B.problem where
  demands := e.inputs
  witnesses := e.witnesses
  satisfaction w i := by
    change B.evaluate (B.interpret (e.witnesses w)) (e.inputs i) =
      B.evaluate B.source (e.inputs i) ↔
        C.evaluate (C.interpret w) i = C.evaluate C.source i
    rw [e.interpretation, ← e.source_eq, e.evaluation, e.evaluation]
    constructor
    · intro h
      exact e.outputs.injective h
    · exact congrArg e.outputs

def planEquiv (e : SourceTransportData C B) (D : Set C.Input) (k : ℕ) :
    SourcePlan C D k ≃ SourcePlan B (e.inputs '' D) k :=
  e.demandIso.licensedPlanEquiv C.menu B.menu
    { allowed := e.allowed, combines := e.combines } D k

theorem plan_process (e : SourceTransportData C B) (ha : e.assemblyLaw)
    (D : Set C.Input) (k : ℕ) (r : SourcePlan C D k) :
    planProcess B (e.planEquiv D k r) = e.processes (planProcess C r) :=
  ha D k r.val.1 r.val.2 r.property.1 r.property.2.1

theorem plan_cost (e : SourceTransportData C B) (ha : e.assemblyLaw) (hr : e.resourceLaw)
    (D : Set C.Input) (k : ℕ) (r : SourcePlan C D k) (j : ℕ) :
    planCost B (e.planEquiv D k r) j = planCost C r j := by
  change B.cost (planProcess B (e.planEquiv D k r)) j = C.cost (planProcess C r) j
  rw [e.plan_process ha D k r]
  exact hr (planProcess C r) j

end SourceTransportData

namespace NativeAssembly

open OperatorKO7 (Trace)

/-- The price fixture changes one resource coordinate while retaining every process. -/
@[reducible]
noncomputable def repricedCounted : SourceContract :=
  { countedContract with
    cost := fun p j => if j = 0 then ((primitiveCalls 1 p + 1 : ℕ) : ℝ) else 0 }

def repricedData : SourceTransportData countedContract repricedCounted where
  processes := Equiv.refl _
  inputs := Equiv.refl _
  outputs := Equiv.refl _
  witnesses := Equiv.refl _
  source_eq := rfl
  evaluation _ _ := rfl
  interpretation _ := rfl
  allowed _ _ := Iff.rfl
  combines _ _ _ := Iff.rfl

def SourceResourceControlGoal : Prop :=
  repricedData.assemblyLaw ∧ ¬ repricedData.resourceLaw ∧
  SourceNativeAssemblyGoal repricedCounted CountedNative ∧
  ∃ r : SourcePlan countedContract {(Trace.void, 0)} 1,
    let r' := repricedData.planEquiv {(Trace.void, 0)} 1 r
    planProcess repricedCounted r' = repricedData.processes (planProcess countedContract r) ∧
    CountedNative (planProcess repricedCounted r') ∧
    (∀ i ∈ repricedData.inputs '' {(Trace.void, 0)},
      repricedCounted.evaluate (planProcess repricedCounted r') i =
        repricedCounted.evaluate repricedCounted.source i) ∧
    planCost countedContract r 0 = 2 ∧ planCost repricedCounted r' 0 = 3

theorem sourceResourceControlGoal : SourceResourceControlGoal := by
  obtain ⟨r⟩ := counted_singleton_plan (Trace.void, 0)
  have ha : repricedData.assemblyLaw := by
    intro D k s ws _ _
    rfl
  have hg : SourceNativeAssemblyGoal repricedCounted CountedNative := counted_goal
  refine ⟨ha, ?_, hg, r, repricedData.plan_process ha _ _ r,
    (hg _ _ (repricedData.planEquiv _ _ r)).1,
    (hg _ _ (repricedData.planEquiv _ _ r)).2, rfl, rfl⟩
  intro hr
  have h := repricedData.plan_cost ha hr {(Trace.void, 0)} 1 r 0
  change (3 : ℝ) = 2 at h
  norm_num at h

end NativeAssembly


/-- Both independent transport laws preserve the actual assembly and every resource coordinate. -/
def SourceTransportDataPlanGoal (C B : SourceContract) (e : SourceTransportData C B) : Prop :=
  e.assemblyLaw → e.resourceLaw →
  ∀ (D : Set C.Input) (k : ℕ) (r : SourcePlan C D k),
    planProcess B (e.planEquiv D k r) = e.processes (planProcess C r) ∧
    ∀ j, planCost B (e.planEquiv D k r) j = planCost C r j

theorem sourceTransportDataPlanGoal (C B : SourceContract) (e : SourceTransportData C B) :
    SourceTransportDataPlanGoal C B e := by
  intro ha hr D k r
  exact ⟨e.plan_process ha D k r, e.plan_cost ha hr D k r⟩

namespace NativeAssembly

open OperatorKO7 (Trace)

/-- The assembler selects one original witness at the retained concrete input. -/
@[reducible]
noncomputable def directCounted : SourceContract :=
  { countedContract with assemble := fun _ s ws => .direct (ws (s (Trace.void, 0))) }

def directData : SourceTransportData countedContract directCounted where
  processes := Equiv.refl _
  inputs := Equiv.refl _
  outputs := Equiv.refl _
  witnesses := Equiv.refl _
  source_eq := rfl
  evaluation _ _ := rfl
  interpretation _ := rfl
  allowed _ _ := Iff.rfl
  combines _ _ _ := Iff.rfl

def SourceAssemblyTransportControlGoal : Prop :=
  directCounted.cost = countedContract.cost ∧
  directData.resourceLaw ∧ ¬ directData.assemblyLaw ∧
  SourceAssemblyClosed directCounted CountedNative ∧
  ∃ r : SourcePlan countedContract {(Trace.void, 0)} 1,
    let r' := directData.planEquiv {(Trace.void, 0)} 1 r
    planProcess directCounted r' ≠ directData.processes (planProcess countedContract r) ∧
    CountedNative (planProcess directCounted r') ∧
    (∀ i ∈ directData.inputs '' {(Trace.void, 0)},
      directCounted.evaluate (planProcess directCounted r') i =
        directCounted.evaluate directCounted.source i) ∧
    planCost countedContract r 0 = 2 ∧ planCost directCounted r' 0 = 1

theorem sourceAssemblyTransportControlGoal : SourceAssemblyTransportControlGoal := by
  obtain ⟨r⟩ := counted_singleton_plan (Trace.void, 0)
  let r' := directData.planEquiv {(Trace.void, 0)} 1 r
  have hr : directData.resourceLaw := by
    intro p j
    rfl
  have hp : planProcess directCounted r' ≠
      directData.processes (planProcess countedContract r) := by
    intro h
    change SelectionProcess.direct (r.val.2 (r.val.1 (Trace.void, 0))) =
      SelectionProcess.selected 1 r.val.1 r.val.2 at h
    cases h
  have hc : ∀ i ∈ directData.inputs '' {(Trace.void, 0)},
      directCounted.evaluate (planProcess directCounted r') i =
        directCounted.evaluate directCounted.source i := by
    rintro i ⟨x, hx, rfl⟩
    change x = (Trace.void, 0) at hx
    subst x
    exact r.property.2.2 (Trace.void, 0) rfl
  refine ⟨rfl, hr, ?_, ?_, r, hp, ?_, hc, rfl, ?_⟩
  · intro ha
    exact hp (directData.plan_process ha {(Trace.void, 0)} 1 r)
  · intro D k s ws _ _
    exact .direct (ws (s (Trace.void, 0)))
  · exact .direct (r.val.2 (r.val.1 (Trace.void, 0)))
  · change ((1 : ℕ) : ℝ) = 1
    norm_num

end NativeAssembly


namespace AffineNative

open Demand Transport NativeAssembly
open OperatorKO7.Meta.BoundaryObserver.AffineSelfObservation
  (Bit affineRows affineRhs copy_kernel_vector)

section General

variable {K V I : Type} [Field K] [AddCommGroup V] [Module K V]

/-- The row batch evaluates every listed original coefficient row once. -/
def rowRun (rows : I → V →ₗ[K] K) (x : V) : List I → List K × ℕ
  | [] => ([], 0)
  | i :: is =>
      let rest := rowRun rows x is
      (rows i x :: rest.1, rest.2 + 1)

theorem rowRun_values (rows : I → V →ₗ[K] K) (x : V) (is : List I) :
    (rowRun rows x is).1 = is.map (fun i => rows i x) := by
  induction is with
  | nil => rfl
  | cons i is ih =>
      change rows i x :: (rowRun rows x is).1 =
        rows i x :: is.map (fun j => rows j x)
      rw [ih]

theorem rowRun_calls (rows : I → V →ₗ[K] K) (x : V) (is : List I) :
    (rowRun rows x is).2 = is.length := by
  induction is with
  | nil => rfl
  | cons i is ih =>
      change (rowRun rows x is).2 + 1 = is.length + 1
      rw [ih]

/-- The decoder reconstructs reports from stored row results. -/
noncomputable def decodeRows : List I → List K → I → K
  | i :: is, v :: vs, j => by
      classical
      exact if j = i then v else decodeRows is vs j
  | _, _, _ => 0

theorem decodeRows_map (is : List I) (f : I → K) :
    ∀ j ∈ is, decodeRows is (is.map f) j = f j := by
  induction is with
  | nil =>
      intro j hj
      cases hj
  | cons i is ih =>
      intro j hj
      classical
      change (if j = i then f i else decodeRows is (is.map f) j) = f j
      by_cases h : j = i
      · rw [if_pos h, h]
      · rw [if_neg h]
        cases hj with
        | head => exact False.elim (h rfl)
        | tail _ hj => exact ih j hj

variable (rows : I → V →ₗ[K] K) (b : I → K) (anchor : I)

/-- The selected program obtains one native vector from its anchor selector. -/
def processRun (p : SelectionProcess I V) (is : List I) :
    List K × (ℕ × ℕ) :=
  match p with
  | .target => (is.map b, (0, 0))
  | .direct x =>
      let run := rowRun rows x is
      (run.1, (run.2, 0))
  | .selected _ s ws =>
      let run := rowRun rows (ws (s anchor)) is
      (run.1, (run.2, 1))

theorem processRun_values (p : SelectionProcess I V) (is : List I) :
    (processRun rows b anchor p is).1 =
      is.map (anchoredEvaluate (fun x i => rows i x) b anchor p) := by
  cases p with
  | target => rfl
  | direct x => exact rowRun_values rows x is
  | selected k s ws => exact rowRun_values rows (ws (s anchor)) is

variable [Fintype I]

/-- The original program charges its complete original row batch and anchor selection. -/
noncomputable def cost (p : SelectionProcess I V) : ℕ → ℝ
  | 0 =>
      (processRun rows b anchor p (Finset.univ : Finset I).toList).2.1
  | 1 =>
      (processRun rows b anchor p (Finset.univ : Finset I).toList).2.2
  | _ => 0

noncomputable def contract : SourceContract :=
  { anchoredContract I V K (fun x i => rows i x) b anchor 1 with
    cost := cost rows b anchor }

theorem native_problem :
    (contract rows b anchor).problem = affineEquationProblem rows b := rfl

theorem combinerLaw :
    (contract rows b anchor).combinerLaw :=
  sourceAssemblyCombinerLaw _
    (anchored_selects I V K (fun x i => rows i x) b anchor 1)

theorem native_assembly :
    SourceNativeAssemblyGoal (contract rows b anchor) AnchoredNative :=
  anchored_goal I V K (fun x i => rows i x) b anchor 1

theorem native_denotes (p : (contract rows b anchor).Process)
    (hp : AnchoredNative p) :
    ∃ x : V, ∀ i, (contract rows b anchor).evaluate p i = rows i x :=
  anchored_denotes (fun x i => rows i x) b anchor p hp

theorem assembled_vector (D : Set I) (k : ℕ)
    (r : SourcePlan (contract rows b anchor) D k) (i : I) :
    (contract rows b anchor).evaluate
        (planProcess (contract rows b anchor) r) i =
      rows i (r.val.2 (r.val.1 anchor)) := rfl

theorem assembled_cost (D : Set I) (k : ℕ)
    (r : SourcePlan (contract rows b anchor) D k) :
    planCost (contract rows b anchor) r 0 = (Fintype.card I : ℝ) ∧
      planCost (contract rows b anchor) r 1 = 1 := by
  constructor
  · change
      ((rowRun rows (r.val.2 (r.val.1 anchor))
        (Finset.univ : Finset I).toList).2 : ℝ) =
        (Fintype.card I : ℝ)
    rw [rowRun_calls, Finset.length_toList, Finset.card_univ]
  · change ((1 : ℕ) : ℝ) = 1
    exact Nat.cast_one

theorem assembled_cost_positive (D : Set I) (k : ℕ)
    (r : SourcePlan (contract rows b anchor) D k) :
    0 < planCost (contract rows b anchor) r 0 := by
  rw [(assembled_cost rows b anchor D k r).1]
  exact Nat.cast_pos'.mpr (Fintype.card_pos_iff.mpr ⟨anchor⟩)

/-- The execution stores its actual output and primitive invocation counters. -/
structure Execution (J W : Type) where
  report : J → W
  rowCalls : ℕ
  selectorCalls : ℕ
  mixingCalls : ℕ

/-- The resource coordinates count row, selector and full report map invocations. -/
noncomputable def Execution.cost {J W : Type} (run : Execution J W) : ℕ → ℝ
  | 0 => run.rowCalls
  | 1 => run.selectorCalls
  | 2 => run.mixingCalls
  | _ => 0

/-- The complete report is reconstructed from the charged original row results. -/
noncomputable def execute (p : SelectionProcess I V) : Execution I K :=
  let indices := (Finset.univ : Finset I).toList
  let run := processRun rows b anchor p indices
  { report := decodeRows indices run.1
    rowCalls := run.2.1
    selectorCalls := run.2.2
    mixingCalls := 0 }

theorem execute_report (p : SelectionProcess I V) :
    (execute rows b anchor p).report = (contract rows b anchor).evaluate p := by
  funext i
  change
    decodeRows (Finset.univ : Finset I).toList
        (processRun rows b anchor p (Finset.univ : Finset I).toList).1 i =
      anchoredEvaluate (fun x j => rows j x) b anchor p i
  rw [processRun_values]
  exact decodeRows_map (Finset.univ : Finset I).toList
    (anchoredEvaluate (fun x j => rows j x) b anchor p) i
    (Finset.mem_toList.mpr (Finset.mem_univ i))

theorem execute_cost (p : SelectionProcess I V) (j : ℕ) :
    (execute rows b anchor p).cost j = (contract rows b anchor).cost p j := by
  cases j with
  | zero => rfl
  | succ j =>
      cases j with
      | zero => rfl
      | succ j =>
          cases j with
          | zero => exact Nat.cast_zero
          | succ j => rfl

variable {J : Type}

/-- The transformed rows are linear compositions of the complete original report map. -/
def mixedRows (R : (I → K) ≃ₗ[K] (J → K)) : J → V →ₗ[K] K :=
  fun j =>
    (LinearMap.proj j : (J → K) →ₗ[K] K).comp
      (R.toLinearMap.comp (LinearMap.pi rows))

theorem full_mixing_candidates (R : (I → K) ≃ₗ[K] (J → K)) :
    Witnesses (affineEquationProblem (mixedRows rows R) (R b)) Set.univ =
      Witnesses (contract rows b anchor).problem Set.univ :=
  affine_invertible_rows_keep_solutions (LinearMap.pi rows) R b

/-- The full certificate retains the original selector and every native component. -/
def FullMixedPlan (R : (I → K) ≃ₗ[K] (J → K)) (k : ℕ) :=
  {r : (I → Fin k) × (Fin k → V) //
    r.1 ∈ (contract rows b anchor).allowed k ∧
      (contract rows b anchor).combines Set.univ k r.1 ∧
      R (fun i => rows i (r.2 (r.1 anchor))) = R b}

def fullMixPlanEquiv (R : (I → K) ≃ₗ[K] (J → K)) (k : ℕ) :
    SourcePlan (contract rows b anchor) Set.univ k ≃
      FullMixedPlan rows b anchor R k where
  toFun r := by
    refine ⟨r.val, r.property.1, r.property.2.1, ?_⟩
    apply congrArg R
    funext i
    have hi := r.property.2.2 i (Set.mem_univ i)
    change rows i (r.val.2 (r.val.1 i)) = b i at hi
    have hc : r.val.1 i = r.val.1 anchor :=
      r.property.2.1 i (Set.mem_univ i)
    rw [hc] at hi
    exact hi
  invFun r := by
    refine ⟨r.val, r.property.1, r.property.2.1, ?_⟩
    intro i _
    have hi := congrFun (R.injective r.property.2.2) i
    change rows i (r.val.2 (r.val.1 i)) = b i
    have hc : r.val.1 i = r.val.1 anchor :=
      r.property.2.1 i (Set.mem_univ i)
    rw [hc]
    exact hi
  left_inv r := rfl
  right_inv r := rfl

/-- The transported certificate retains the original full-row program. -/
def certificatePlanProcess (R : (I → K) ≃ₗ[K] (J → K)) (k : ℕ)
    (r : FullMixedPlan rows b anchor R k) :
    (contract rows b anchor).Process :=
  SelectionProcess.selected k r.val.1 r.val.2

theorem fullMixPlan_data (R : (I → K) ≃ₗ[K] (J → K)) (k : ℕ)
    (r : SourcePlan (contract rows b anchor) Set.univ k) :
    (fullMixPlanEquiv rows b anchor R k r).val = r.val := rfl

theorem fullMixPlan_process (R : (I → K) ≃ₗ[K] (J → K)) (k : ℕ)
    (r : SourcePlan (contract rows b anchor) Set.univ k) :
    certificatePlanProcess rows b anchor R k
        (fullMixPlanEquiv rows b anchor R k r) =
      planProcess (contract rows b anchor) r := rfl

theorem fullMixPlan_execution (R : (I → K) ≃ₗ[K] (J → K)) (k : ℕ)
    (r : SourcePlan (contract rows b anchor) Set.univ k) :
    execute rows b anchor
        (certificatePlanProcess rows b anchor R k
          (fullMixPlanEquiv rows b anchor R k r)) =
      execute rows b anchor (planProcess (contract rows b anchor) r) := rfl

/-- The unchanged charges belong to the retained original-row implementation. -/
theorem fullMixPlan_cost (R : (I → K) ≃ₗ[K] (J → K)) (k : ℕ)
    (r : SourcePlan (contract rows b anchor) Set.univ k) (j : ℕ) :
    (contract rows b anchor).cost
        (certificatePlanProcess rows b anchor R k
          (fullMixPlanEquiv rows b anchor R k r)) j =
      planCost (contract rows b anchor) r j := rfl

theorem fullMixPlan_report (R : (I → K) ≃ₗ[K] (J → K)) (k : ℕ)
    (r : SourcePlan (contract rows b anchor) Set.univ k) :
    (fun j => mixedRows rows R j (r.val.2 (r.val.1 anchor))) =
      R ((contract rows b anchor).evaluate
        (planProcess (contract rows b anchor) r)) := rfl

theorem fullMixBudget_iff (R : (I → K) ≃ₗ[K] (J → K))
    (k : ℕ) (budget : ℕ → ℝ) :
    LicensedBudget (contract rows b anchor).problem
        (contract rows b anchor).menu Set.univ k
        (planCost (contract rows b anchor)) budget ↔
      ∃ r : FullMixedPlan rows b anchor R k,
        ∀ j, (contract rows b anchor).cost
          (certificatePlanProcess rows b anchor R k r) j ≤ budget j := by
  constructor
  · rintro ⟨r, hr⟩
    exact ⟨fullMixPlanEquiv rows b anchor R k r, hr⟩
  · rintro ⟨r, hr⟩
    exact ⟨(fullMixPlanEquiv rows b anchor R k).symm r, hr⟩

/-- The added operation applies the complete report map once to the actual original report. -/
noncomputable def executeMixed (R : (I → K) ≃ₗ[K] (J → K))
    (p : SelectionProcess I V) : Execution J K :=
  let run := execute rows b anchor p
  { report := R run.report
    rowCalls := run.rowCalls
    selectorCalls := run.selectorCalls
    mixingCalls := run.mixingCalls + 1 }

theorem executeMixed_report (R : (I → K) ≃ₗ[K] (J → K))
    (p : SelectionProcess I V) :
    (executeMixed rows b anchor R p).report =
      R ((contract rows b anchor).evaluate p) := by
  change R ((execute rows b anchor p).report) =
    R ((contract rows b anchor).evaluate p)
  exact congrArg R (execute_report rows b anchor p)

theorem executeMixed_charge (R : (I → K) ≃ₗ[K] (J → K))
    (p : SelectionProcess I V) :
    (executeMixed rows b anchor R p).cost 2 = 1 :=
  Nat.cast_one

theorem executeMixed_cost (R : (I → K) ≃ₗ[K] (J → K))
    (p : SelectionProcess I V) (j : ℕ) :
    (executeMixed rows b anchor R p).cost j =
      if j = 2 then (contract rows b anchor).cost p j + 1
      else (contract rows b anchor).cost p j := by
  cases j with
  | zero => rfl
  | succ j =>
      cases j with
      | zero => rfl
      | succ j =>
          cases j with
          | zero =>
              change ((1 : ℕ) : ℝ) = (0 : ℝ) + 1
              exact Nat.cast_one.trans (zero_add (1 : ℝ)).symm
          | succ j => rfl

theorem executeMixed_plan_vector (R : (I → K) ≃ₗ[K] (J → K)) (k : ℕ)
    (r : SourcePlan (contract rows b anchor) Set.univ k) :
    (executeMixed rows b anchor R
        (planProcess (contract rows b anchor) r)).report =
      fun j => mixedRows rows R j (r.val.2 (r.val.1 anchor)) :=
  (executeMixed_report rows b anchor R
    (planProcess (contract rows b anchor) r)).trans
      (fullMixPlan_report rows b anchor R k r).symm

theorem executeMixed_plan_correct (R : (I → K) ≃ₗ[K] (J → K)) (k : ℕ)
    (r : SourcePlan (contract rows b anchor) Set.univ k) :
    (executeMixed rows b anchor R
        (planProcess (contract rows b anchor) r)).report = R b := by
  rw [executeMixed_report]
  apply congrArg R
  funext i
  exact (native_assembly rows b anchor Set.univ k r).2 i (Set.mem_univ i)

/-- The unchanged total charge is the rejected execution-cost strengthening. -/
def UnchangedMixedExecutionCostGoal (R : (I → K) ≃ₗ[K] (J → K)) : Prop :=
  ∀ (p : SelectionProcess I V) (j : ℕ),
    (executeMixed rows b anchor R p).cost j =
      (contract rows b anchor).cost p j

/-- The corrected total charge includes the executed full report map invocation. -/
def MixedExecutionCostGoal (R : (I → K) ≃ₗ[K] (J → K)) : Prop :=
  ∀ (p : SelectionProcess I V) (j : ℕ),
    (executeMixed rows b anchor R p).cost j =
      if j = 2 then (contract rows b anchor).cost p j + 1
      else (contract rows b anchor).cost p j

theorem mixedExecutionCostGoal (R : (I → K) ≃ₗ[K] (J → K)) :
    MixedExecutionCostGoal rows b anchor R :=
  executeMixed_cost rows b anchor R

/-- The certificate Goal preserves native data, the original execution and its full budget set. -/
def AffineFullMixCertificateGoal (R : (I → K) ≃ₗ[K] (J → K)) : Prop :=
  Witnesses (affineEquationProblem (mixedRows rows R) (R b)) Set.univ =
      Witnesses (contract rows b anchor).problem Set.univ ∧
  (∀ k (r : SourcePlan (contract rows b anchor) Set.univ k),
    (fullMixPlanEquiv rows b anchor R k r).val = r.val ∧
    certificatePlanProcess rows b anchor R k
        (fullMixPlanEquiv rows b anchor R k r) =
      planProcess (contract rows b anchor) r ∧
    execute rows b anchor
        (certificatePlanProcess rows b anchor R k
          (fullMixPlanEquiv rows b anchor R k r)) =
      execute rows b anchor (planProcess (contract rows b anchor) r) ∧
    (∀ j, (contract rows b anchor).cost
        (certificatePlanProcess rows b anchor R k
          (fullMixPlanEquiv rows b anchor R k r)) j =
      planCost (contract rows b anchor) r j) ∧
    (fun j => mixedRows rows R j (r.val.2 (r.val.1 anchor))) =
      R ((contract rows b anchor).evaluate
        (planProcess (contract rows b anchor) r))) ∧
  (∀ k budget,
    LicensedBudget (contract rows b anchor).problem
        (contract rows b anchor).menu Set.univ k
        (planCost (contract rows b anchor)) budget ↔
      ∃ r : FullMixedPlan rows b anchor R k,
        ∀ j, (contract rows b anchor).cost
          (certificatePlanProcess rows b anchor R k r) j ≤ budget j)

theorem affineFullMixCertificateGoal (R : (I → K) ≃ₗ[K] (J → K)) :
    AffineFullMixCertificateGoal rows b anchor R := by
  refine ⟨full_mixing_candidates rows b anchor R, ?_,
    fullMixBudget_iff rows b anchor R⟩
  intro k r
  exact ⟨fullMixPlan_data rows b anchor R k r,
    fullMixPlan_process rows b anchor R k r,
    fullMixPlan_execution rows b anchor R k r,
    fullMixPlan_cost rows b anchor R k r,
    fullMixPlan_report rows b anchor R k r⟩

/-- The execution Goal records transformed output, its extra charge and full-source correctness. -/
def AffineFullMixExecutionGoal (R : (I → K) ≃ₗ[K] (J → K)) : Prop :=
  (∀ p : SelectionProcess I V,
    (executeMixed rows b anchor R p).report =
      R ((contract rows b anchor).evaluate p)) ∧
  MixedExecutionCostGoal rows b anchor R ∧
  (∀ k (r : SourcePlan (contract rows b anchor) Set.univ k),
    (executeMixed rows b anchor R
        (planProcess (contract rows b anchor) r)).report =
      (fun j => mixedRows rows R j (r.val.2 (r.val.1 anchor))) ∧
    (executeMixed rows b anchor R
        (planProcess (contract rows b anchor) r)).report = R b)

theorem affineFullMixExecutionGoal (R : (I → K) ≃ₗ[K] (J → K)) :
    AffineFullMixExecutionGoal rows b anchor R :=
  ⟨executeMixed_report rows b anchor R,
    mixedExecutionCostGoal rows b anchor R,
    fun k r =>
      ⟨executeMixed_plan_vector rows b anchor R k r,
        executeMixed_plan_correct rows b anchor R k r⟩⟩

/-- The full mixing Goal distinguishes certificate preservation from executed transformation. -/
def AffineFullMixGoal (R : (I → K) ≃ₗ[K] (J → K)) : Prop :=
  AffineFullMixCertificateGoal rows b anchor R ∧
    AffineFullMixExecutionGoal rows b anchor R

theorem affineFullMixGoal (R : (I → K) ≃ₗ[K] (J → K)) :
    AffineFullMixGoal rows b anchor R :=
  ⟨affineFullMixCertificateGoal rows b anchor R,
    affineFullMixExecutionGoal rows b anchor R⟩

/-- The native Goal retains original equations, an actual common vector and justified resources. -/
def AffineNativeGoal : Prop :=
  (contract rows b anchor).problem = affineEquationProblem rows b ∧
  (contract rows b anchor).combinerLaw ∧
  CoreGoal (contract rows b anchor) ∧
  SourceNativeAssemblyGoal (contract rows b anchor) AnchoredNative ∧
  (∀ p : (contract rows b anchor).Process, AnchoredNative p →
    ∃ x : V, ∀ i, (contract rows b anchor).evaluate p i = rows i x) ∧
  (∀ p : SelectionProcess I V,
    (execute rows b anchor p).report = (contract rows b anchor).evaluate p ∧
    ∀ j, (execute rows b anchor p).cost j =
      (contract rows b anchor).cost p j) ∧
  (∀ D k (r : SourcePlan (contract rows b anchor) D k),
    (∀ i, (contract rows b anchor).evaluate
        (planProcess (contract rows b anchor) r) i =
      rows i (r.val.2 (r.val.1 anchor))) ∧
    (planCost (contract rows b anchor) r 0 = (Fintype.card I : ℝ) ∧
      planCost (contract rows b anchor) r 1 = 1) ∧
    0 < planCost (contract rows b anchor) r 0) ∧
  (∀ (J : Type) (R : (I → K) ≃ₗ[K] (J → K)),
    AffineFullMixGoal rows b anchor R)

theorem affineNativeGoal :
    AffineNativeGoal rows b anchor := by
  refine ⟨native_problem rows b anchor, combinerLaw rows b anchor,
    source_observation_repair_core _, native_assembly rows b anchor,
    native_denotes rows b anchor, ?_, ?_, ?_⟩
  · intro p
    exact ⟨execute_report rows b anchor p, execute_cost rows b anchor p⟩
  · intro D k r
    exact ⟨assembled_vector rows b anchor D k r,
      assembled_cost rows b anchor D k r,
      assembled_cost_positive rows b anchor D k r⟩
  · intro J R
    exact affineFullMixGoal rows b anchor R

end General

/-- The original copy-cycle equations supply a concrete licensed native plan. -/
def copyPlan :
    SourcePlan (contract (affineRows 0) (affineRhs 0) (0 : Fin 2))
      Set.univ 1 :=
  ⟨((fun _ => 0), fun _ => ((0, 0) : Bit × Bit)),
    Set.mem_univ _, fun _ _ => rfl,
    fun i _ => copy_kernel_vector.1 i⟩

theorem copyPlan_cost :
    planCost (contract (affineRows 0) (affineRhs 0) (0 : Fin 2))
        copyPlan 0 = ((2 : ℕ) : ℝ) ∧
    planCost (contract (affineRows 0) (affineRhs 0) (0 : Fin 2))
        copyPlan 1 = 1 := by
  simpa only [Fintype.card_fin] using
    assembled_cost (affineRows 0) (affineRhs 0) (0 : Fin 2)
      Set.univ 1 copyPlan

theorem copy_native_goal :
    AffineNativeGoal (affineRows 0) (affineRhs 0) (0 : Fin 2) :=
  affineNativeGoal (affineRows 0) (affineRhs 0) (0 : Fin 2)

namespace MixingCostControl

def rows (_i : Fin 2) : ℝ →ₗ[ℝ] ℝ := LinearMap.id

def rhs (_i : Fin 2) : ℝ := 1

noncomputable def source : SourceContract :=
  contract rows rhs (0 : Fin 2)

def plan : SourcePlan source Set.univ 1 :=
  ⟨((fun _ => 0), fun _ => (1 : ℝ)),
    Set.mem_univ _, fun _ _ => rfl, fun _ _ => rfl⟩

theorem report_changes : rowShear rhs ≠ rhs := by
  intro h
  have h1 := congrFun h (1 : Fin 2)
  change (1 : ℝ) - 1 = 1 at h1
  exact zero_ne_one ((sub_self (1 : ℝ)).symm.trans h1)

/-- The native shear execution disproves unchanged total invocation cost. -/
theorem unchangedMixedExecutionCostGoal_counterexample :
    AnchoredNative (planProcess source plan) ∧
    (planCost source plan 0 = ((2 : ℕ) : ℝ) ∧
      planCost source plan 1 = 1) ∧
    planCost source plan 2 = 0 ∧
    (executeMixed rows rhs (0 : Fin 2) rowShear
        (planProcess source plan)).cost 2 = 1 ∧
    (executeMixed rows rhs (0 : Fin 2) rowShear
        (planProcess source plan)).report = rowShear rhs ∧
    rowShear rhs ≠ rhs ∧
    ¬ UnchangedMixedExecutionCostGoal rows rhs (0 : Fin 2) rowShear := by
  refine ⟨(native_assembly rows rhs (0 : Fin 2) Set.univ 1 plan).1,
    ?_, rfl,
    executeMixed_charge rows rhs (0 : Fin 2) rowShear
      (planProcess source plan),
    executeMixed_plan_correct rows rhs (0 : Fin 2) rowShear 1 plan,
    report_changes, ?_⟩
  · simpa only [Fintype.card_fin] using
      assembled_cost rows rhs (0 : Fin 2) Set.univ 1 plan
  · intro h
    have h2 := h (planProcess source plan) 2
    have he : (1 : ℝ) = 0 :=
      (executeMixed_charge rows rhs (0 : Fin 2) rowShear
        (planProcess source plan)).symm.trans h2
    exact zero_ne_one he.symm

end MixingCostControl

end AffineNative


namespace AffineNative.AnchorConstancyControl

open Demand Transport NativeAssembly

/-- Both original equations evaluate the same native scalar. -/
def rows (_i : Fin 2) : ℝ →ₗ[ℝ] ℝ := LinearMap.id

def components (i : Fin 2) : ℝ :=
  match i.val with
  | 0 => 0
  | _ + 1 => 1

def rhs (i : Fin 2) : ℝ := components i

def selector (i : Fin 2) : Fin 2 := i

noncomputable def licensed : SourceContract :=
  contract rows rhs (0 : Fin 2)

/-- The altered source deletes only the anchor constancy permission. -/
noncomputable def withoutConstancy : SourceContract :=
  { licensed with combines := fun _ _ _ => True }

theorem source_data_preserved :
    withoutConstancy.source = licensed.source ∧
    withoutConstancy.evaluate = licensed.evaluate ∧
    withoutConstancy.interpret = licensed.interpret ∧
    withoutConstancy.problem = licensed.problem ∧
    withoutConstancy.allowed = licensed.allowed ∧
    withoutConstancy.assemble = licensed.assemble ∧
    withoutConstancy.cost = licensed.cost :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem selector_allowed :
    selector ∈ withoutConstancy.allowed 2 :=
  Set.mem_univ _

theorem original_combination_denied :
    ¬ licensed.combines Set.univ 2 selector := by
  intro hc
  have h := hc (1 : Fin 2) (Set.mem_univ (1 : Fin 2))
  change (1 : Fin 2) = 0 at h
  have hn : (1 : Fin 2) ≠ 0 := by decide
  exact hn h

/-- Each selected native scalar separately satisfies its original equation. -/
theorem selected_rows_correct :
    ∀ i : Fin 2,
      withoutConstancy.problem.sat (components (selector i)) i := by
  intro i
  rfl

/-- The original duplicated rows have incompatible right sides. -/
theorem original_global_obstruction :
    ¬ Good licensed.problem Set.univ := by
  rintro ⟨x, hx⟩
  have h0 := hx (0 : Fin 2) (Set.mem_univ (0 : Fin 2))
  have h1 := hx (1 : Fin 2) (Set.mem_univ (1 : Fin 2))
  change x = (0 : ℝ) at h0
  change x = (1 : ℝ) at h1
  exact (zero_ne_one : (0 : ℝ) ≠ 1) (h0.symm.trans h1)

/-- The weakened permission admits the individually correct split selection. -/
def splitPlan : SourcePlan withoutConstancy Set.univ 2 :=
  ⟨(selector, components), Set.mem_univ _, trivial, fun _ _ => rfl⟩

/-- Native structural closure survives the deleted constancy condition. -/
theorem closure_retained :
    SourceAssemblyClosed withoutConstancy AnchoredNative := by
  intro D k s ws _ _
  exact .selected k s ws

theorem actual_process_native :
    AnchoredNative (planProcess withoutConstancy splitPlan) :=
  .selected 2 selector components

/-- The actual anchored assembly retains one native scalar throughout its report. -/
theorem actual_process_vector (i : Fin 2) :
    withoutConstancy.evaluate (planProcess withoutConstancy splitPlan) i =
      rows i (0 : ℝ) := rfl

theorem actual_process_fails :
    withoutConstancy.evaluate
        (planProcess withoutConstancy splitPlan) (1 : Fin 2) ≠
      withoutConstancy.evaluate withoutConstancy.source (1 : Fin 2) := by
  change (0 : ℝ) ≠ 1
  exact zero_ne_one

/-- The failed native assembly still executes both original rows and one selector call. -/
theorem actual_process_cost :
    planCost withoutConstancy splitPlan 0 = ((2 : ℕ) : ℝ) ∧
      planCost withoutConstancy splitPlan 1 = 1 := by
  constructor
  · change
      ((rowRun rows (components (selector (0 : Fin 2)))
        (Finset.univ : Finset (Fin 2)).toList).2 : ℝ) =
        ((2 : ℕ) : ℝ)
    apply congrArg (fun n : ℕ => (n : ℝ))
    exact
      (rowRun_calls rows (components (selector (0 : Fin 2)))
        (Finset.univ : Finset (Fin 2)).toList).trans
        ((Finset.length_toList (Finset.univ : Finset (Fin 2))).trans
          (Fintype.card_fin 2))
  · change ((1 : ℕ) : ℝ) = 1
    exact Nat.cast_one

theorem no_selects :
    ¬ SourceAssemblySelects withoutConstancy := by
  intro hs
  have h := hs Set.univ 2 selector components
    splitPlan.property.1 splitPlan.property.2.1
    (1 : Fin 2) (Set.mem_univ (1 : Fin 2))
  change (0 : ℝ) = 1 at h
  exact zero_ne_one h

theorem no_combinerLaw :
    ¬ withoutConstancy.combinerLaw := by
  intro h
  have he := h Set.univ 2 splitPlan.val.1 splitPlan.val.2
    splitPlan.property.1 splitPlan.property.2.1 splitPlan.property.2.2
    (1 : Fin 2) (Set.mem_univ (1 : Fin 2))
  exact actual_process_fails he

theorem no_nativeGoal :
    ¬ SourceNativeAssemblyGoal withoutConstancy AnchoredNative := by
  intro h
  exact actual_process_fails
    ((h Set.univ 2 splitPlan).2 (1 : Fin 2) (Set.mem_univ (1 : Fin 2)))

/-- The deletion Goal retains the native data and exposes the failed actual assembly. -/
def AnchorConstancyDeletionGoal : Prop :=
  (withoutConstancy.source = licensed.source ∧
    withoutConstancy.evaluate = licensed.evaluate ∧
    withoutConstancy.interpret = licensed.interpret ∧
    withoutConstancy.problem = licensed.problem ∧
    withoutConstancy.allowed = licensed.allowed ∧
    withoutConstancy.assemble = licensed.assemble ∧
    withoutConstancy.cost = licensed.cost) ∧
  selector ∈ withoutConstancy.allowed 2 ∧
  ¬ licensed.combines Set.univ 2 selector ∧
  (∀ i : Fin 2,
    withoutConstancy.problem.sat (components (selector i)) i) ∧
  ¬ Good licensed.problem Set.univ ∧
  SourceAssemblyClosed withoutConstancy AnchoredNative ∧
  AnchoredNative (planProcess withoutConstancy splitPlan) ∧
  (∀ i : Fin 2,
    withoutConstancy.evaluate (planProcess withoutConstancy splitPlan) i =
      rows i (0 : ℝ)) ∧
  withoutConstancy.evaluate
      (planProcess withoutConstancy splitPlan) (1 : Fin 2) ≠
    withoutConstancy.evaluate withoutConstancy.source (1 : Fin 2) ∧
  (planCost withoutConstancy splitPlan 0 = ((2 : ℕ) : ℝ) ∧
    planCost withoutConstancy splitPlan 1 = 1) ∧
  ¬ SourceAssemblySelects withoutConstancy ∧
  ¬ withoutConstancy.combinerLaw ∧
  ¬ SourceNativeAssemblyGoal withoutConstancy AnchoredNative

theorem anchorConstancyDeletionGoal :
    AnchorConstancyDeletionGoal :=
  ⟨source_data_preserved, selector_allowed, original_combination_denied,
    selected_rows_correct, original_global_obstruction, closure_retained,
    actual_process_native, actual_process_vector, actual_process_fails,
    actual_process_cost, no_selects, no_combinerLaw, no_nativeGoal⟩

/-- Structural native closure alone does not prove correctness of the stored plan. -/
theorem closure_alone_insufficient :
    ¬ (∀ (C : SourceContract) (native : Set C.Process),
      SourceAssemblyClosed C native → SourceNativeAssemblyGoal C native) := by
  intro h
  exact no_nativeGoal (h withoutConstancy AnchoredNative closure_retained)

end AffineNative.AnchorConstancyControl


namespace SourceInstrument

open OperatorKO7.Meta.BoundaryObserver
open InstrumentLoss InstrumentComposition ProtocolResolution

def continuedReadout {Y Z W T V : Type} (restore : Y → W × T → Z)
    (d : Y × Z → V) : ((Y × W) × T) → V :=
  fun out => d (out.1.1, restore out.1.1 (out.1.2, out.2))

theorem continued_readouts_correct {X Y Z W T V : Type}
    [Fintype Y] [Fintype Z] [Fintype W] [Fintype T]
    (I : StochasticInstrument X Y Z) (J : Y → StochasticInstrument Z W T)
    (P : X → V) (k : ℕ) (side : X → Fin k) (parts : Fin k → Y × Z → V)
    (restore : Y → W × T → Z)
    (hrestore : ∀ y z w t, 0 < (J y).weight z w t → restore y (w, t) = z)
    (hparts : ∀ x yz, 0 < (jointChannel I).prob x yz → parts (side x) yz = P x) :
    ∀ x out, 0 < (jointChannel (sequential I J)).prob x out →
      continuedReadout restore (parts (side x)) out = P x := by
  rintro x ⟨⟨y, w⟩, t⟩ hp
  obtain ⟨z, hi, hj⟩ := (sequential_positive_iff I J x y w t).mp hp
  change parts (side x) (y, restore y (w, t)) = P x
  rw [hrestore y z w t hj]
  exact hparts x (y, z) hi

def InstrumentCompositionGoal {X Y Z W T V : Type}
    [Fintype Y] [Fintype Z] [Fintype W] [Fintype T]
    (I : StochasticInstrument X Y Z) (J : Y → StochasticInstrument Z W T)
    (P : X → V) (F : Set (((Y × W) × T) → V))
    (allowed : (k : ℕ) → Set (X → Fin k))
    (combines : Set (Support (jointChannel (sequential I J)).prob) → (k : ℕ) →
      (Support (jointChannel (sequential I J)).prob → Fin k) → Prop)
    (charge : ℝ) (k : ℕ) (side : X → Fin k)
    (parts : Fin k → ((Y × W) × T) → V) : Prop :=
  let K := jointChannel (sequential I J)
  let C := contract K P F allowed combines charge
  ∃ r : SourcePlan C Set.univ k,
    r.val.1 = liftSelector K.prob side ∧
    (∀ j, (r.val.2 j).val = parts j) ∧
    (∀ xo, planProcess C r xo = parts (side xo.val.1) xo.val.2) ∧
    planCost C r 0 = charge

theorem instrumentCompositionGoal {X Y Z W T V : Type}
    [Fintype Y] [Fintype Z] [Fintype W] [Fintype T]
    (I : StochasticInstrument X Y Z) (J : Y → StochasticInstrument Z W T)
    (P : X → V) (F : Set (Y × Z → V)) (F' : Set (((Y × W) × T) → V))
    (allowed : (k : ℕ) → Set (X → Fin k))
    (combines : Set (Support (jointChannel (sequential I J)).prob) → (k : ℕ) →
      (Support (jointChannel (sequential I J)).prob → Fin k) → Prop)
    (charge : ℝ) (k : ℕ) (side : X → Fin k) (hside : side ∈ allowed k)
    (parts : Fin k → F) (restore : Y → W × T → Z)
    (restorers : Y → Set (W × T → Z))
    (continues : (Y → StochasticInstrument Z W T) → (Y → W × T → Z) → Prop)
    (hr : ∀ y, restore y ∈ restorers y) (hj : continues J restore)
    (hconstruct : ∀ r, (∀ y, r y ∈ restorers y) → continues J r →
      ∀ d ∈ F, continuedReadout r d ∈ F')
    (hrestore : ∀ y z w t, 0 < (J y).weight z w t → restore y (w, t) = z)
    (hcombine : combines Set.univ k
      (liftSelector (jointChannel (sequential I J)).prob side))
    (hparts : ∀ x yz, 0 < (jointChannel I).prob x yz →
      (parts (side x)).val yz = P x) :
    InstrumentCompositionGoal I J P F' allowed combines charge k side
      (fun j => continuedReadout restore (parts j).val) := by
  let K := jointChannel (sequential I J)
  let ws : Fin k → F' := fun j =>
    ⟨continuedReadout restore (parts j).val,
      hconstruct restore hr hj (parts j).val (parts j).property⟩
  let r : SourcePlan (contract K P F' allowed combines charge) Set.univ k :=
    ⟨(liftSelector K.prob side, ws), ⟨side, hside, rfl⟩, hcombine, by
      intro xo _
      exact continued_readouts_correct I J P k side (fun j => (parts j).val)
        restore hrestore hparts xo.val.1 xo.val.2 xo.property⟩
  exact ⟨r, rfl, fun _ => rfl, fun _ => rfl, rfl⟩

structure NativeInstrumentProgram (X Y Z : Type) [Fintype Y] [Fintype Z] where
  instrument : StochasticInstrument X Y Z
  calls : ℕ

def primitiveInstrument {X Y Z : Type} [Fintype Y] [Fintype Z]
    (I : StochasticInstrument X Y Z) : NativeInstrumentProgram X Y Z := ⟨I, 1⟩

noncomputable def appendInstrument {X Y Z W T : Type}
    [Fintype Y] [Fintype Z] [Fintype W] [Fintype T]
    (I : NativeInstrumentProgram X Y Z) (J : NativeInstrumentProgram Z W T) :
    NativeInstrumentProgram X (Y × W) T :=
  ⟨sequential I.instrument (fun _ => J.instrument), I.calls + J.calls⟩

noncomputable def keepProgram : NativeInstrumentProgram Bool (Unit × Unit) Bool :=
  appendInstrument (primitiveInstrument (deterministic silentKeep))
    (primitiveInstrument (deterministic silentKeep))

noncomputable def keepKernel : StochasticGraph.Channel Bool ((Unit × Unit) × Bool) :=
  jointChannel keepProgram.instrument

noncomputable def keepCharge : ℝ := keepProgram.calls

theorem keepCharge_two : keepCharge = 2 := by
  change (↑(1 + 1 : ℕ) : ℝ) = 2
  norm_num

theorem keepCharge_pos : 0 < keepCharge := by
  rw [keepCharge_two]
  norm_num

theorem keepKernel_eq (x b : Bool) :
    keepKernel.prob x (((), ()), b) = binaryKernel (1 / 2) x b := by
  classical
  change (sequential (deterministic silentKeep)
    (fun _ : Unit => deterministic silentKeep)).weight x ((), ()) b = _
  rw [deterministic_composition_commutes silentKeep (fun _ : Unit => silentKeep)]
  cases x <;> cases b <;>
    norm_num [deterministic, adaptiveDeterministic, silentKeep, binaryKernel]

def keepOutputEquiv : Bool ≃ ((Unit × Unit) × Bool) where
  toFun b := (((), ()), b)
  invFun out := out.2
  left_inv _ := rfl
  right_inv out := by
    rcases out with ⟨⟨u, v⟩, b⟩
    cases u
    cases v
    rfl

theorem keep_capacity : SourceProtocol.Capacity keepKernel 1 :=
  SourceProtocol.capacity_reindex endpointKernel keepKernel keepOutputEquiv
    (fun x b => keepKernel_eq x b) 1 endpoint_capacity

theorem keep_retains (x : Bool) (out : (Unit × Unit) × Bool)
    (hp : 0 < keepKernel.prob x out) : out.2 = x := by
  rcases out with ⟨⟨u, v⟩, b⟩
  cases u
  cases v
  rw [keepKernel_eq] at hp
  exact endpoint_retains x b hp

def keepReadouts : Set (((Unit × Unit) × Bool) → Bool) := {f | ∀ out, f out = out.2}

def keepAllowed (k : ℕ) : Set (Bool → Fin k) := Set.univ

def keepCombines : Set (Support keepKernel.prob) → (k : ℕ) →
    (Support keepKernel.prob → Fin k) → Prop := fun _ _ _ => True

def keepNative : Set (Support keepKernel.prob → Bool) := {p | ∀ xo, p xo = xo.val.2.2}

noncomputable def keepContract : SourceContract :=
  contract keepKernel id keepReadouts keepAllowed keepCombines keepCharge

theorem keep_problem_satisfaction (d : keepReadouts) (xo : Support keepKernel.prob) :
    keepContract.problem.sat d xo ↔
      (Transport.InstrumentAdapter.instrumentProblem keepProgram.instrument
        (id : Bool → Bool)).sat d.val xo := Iff.rfl

theorem keep_native_closure :
    NativeClosure keepKernel.prob keepReadouts keepAllowed keepCombines keepNative := by
  intro D k side _ _ ws xo
  exact (ws (side xo.val.1)).property xo.val.2

theorem keep_denotes (p : keepContract.Process) (hp : p ∈ keepNative) :
    ∃ d ∈ keepReadouts, ∀ xo, p xo = d xo.val.2 :=
  ⟨Prod.snd, fun _ => rfl, hp⟩

noncomputable def keepPlan : SourcePlan keepContract Set.univ 1 := by
  refine ⟨(liftSelector keepKernel.prob (fun _ => (0 : Fin 1)),
    fun _ => ⟨fun out => out.2, fun _ => rfl⟩),
    ⟨(fun _ => (0 : Fin 1)), trivial, rfl⟩, trivial, ?_⟩
  intro xo _
  exact keep_retains xo.val.1 xo.val.2 xo.property

theorem keep_closed : SourceAssemblyClosed keepContract keepNative :=
  contract_closed keepKernel id keepReadouts keepAllowed keepCombines keepNative
    keepCharge keep_native_closure

theorem keep_selects : SourceAssemblySelects keepContract :=
  contract_selects keepKernel id keepReadouts keepAllowed keepCombines keepCharge

theorem keep_combiner : keepContract.combinerLaw :=
  contract_combiner keepKernel id keepReadouts keepAllowed keepCombines keepCharge

theorem keep_core : CoreGoal keepContract := source_observation_repair_core _

theorem keep_structural : SourceStructuralGoal keepContract keepNative :=
  sourceStructuralGoal _ _ keep_closed keep_selects

theorem endpoint_structural : SourceStructuralGoal endpointContract endpointNative :=
  sourceStructuralGoal _ _ endpoint_closed endpoint_selects

def keepCompositionOriginalReadouts : Set (Unit × Bool → Bool) :=
  {d | ∀ out, d out = out.2}

def keepCompositionRestorers (_y : Unit) : Set (Unit × Bool → Bool) :=
  {r | ∀ out, r out = out.2}

def keepCompositionRestore : Unit → Unit × Bool → Bool := fun _ out => out.2

def keepCompositionContinues (J : Unit → StochasticInstrument Bool Unit Bool)
    (restore : Unit → Unit × Bool → Bool) : Prop :=
  (∀ y, J y = deterministic silentKeep) ∧
    ∀ y, restore y ∈ keepCompositionRestorers y

def keepCompositionSide : Bool → Fin 1 := fun _ => 0

def keepCompositionParts (_j : Fin 1) : keepCompositionOriginalReadouts :=
  ⟨fun out => out.2, fun _ => rfl⟩

theorem keep_composition_stage_retains (x : Bool) (y : Unit) (z : Bool)
    (hp : 0 < (deterministic silentKeep).weight x y z) : z = x := by
  classical
  by_contra hn
  have hbad : ¬ (silentKeep.read x = y ∧ silentKeep.post x = z) :=
    fun h => hn h.2.symm
  unfold deterministic at hp
  dsimp only at hp
  rw [if_neg hbad] at hp
  norm_num at hp

theorem keep_composition_restorers_admitted :
    ∀ y, keepCompositionRestore y ∈ keepCompositionRestorers y := by
  intro y out
  rfl

theorem keep_composition_continuation_admitted :
    keepCompositionContinues
      (fun _ : Unit => deterministic silentKeep) keepCompositionRestore :=
  ⟨fun _ => rfl, keep_composition_restorers_admitted⟩

theorem keep_composition_readout_closed (r : Unit → Unit × Bool → Bool)
    (hr : ∀ y, r y ∈ keepCompositionRestorers y)
    (d : Unit × Bool → Bool) (hd : d ∈ keepCompositionOriginalReadouts) :
    continuedReadout r d ∈ keepReadouts := by
  intro out
  change d (out.1.1, r out.1.1 (out.1.2, out.2)) = out.2
  exact (hd (out.1.1, r out.1.1 (out.1.2, out.2))).trans
    (hr out.1.1 (out.1.2, out.2))

theorem keep_composition_source :
    keepKernel = jointChannel (sequential (deterministic silentKeep)
      (fun _ : Unit => deterministic silentKeep)) := rfl

theorem keep_composition :
    InstrumentCompositionGoal (deterministic silentKeep)
      (fun _ : Unit => deterministic silentKeep) (id : Bool → Bool)
      keepReadouts keepAllowed keepCombines keepCharge 1 keepCompositionSide
      (fun j => continuedReadout keepCompositionRestore (keepCompositionParts j).val) := by
  exact instrumentCompositionGoal
    (I := deterministic silentKeep) (J := fun _ : Unit => deterministic silentKeep)
    (P := (id : Bool → Bool)) (F := keepCompositionOriginalReadouts) (F' := keepReadouts)
    (allowed := keepAllowed) (combines := keepCombines) (charge := keepCharge)
    (k := 1) (side := keepCompositionSide) (hside := by trivial)
    (parts := keepCompositionParts) (restore := keepCompositionRestore)
    (restorers := keepCompositionRestorers) (continues := keepCompositionContinues)
    (hr := keep_composition_restorers_admitted)
    (hj := keep_composition_continuation_admitted)
    (hconstruct := fun r hr _ d hd => keep_composition_readout_closed r hr d hd)
    (hrestore := by
      intro y z w t hp
      exact keep_composition_stage_retains z w t hp)
    (hcombine := by trivial)
    (hparts := by
      intro x yz hp
      exact keep_composition_stage_retains x yz.1 yz.2 hp)

theorem keep_acquisition_lower {A : Type} [Fintype A] (μ : FiniteLaw Bool)
    (policy : List (A × ((Unit × Unit) × Bool)) → FiniteLaw A)
    (stop : List (A × ((Unit × Unit) × Bool)) → Bool)
    (n : ℕ) (bank : List (List (A × ((Unit × Unit) × Bool))))
    (hbank : HistoryBank n bank) (required : ℝ)
    (htarget : required ≤ terminalMI
      (SourceProtocol.acquisition keepKernel μ policy stop keepCharge keepCharge_pos) n bank) :
    2 * required ≤ expectedCost
      (SourceProtocol.acquisition keepKernel μ policy stop keepCharge keepCharge_pos) n bank := by
  have h := SourceProtocol.acquisition_cost_lower keepKernel μ policy stop
    keepCharge keepCharge_pos 1 (by norm_num) keep_capacity n bank hbank required htarget
  have he : required / (1 / keepCharge) = 2 * required := by rw [keepCharge_two]; ring
  rw [he] at h
  exact h

def SilentKeepOperationalGoal : Prop :=
  SourceOperationalGoal keepKernel (fun _ out => out.2) id keepReadouts
    keepAllowed keepCombines keepNative keepCharge keepCharge_pos 1 ∧
  keepProgram.calls = 2 ∧
  planProcess keepContract keepPlan ∈ keepNative ∧
  planCost keepContract keepPlan 0 = 2 ∧
  (∀ xo, planProcess keepContract keepPlan xo =
    continuedReadout (fun _ : Unit => (Prod.snd : Unit × Bool → Bool))
      (Prod.snd : Unit × Bool → Bool) xo.val.2) ∧
  0 < keepKernel.prob false (((), ()), false) ∧
  0 < keepKernel.prob true (((), ()), true) ∧
  (false : Bool) ≠ true ∧
  InstrumentCompositionGoal (deterministic silentKeep)
    (fun _ : Unit => deterministic silentKeep) (id : Bool → Bool)
    keepReadouts keepAllowed keepCombines keepCharge 1 keepCompositionSide
    (fun j => continuedReadout keepCompositionRestore (keepCompositionParts j).val)

theorem silentKeepOperationalGoal : SilentKeepOperationalGoal := by
  refine ⟨sourceOperationalGoal keepKernel (fun _ out => out.2) id keepReadouts
    keepAllowed keepCombines keepNative keepCharge keepCharge_pos 1
    keep_retains keep_native_closure keep_capacity,
    rfl, (fun _ => rfl), keepCharge_two, (fun _ => rfl),
    ?_, ?_, by decide, keep_composition⟩
  · rw [keepKernel_eq]
    norm_num [binaryKernel]
  · rw [keepKernel_eq]
    norm_num [binaryKernel]

theorem repeated_state_premise_control :
    let K := jointChannel (deterministic readAndErase)
    traceWeight K (fun _ out => out.2) true [(true, false), (false, false)] = 1 ∧
      traceWeight K (fun x _ => x) true [(true, false), (false, false)] = 0 := by
  classical
  norm_num [traceWeight, jointChannel, deterministic, readAndErase]

end SourceInstrument


namespace SourceInstrument

open OperatorKO7.Meta.BoundaryObserver
open InstrumentLoss InstrumentComposition

def restorationFalseRestore : Unit → Unit × Bool → Bool := fun _ _ => false

def restorationControlAllowed (k : ℕ) : Set (Bool → Fin k) :=
  {side | ∀ x, side x = side false}

def restorationControlRestorers (_y : Unit) : Set (Unit × Bool → Bool) := Set.univ

def restorationControlContinues (J : Unit → StochasticInstrument Bool Unit Bool)
    (_restore : Unit → Unit × Bool → Bool) : Prop :=
  ∀ y, J y = deterministic silentKeep

def restorationControlNative : Set (Support keepKernel.prob → Bool) :=
  {p | ∃ d : ((Unit × Unit) × Bool) → Bool, ∀ xo, p xo = d xo.val.2}

noncomputable def restorationControlSource : SourceContract :=
  contract keepKernel id Set.univ restorationControlAllowed keepCombines keepCharge

noncomputable def restorationControlProcess : restorationControlSource.Process :=
  restorationControlSource.assemble 1
    (liftSelector keepKernel.prob keepCompositionSide)
    (fun j => ⟨continuedReadout restorationFalseRestore (keepCompositionParts j).val,
      Set.mem_univ _⟩)

theorem restorationControl_stage_positive :
    0 < (deterministic silentKeep).weight true () true := by
  classical
  have hpos : silentKeep.read true = () ∧ silentKeep.post true = true :=
    ⟨rfl, rfl⟩
  unfold deterministic
  dsimp only
  rw [if_pos hpos]
  norm_num

noncomputable def restorationControlTrue : Support keepKernel.prob := by
  refine ⟨(true, (((), ()), true)), ?_⟩
  change 0 < (sequential (deterministic silentKeep)
    (fun _ : Unit => deterministic silentKeep)).weight true ((), ()) true
  exact (sequential_positive_iff (deterministic silentKeep)
    (fun _ : Unit => deterministic silentKeep) true () () true).mpr
    ⟨true, restorationControl_stage_positive, restorationControl_stage_positive⟩

theorem restorationControl_closed :
    NativeClosure keepKernel.prob Set.univ restorationControlAllowed keepCombines
      restorationControlNative := by
  intro D k side hs _ ws
  refine ⟨(ws (side false)).val, ?_⟩
  intro xo
  exact congrArg (fun j => (ws j).val xo.val.2) (hs xo.val.1)

theorem restorationControl_plan :
    ∃ r : SourcePlan restorationControlSource Set.univ 1,
      planProcess restorationControlSource r ∈ restorationControlNative ∧
      (∀ xo, planProcess restorationControlSource r xo = xo.val.1) ∧
      planCost restorationControlSource r 0 = keepCharge := by
  let r : SourcePlan restorationControlSource Set.univ 1 :=
    ⟨(liftSelector keepKernel.prob keepCompositionSide,
      fun _ => ⟨fun out => out.2, Set.mem_univ _⟩),
      ⟨keepCompositionSide, (fun _ => rfl), rfl⟩, trivial, by
        intro xo _
        exact keep_retains xo.val.1 xo.val.2 xo.property⟩
  exact ⟨r, ⟨Prod.snd, fun _ => rfl⟩,
    (fun xo => keep_retains xo.val.1 xo.val.2 xo.property), rfl⟩

def restorationControlResult (restore : Unit → Unit × Bool → Bool) : Prop :=
  InstrumentCompositionGoal (deterministic silentKeep)
    (fun _ : Unit => deterministic silentKeep) (id : Bool → Bool)
    Set.univ restorationControlAllowed keepCombines keepCharge 1 keepCompositionSide
    (fun j => continuedReadout restore (keepCompositionParts j).val)

theorem restorationControl_with_fidelity (restore : Unit → Unit × Bool → Bool)
    (hrestore : ∀ y z w t, 0 < (deterministic silentKeep).weight z w t →
      restore y (w, t) = z) : restorationControlResult restore := by
  exact instrumentCompositionGoal
    (I := deterministic silentKeep) (J := fun _ : Unit => deterministic silentKeep)
    (P := (id : Bool → Bool)) (F := keepCompositionOriginalReadouts) (F' := Set.univ)
    (allowed := restorationControlAllowed) (combines := keepCombines)
    (charge := keepCharge) (k := 1) (side := keepCompositionSide)
    (hside := fun _ => rfl) (parts := keepCompositionParts) (restore := restore)
    (restorers := restorationControlRestorers) (continues := restorationControlContinues)
    (hr := fun _ => Set.mem_univ _) (hj := fun _ => rfl)
    (hconstruct := fun _ _ _ _ _ => Set.mem_univ _)
    (hrestore := hrestore) (hcombine := by trivial)
    (hparts := fun x yz hp => keep_composition_stage_retains x yz.1 yz.2 hp)

theorem restorationControl_wrong_result :
    ¬ restorationControlResult restorationFalseRestore := by
  rintro ⟨r, _, _, hout, _⟩
  have hf := hout restorationControlTrue
  change planProcess restorationControlSource r restorationControlTrue = false at hf
  have ht := r.property.2.2 restorationControlTrue (Set.mem_univ _)
  change planProcess restorationControlSource r restorationControlTrue = true at ht
  have h : false = true := hf.symm.trans ht
  cases h

/-- The supplied restoring map fails while both native stages and their charge remain intact. -/
def InstrumentRestorationControlGoal : Prop :=
  (∀ y : Unit, StochasticRecoverable
    ((fun _ : Unit => deterministic silentKeep) y)) ∧
  (∀ x yz, 0 < (jointChannel (deterministic silentKeep)).prob x yz →
    (keepCompositionParts (keepCompositionSide x)).val yz = x) ∧
  keepCompositionSide ∈ restorationControlAllowed 1 ∧
  (∀ y, restorationFalseRestore y ∈ restorationControlRestorers y) ∧
  restorationControlContinues (fun _ : Unit => deterministic silentKeep)
    restorationFalseRestore ∧
  (∀ r, (∀ y, r y ∈ restorationControlRestorers y) →
    restorationControlContinues (fun _ : Unit => deterministic silentKeep) r →
    ∀ d ∈ keepCompositionOriginalReadouts,
      continuedReadout r d ∈ (Set.univ : Set (((Unit × Unit) × Bool) → Bool))) ∧
  NativeClosure keepKernel.prob Set.univ restorationControlAllowed keepCombines
    restorationControlNative ∧
  (∃ r : SourcePlan restorationControlSource Set.univ 1,
    planProcess restorationControlSource r ∈ restorationControlNative ∧
    (∀ xo, planProcess restorationControlSource r xo = xo.val.1) ∧
    planCost restorationControlSource r 0 = keepCharge) ∧
  restorationControlProcess ∈ restorationControlNative ∧
  (∀ xo, restorationControlProcess xo =
    continuedReadout restorationFalseRestore
      (keepCompositionParts (keepCompositionSide xo.val.1)).val xo.val.2) ∧
  (∀ xo, restorationControlProcess xo = false) ∧
  restorationControlProcess restorationControlTrue ≠ restorationControlTrue.val.1 ∧
  restorationControlSource.cost restorationControlProcess 0 = keepCharge ∧
  keepCharge = (keepProgram.calls : ℝ) ∧ keepCharge = 2 ∧ 0 < keepCharge ∧
  ¬ (∀ y z w t, 0 < (deterministic silentKeep).weight z w t →
    restorationFalseRestore y (w, t) = z) ∧
  ¬ restorationControlResult restorationFalseRestore ∧
  ¬ (∀ restore, restorationControlResult restore) ∧
  ∀ restore, (∀ y z w t, 0 < (deterministic silentKeep).weight z w t →
    restore y (w, t) = z) → restorationControlResult restore

theorem instrumentRestorationControlGoal : InstrumentRestorationControlGoal := by
  refine ⟨?_, ?_, (fun _ => rfl), (fun _ => Set.mem_univ _), (fun _ => rfl),
    (fun _ _ _ _ _ => Set.mem_univ _), restorationControl_closed,
    restorationControl_plan, ?_, (fun _ => rfl), (fun _ => rfl), ?_,
    rfl, rfl, keepCharge_two, keepCharge_pos, ?_,
    restorationControl_wrong_result, ?_, restorationControl_with_fidelity⟩
  · intro _
    exact (deterministic_restoration_iff silentKeep).mpr ⟨Prod.snd, fun _ => rfl⟩
  · intro x yz hp
    exact keep_composition_stage_retains x yz.1 yz.2 hp
  · exact ⟨continuedReadout restorationFalseRestore (keepCompositionParts 0).val,
      fun _ => rfl⟩
  · change false ≠ true
    decide
  · intro hf
    have h := hf () true () true restorationControl_stage_positive
    change false = true at h
    cases h
  · intro h
    exact restorationControl_wrong_result (h restorationFalseRestore)

end SourceInstrument

namespace SourceIndexed

open Demand Transport NativeAssembly SourceInstrument
open OperatorKO7 (Trace)
open OperatorKO7.Meta.BoundaryObserver
open OperatorKO7.Meta.BoundaryObserver.SelfEvaluationBounds (pairedEval)
open OperatorKO7.Meta.BoundaryObserver.ObserverRealization (triangleReport)
open OperatorKO7.Meta.BoundaryObserver.AffineSelfObservation (Bit affineRows affineRhs)

inductive NativeKind where
  | recursor | evaluator | probabilistic | commonLaw | affine

inductive NativeSource : NativeKind → (C : SourceContract) → Set C.Process → Type 1 where
  | recursor (R : Trace) (horizon : ℕ) :
      NativeSource .recursor (retainedContract R horizon) (retainedNative R horizon)
  | evaluator (A V : Type) (E : A → A → V) (j : V → V) (anchor : A)
      (hj : ∀ v, j v ≠ v) :
      NativeSource .evaluator (evaluatorContract A V E j anchor) AnchoredNative
  | channel {X O V : Type} [Fintype X] [Fintype O]
      (K : StochasticGraph.Channel X O) (next : X → O → X)
      (P : X → V) (F : Set (O → V))
      (allowed : (k : ℕ) → Set (X → Fin k))
      (combines : Set (Support K.prob) → (k : ℕ) →
        (Support K.prob → Fin k) → Prop) (charge cap : ℝ)
      (native : Set (contract K P F allowed combines charge).Process)
      (hcharge : 0 < charge) (hretain : ∀ x o, 0 < K.prob x o → next x o = x)
      (hcap : SourceProtocol.Capacity K cap) :
      NativeSource .probabilistic (contract K P F allowed combines charge) native
  | instrument : NativeSource .probabilistic keepContract keepNative
  | commonLaw {A J : Type} [Fintype A]
      (v : A → J → ℝ) (p : J → ℝ) (anchor : J) :
      NativeSource .commonLaw (commonLawContract v p anchor) AnchoredNative
  | affine {K V I : Type} [Field K] [AddCommGroup V] [Module K V] [Fintype I]
      (rows : I → V →ₗ[K] K) (b : I → K) (anchor : I) :
      NativeSource .affine (AffineNative.contract rows b anchor) AnchoredNative

/-- The two assembly laws of a native source; its specialized laws are constructor fields. -/
def PrimitiveLaws {kind : NativeKind} {C : SourceContract} {native : Set C.Process}
    (_s : NativeSource kind C native) : Prop :=
  SourceAssemblyClosed C native ∧ SourceAssemblySelects C

def SpecializedGoal {kind : NativeKind} {C : SourceContract} {native : Set C.Process}
    (s : NativeSource kind C native) : Prop :=
  match s with
  | .recursor R horizon =>
      SourceRetainedRunGoal R horizon ∧ CountedOperationalGoal ∧
      (∀ w i, (retainedContract R horizon).problem.sat w i ↔
        countedContract.problem.sat w (retainedEmbedding R horizon i)) ∧
      (∀ D, Good (retainedContract R horizon).problem D ↔
        Good countedContract.problem (retainedEmbedding R horizon '' D))
  | .evaluator A V E j anchor _ =>
      EvaluatorNativeGoal A V E j anchor ∧
      ∀ v0, (∀ c x, extendEval E j v0 (some c) (some x) = E c x) ∧
        (∀ x, extendEval E j v0 none (some x) = j (E x x)) ∧
        ¬ ∃ c, ∀ x, extendEval E j v0 c x = j (extendEval E j v0 x x)
  | @NativeSource.channel X O _ fx fo K next P F allowed combines charge cap native hcharge _ _ =>
      letI : Fintype X := fx
      letI : Fintype O := fo
      SourceOperationalGoal K next P F allowed combines native charge hcharge cap
  | .instrument => SilentKeepOperationalGoal
  | @NativeSource.commonLaw A _ fa v p anchor =>
      letI : Fintype A := fa
      CommonLawNativeGoal v p anchor
  | @NativeSource.affine K V I fk gv mv fi rows b anchor =>
      letI : Field K := fk
      letI : AddCommGroup V := gv
      letI : Module K V := mv
      letI : Fintype I := fi
      AffineNative.AffineNativeGoal rows b anchor

def IndexedSourceGoal {kind : NativeKind} {C : SourceContract} {native : Set C.Process}
    (s : NativeSource kind C native) : Prop :=
  SourceStructuralGoal C native ∧ SpecializedGoal s

theorem nativeClosure_of_closed {X O V : Type} [Fintype O]
    (K : StochasticGraph.Channel X O) (P : X → V) (F : Set (O → V))
    (allowed : (k : ℕ) → Set (X → Fin k))
    (combines : Set (Support K.prob) → (k : ℕ) →
      (Support K.prob → Fin k) → Prop)
    (native : Set (Support K.prob → V)) (charge : ℝ)
    (hc : SourceAssemblyClosed (contract K P F allowed combines charge) native) :
    NativeClosure K.prob F allowed combines native := by
  intro D k side hs hb ws
  exact hc D k (liftSelector K.prob side) ws ⟨side, hs, rfl⟩ hb

theorem specializedGoal {kind : NativeKind} {C : SourceContract}
    {native : Set C.Process} (s : NativeSource kind C native) (h : PrimitiveLaws s) :
    SpecializedGoal s := by
  cases s with
  | recursor R horizon =>
      exact ⟨sourceRetainedRunGoal R horizon, countedOperationalGoal,
        retained_incidence R horizon, retained_good_iff R horizon⟩
  | evaluator A V E j anchor hj =>
      exact ⟨evaluatorNativeGoal A V E j anchor, fun v0 => evaluator_conservative E j v0 hj⟩
  | @channel X O _ fx fo K next P F allowed combines charge cap native hcharge hretain hcap =>
      letI : Fintype X := fx
      letI : Fintype O := fo
      exact sourceOperationalGoal K next P F allowed combines native charge hcharge cap
        hretain (nativeClosure_of_closed K P F allowed combines native charge h.1) hcap
  | instrument => exact silentKeepOperationalGoal
  | @commonLaw A _ fa v p anchor =>
      letI : Fintype A := fa
      exact commonLawNativeGoal v p anchor
  | @affine K V I fk gv mv fi rows b anchor =>
      letI : Field K := fk
      letI : AddCommGroup V := gv
      letI : Module K V := mv
      letI : Fintype I := fi
      exact AffineNative.affineNativeGoal rows b anchor

theorem indexedSourceGoal {kind : NativeKind} {C : SourceContract}
    {native : Set C.Process} (s : NativeSource kind C native) (h : PrimitiveLaws s) :
    IndexedSourceGoal s :=
  ⟨sourceStructuralGoal C native h.1 h.2, specializedGoal s h⟩

structure NativeCase (kind : NativeKind) where
  contract : SourceContract
  native : Set contract.Process
  origin : NativeSource kind contract native

def pack {kind : NativeKind} {C : SourceContract} {native : Set C.Process}
    (s : NativeSource kind C native) : NativeCase kind := ⟨C, native, s⟩

def UniversalSourceOperationalGoal (sources : (kind : NativeKind) → NativeCase kind) : Prop :=
  ∀ kind, IndexedSourceGoal (sources kind).origin

theorem universalSourceOperationalGoal (sources : (kind : NativeKind) → NativeCase kind)
    (h : ∀ kind, PrimitiveLaws (sources kind).origin) :
    UniversalSourceOperationalGoal sources :=
  fun kind => indexedSourceGoal (sources kind).origin (h kind)

theorem universal_observation_repair (sources : (kind : NativeKind) → NativeCase kind)
    (h : ∀ kind, PrimitiveLaws (sources kind).origin) :
    UniversalSourceOperationalGoal sources :=
  universalSourceOperationalGoal sources h

noncomputable def canonicalSources : (kind : NativeKind) → NativeCase kind
  | .recursor => pack (.recursor Trace.void 1)
  | .evaluator => pack (.evaluator (ℕ × Bool) Bool pairedEval Bool.not (0, false)
      (fun b => by cases b <;> decide))
  | .probabilistic => pack .instrument
  | .commonLaw => pack (.commonLaw triangleReport (fun _ => (2 : ℝ) / 3) (0 : Fin 3))
  | .affine => pack (.affine (affineRows 0) (affineRhs 0) (0 : Fin 2))

theorem canonicalLaws (kind : NativeKind) : PrimitiveLaws (canonicalSources kind).origin := by
  cases kind with
  | recursor => exact ⟨retained_closed Trace.void 1, retained_selects Trace.void 1⟩
  | evaluator =>
      exact ⟨anchored_closed (ℕ × Bool) (ℕ × Bool) Bool pairedEval
        (fun x => !(pairedEval x x)) (0, false) 2,
        anchored_selects (ℕ × Bool) (ℕ × Bool) Bool pairedEval
        (fun x => !(pairedEval x x)) (0, false) 2⟩
  | probabilistic => exact ⟨keep_closed, keep_selects⟩
  | commonLaw =>
      exact ⟨anchored_closed (Fin 3) (AssignmentLaw (Bool × Bool × Bool)) ℝ
        (lawEvaluate triangleReport) (fun _ => (2 : ℝ) / 3) (0 : Fin 3) 1,
        anchored_selects (Fin 3) (AssignmentLaw (Bool × Bool × Bool)) ℝ
        (lawEvaluate triangleReport) (fun _ => (2 : ℝ) / 3) (0 : Fin 3) 1⟩
  | affine =>
      exact ⟨anchored_closed (Fin 2) (Bit × Bit) Bit
        (fun x i => affineRows 0 i x) (affineRhs 0) (0 : Fin 2) 1,
        anchored_selects (Fin 2) (Bit × Bit) Bit
        (fun x i => affineRows 0 i x) (affineRhs 0) (0 : Fin 2) 1⟩

def NativeNonvacuous {kind : NativeKind} (c : NativeCase kind) : Prop :=
  ∃ (D : Set c.contract.Input) (k : ℕ) (r : SourcePlan c.contract D k),
    D.Nonempty ∧ planProcess c.contract r ∈ c.native ∧ 0 < planCost c.contract r 0

theorem nonvacuous_of_paid {kind : NativeKind} (c : NativeCase kind)
    (hc : SourceAssemblyClosed c.contract c.native) {D : Set c.contract.Input}
    {k : ℕ} (hD : D.Nonempty) (r : SourcePlan c.contract D k)
    (hp : 0 < planCost c.contract r 0) : NativeNonvacuous c :=
  ⟨D, k, r, hD, hc D k r.val.1 r.val.2 r.property.1 r.property.2.1, hp⟩

theorem canonical_nonvacuous (kind : NativeKind) :
    NativeNonvacuous (canonicalSources kind) := by
  cases kind with
  | recursor =>
      obtain ⟨r, hr, _⟩ := retained_positive_plan Trace.void
      refine nonvacuous_of_paid (canonicalSources .recursor) (canonicalLaws .recursor).1
        (Set.singleton_nonempty _) r ?_
      change 0 < planCost (retainedContract Trace.void 1) r 0
      rw [hr]
      norm_num
  | evaluator =>
      obtain ⟨r⟩ := paired_singleton_plan
      refine nonvacuous_of_paid (canonicalSources .evaluator) (canonicalLaws .evaluator).1
        (Set.singleton_nonempty _) r ?_
      change 0 < planCost
        (evaluatorContract (ℕ × Bool) Bool pairedEval Bool.not (0, false)) r 0
      rw [evaluator_plan_cost]
      norm_num
  | probabilistic =>
      let xo : Support keepKernel.prob := ⟨(false, (((), ()), false)), by
        rw [keepKernel_eq]
        change (0 : ℝ) < 1 / 2 + 1 / 2
        norm_num⟩
      exact nonvacuous_of_paid _ keep_closed ⟨xo, Set.mem_univ xo⟩ keepPlan keepCharge_pos
  | commonLaw =>
      obtain ⟨r, _, hr⟩ := common_triangle_native_instance.2.2.2
      refine nonvacuous_of_paid (canonicalSources .commonLaw) (canonicalLaws .commonLaw).1
        ⟨(0 : Fin 3), Set.mem_univ _⟩ r ?_
      change 0 < planCost (commonLawContract triangleReport (fun _ => (2 : ℝ) / 3) 0) r 0
      rw [hr]
      norm_num
  | affine =>
      refine nonvacuous_of_paid (canonicalSources .affine) (canonicalLaws .affine).1
        ⟨(0 : Fin 2), Set.mem_univ _⟩ AffineNative.copyPlan ?_
      change 0 < planCost (AffineNative.contract (affineRows 0) (affineRhs 0) (0 : Fin 2))
        AffineNative.copyPlan 0
      rw [AffineNative.copyPlan_cost.1]
      norm_num

noncomputable def endpointCase : NativeCase .probabilistic :=
  pack (.channel endpointKernel (fun _ o => o) id endpointReadouts endpointAllowed
    endpointCombines endpointCharge 1 endpointNative endpointCharge_pos endpoint_retains
    endpoint_capacity)

theorem endpointLaws : PrimitiveLaws endpointCase.origin :=
  ⟨endpoint_closed, endpoint_selects⟩

def EndpointIndexedGoal : Prop :=
  IndexedSourceGoal endpointCase.origin ∧ EndpointChannelOperationalGoal ∧
    NativeNonvacuous endpointCase

theorem endpointIndexedGoal : EndpointIndexedGoal := by
  refine ⟨indexedSourceGoal endpointCase.origin endpointLaws, endpointChannelOperationalGoal, ?_⟩
  let xo : Support endpointKernel.prob := ⟨(false, false), by
    change (0 : ℝ) < 1 / 2 + 1 / 2
    norm_num⟩
  exact nonvacuous_of_paid endpointCase endpoint_closed
    ⟨xo, Set.mem_univ xo⟩ endpointPlan endpointCharge_pos

def FiveNativeSourcesGoal : Prop :=
  UniversalSourceOperationalGoal canonicalSources ∧
    (∀ kind, NativeNonvacuous (canonicalSources kind)) ∧ EndpointIndexedGoal

theorem fiveNativeSourcesGoal : FiveNativeSourcesGoal :=
  ⟨universal_observation_repair canonicalSources canonicalLaws,
    canonical_nonvacuous, endpointIndexedGoal⟩

end SourceIndexed

end UniversalObservation.Completion.Operational
