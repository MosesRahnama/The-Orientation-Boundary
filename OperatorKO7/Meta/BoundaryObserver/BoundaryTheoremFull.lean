import OperatorKO7.Meta.BoundaryObserver.CountedPassInformation
import OperatorKO7.Meta.BoundaryObserver.AffineSelfObservation
import OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation
import OperatorKO7.Meta.BoundaryObserver.KalmanObservability
import OperatorKO7.Meta.BoundaryObserver.LinearObservability
import OperatorKO7.Meta.BoundaryObserver.StochasticGraph
import OperatorKO7.Meta.BoundaryObserver.RiceBoundary
import OperatorKO7.Meta.BoundaryObserver.DemandDetector
import OperatorKO7.Meta.BoundaryObserver.PartialSelfEvaluation
import OperatorKO7.Meta.BoundaryObserver.SelfEvaluationBounds
import OperatorKO7.Meta.BoundaryObserver.FourTestTables
import OperatorKO7.Meta.BoundaryObserver.ObserverRealization
import OperatorKO7.Meta.BoundaryObserver.PitowskyPolytope
import OperatorKO7.Meta.BoundaryObserver.Instances.KernelCases
import OperatorKO7.Meta.SafeStep.EqWVoidAnomaly
import OperatorKO7.Meta.DistinctionBoundary.CriticalPairCompleteness
import OperatorKO7.Meta.DistinctionBoundary.ContextualDiagonalScope
import OperatorKO7.Meta.DistinctionBoundary.ContextualClassification
import OperatorKO7.Meta.BoundaryGeneral.HomomorphicInexpressibility
import OperatorKO7.Meta.SafeStep.HomomorphicGuardBarrier
import OperatorKO7.Meta.BoundaryObserver.MergedPair
import OperatorKO7.Meta.BoundaryObserver.PairInvariants
import OperatorKO7.Meta.BoundaryObserver.BitDivision
import OperatorKO7.Meta.BoundaryObserver.PlaceCoordinates
import OperatorKO7.Meta.BoundaryObserver.SeedFrontier
import OperatorKO7.Meta.BoundaryObserver.BoundaryInfiniteCost
import OperatorKO7.Meta.BoundaryObserver.PlaceOrbitGeneral
import OperatorKO7.Meta.BoundaryObserver.LandauDictionary
import OperatorKO7.Meta.BoundaryObserver.InstrumentComposition
import OperatorKO7.Meta.BoundaryObserver.NoReturn
import OperatorKO7.Meta.BoundaryObserver.SecrecyGeneralMessages
import OperatorKO7.Meta.DistinctionBoundary.TarskiUndefinability

/-!
# The full Boundary Theorem

Proof graph: `Audit/ledgers/boundary-theorem/BOUNDARY-THEOREM-MATH-COMPLETION-PROOF-GRAPH.md`,
node N43. The conclusion of the mathematics manuscript states that the Boundary Theorem states the
results of its fourteen instances (Table `tab:readings`). `BoundaryTheoremCoreGoal` holds the
twenty-four core clauses, and the rows of logic, diagonalization, cryptography, privacy,
statistics and termination. This module adds one goal for each other row of the table and for
each general theorem of the development, each goal the universally closed statement of named
theorems, and proves the conjunction `BoundaryTheoremFullGoal` with one proof term. Every
declaration it wraps keeps its name, type and hypotheses; the module adds wrappers only.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.BoundaryObserver.BoundaryTheoremFull

universe u v w r s

open scoped BigOperators
open OperatorKO7.Meta.BoundaryObserver

noncomputable section

/-! ## Linear algebra: the Fredholm alternative with source-row certificates -/

open AffineSelfObservation in
/-- Theorem `thm:affine-self-certificates`: a fiber of a linear map is one solution translated by
the kernel; a linear target is forced on a fiber exactly when it vanishes on the kernel, and
exactly when it is a combination of the rows; an inconsistent system has a left annihilator and a
row refutation; a missing row certificate has a kernel displacement; and every finite system has
one of the three certificates. -/
def LinearAlgebraGoal : Prop :=
  (∀ (K V W : Type) [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
      (M : V →ₗ[K] W) (b : W) (p x : V), M p = b → (M x = b ↔ ∃ k, M k = 0 ∧ x = p + k)) ∧
  (∀ (K V W : Type) [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
      (M : V →ₗ[K] W) (L : V →ₗ[K] K) (b : W) (p : V), M p = b →
        ((∀ x, M x = b → L x = L p) ↔ ∀ k, M k = 0 → L k = 0)) ∧
  (∀ (K V W : Type) [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
      (M : V →ₗ[K] W) (b : W),
        (¬ ∃ x, M x = b) ↔ ∃ l : W →ₗ[K] K, l.comp M = 0 ∧ l b ≠ 0) ∧
  (∀ (K V I : Type) [Field K] [AddCommGroup V] [Module K V] [Fintype I]
      (rows : I → V →ₗ[K] K) (L : V →ₗ[K] K) (b : I → K) (p : V), Satisfies rows b p →
        ((∀ x, Satisfies rows b x → L x = L p) ↔ ∃ c : I → K, ∑ i, c i • rows i = L)) ∧
  (∀ (K V I : Type) [Field K] [AddCommGroup V] [Module K V] [Fintype I]
      (rows : I → V →ₗ[K] K) (L : V →ₗ[K] K),
        (¬ ∃ c : I → K, ∑ i, c i • rows i = L) ↔ ∃ k, (∀ i, rows i k = 0) ∧ L k ≠ 0) ∧
  (∀ (K V I : Type) [Field K] [AddCommGroup V] [Module K V] [Fintype I]
      (rows : I → V →ₗ[K] K) (b : I → K),
        (¬ ∃ x, Satisfies rows b x) ↔
          ∃ c : I → K, (∑ i, c i • rows i) = 0 ∧ (∑ i, c i * b i) ≠ 0) ∧
  (∀ (K V I : Type) [Field K] [AddCommGroup V] [Module K V] [Fintype I]
      (rows : I → V →ₗ[K] K) (b : I → K) (L : V →ₗ[K] K),
        (∃ c : I → K, (∑ i, c i • rows i) = 0 ∧ (∑ i, c i * b i) ≠ 0) ∨
        (∃ (p : V) (c : I → K), Satisfies rows b p ∧ (∑ i, c i • rows i) = L) ∨
        (∃ p k, Satisfies rows b p ∧ (∀ i, rows i k = 0) ∧ L k ≠ 0))

/-- The linear algebra row holds, each clause by its theorem. -/
theorem linearAlgebraGoal : LinearAlgebraGoal :=
  ⟨@AffineSelfObservation.solution_iff_kernel_translate,
    @AffineSelfObservation.target_forced_iff_kernel,
    @AffineSelfObservation.no_solution_iff_annihilator,
    @AffineSelfObservation.target_forced_iff_row_certificate,
    @AffineSelfObservation.no_row_certificate_iff_kernel_witness,
    @AffineSelfObservation.no_solution_iff_row_refutation,
    @AffineSelfObservation.source_certificate_trichotomy⟩

/-! ## Automata and control: permitted experiments, Moore, Myhill and Nerode, and Kalman -/

open AdmissibleObservation KalmanObservability in
/-- Theorem `thm:permitted-equivalence` and Proposition `prop:kalman`: the indistinguishability of
permitted finite experiments is the greatest action-stable relation inside the kernel of the
record, it agrees with every adaptive experiment, and every resolving experiment has a boundary
event; for a linear system two states are indistinguishable exactly when their difference lies in
the unobservable subspace, the largest invariant subspace inside the kernel of the output, the
behavior is injective exactly when that subspace is zero and exactly when the stacked
observability map has full rank, and the quotient by it is the minimal observer. -/
def AutomataControlGoal : Prop :=
  (∀ (X : Type u) (A : Type v) (Q : Type w) (q : X → Q) (step : A → X → X),
    (∀ x y, FutureEq q step x y → q x = q y) ∧
      (∀ a x y, FutureEq q step x y → FutureEq q step (step a x) (step a y)) ∧
      ∀ R : X → X → Prop, (∀ x y, R x y → q x = q y) →
        (∀ a x y, R x y → R (step a x) (step a y)) →
          ∀ x y, R x y → FutureEq q step x y) ∧
  (∀ (X : Type u) (A : Type v) (Q : Type w) (q : X → Q) (step : A → X → X) (x y : X),
    FutureEq q step x y ↔
      ∀ e : Experiment A Q Q, evaluate q step e x = evaluate q step e y) ∧
  (∀ (X : Type u) (A : Type v) (Q : Type w) (V : Type r) (q : X → Q) (step : A → X → X)
      (e : Experiment A Q V),
    ∀ x y, q x = q y → evaluate q step e x ≠ evaluate q step e y →
      ∃ (before : List A) (a : A) (afterX afterY : List A),
        executedTrace q step e x = before ++ a :: afterX ∧
        executedTrace q step e y = before ++ a :: afterY ∧
        q (run step before x) = q (run step before y) ∧
        q (step a (run step before x)) ≠ q (step a (run step before y))) ∧
  (∀ (K : Type u) [Field K] (V : Type v) (W : Type w)
      [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
      (A : V →ₗ[K] V) (C : V →ₗ[K] W) (x y : V),
    FutureEq (C : V → W) (fun _ : Unit => (A : V → V)) x y ↔
      x - y ∈ unobservable K A C) ∧
  (∀ (K : Type u) [Field K] (V : Type v) (W : Type w)
      [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
      (A : V →ₗ[K] V) (C : V →ₗ[K] W),
    (∀ x ∈ unobservable K A C, A x ∈ unobservable K A C) ∧
      unobservable K A C ≤ LinearMap.ker C ∧
      ∀ S : Submodule K V, (∀ x ∈ S, A x ∈ S) →
        S ≤ LinearMap.ker C → S ≤ unobservable K A C) ∧
  (∀ (K : Type u) [Field K] (V : Type v) (W : Type w)
      [AddCommGroup V] [Module K V] [FiniteDimensional K V] [AddCommGroup W] [Module K W]
      (A : V →ₗ[K] V) (C : V →ₗ[K] W),
    (Function.Injective (behavioralRecord K A C) ↔ unobservable K A C = ⊥) ∧
      (unobservable K A C = ⊥ ↔ Function.Injective (stackedObservability K A C))) ∧
  (∀ (K : Type u) [Field K] (V : Type v) (W : Type w)
      [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
      (A : V →ₗ[K] V) (C : V →ₗ[K] W),
    (∀ x : V, quotientRecord K A C ((unobservable K A C).mkQ x) = C x) ∧
      (∀ x : V, quotientAction K A C ((unobservable K A C).mkQ x) =
        (unobservable K A C).mkQ (A x)) ∧
      ∃! f : (V ⧸ unobservable K A C) →
          MinimalState (C : V → W) (fun _ : Unit => (A : V → V)),
        ∀ x : V, f ((unobservable K A C).mkQ x) =
          minimalRecord (C : V → W) (fun _ : Unit => (A : V → V)) x) ∧
  (∀ (K : Type u) [Field K] (V : Type v) (W : Type w)
      [AddCommGroup V] [Module K V] [FiniteDimensional K V] [AddCommGroup W] [Module K W]
      (A : V →ₗ[K] V) (C : V →ₗ[K] W) (x y : V),
    FutureEq (C : V → W) (fun _ : Unit => (A : V → V)) x y ↔
      x - y ∈ LinearMap.ker (stackedObservability K A C)) ∧
  (∀ (K : Type u) [Field K] (V : Type v) (W : Type w)
      [AddCommGroup V] [Module K V] [FiniteDimensional K V] [AddCommGroup W] [Module K W]
      (A : V →ₗ[K] V) (C : V →ₗ[K] W),
    Function.Injective (behavioralRecord K A C) ↔
      Module.finrank K (LinearMap.range (stackedObservability K A C)) = Module.finrank K V)

/-- The automata and control row holds, each clause by its theorem. -/
theorem automataControlGoal : AutomataControlGoal.{u, v, w, r} :=
  ⟨@AdmissibleObservation.futureEq_greatest, @AdmissibleObservation.futureEq_iff_all_adaptive,
    @AdmissibleObservation.actual_resolution_has_boundary_event,
    @KalmanObservability.futureEq_iff_sub_mem_unobservable,
    @KalmanObservability.unobservable_largest_invariant,
    @KalmanObservability.behavior_injective_iff,
    @KalmanObservability.unobservable_quotient_universal,
    @LinearObservability.behavioral_equiv_iff_mem_ker_obs,
    @LinearObservability.observable_iff_rank_eq⟩

/-! ## Zero-error coding: Witsenhausen's chromatic bound and its repetition invariance -/

open StochasticGraph in
/-- Theorem `thm:stochastic-side-records`, Example `ex:stochastic-cycle` and Proposition
`prop:full-support-repetition` in general form: zero-error decoding with a side record is a proper
coloring of the support-conflict graph, a side alphabet of `n` symbols exists exactly when the
graph is `n`-colorable and exactly when its chromatic number is at most `n`, a deterministic
reading has the confusability graph, the five-cycle needs three symbols, and positive finite
repetition of a nonnegative reading leaves the graph unchanged. -/
def ZeroErrorCodingGoal : Prop :=
  (∀ (X : Type u) (Y : Type v) (V : Type w) (C : Type r) [Nonempty V]
      (K : X → Y → ℝ) (P : X → V) (side : X → C),
    (∃ d, Decodes K P side d) ↔
      ∀ ⦃x x'⦄, (conflictGraph K P).Adj x x' → side x ≠ side x') ∧
  (∀ (X : Type u) (Y : Type v) (V : Type w) [Nonempty V] (K : X → Y → ℝ) (P : X → V) (n : ℕ),
    (conflictGraph K P).Colorable n ↔ ∃ side : X → Fin n, ∃ d, Decodes K P side d) ∧
  (∀ (X : Type u) (Y : Type v) (V : Type w) [Nonempty V] (K : X → Y → ℝ) (P : X → V) (n : ℕ),
    (conflictGraph K P).chromaticNumber ≤ n ↔ ∃ side : X → Fin n, ∃ d, Decodes K P side d) ∧
  (∀ (X : Type u) (Y : Type v) (V : Type w) [Fintype Y] [DecidableEq Y] (q : X → Y) (P : X → V),
    conflictGraph (deterministic q).prob P =
      OperatorKO7.Meta.OperationalInexpressibility.Confusability.confusabilityGraph q P) ∧
  (∀ x y : Fin 5, (conflictGraph cycleChannel.prob id).Adj x y ↔ cycleAdjacent x y) ∧
  (¬ ∃ side : Fin 5 → Fin 2, ∃ d, Decodes cycleChannel.prob id side d) ∧
  (∃ side : Fin 5 → Fin 3, ∃ d, Decodes cycleChannel.prob id side d) ∧
  (∀ (X : Type u) (Y : Type v) (V : Type w) (K : X → Y → ℝ), (∀ x y, 0 ≤ K x y) →
    ∀ (P : X → V) (N : ℕ), conflictGraph (repeated K (N + 1)) P = conflictGraph K P) ∧
  (∀ (X : Type u) (Y : Type v) (V : Type w) (C : Type r) [Nonempty V] (K : X → Y → ℝ),
    (∀ x y, 0 ≤ K x y) → ∀ (P : X → V) (side : X → C) (N : ℕ),
      (∃ d, Decodes (repeated K (N + 1)) P side d) ↔ (∃ d, Decodes K P side d)) ∧
  (∀ (X : Type u) (Y : Type v) (V : Type w) (C : Type r) [Nonempty V]
      (K : X → Y → ℝ) (P : X → V) (side : X → C),
    (∃ d, Decodes (repeated K 0) P side d) ↔ ∀ x x', side x = side x' → P x = P x') ∧
  (∀ (X : Type u) (Y : Type v) (V : Type w) [Fintype Y] (K : Channel X Y) (P : X → V) (N : ℕ),
    conflictGraph (repeatedChannel K (N + 1)).prob P = conflictGraph K.prob P) ∧
  (∀ (X : Type u) (Y : Type v) (V : Type w) [Nonempty Y] (K : X → Y → ℝ), (∀ x y, 0 < K x y) →
    ∀ (P : X → V) (x x' : X), (conflictGraph K P).Adj x x' ↔ P x ≠ P x')

/-- The zero-error coding row holds, each clause by its theorem. -/
theorem zeroErrorCodingGoal : ZeroErrorCodingGoal.{u, v, w, r} :=
  ⟨@StochasticGraph.decoder_iff_coloring, @StochasticGraph.colorable_iff_decoder,
    @StochasticGraph.chromaticNumber_le_iff_decoder, @StochasticGraph.deterministic_graph,
    StochasticGraph.cycle_graph, StochasticGraph.cycle_no_binary_decoder,
    StochasticGraph.cycle_ternary_decoder, @StochasticGraph.repeated_conflictGraph_eq,
    @StochasticGraph.repeated_decoder_iff, @StochasticGraph.repeated_zero_decoder_iff,
    @StochasticGraph.repeatedChannel_conflictGraph_eq,
    @StochasticGraph.full_support_conflictGraph_adj⟩

/-! ## Computability: Rice's theorem and the bounded records -/

open RiceBoundary UniversalObservation.Completion UniversalObservation.Demand in
/-- Theorem `thm:rice` and Proposition `prop:m44-bounded-records`: an extensional test is
computable exactly when it is constant; every bounded record has a merged pair for a nontrivial
extensional test, with discrimination zero for every record-determined reading and zero
information for every record-determined protocol; no computable code map shifts an extensional
test by a fixed-point-free map; halting is the union of the bounded records, semi-decidable with a
complement that is not; the union of the bounded records determines the semantics and each record
is finer than it; a fixed budget returns no output at its own input, and no classifier of the
fixed-budget record decides the bounded halting status. -/
def ComputabilityGoal : Prop :=
  (∀ (P : Nat.Partrec.Code → Bool), (∀ c c', c.eval = c'.eval → P c = P c') →
    (ComputablePred (fun c => P c = true) ↔ (∀ c, P c = true) ∨ (∀ c, P c = false))) ∧
  (∀ (P : Nat.Partrec.Code → Bool), (∀ c c', c.eval = c'.eval → P c = P c') →
    (ComputablePred (fun c => P c = true) ↔ ∃ v : Bool, ∀ c, P c = v)) ∧
  (∀ (P : Nat.Partrec.Code → Bool), (∀ c c', c.eval = c'.eval → P c = P c') →
    ¬ ((∀ c, P c = true) ∨ (∀ c, P c = false)) → ∀ b : ℕ,
      ∃ cPos cNeg : Nat.Partrec.Code,
        P cPos = true ∧ P cNeg = false ∧ boundedRecord b cPos = boundedRecord b cNeg) ∧
  (∀ (P : Nat.Partrec.Code → Bool), (∀ c c', c.eval = c'.eval → P c = P c') →
    ¬ ((∀ c, P c = true) ∨ (∀ c, P c = false)) → ∀ b : ℕ,
      ∃ cPos cNeg : Nat.Partrec.Code,
        P cPos = true ∧ P cNeg = false ∧
        boundedRecord b cPos = boundedRecord b cNeg ∧
        ∀ (Y : Type) [Fintype Y] (K : BoundaryPole.Reading Nat.Partrec.Code Y),
          BoundaryPole.RecordDetermined (boundedRecord b) K →
            BoundaryPole.readingDiscrimination K cPos cNeg = 0) ∧
  (∀ (b : ℕ) (cPos cNeg : Nat.Partrec.Code), cPos ≠ cNeg →
    boundedRecord b cPos = boundedRecord b cNeg →
    ∀ (A Y : Type) [Fintype A] [Fintype Y] (p : ProtocolResolution.FiniteProtocol Bool A Y)
      (K : List (A × Y) → A → BoundaryPole.Reading Nat.Partrec.Code Y),
      (∀ h a, BoundaryPole.RecordDetermined (boundedRecord b) (K h a)) →
      (∀ h a v, p.observation h a v = K h a (BoundaryPole.pairState cPos cNeg v)) →
      (∀ n bank, ProtocolResolution.HistoryBank n bank →
          ProtocolResolution.terminalMI p n bank = 0) ∧
        ProtocolResolution.informationLimit p = 0) ∧
  (∀ (n : Nat.Partrec.Code → Nat.Partrec.Code), Computable n →
    (∃ e : Nat.Partrec.Code, (n e).eval = e.eval) ∧
      ∀ (P : Nat.Partrec.Code → Bool),
        (∀ c c', c.eval = c'.eval → P c = P c') →
          ∀ (j : Bool → Bool), (∀ v, j v ≠ v) → ¬ ∀ c, P (n c) = j (P c)) ∧
  (({c : Nat.Partrec.Code | (c.eval 0).Dom} =
      ⋃ b : ℕ, {c : Nat.Partrec.Code |
        boundedRecord b c ⟨0, Nat.zero_lt_succ b⟩ ≠ none}) ∧
    (∀ b : ℕ, Nonempty (DecidablePred
      (fun c : Nat.Partrec.Code => boundedRecord b c ⟨0, Nat.zero_lt_succ b⟩ ≠ none))) ∧
    REPred (fun c : Nat.Partrec.Code => (c.eval 0).Dom) ∧
    ¬ REPred (fun c : Nat.Partrec.Code => ¬ (c.eval 0).Dom) ∧
    (∀ R : Nat.Partrec.Code → Prop, ComputablePred R ↔ REPred R ∧ REPred (fun c => ¬ R c))) ∧
  (∀ (c c' : Nat.Partrec.Code), (∀ b, boundedRecord b c = boundedRecord b c') →
    c.eval = c'.eval) ∧
  (∃ c c' : Nat.Partrec.Code, c.eval = c'.eval ∧ ∃ b, boundedRecord b c ≠ boundedRecord b c') ∧
  (∀ (budget : ℕ) (c : Nat.Partrec.Code), Nat.Partrec.Code.evaln budget c budget = none) ∧
  (∀ budget : ℕ, ∃ (cSuccess cFailure : Nat.Partrec.Code),
    Good (boundedHaltingSourceAt cSuccess budget).problem Set.univ ∧
      ¬ Good (boundedHaltingSourceAt cFailure budget).problem Set.univ ∧
      Nat.Partrec.Code.evaln budget cSuccess budget = none ∧
      Nat.Partrec.Code.evaln budget cFailure budget = none) ∧
  (∀ budget : ℕ, ¬ ∃ classify : Option ℕ → Bool, ∀ c : Nat.Partrec.Code,
    (classify (Nat.Partrec.Code.evaln budget c budget) = true ↔
      Good (boundedHaltingSourceAt c budget).problem Set.univ))

/-- The computability row holds, each clause by its theorem. -/
theorem computabilityGoal : ComputabilityGoal :=
  ⟨RiceBoundary.rice_computable_iff_constant, RiceBoundary.extensional_computable_iff_const,
    RiceBoundary.bounded_record_merged_pair, RiceBoundary.bounded_record_pole,
    @RiceBoundary.bounded_record_protocol_pole, RiceBoundary.no_fixed_point_free_code_map,
    RiceBoundary.halting_one_sided, RiceBoundary.bounded_records_union_determines_eval,
    RiceBoundary.bounded_records_finer_than_eval,
    UniversalObservation.Completion.evaln_input_budget_none,
    UniversalObservation.Completion.finite_budget_same_record_opposite_statuses,
    UniversalObservation.Completion.no_uniform_fixed_budget_record_classifier⟩

/-! ## Self-reference: the three-valued self-input and the randomized readouts -/

open PartialSelfEvaluation SelfEvaluationBounds in
/-- Theorem `thm:partial-self-evaluation` and Proposition `prop:readouts`: a three-valued
evaluator with a negation code evaluates the self-input to `none`, the one fixed point of
negation; the witness evaluator is not constant; no total Boolean readout preserves negation; a
randomized readout preserves negation in law exactly when it returns `none` as a fair coin and
keeps the definite values complementary, the readout kernels and the readout probabilities
correspond one to one, and the fair readout is the one readout that preserves negation in law and
reads definite values exactly. -/
def SelfReferenceGoal : Prop :=
  (∀ (C : Type u) (eval : C → C → Option Bool) (negCode : C → C),
    (∀ c x, eval (negCode c) x = negate (eval c x)) → ∀ (s : C), (∀ c, eval s c = eval c c) →
      eval s (negCode s) = none ∧ eval (negCode s) (negCode s) = none) ∧
  (∀ v : Option Bool, negate v = v ↔ v = none) ∧
  ((∀ c x, witnessEval (!c) x = negate (witnessEval c x)) ∧
    (∀ c, witnessEval false c = witnessEval c c) ∧
    witnessEval false false = some true ∧ witnessEval true false = some false ∧
    witnessEval false true = none) ∧
  (¬ ∃ h : Option Bool → Bool, ∀ v, h (negate v) = !(h v)) ∧
  ((∀ p : ReadoutProbability, (p : ℝ) = 1 - (p : ℝ) ↔ (p : ℝ) = 1 / 2) ∧
    (∀ p : Option Bool → ReadoutProbability,
      (∀ v b, (realReadoutKernel p).mass (negate v) (!b) =
        (realReadoutKernel p).mass v b) ↔
      (p none : ℝ) = 1 / 2 ∧
        (p (some true) : ℝ) = 1 - (p (some false) : ℝ)) ∧
    (∀ v b, (realReadoutKernel realFairReadout).mass (negate v) (!b) =
      (realReadoutKernel realFairReadout).mass v b) ∧
    (¬ ∃ h : Option Bool → Bool, ∀ v, h (negate v) = !(h v))) ∧
  (∀ (K : RealBooleanReadoutKernel) (v : Option Bool) (b : Bool),
    (realReadoutKernel (realReadoutProbabilityOfKernel K)).mass v b = K.mass v b) ∧
  (∀ p : Option Bool → ReadoutProbability,
    realReadoutProbabilityOfKernel (realReadoutKernel p) = p) ∧
  (∀ p : Option Bool → ReadoutProbability,
    (∀ v, (p (negate v) : ℝ) = 1 - (p v : ℝ)) →
    (∀ b : Bool, (p (some b) : ℝ) = if b then 1 else 0) → p = realFairReadout) ∧
  constantHalfRealReadout ≠ realFairReadout

/-- The self-reference row holds, each clause by its theorem. -/
theorem selfReferenceGoal : SelfReferenceGoal.{u} :=
  ⟨@PartialSelfEvaluation.self_evaluation_forces_none, PartialSelfEvaluation.negate_fixed_iff,
    PartialSelfEvaluation.nonconstant_completion, PartialSelfEvaluation.no_total_boolean_readout,
    SelfEvaluationBounds.real_readouts_full, SelfEvaluationBounds.realReadoutKernel_recovers,
    SelfEvaluationBounds.realReadoutProbabilityOfKernel_recovers,
    SelfEvaluationBounds.realFairReadout_unique_of_definite_and_negation,
    SelfEvaluationBounds.constantHalf_ne_realFairReadout⟩

/-! ## Common causes: tables with an observer, Boole's conditions and Fine's theorem -/

open FourTestTables PitowskyPolytope in
/-- Theorem `thm:observer-tables` and Proposition `prop:symbol`: a table with an observer
satisfies the cycle inequality and has CHSH score at most two in absolute value; a table with
rates in `[0, 1]` has an observer exactly when it satisfies the cycle inequality (Fine's theorem);
the score is four minus four times the refused mass, and a table with an observer refuses at
least one half; a correlation vector lies in the convex hull of the eight deterministic
correlation vectors exactly when it lies in the box and satisfies the eight cycle inequalities. -/
def CommonCausesGoal : Prop :=
  (∀ d : Table, HasObserver d → CycleIneq d 1) ∧
  (∀ d : Table, HasObserver d → |score d| ≤ 2) ∧
  (∀ d : Table, (∀ x y, 0 ≤ d x y ∧ d x y ≤ 1) → (HasObserver d ↔ CycleIneq d 1)) ∧
  (∀ d : Table, score d = 4 - 4 * (refused0 d + refused1 d)) ∧
  (∀ d : Table, HasObserver d → 1 / 2 ≤ refused0 d + refused1 d) ∧
  (∀ d : Table, (∀ x y, 0 ≤ d x y ∧ d x y ≤ 1) → CycleIneq d 1 → HasObserver d) ∧
  (∀ E : Bool × Bool → ℝ,
    E ∈ convexHull ℝ (Set.range (fun ab : (Bool → Bool) × (Bool → Bool) =>
      deterministicCorrelation ab.1 ab.2)) ↔ InBox E ∧ CycleIneqE E)

/-- The common-causes row holds, each clause by its theorem. -/
theorem commonCausesGoal : CommonCausesGoal :=
  ⟨@FourTestTables.observer_cycleIneq, @FourTestTables.observer_abs_score_le_two,
    ObserverRealization.hasObserver_iff_cycle, FourTestTables.score_eq_refused,
    @FourTestTables.observer_refused_ge_half, PitowskyPolytope.fine_theorem,
    PitowskyPolytope.mem_correlationPolytope_iff⟩

/-! ## Rewriting: the fork of the equality test, its contextual closure and the orientation -/

open OperatorKO7 Trace OperatorKO7.Meta.DistinctionBoundary.ContextualDiagonalScope
  OperatorKO7.Meta.BoundaryGeneral.HomomorphicInexpressibility
  OperatorKO7.Meta.SafeStep.SigmaFreeAlgebra OperatorKO7.Meta.SafeStep.HomomorphicGuardBarrier in
/-- Theorems `thm:fork` and `thm:object` and Proposition `prop:orientation`: `eqW void void` has two
root reducts with no common reduct, the reflexive equality test is the one root obstruction to
local joinability, the root reducts of `eqW a b` are the merge and, at `a = b`, the void; in the
contextual closure `eqW void void` has four reducts and two normal forms, the diagonal at a delta
term joins, and the diagonal joins exactly when its argument reaches a delta term; an algebra
homomorphism that fixes the truth value and breaks a binary predicate at a pair shows that no
term defines the predicate, and the variable collapse of the seven-constructor calculus shows
that no term defines disequality. -/
def RewritingGoal : Prop :=
  (Step (eqW void void) void ∧ Step (eqW void void) (integrate (merge void void))) ∧
  (¬ ∃ d, StepStar void d ∧ StepStar (integrate (merge void void)) d) ∧
  (∀ a : Trace, ¬ MetaSN_KO7.LocalJoinStep a ↔
    OperatorKO7.Meta.DistinctionBoundary.CriticalPairCompleteness.IsEqWDiagonal a) ∧
  (∀ a b t : Trace, Step (eqW a b) t ↔ (t = integrate (merge a b) ∨ (a = b ∧ t = void))) ∧
  (∀ t : Trace, Relation.ReflTransGen MetaSN_KO7.StepCtxFull (eqW void void) t ↔
    (t = eqW void void ∨ t = void ∨ t = integrate (merge void void) ∨ t = integrate void)) ∧
  (∀ t : Trace, (Relation.ReflTransGen MetaSN_KO7.StepCtxFull (eqW void void) t ∧
      ∀ u, ¬ MetaSN_KO7.StepCtxFull t u) ↔ (t = void ∨ t = integrate void)) ∧
  (∀ t : Trace, ∃ d, CtxStar void d ∧ CtxStar (integrate (merge (delta t) (delta t))) d) ∧
  ((¬ ∃ d, CtxStar void d ∧ CtxStar (integrate (merge void void)) d) ∧
    (∀ t : Trace,
      ∃ d, CtxStar void d ∧ CtxStar (integrate (merge (delta t) (delta t))) d)) ∧
  (∀ a : Trace,
    OperatorKO7.Meta.DistinctionBoundary.ContextualClassification.JoinCtx void
        (integrate (merge a a)) ↔ ∃ t, CtxStar a (delta t)) ∧
  (∀ (S : FinitarySignature.{u}) (A : FinitaryAlgebra.{u, v} S) (truth : A.Carrier)
      (P : A.Carrier → A.Carrier → Prop) (h : AlgebraHom A A),
    h.toFun truth = truth → ∀ (a b : A.Carrier), P a b → ¬ P (h.toFun a) (h.toFun b) →
      ¬ TermDefinesBinaryPredicate A truth P) ∧
  ko7VariableCollapseHom.toFun ko7PositiveTruth = ko7PositiveTruth ∧
  ko7VariableCollapseHom.toFun SigmaTerm.varA = ko7VariableCollapseHom.toFun SigmaTerm.varB ∧
  (¬ ∃ t : FreeTerm ko7Signature BinaryVar, ∀ a b : SigmaTerm,
    FreeTerm.eval ko7SigmaAlgebra (binaryVal a b) t = ko7PositiveTruth ↔ a ≠ b)

/-- The rewriting row holds, each clause by its theorem. -/
theorem rewritingGoal : RewritingGoal.{u, v} :=
  ⟨OperatorKO7.Meta.SafeStep.EqWVoidAnomaly.eqW_void_void_admits_two_normal_forms,
    OperatorKO7.Meta.SafeStep.EqWVoidAnomaly.eqW_void_void_normal_forms_are_unjoinable,
    OperatorKO7.Meta.DistinctionBoundary.CriticalPairCompleteness.eqW_diagonal_is_the_unique_root_obstruction,
    KernelCases.eqW_root_reducts, KernelCases.eqW_void_void_ctx_reducts,
    KernelCases.eqW_void_void_ctx_normal_forms,
    OperatorKO7.Meta.DistinctionBoundary.ContextualDiagonalScope.eqW_delta_diagonal_ctx_joinable,
    OperatorKO7.Meta.DistinctionBoundary.ContextualDiagonalScope.contextual_fracture_scope,
    OperatorKO7.Meta.DistinctionBoundary.ContextualClassification.diagonal_ctx_joins_iff_reaches_delta,
    @OperatorKO7.Meta.BoundaryGeneral.HomomorphicInexpressibility.predicate_not_termDefinable_of_hom_collapse,
    OperatorKO7.Meta.SafeStep.HomomorphicGuardBarrier.ko7VariableCollapseHom_fixes_positiveTruth,
    OperatorKO7.Meta.SafeStep.HomomorphicGuardBarrier.ko7VariableCollapseHom_identifies_variables,
    OperatorKO7.Meta.SafeStep.HomomorphicGuardBarrier.ko7_sevenConstructor_disequality_not_termDefinable⟩

/-! ## Identity: the relation distinct, the self-test and the complement of content and place -/

open OperatorKO7.Meta.OperationalInexpressibility.LicenseStabilizer in
/-- Theorem `thm:pair`(3) and Propositions `prop:self-test` and `prop:complement`: no Boolean
combination of invariant tests at the two states defines the relation distinct; a binary map is
invariant under the invisible group exactly when it depends on the records and on equality; the
point stabilizer acts transitively on the other points, and a test is invariant under it exactly
when it is constant off the point; the self-test on `n` labels captures one bit, and the whole
fiber entropy, exactly when `n = 2`; content and place form an injective pair, every content meets
every place in exactly one occurrence, the two kernels generate the total relation, and two
occurrences are equal, share the content at distinct places, or differ in content. -/
def IdentityGoal : Prop :=
  (∀ (X : Type u) [DecidableEq X] (x₀ x₁ : X), x₀ ≠ x₁ → ∀ (ι : Type v) (f : ι → X → Bool),
    (∀ i a, f i (Equiv.swap x₀ x₁ a) = f i a) → ∀ (g : (ι → Bool) → (ι → Bool) → Prop),
      ¬ ∀ a ∈ ({x₀, x₁} : Set X), ∀ b ∈ ({x₀, x₁} : Set X),
        (g (fun i => f i a) (fun i => f i b) ↔ a ≠ b)) ∧
  (∀ (X : Type u) (Q : Type v) (V : Type w) (q : X → Q) (F : X → X → V),
    (∀ σ ∈ licenseStabilizer q, ∀ a a', F (σ a) (σ a') = F a a') ↔
      (∀ a a' b b', q a = q b → q a' = q b' → (a = a' ↔ b = b') → F a a' = F b b')) ∧
  (∀ (C : Type u) (x a b : C), a ≠ x → b ≠ x → ∃ σ : Equiv.Perm C, σ x = x ∧ σ a = b) ∧
  (∀ (C : Type u) (x : C) (f : C → Bool),
    (∀ σ : Equiv.Perm C, σ x = x → ∀ c, f (σ c) = f c) ↔ ∀ a b, a ≠ x → b ≠ x → f a = f b) ∧
  (∀ n : ℕ, 2 ≤ n → Real.log n =
    Real.binEntropy (1 / (n : ℝ)) + (((n : ℝ) - 1) / n) * Real.log ((n : ℝ) - 1)) ∧
  (∀ n : ℕ, Real.binEntropy (1 / (n : ℝ)) = Real.log 2 ↔ n = 2) ∧
  (∀ n : ℕ, 2 ≤ n → (Real.binEntropy (1 / (n : ℝ)) = Real.log n ↔ n = 2)) ∧
  (∀ n : ℕ, 2 ≤ n → (Real.binEntropy (1 / (n : ℝ)) / Real.log 2 = Real.logb 2 n ↔ n = 2)) ∧
  (∀ (Y : Type u) (R : Type v), Function.Injective (fun o : Y × R => (o.1, o.2))) ∧
  (∀ (Y : Type u) (R : Type v) (o o' : Y × R), ∃ o'' : Y × R, o''.2 = o.2 ∧ o''.1 = o'.1) ∧
  (∀ (Y : Type u) (R : Type v),
    Relation.TransGen (fun a b : Y × R => a.1 = b.1 ∨ a.2 = b.2) = (fun _ _ => True)) ∧
  (∀ (Y : Type u) (R : Type v) (y : Y) (r : R), ∃! o : Y × R, o.1 = y ∧ o.2 = r) ∧
  (∀ (Y : Type u) (R : Type v) (o o' : Y × R),
    o = o' ∨ (o.1 = o'.1 ∧ o.2 ≠ o'.2) ∨ o.1 ≠ o'.1)

/-- The identity row holds, each clause by its theorem. -/
theorem identityGoal : IdentityGoal.{u, v, w} :=
  ⟨@MergedPair.distinct_not_from_invariant_tests, @PairInvariants.pair_invariant_iff,
    @PairInvariants.point_stabilizer_transitive, @PairInvariants.point_stabilizer_invariant_iff,
    BitDivision.log_eq_binEntropy_add, BitDivision.selfTest_one_bit_iff,
    BitDivision.selfTest_entropy_eq_log_iff, BitDivision.selfTest_bits_eq_logb_iff,
    PlaceCoordinates.content_place_injective, @PlaceCoordinates.content_place_join,
    @PlaceCoordinates.content_place_kernel_union_transGen_eq_total,
    @PlaceCoordinates.content_class_meets_place_class,
    @PlaceCoordinates.occurrence_trichotomy⟩

/-! ## The general theorems -/

open ProtocolResolution in
/-- Theorem `thm:pair-resolution-sharp`(iv), the deterministic end: for every `c` in `[0, 1]` a
seeded protocol with one perfect reading acquires `c` bits at expected cost `c`, and every
conditional protocol with binary outputs and readings of cost at least one acquires at most its
expected cost in bits. -/
def SeedFrontierGoal : Prop :=
  ∀ c : ℝ, 0 ≤ c → c ≤ 1 →
    (∃ p : ConditionalProtocol Bool Bool Unit Bool,
      (∀ u z, p.initialJoint.mass (u, z) = p.initialRecord.mass u * binaryPrior (1 / 2) z) ∧
      (∀ u h a z y, ((p.given u).observation h a z).mass y = if y = z then 1 else 0) ∧
      (∀ u h a, (p.given u).cost h a = 1) ∧
      conditionalMI p 1 (historyBank Unit Bool 1) = c ∧
      conditionalExpectedCost p 1 (historyBank Unit Bool 1) = c) ∧
    (∀ (H0 Z A : Type) [Fintype H0] [Fintype Z] [Fintype A]
      (p : ConditionalProtocol H0 Z A Bool),
      (∀ u, 0 < p.initialRecord.mass u → ∀ h a, 1 ≤ (p.given u).cost h a) →
      ∀ (n : ℕ) (bank : List (List (A × Bool))), HistoryBank n bank →
        conditionalMI p n bank ≤ conditionalExpectedCost p n bank)

/-- The seed frontier holds by `seed_frontier`. -/
theorem seedFrontierGoal : SeedFrontierGoal := SeedFrontier.seed_frontier

open PlaceOrbitGeneral OperatorKO7.Meta.OperationalInexpressibility.LicenseStabilizer in
/-- Theorem `thm:place`(ii) and Remark `rem:landau`, the general form: for every observer and every
alphabet family the place families form one free orbit of the invisible group, each family with
the record is a bijection onto the dependent pairs, the identity family exists, and a common
alphabet on fibers of unequal size gives two orbits. -/
def PlaceOrbitGeneralGoal : Prop :=
  (∀ (X : Type u) (Q : Type v) (q : X → Q) (A : Set.range q → Type w)
      (σ : licenseStabilizer q) (f : PlaceFamily q A), σ • f = f → σ = 1) ∧
  (∀ (X : Type u) (Q : Type v) (q : X → Q) (A : Set.range q → Type w)
      (f g : PlaceFamily q A), ∃! σ : licenseStabilizer q, σ • f = g) ∧
  (∀ (X : Type u) (Q : Type v) (q : X → Q) (A : Set.range q → Type w) (f : PlaceFamily q A),
    Function.Bijective (fun x : X =>
      (⟨Set.rangeFactorization q x, f (Set.rangeFactorization q x) ⟨x, rfl⟩⟩ :
        Σ y : Set.range q, A y))) ∧
  (∀ (X : Type u) (Q : Type v) (q : X → Q),
    ∃ f : PlaceFamily q (ObserverFiber q),
      Function.Bijective (fun x : X =>
        (⟨Set.rangeFactorization q x, f (Set.rangeFactorization q x) ⟨x, rfl⟩⟩ :
          Σ y : Set.range q, ObserverFiber q y))) ∧
  (∀ q : Fin 3 → Bool, q 0 = false → q 1 = false → q 2 = true →
    ∃ p p' : Fin 3 → Fin 2,
      Function.Injective (fun x => (q x, p x)) ∧ Function.Injective (fun x => (q x, p' x)) ∧
        ¬ ∃ σ ∈ licenseStabilizer q, p' = p ∘ σ.symm)

/-- The general place orbit holds, each clause by its theorem. -/
theorem placeOrbitGeneralGoal : PlaceOrbitGeneralGoal.{u, v, w} :=
  ⟨@PlaceOrbitGeneral.placeFamily_free, @PlaceOrbitGeneral.placeFamily_exists_unique,
    @PlaceOrbitGeneral.placeFamily_joint_bijective, @PlaceOrbitGeneral.placeFamily_self,
    PlaceOrbitGeneral.common_alphabet_two_orbits⟩

open InstrumentLoss InstrumentComposition NoReturn in
/-- Section `sec:extensions`, the instrument laws: a sequential instrument is recoverable exactly
when its first stage is, given recoverable second stages; equal joint laws persist under
composition; the instrument that keeps the state has an injective retained output; and the
instrument that moves to a chosen state gives two states one retained pair exactly when they have
one record. -/
def InstrumentGoal : Prop :=
  (∀ (X : Type u) (Y : Type v) (Z : Type w) (W : Type r) (T : Type s) [Nonempty X]
      [Fintype Y] [Fintype Z] [Fintype W] [Fintype T]
      (I : StochasticInstrument X Y Z) (J : Y → StochasticInstrument Z W T),
    (∀ y, StochasticRecoverable (J y)) →
      (StochasticRecoverable (sequential I J) ↔ StochasticRecoverable I)) ∧
  (∀ (X : Type u) (Y : Type v) (Z : Type w) (W : Type r) (T : Type s)
      [Fintype Y] [Fintype Z] [Fintype W] [Fintype T]
      (I : StochasticInstrument X Y Z) (J : Y → StochasticInstrument Z W T) (x x' : X),
    (∀ y z, I.weight x y z = I.weight x' y z) →
      ∀ yw t, (sequential I J).weight x yw t = (sequential I J).weight x' yw t) ∧
  (∀ (X : Type u) (Q : Type v) (q : X → Q), Function.Injective (fun x => (q x, x))) ∧
  (∀ (X : Type u) (Q : Type v) (q : X → Q) (c : Set.range q → X) (x x' : X),
    (q x, recordChoice q c x) = (q x', recordChoice q c x') ↔ q x = q x')

/-- The instrument laws hold, each clause by its theorem. -/
theorem instrumentGoal : InstrumentGoal.{u, v, w, r, s} :=
  ⟨@InstrumentComposition.sequential_recoverable_iff,
    @InstrumentComposition.equal_joint_laws_persist,
    @NoReturn.nondisturbing_joint_injective, @NoReturn.recordChoice_joint_eq_iff⟩

open ProtocolResolution BoundarySingularity in
/-- Perfect secrecy for general message sets: every pair of messages has discrimination zero
exactly when the ciphertext rows are equal; equal rows give zero information under every prior;
and zero information under a prior of full support gives equal rows. -/
def SecrecyGeneralGoal : Prop :=
  (∀ (M C : Type) [Fintype C] (E : M → FiniteLaw C),
    (∀ m m', discrimination (E m).mass (E m').mass = 0) ↔
      ∀ m m' c, (E m).mass c = (E m').mass c) ∧
  (∀ (Z C : Type) [Fintype Z] [Fintype C] (q : Z → ℝ), ∑ z, q z = 1 →
    ∀ (K : Z → FiniteLaw C), (∀ z z' c, (K z).mass c = (K z').mass c) → Z →
      jointMI (fun zc : Z × C => q zc.1 * (K zc.1).mass zc.2) = 0) ∧
  (∀ (Z C : Type) [Fintype Z] [Fintype C] (q : Z → ℝ), (∀ z, 0 < q z) → ∑ z, q z = 1 →
    ∀ (K : Z → FiniteLaw C), jointMI (fun zc : Z × C => q zc.1 * (K zc.1).mass zc.2) = 0 →
      ∀ z z' c, (K z).mass c = (K z').mass c)

/-- Secrecy for general messages holds, each clause by its theorem. -/
theorem secrecyGeneralGoal : SecrecyGeneralGoal :=
  ⟨@SecrecyGeneralMessages.zero_discrimination_iff_equal_rows,
    @SecrecyGeneralMessages.zero_information_of_equal_rows,
    @SecrecyGeneralMessages.equal_rows_of_zero_information_of_pos⟩

/-! ## The full Boundary Theorem -/

/-- The full Boundary Theorem: the twenty-four core clauses, the recursion clause on every
carrier, Tarski undefinability with the Godel pair separator, the instance theorems of the eight
rows of Table `tab:readings` outside the core, the seed frontier, the boundary as the set of
infinite resolution cost, the free orbit of place families, the Landau dictionary, the
instrument laws and secrecy for general messages. -/
def BoundaryTheoremFullGoal : Prop :=
  BoundaryTheorem.BoundaryTheoremCoreGoal.{u} ∧
    CountedPassInformation.AllCarrierRecursionGoal.{u} ∧
    OperatorKO7.Meta.DistinctionBoundary.GodelArith.TarskiGoal ∧
    LinearAlgebraGoal ∧ AutomataControlGoal.{u, v, w, r} ∧ ZeroErrorCodingGoal.{u, v, w, r} ∧
    ComputabilityGoal ∧ SelfReferenceGoal.{u} ∧ CommonCausesGoal ∧ RewritingGoal.{u, v} ∧
    IdentityGoal.{u, v, w} ∧ SeedFrontierGoal ∧ BoundaryInfiniteCost.BoundaryInfiniteCostGoal ∧
    PlaceOrbitGeneralGoal.{u, v, w} ∧ LandauDictionary.LandauDictionaryGoal.{u, v, w} ∧
    InstrumentGoal.{u, v, w, r, s} ∧ SecrecyGeneralGoal

/-- The full Boundary Theorem holds, every conjunct with its accepted proof. -/
theorem boundaryTheoremFullGoal : BoundaryTheoremFullGoal.{u, v, w, r, s} :=
  ⟨BoundaryTheorem.boundaryTheoremCoreGoal.{u},
    CountedPassInformation.allCarrierRecursionGoal.{u},
    OperatorKO7.Meta.DistinctionBoundary.GodelArith.tarskiGoal,
    linearAlgebraGoal, automataControlGoal.{u, v, w, r}, zeroErrorCodingGoal.{u, v, w, r},
    computabilityGoal, selfReferenceGoal.{u}, commonCausesGoal, rewritingGoal.{u, v},
    identityGoal.{u, v, w}, seedFrontierGoal, BoundaryInfiniteCost.boundaryInfiniteCostGoal,
    placeOrbitGeneralGoal.{u, v, w}, LandauDictionary.landauDictionary.{u, v, w},
    instrumentGoal.{u, v, w, r, s}, secrecyGeneralGoal⟩

end

end OperatorKO7.Meta.BoundaryObserver.BoundaryTheoremFull
