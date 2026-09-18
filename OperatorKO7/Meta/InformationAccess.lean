import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Tactic
import OperatorKO7.Meta.InformationalIncompleteness.FiniteSupportEntropy

/-!
# Functional access predicates and a primitive-duplicator counting model

The first part defines accessibility by factorization through an observation function and proves
elementary consequences of that definition. The second part defines explicit arithmetic cost
functions and counts active `F` sites, `G` frames, and the live counter in canonical syntax trees.
The structural channel computes the frame count, the origin channel reads and subtracts the live
counter height from its initial height, and the clock channel reads an explicit bounded external
clock state. Each is proved extensionally equal to the progress coordinate. The final part gives the
uniform prior, deterministic channels, their Dirac posteriors, exact conditional entropy and mutual
information, and the least-width coding theorem.
-/

namespace OperatorKO7.InformationAccess

open scoped Real

universe uα uβ uγ uM uV uT

/-! ## Generic access-based layer -/

/-- `target` is directly accessible from `obs` when some decoder recovers it
from the observable state alone. -/
def AccessibleFrom {α : Type uα} {β : Type uβ} {γ : Type uγ}
    (obs : α → β) (target : α → γ) : Prop :=
  ∃ decode : β → γ, target = decode ∘ obs

/-- Generic meta/object access model. -/
structure MetaAccessModel (α : Type uα) (M : Type uM) (V : Type uV) (T : Type uT) where
  metaView : α → M
  verdict : α → V
  trace : Nat → α → T

namespace MetaAccessModel

variable {α : Type uα} {M : Type uM} {V : Type uV} {T : Type uT}

/-- The initial access point available to the meta layer. -/
def initialAccess (A : MetaAccessModel α M V T) : α → M × T :=
  fun x => (A.metaView x, A.trace 0 x)

/-- The stage-`k` access point available after sequential object computation. -/
def stageAccess (A : MetaAccessModel α M V T) (k : Nat) : α → M × T :=
  fun x => (A.metaView x, A.trace k x)

/-- A query is non-vacuous if the verdict is not already meta-accessible. -/
def NonvacuousMetaQuery (A : MetaAccessModel α M V T) : Prop :=
  ¬ AccessibleFrom A.metaView A.verdict

/-- Direct retrieval means the verdict is already available at the initial
access point. -/
def DirectRetrieval (A : MetaAccessModel α M V T) : Prop :=
  AccessibleFrom A.initialAccess A.verdict

/-- Sequential uncertainty reduction means the verdict is not directly
retrievable at the initial access point, but becomes retrievable at a later
stage. -/
def SequentialUncertaintyReduction
    (A : MetaAccessModel α M V T) (k : Nat) : Prop :=
  ¬ A.DirectRetrieval ∧ AccessibleFrom (A.stageAccess k) A.verdict

/-- Unfolding `NonvacuousMetaQuery` yields failure of factorization through `metaView`. -/
theorem information_seeking_character_of_nonvacuous_query
    (A : MetaAccessModel α M V T) :
    A.NonvacuousMetaQuery ↔ ¬ AccessibleFrom A.metaView A.verdict := by
  rfl

/-- If the verdict is meta-accessible already, then it is also directly
retrievable at the initial access point by ignoring the object component. -/
theorem meta_accessible_implies_directRetrieval
    (A : MetaAccessModel α M V T)
    (hmeta : AccessibleFrom A.metaView A.verdict) :
    A.DirectRetrieval := by
  rcases hmeta with ⟨decode, hdecode⟩
  refine ⟨fun mt => decode mt.1, ?_⟩
  funext x
  simp [initialAccess, hdecode, Function.comp]

/-- Direct retrieval is incompatible with sequential uncertainty reduction. -/
theorem directRetrieval_not_sequential_resolution
    (A : MetaAccessModel α M V T) (k : Nat) :
    A.DirectRetrieval → ¬ A.SequentialUncertaintyReduction k := by
  intro hdirect hseq
  exact hseq.1 hdirect

/-- Any sequential resolver is automatically non-vacuous at the pure meta
layer: otherwise the verdict would already be directly retrievable. -/
theorem sequential_resolution_implies_nonvacuous
    (A : MetaAccessModel α M V T) {k : Nat}
    (hseq : A.SequentialUncertaintyReduction k) :
    A.NonvacuousMetaQuery := by
  intro hmeta
  exact hseq.1 (A.meta_accessible_implies_directRetrieval hmeta)

/-- If the terminal trace state were itself meta-accessible, then the verdict
would already be directly retrievable. Hence sequential resolution forces the
terminal trace state to remain hidden from the meta layer alone. -/
theorem sequential_resolution_requires_hidden_terminal_state
    (A : MetaAccessModel α M V T) {k : Nat}
    (hseq : A.SequentialUncertaintyReduction k) :
    ¬ AccessibleFrom A.metaView (A.trace k) := by
  intro hterminal
  rcases hterminal with ⟨lift, hlift⟩
  rcases hseq.2 with ⟨decode, hdecode⟩
  have hmeta : AccessibleFrom A.metaView A.verdict := by
    refine ⟨fun m => decode (m, lift m), ?_⟩
    funext x
    simp [stageAccess, hlift, hdecode, Function.comp]
  exact hseq.1 (A.meta_accessible_implies_directRetrieval hmeta)

/-- A sequential-resolution witness supplies the terminal trace as an inaccessible statistic through
which the verdict factors together with `metaView`. -/
theorem sequential_resolution_requires_hidden_state
    (A : MetaAccessModel α M V T) {k : Nat}
    (hseq : A.SequentialUncertaintyReduction k) :
    ∃ φ : α → T,
      ¬ AccessibleFrom A.metaView φ
        ∧ AccessibleFrom (fun x => (A.metaView x, φ x)) A.verdict := by
  refine ⟨A.trace k, A.sequential_resolution_requires_hidden_terminal_state hseq, ?_⟩
  simpa using hseq.2

end MetaAccessModel

/-! ## Progress coordinate and channel costs -/

/-- The real-valued expression `logb 2 (K + 1)`. No distribution is represented in the type. -/
noncomputable def progressEntropyBits (K : Nat) : ℝ :=
  Real.logb 2 (K + 1 : ℝ)

/-- The arithmetic expression `Nat.clog 2 (K + 1)`. -/
def optimalRecoveryBits (K : Nat) : Nat :=
  Nat.clog 2 (K + 1)

/-- History observation cost model: storing the full prefix of `j + 1`
progress-bearing states with per-state payload width `atomWidth`. -/
def historyObservationBitCost (atomWidth j : Nat) : Nat :=
  atomWidth * ((j + 1) * (j + 2) / 2)

/-- Declared width of the structural-counting code. Its optimality is proved below by constructing
an injective binary code and proving the cardinal lower bound for every exact code. -/
def structuralCountingBitCost (K : Nat) : Nat :=
  optimalRecoveryBits K

/-- Declared width of the origin-comparison code. -/
def originComparisonBitCost (K : Nat) : Nat :=
  optimalRecoveryBits K

/-- Declared width of the parallel-clock code. -/
def parallelClockBitCost (K : Nat) : Nat :=
  optimalRecoveryBits K

@[simp] theorem progress_entropy_uniform (K : Nat) :
    progressEntropyBits K = Real.logb 2 (K + 1 : ℝ) := rfl

@[simp] theorem structural_counting_optimal (K : Nat) :
    structuralCountingBitCost K = optimalRecoveryBits K := rfl

@[simp] theorem origin_comparison_optimal (K : Nat) :
    originComparisonBitCost K = optimalRecoveryBits K := rfl

@[simp] theorem parallel_clocking_optimal (K : Nat) :
    parallelClockBitCost K = optimalRecoveryBits K := rfl

/-- Terminal history-observation cost is quadratic in the trace length in the
explicit prefix-storage model. -/
@[simp] theorem history_observation_terminal_cost (atomWidth K : Nat) :
    historyObservationBitCost atomWidth K =
      atomWidth * ((K + 1) * (K + 2) / 2) := rfl

/-- For positive payload width, the history-observation channel incurs at least
quadratic-over-linear growth in the terminal trace length. -/
theorem history_observation_quadratic_overcost
    (atomWidth K : Nat) (hwidth : 1 ≤ atomWidth) :
    (K * (K + 1)) / 2 ≤ historyObservationBitCost atomWidth K := by
  unfold historyObservationBitCost
  have hquad :
      (K * (K + 1)) / 2 ≤ ((K + 1) * (K + 2)) / 2 := by
    apply Nat.div_le_div_right
    nlinarith [Nat.zero_le K]
  have hscale :
      ((K + 1) * (K + 2)) / 2 ≤
        (((K + 1) * (K + 2)) / 2) * atomWidth := by
    simpa using Nat.mul_le_mul_left (((K + 1) * (K + 2)) / 2) hwidth
  calc
    (K * (K + 1)) / 2 ≤ ((K + 1) * (K + 2)) / 2 := hquad
    _ ≤ (((K + 1) * (K + 2)) / 2) * atomWidth := hscale
    _ = atomWidth * (((K + 1) * (K + 2)) / 2) := by ring

/-! ## Primitive duplicator syntax and terminal record -/

/-- Syntax used by the primitive-duplicator counting model. -/
inductive PrimitiveDuplicatorTerm
  | seedX
  | seedY
  | zero
  | succ : PrimitiveDuplicatorTerm → PrimitiveDuplicatorTerm
  | g : PrimitiveDuplicatorTerm → PrimitiveDuplicatorTerm → PrimitiveDuplicatorTerm
  | f : PrimitiveDuplicatorTerm → PrimitiveDuplicatorTerm → PrimitiveDuplicatorTerm → PrimitiveDuplicatorTerm
  deriving DecidableEq, Repr

namespace PrimitiveDuplicatorTerm

/-- Counter `S^K(0)`. -/
def counter : Nat → PrimitiveDuplicatorTerm
  | 0 => .zero
  | n + 1 => .succ (counter n)

/-- Left-nested `G`-stack `G^i(Y, t)`. -/
def gChain : Nat → PrimitiveDuplicatorTerm → PrimitiveDuplicatorTerm
  | 0, t => t
  | n + 1, t => .g .seedY (gChain n t)

/-- Canonical nonterminal stage
`G^i(Y, F(X,Y,S^{K-i}(0)))`. -/
def stage (K i : Nat) : PrimitiveDuplicatorTerm :=
  gChain i (.f .seedX .seedY (counter (K - i)))

/-- Terminal record map `R_K(X,Y) = G^K(Y,X)`. -/
def terminalRecordMap (K : Nat) : PrimitiveDuplicatorTerm :=
  gChain K .seedX

/-- Count active `F`-sites. -/
def activeFCount : PrimitiveDuplicatorTerm → Nat
  | .seedX => 0
  | .seedY => 0
  | .zero => 0
  | .succ t => activeFCount t
  | .g x y => activeFCount x + activeFCount y
  | .f x y z => activeFCount x + activeFCount y + activeFCount z + 1

/-- Count visible `G`-frames. -/
def gFrameCount : PrimitiveDuplicatorTerm → Nat
  | .seedX => 0
  | .seedY => 0
  | .zero => 0
  | .succ t => gFrameCount t
  | .g x y => gFrameCount x + gFrameCount y + 1
  | .f x y z => gFrameCount x + gFrameCount y + gFrameCount z

@[simp] theorem counter_zero : counter 0 = .zero := rfl

@[simp] theorem counter_succ (n : Nat) : counter (n + 1) = .succ (counter n) := rfl

@[simp] theorem activeFCount_counter (K : Nat) : activeFCount (counter K) = 0 := by
  induction K with
  | zero => rfl
  | succ K ih => simpa [counter, activeFCount] using ih

@[simp] theorem gFrameCount_counter (K : Nat) : gFrameCount (counter K) = 0 := by
  induction K with
  | zero => rfl
  | succ K ih => simpa [counter, gFrameCount] using ih

/-- Read the height of a pure successor counter, failing on non-counter syntax. -/
def counterHeight? : PrimitiveDuplicatorTerm → Option Nat
  | .zero => some 0
  | .succ t => (counterHeight? t).map Nat.succ
  | _ => none

@[simp] theorem counterHeight?_counter (K : Nat) : counterHeight? (counter K) = some K := by
  induction K with
  | zero => rfl
  | succ K ih => simp [counter, counterHeight?, ih]

/-- Read the counter from the unique active `F` site beneath the visible `G` frames. -/
def activeCounterHeight? : PrimitiveDuplicatorTerm → Option Nat
  | .f _ _ z => counterHeight? z
  | .g _ t => activeCounterHeight? t
  | _ => none

@[simp] theorem activeCounterHeight?_gChain (i : Nat) (t : PrimitiveDuplicatorTerm) :
    activeCounterHeight? (gChain i t) = activeCounterHeight? t := by
  induction i with
  | zero => rfl
  | succ i ih => simp [gChain, activeCounterHeight?, ih]

@[simp] theorem activeCounterHeight?_stage (K i : Nat) :
    activeCounterHeight? (stage K i) = some (K - i) := by
  simp [stage, activeCounterHeight?]

@[simp] theorem activeFCount_gChain (i : Nat) (t : PrimitiveDuplicatorTerm) :
    activeFCount (gChain i t) = activeFCount t := by
  induction i with
  | zero => rfl
  | succ i ih =>
      simp [gChain, activeFCount, ih]

@[simp] theorem gFrameCount_gChain (i : Nat) (t : PrimitiveDuplicatorTerm) :
    gFrameCount (gChain i t) = i + gFrameCount t := by
  induction i with
  | zero => simp [gChain]
  | succ i ih =>
      simp [gChain, gFrameCount, ih, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/-- Along every nonterminal canonical stage there is exactly one active `F`-site. -/
theorem live_computation_channel_unique (K i : Nat) :
    activeFCount (stage K i) = 1 := by
  simp [stage, activeFCount_gChain, activeFCount_counter, activeFCount]

/-- The visible multiplicity of `G`-frames along the canonical stage is exactly
its progress index. -/
theorem visible_record_multiplicity (K i : Nat) :
    gFrameCount (stage K i) = i := by
  simp [stage, gFrameCount_gChain, gFrameCount_counter, gFrameCount]

/-- The terminal record contains no active `F`-site. -/
theorem terminal_record_has_no_live_site (K : Nat) :
    activeFCount (terminalRecordMap K) = 0 := by
  rw [terminalRecordMap, activeFCount_gChain, activeFCount]

/-- The terminal record retains exact depth via `G`-multiplicity. -/
theorem terminal_record_recovers_progress_exactly (K : Nat) :
    gFrameCount (terminalRecordMap K) = K := by
  rw [terminalRecordMap, gFrameCount_gChain, gFrameCount, Nat.add_zero]

/-- Collect the four active-site and frame-count equalities for canonical stages and records. -/
theorem live_computation_vs_terminal_record (K i : Nat) :
    activeFCount (stage K i) = 1
      ∧ gFrameCount (stage K i) = i
      ∧ activeFCount (terminalRecordMap K) = 0
      ∧ gFrameCount (terminalRecordMap K) = K := by
  exact ⟨live_computation_channel_unique K i,
    visible_record_multiplicity K i,
    terminal_record_has_no_live_site K,
    terminal_record_recovers_progress_exactly K⟩

end PrimitiveDuplicatorTerm

/-! ## Executable progress-recovery channels -/

/-- Structural-counting observation on the actual canonical stage. Its value is packaged back into
the finite progress space using the proved exact `G`-frame count. -/
def structuralCountingChannel {K : Nat} : Fin (K + 1) → Fin (K + 1) :=
  fun j =>
    ⟨PrimitiveDuplicatorTerm.gFrameCount (PrimitiveDuplicatorTerm.stage K j), by
      rw [PrimitiveDuplicatorTerm.visible_record_multiplicity]
      exact j.isLt⟩

/-- The executable structural-counting observation recovers every progress state exactly. -/
@[simp] theorem structuralCountingChannel_eq {K : Nat} (j : Fin (K + 1)) :
    structuralCountingChannel j = j := by
  apply Fin.ext
  exact PrimitiveDuplicatorTerm.visible_record_multiplicity K j

/-- Origin comparison reads the live counter from the actual canonical stage and subtracts its
height from the initial height. -/
def originComparisonChannel {K : Nat} : Fin (K + 1) → Fin (K + 1) :=
  fun j =>
    ⟨K - (PrimitiveDuplicatorTerm.activeCounterHeight?
        (PrimitiveDuplicatorTerm.stage K j)).getD 0,
      Nat.lt_succ_of_le (Nat.sub_le K _)⟩

/-- State of an external rule-firing clock, bounded by the fixed trace horizon. -/
structure ParallelClockState (K : Nat) where
  ticks : Nat
  ticks_le : ticks ≤ K

/-- Clock state after the canonical stage index has fired. -/
def parallelClockAt (K : Nat) (j : Fin (K + 1)) : ParallelClockState K :=
  ⟨j, Nat.le_of_lt_succ j.isLt⟩

/-- Parallel clocking reads the explicit external clock state. -/
def parallelClockChannel {K : Nat} : Fin (K + 1) → Fin (K + 1) :=
  fun j => ⟨(parallelClockAt K j).ticks,
    Nat.lt_succ_of_le (parallelClockAt K j).ticks_le⟩

/-- The executable origin-comparison observation recovers every progress state exactly. -/
@[simp] theorem originComparisonChannel_eq {K : Nat} (j : Fin (K + 1)) :
    originComparisonChannel j = j := by
  apply Fin.ext
  simp only [originComparisonChannel, PrimitiveDuplicatorTerm.activeCounterHeight?_stage,
    Option.getD_some]
  have hj : (j : Nat) ≤ K := Nat.le_of_lt_succ j.isLt
  omega

/-- The executable external clock recovers every progress state exactly. -/
@[simp] theorem parallelClockChannel_eq {K : Nat} (j : Fin (K + 1)) :
    parallelClockChannel j = j := by
  apply Fin.ext
  rfl

@[simp] theorem structuralCountingChannel_injective {K : Nat} :
    Function.Injective (@structuralCountingChannel K) := by
  intro a b h
  simpa using h

@[simp] theorem originComparisonChannel_injective {K : Nat} :
    Function.Injective (@originComparisonChannel K) := by
  intro a b h
  simpa using h

@[simp] theorem parallelClockChannel_injective {K : Nat} :
    Function.Injective (@parallelClockChannel K) := by
  intro a b h
  simpa using h

/-- An exact `b`-bit recovery code for the `K + 1` progress states. Injectivity is the complete
recovery requirement; the codomain has exactly `2^b` binary words. -/
structure ExactProgressCode (K b : Nat) where
  encode : Fin (K + 1) → Fin (2 ^ b)
  injective : Function.Injective encode

/-- Prior entropy on the `Kmax + 1` progress states. -/
noncomputable def terminalPriorEntropyBits (Kmax : Nat) : ℝ :=
  progressEntropyBits Kmax

/-- Posterior entropy of the Dirac law at the progress value recovered from the terminal record. -/
noncomputable def terminalPosteriorEntropyBits (Kmax : Nat) : ℝ :=
  OperatorKO7.Meta.InformationalIncompleteness.FiniteSupportEntropy.HBits
    (fun j : Fin (Kmax + 1) =>
      if j = ⟨Kmax, Nat.lt_succ_self Kmax⟩ then 1 else 0)

/-- Difference between the uniform-prior entropy and the exact-recovery posterior entropy. -/
noncomputable def terminalMutualInformationGainBits (Kmax : Nat) : ℝ :=
  terminalPriorEntropyBits Kmax - terminalPosteriorEntropyBits Kmax

open OperatorKO7.Meta.InformationalIncompleteness.FiniteSupportEntropy in
open OperatorKO7.Meta.InformationalIncompleteness.ShannonFinite in
/-- The executable exact-recovery posterior has zero entropy. -/
theorem terminalPosteriorEntropyBits_zero (Kmax : Nat) :
    terminalPosteriorEntropyBits Kmax = 0 := by
  let terminal : Fin (Kmax + 1) := ⟨Kmax, Nat.lt_succ_self Kmax⟩
  have hH :
      H (fun j : Fin (Kmax + 1) => if j = terminal then 1 else 0) = 0 :=
    H_dirac_eq_zero terminal
  simp [terminalPosteriorEntropyBits, HBits, terminal, hH]

/-- The terminal gain equals the prior because the exact-recovery posterior is a Dirac law. -/
theorem meta_trace_mutual_information_at_terminal (Kmax : Nat) :
    terminalMutualInformationGainBits Kmax = terminalPriorEntropyBits Kmax := by
  rw [terminalMutualInformationGainBits, terminalPosteriorEntropyBits_zero, sub_zero]

/-! ## The declared expressions are the entropies of named distributions

The quantities above are executable expressions: `progressEntropyBits` is a logarithm,
`optimalRecoveryBits` is a ceiling logarithm, and `terminalPosteriorEntropyBits` is the entropy of
the explicit Dirac posterior. This section identifies each expression with its finite-support
probability model, so the paper's model reading is derived rather than declared.

* `progressEntropyBits` is the Shannon entropy in bits of the uniform law on the `K + 1` progress
  states.
* `optimalRecoveryBits` is the least `b` with `K + 1 ≤ 2 ^ b`, so it is the exact width of a
  recovery code and not one choice among many.
* the terminal posterior is the Dirac mass at the recovered progress value, whose entropy is zero
  by `H_dirac_eq_zero`. The recovery itself is `terminal_record_recovers_progress_exactly`.
-/

open OperatorKO7.Meta.InformationalIncompleteness.FiniteSupportEntropy in
/-- The progress-entropy expression is the entropy in bits of the uniform law on the `K + 1`
progress states. -/
theorem progressEntropyBits_eq_HBits_uniform (K : Nat) :
    HBits (uniformMass (Fin (K + 1))) = progressEntropyBits K := by
  rw [HBits_uniformMass_eq_logb_card (Fin (K + 1))]
  simp [progressEntropyBits]

/-- The recovery width is a code width: `K + 1` states fit, and no smaller width does. -/
theorem optimalRecoveryBits_least (K : Nat) :
    K + 1 ≤ 2 ^ (optimalRecoveryBits K)
      ∧ ∀ b : Nat, K + 1 ≤ 2 ^ b → optimalRecoveryBits K ≤ b := by
  refine ⟨Nat.le_pow_clog (by omega) (K + 1), ?_⟩
  intro b hb
  exact (Nat.le_pow_iff_clog_le (by omega)).1 hb

/-- Every exact binary recovery code needs at least `optimalRecoveryBits K` bits. -/
theorem exactProgressCode_width_lower {K b : Nat} (C : ExactProgressCode K b) :
    optimalRecoveryBits K ≤ b := by
  apply (optimalRecoveryBits_least K).2 b
  simpa using Fintype.card_le_of_injective C.encode C.injective

/-- Any injective observation channel has an exact code at the optimal width. -/
def exactProgressCodeOfInjective {K : Nat}
    (channel : Fin (K + 1) → Fin (K + 1))
    (hinj : Function.Injective channel) :
    ExactProgressCode K (optimalRecoveryBits K) where
  encode := fun j => Fin.castLE (optimalRecoveryBits_least K).1 (channel j)
  injective := (Fin.castLE_injective (optimalRecoveryBits_least K).1).comp hinj

/-- The executable structural-counting channel attains the universal exact-code lower bound. -/
def structuralCountingExactCode (K : Nat) : ExactProgressCode K (optimalRecoveryBits K) :=
  exactProgressCodeOfInjective (@structuralCountingChannel K) structuralCountingChannel_injective

/-- Origin comparison attains the universal exact-code lower bound. -/
def originComparisonExactCode (K : Nat) : ExactProgressCode K (optimalRecoveryBits K) :=
  exactProgressCodeOfInjective (@originComparisonChannel K) originComparisonChannel_injective

/-- Parallel clocking attains the universal exact-code lower bound. -/
def parallelClockExactCode (K : Nat) : ExactProgressCode K (optimalRecoveryBits K) :=
  exactProgressCodeOfInjective (@parallelClockChannel K) parallelClockChannel_injective

/-- Exact minimax statement for all three named channels: each has a code of width
`optimalRecoveryBits K`, and every exact binary code for the same progress space has at least that
width. -/
theorem named_channels_attain_universal_exact_code_minimum (K : Nat) :
    Nonempty (ExactProgressCode K (structuralCountingBitCost K))
      ∧ Nonempty (ExactProgressCode K (originComparisonBitCost K))
      ∧ Nonempty (ExactProgressCode K (parallelClockBitCost K))
      ∧ ∀ {b : Nat}, ExactProgressCode K b → optimalRecoveryBits K ≤ b := by
  exact ⟨⟨structuralCountingExactCode K⟩,
    ⟨originComparisonExactCode K⟩,
    ⟨parallelClockExactCode K⟩,
    fun C => exactProgressCode_width_lower C⟩

/-- The three named channel-width functions equal the proved exact-code minimum. -/
theorem named_channel_costs_are_optimal (K : Nat) :
    structuralCountingBitCost K = optimalRecoveryBits K
      ∧ originComparisonBitCost K = optimalRecoveryBits K
      ∧ parallelClockBitCost K = optimalRecoveryBits K :=
  ⟨rfl, rfl, rfl⟩

open OperatorKO7.Meta.InformationalIncompleteness.FiniteSupportEntropy in
open OperatorKO7.Meta.InformationalIncompleteness.ShannonFinite in
/-- Uniform prior on the progress states. -/
noncomputable def terminalPriorMass (K : Nat) : Fin (K + 1) → ℝ :=
  uniformMass (Fin (K + 1))

open OperatorKO7.Meta.InformationalIncompleteness.FiniteSupportEntropy in
open OperatorKO7.Meta.InformationalIncompleteness.ShannonFinite in
/-- Posterior after the identity recovery channel reports `observed`. -/
noncomputable def terminalPosteriorGiven (K : Nat) (observed : Fin (K + 1)) :
    Fin (K + 1) → ℝ :=
  fun j => if j = observed then 1 else 0

/-- Likelihood of an observation under the executable structural-counting channel. -/
noncomputable def terminalLikelihood (K : Nat) (observed state : Fin (K + 1)) : ℝ :=
  if structuralCountingChannel state = observed then 1 else 0

/-- Joint mass of the uniform prior and the executable deterministic channel. -/
noncomputable def terminalJointMass (K : Nat) (state observed : Fin (K + 1)) : ℝ :=
  terminalPriorMass K state * terminalLikelihood K observed state

/-- Marginal mass of an observation. -/
noncomputable def terminalEvidenceMass (K : Nat) (observed : Fin (K + 1)) : ℝ :=
  ∑ state, terminalJointMass K state observed

/-- Bayes posterior computed from the joint law and its observation marginal. -/
noncomputable def terminalBayesPosterior (K : Nat) (observed : Fin (K + 1)) :
    Fin (K + 1) → ℝ :=
  fun state => terminalJointMass K state observed / terminalEvidenceMass K observed

/-- Every observation has the uniform positive marginal. -/
theorem terminalEvidenceMass_eq_uniform (K : Nat) (observed : Fin (K + 1)) :
    terminalEvidenceMass K observed = 1 / (K + 1 : ℝ) := by
  simp [terminalEvidenceMass, terminalJointMass, terminalLikelihood, terminalPriorMass,
    OperatorKO7.Meta.InformationalIncompleteness.FiniteSupportEntropy.uniformMass,
    structuralCountingChannel_eq]

/-- The declared point posterior is exactly Bayes' rule for the uniform prior and executable
structural-counting channel. -/
theorem terminalBayesPosterior_eq_declared (K : Nat) (observed : Fin (K + 1)) :
    terminalBayesPosterior K observed = terminalPosteriorGiven K observed := by
  funext state
  rw [terminalBayesPosterior, terminalEvidenceMass_eq_uniform]
  by_cases h : state = observed
  · subst state
    simp [terminalJointMass, terminalLikelihood, terminalPriorMass, terminalPosteriorGiven,
      OperatorKO7.Meta.InformationalIncompleteness.FiniteSupportEntropy.uniformMass,
      structuralCountingChannel_eq]
    have hne : (K + 1 : ℝ) ≠ 0 := by positivity
    exact inv_mul_cancel₀ hne
  · simp [terminalJointMass, terminalLikelihood, terminalPriorMass, terminalPosteriorGiven, h,
      structuralCountingChannel_eq]

/-! ## Random positive terminal depth

The manuscript's terminal-record corollary samples a completed depth uniformly from
`{1, ..., Kmax}`, not a progress state from `{0, ..., K}`.  `Fin Kmax` encodes depth `j + 1`.
-/

/-- Counting frames in the actual terminal record at depth `j + 1`, then translating back to the
zero-based `Fin Kmax` code. -/
def positiveTerminalCountingChannel {Kmax : Nat} (j : Fin Kmax) : Fin Kmax :=
  ⟨PrimitiveDuplicatorTerm.gFrameCount
      (PrimitiveDuplicatorTerm.terminalRecordMap (j.val + 1)) - 1, by
    rw [PrimitiveDuplicatorTerm.terminal_record_recovers_progress_exactly]
    omega⟩

/-- The terminal-record frame count recovers every positive sampled depth exactly. -/
@[simp] theorem positiveTerminalCountingChannel_eq {Kmax : Nat} (j : Fin Kmax) :
    positiveTerminalCountingChannel j = j := by
  apply Fin.ext
  simp [positiveTerminalCountingChannel,
    PrimitiveDuplicatorTerm.terminal_record_recovers_progress_exactly]

open OperatorKO7.Meta.InformationalIncompleteness.FiniteSupportEntropy in
/-- Uniform prior on positive terminal depths `1, ..., Kmax`, represented by `Fin Kmax`. -/
noncomputable def positiveTerminalPriorMass (Kmax : Nat) : Fin Kmax → ℝ :=
  uniformMass (Fin Kmax)

/-- Posterior after the terminal-record counting channel reports a sampled depth. -/
noncomputable def positiveTerminalPosteriorGiven (Kmax : Nat) (observed : Fin Kmax) :
    Fin Kmax → ℝ :=
  fun j => if j = observed then 1 else 0

/-- Likelihood of an observation under the actual terminal-record counting channel. -/
noncomputable def positiveTerminalLikelihood
    (Kmax : Nat) (observed state : Fin Kmax) : ℝ :=
  if positiveTerminalCountingChannel state = observed then 1 else 0

/-- Joint mass of sampled positive depth and terminal-record observation. -/
noncomputable def positiveTerminalJointMass
    (Kmax : Nat) (state observed : Fin Kmax) : ℝ :=
  positiveTerminalPriorMass Kmax state * positiveTerminalLikelihood Kmax observed state

/-- Observation marginal for the positive-depth terminal-record channel. -/
noncomputable def positiveTerminalEvidenceMass (Kmax : Nat) (observed : Fin Kmax) : ℝ :=
  ∑ state, positiveTerminalJointMass Kmax state observed

/-- Bayes posterior for a sampled positive terminal depth. -/
noncomputable def positiveTerminalBayesPosterior (Kmax : Nat) (observed : Fin Kmax) :
    Fin Kmax → ℝ :=
  fun state =>
    positiveTerminalJointMass Kmax state observed / positiveTerminalEvidenceMass Kmax observed

/-- Every observable positive depth has marginal mass `1 / Kmax`. -/
theorem positiveTerminalEvidenceMass_eq_uniform (Kmax : Nat) (observed : Fin Kmax) :
    positiveTerminalEvidenceMass Kmax observed = 1 / (Kmax : ℝ) := by
  simp [positiveTerminalEvidenceMass, positiveTerminalJointMass, positiveTerminalLikelihood,
    positiveTerminalPriorMass,
    OperatorKO7.Meta.InformationalIncompleteness.FiniteSupportEntropy.uniformMass,
    positiveTerminalCountingChannel_eq]

/-- The point posterior is exactly Bayes' rule for the uniform positive-depth prior and actual
terminal-record counting channel. -/
theorem positiveTerminalBayesPosterior_eq_declared
    (Kmax : Nat) (observed : Fin Kmax) :
    positiveTerminalBayesPosterior Kmax observed =
      positiveTerminalPosteriorGiven Kmax observed := by
  funext state
  rw [positiveTerminalBayesPosterior, positiveTerminalEvidenceMass_eq_uniform]
  by_cases h : state = observed
  · subst state
    have hKnat : Kmax ≠ 0 := Nat.ne_of_gt (Nat.zero_lt_of_lt observed.isLt)
    have hKreal : (Kmax : ℝ) ≠ 0 := by exact_mod_cast hKnat
    simp [positiveTerminalJointMass, positiveTerminalLikelihood, positiveTerminalPriorMass,
      positiveTerminalPosteriorGiven,
      OperatorKO7.Meta.InformationalIncompleteness.FiniteSupportEntropy.uniformMass,
      positiveTerminalCountingChannel_eq, hKreal]
  · simp [positiveTerminalJointMass, positiveTerminalLikelihood, positiveTerminalPriorMass,
      positiveTerminalPosteriorGiven, h, positiveTerminalCountingChannel_eq]

open OperatorKO7.Meta.InformationalIncompleteness.FiniteSupportEntropy in
open OperatorKO7.Meta.InformationalIncompleteness.ShannonFinite in
/-- Every positive-depth posterior has zero entropy. -/
theorem positiveTerminalPosteriorGiven_HBits_zero
    (Kmax : Nat) (observed : Fin Kmax) :
    HBits (positiveTerminalPosteriorGiven Kmax observed) = 0 := by
  unfold HBits positiveTerminalPosteriorGiven
  rw [H_dirac_eq_zero observed]
  simp

open OperatorKO7.Meta.InformationalIncompleteness.FiniteSupportEntropy in
open OperatorKO7.Meta.InformationalIncompleteness.ShannonFinite in
/-- Expected posterior entropy for the random positive terminal depth. -/
noncomputable def positiveTerminalConditionalEntropyBits (Kmax : Nat) : ℝ :=
  ∑ observed, positiveTerminalPriorMass Kmax observed *
    HBits (positiveTerminalPosteriorGiven Kmax observed)

open OperatorKO7.Meta.InformationalIncompleteness.FiniteSupportEntropy in
open OperatorKO7.Meta.InformationalIncompleteness.ShannonFinite in
theorem positiveTerminalConditionalEntropyBits_eq_zero (Kmax : Nat) :
    positiveTerminalConditionalEntropyBits Kmax = 0 := by
  simp [positiveTerminalConditionalEntropyBits, positiveTerminalPosteriorGiven_HBits_zero]

open OperatorKO7.Meta.InformationalIncompleteness.FiniteSupportEntropy in
open OperatorKO7.Meta.InformationalIncompleteness.ShannonFinite in
/-- Mutual information between a uniformly sampled positive depth and its terminal record. -/
noncomputable def positiveTerminalMutualInformationBits (Kmax : Nat) : ℝ :=
  HBits (positiveTerminalPriorMass Kmax) - positiveTerminalConditionalEntropyBits Kmax

open OperatorKO7.Meta.InformationalIncompleteness.FiniteSupportEntropy in
/-- **Exact manuscript theorem.** For `Kmax > 0`, the actual terminal-record channel carries
exactly `log₂ Kmax` bits about a depth sampled uniformly from `1, ..., Kmax`. -/
theorem positive_terminal_mutual_information_exact (Kmax : Nat) (hK : 0 < Kmax) :
    positiveTerminalMutualInformationBits Kmax = Real.logb 2 Kmax := by
  letI : Nonempty (Fin Kmax) := ⟨⟨0, hK⟩⟩
  rw [positiveTerminalMutualInformationBits, positiveTerminalConditionalEntropyBits_eq_zero,
    sub_zero]
  simpa [positiveTerminalPriorMass] using
    (OperatorKO7.Meta.InformationalIncompleteness.FiniteSupportEntropy.HBits_uniformMass_eq_logb_card
      (Fin Kmax))

open OperatorKO7.Meta.InformationalIncompleteness.FiniteSupportEntropy in
open OperatorKO7.Meta.InformationalIncompleteness.ShannonFinite in
/-- The terminal posterior law: the record determines the progress value, so the posterior is the
Dirac mass at that value. -/
noncomputable def terminalPosteriorMass (K : Nat) : Fin (K + 1) → ℝ :=
  terminalPosteriorGiven K ⟨K, Nat.lt_succ_self K⟩

open OperatorKO7.Meta.InformationalIncompleteness.FiniteSupportEntropy in
open OperatorKO7.Meta.InformationalIncompleteness.ShannonFinite in
/-- Every posterior is normalized. -/
theorem terminalPosteriorGiven_sum_one (K : Nat) (observed : Fin (K + 1)) :
    ∑ j, terminalPosteriorGiven K observed j = 1 := by
  simp [terminalPosteriorGiven]

open OperatorKO7.Meta.InformationalIncompleteness.FiniteSupportEntropy in
open OperatorKO7.Meta.InformationalIncompleteness.ShannonFinite in
/-- Every posterior of the exact recovery channel has zero entropy in bits. -/
theorem terminalPosteriorGiven_HBits_zero (K : Nat) (observed : Fin (K + 1)) :
    HBits (terminalPosteriorGiven K observed) = 0 := by
  unfold HBits terminalPosteriorGiven
  rw [H_dirac_eq_zero observed]
  simp

open OperatorKO7.Meta.InformationalIncompleteness.FiniteSupportEntropy in
open OperatorKO7.Meta.InformationalIncompleteness.ShannonFinite in
/-- Expected posterior entropy of the exact recovery channel. -/
noncomputable def terminalConditionalEntropyBits (K : Nat) : ℝ :=
  ∑ observed, terminalPriorMass K observed *
    HBits (terminalPosteriorGiven K observed)

open OperatorKO7.Meta.InformationalIncompleteness.FiniteSupportEntropy in
open OperatorKO7.Meta.InformationalIncompleteness.ShannonFinite in
theorem terminalConditionalEntropyBits_eq_zero (K : Nat) :
    terminalConditionalEntropyBits K = 0 := by
  simp [terminalConditionalEntropyBits, terminalPosteriorGiven_HBits_zero]

open OperatorKO7.Meta.InformationalIncompleteness.FiniteSupportEntropy in
open OperatorKO7.Meta.InformationalIncompleteness.ShannonFinite in
/-- Mutual information of the uniform prior and exact recovery channel. -/
noncomputable def terminalChannelMutualInformationBits (K : Nat) : ℝ :=
  HBits (terminalPriorMass K) - terminalConditionalEntropyBits K

open OperatorKO7.Meta.InformationalIncompleteness.FiniteSupportEntropy in
open OperatorKO7.Meta.InformationalIncompleteness.ShannonFinite in
/-- The executable structural channel's Bayes posterior is calibrated at every progress value. -/
theorem terminalPosteriorGiven_calibrated (K : Nat) (i : Fin (K + 1)) :
    terminalPosteriorGiven K (structuralCountingChannel i) i = 1 := by
  rw [structuralCountingChannel_eq]
  simp [terminalPosteriorGiven]

open OperatorKO7.Meta.InformationalIncompleteness.FiniteSupportEntropy in
open OperatorKO7.Meta.InformationalIncompleteness.ShannonFinite in
/-- The exact recovery channel carries the full uniform-prior entropy. -/
theorem terminalChannelMutualInformationBits_eq_progress (K : Nat) :
    terminalChannelMutualInformationBits K = progressEntropyBits K := by
  rw [terminalChannelMutualInformationBits, terminalConditionalEntropyBits_eq_zero,
    sub_zero]
  simpa [terminalPriorMass] using progressEntropyBits_eq_HBits_uniform K

open OperatorKO7.Meta.InformationalIncompleteness.FiniteSupportEntropy in
open OperatorKO7.Meta.InformationalIncompleteness.ShannonFinite in
/-- **The posterior entropy is derived, not stipulated.** The terminal record recovers the
progress value exactly (`terminal_record_recovers_progress_exactly`), and
`terminalBayesPosterior_eq_declared` identifies the point mass with Bayes' rule for the executable
channel. Its entropy is therefore zero through the library. -/
theorem terminalPosteriorEntropyBits_eq_H_dirac (K : Nat) :
    H (terminalPosteriorMass K) = 0 ∧ terminalPosteriorEntropyBits K = 0 := by
  refine ⟨?_, terminalPosteriorEntropyBits_zero K⟩
  simpa [terminalPosteriorMass, terminalPosteriorGiven] using
    H_dirac_eq_zero (α := Fin (K + 1)) ⟨K, Nat.lt_succ_self K⟩

open OperatorKO7.Meta.InformationalIncompleteness.FiniteSupportEntropy in
/-- The public posterior-entropy object is definitionally the entropy of the calibrated posterior
model used by the channel calculation. -/
theorem terminalPosteriorEntropyBits_eq_model (K : Nat) :
    terminalPosteriorEntropyBits K = HBits (terminalPosteriorMass K) := by
  rfl

/-- The recovered progress value the posterior concentrates on is the one the terminal record
carries. -/
theorem terminalPosteriorMass_at_recovered (K : Nat) :
    (PrimitiveDuplicatorTerm.terminalRecordMap K).gFrameCount = K
      ∧ terminalPosteriorMass K ⟨K, Nat.lt_succ_self K⟩ = 1 := by
  refine ⟨PrimitiveDuplicatorTerm.terminal_record_recovers_progress_exactly K, ?_⟩
  simp [terminalPosteriorMass, terminalPosteriorGiven]

open OperatorKO7.Meta.InformationalIncompleteness.FiniteSupportEntropy in
/-- **The terminal gain, with both ends derived.** The prior is the entropy in bits of the uniform
law on the `Kmax + 1` progress states, the posterior is the entropy of the recovered point mass,
and the gain is their difference. -/
theorem meta_trace_mutual_information_at_terminal_derived (Kmax : Nat) :
    terminalMutualInformationGainBits Kmax =
        terminalChannelMutualInformationBits Kmax
      ∧ terminalChannelMutualInformationBits Kmax =
        HBits (uniformMass (Fin (Kmax + 1)))
      ∧ terminalChannelMutualInformationBits Kmax = progressEntropyBits Kmax := by
  have hchannel := terminalChannelMutualInformationBits_eq_progress Kmax
  refine ⟨?_, ?_, hchannel⟩
  · rw [meta_trace_mutual_information_at_terminal, terminalPriorEntropyBits, hchannel]
  · rw [hchannel, ← progressEntropyBits_eq_HBits_uniform]

end OperatorKO7.InformationAccess
