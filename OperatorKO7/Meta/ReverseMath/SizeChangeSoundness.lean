import OperatorKO7.Kernel
import OperatorKO7.Meta.ReverseMath.Complexity
import OperatorKO7.Meta.ReverseMath.StandardModel
import Mathlib.SetTheory.Ordinal.Rank

/-!
# Size-change soundness for the step-duplicating recursor's dependency-pair problem

This module gives both the object-level dependency-pair proof and an exact arithmetization of
that same fixed relation. The displayed `L₂` sentence `DupDPBoundedSNSentence` is proved
`Pi02`, its standard-model semantics is proved equivalent to the natural counter bound, and
that bound is proved equivalent to `BoundedSN DupDPStep`. This closes the gap left by the older
predecessor-shape calibration modules without claiming an internal `RCA₀` derivation.

* `sizeChangeGraph_has_no_infinite_call_chain` is one-thread size-change soundness: a call
  relation carrying an everywhere-strict descent thread admits no infinite chain.
* `sizeChangeGraph_boundedSN` upgrades that to the bounded `∀∃` presentation the manuscript's
  `Π⁰₂` proposition uses, with the descent value itself as the explicit witness.
* `dupDP_boundedSN` and `dupDPStep_wellFounded` instantiate both on the singleton
  dependency pair `recΔ♯ b s (delta n) → recΔ♯ b s n` extracted from the step-duplicating
  recursor.
* `dupDP_boundedSN_iff_stdModel_formula` identifies bounded SN of that actual relation with
  standard-model satisfaction of the displayed `Pi02` sentence.
* `dupDPStepRank_eq_counter` computes the well-founded rank of every residual term exactly,
  and `dupDPStepHeight_eq_omega` proves that the residual relation itself has height `ω`.
* `dupDPStep_projection_strict_iff` records that the third-argument projection is the
  coordinate carrying the descent, which is the simple projection `π` of the subterm
  criterion.

Relation: the extracted dependency-pair relation `DupDPStep`, not the KO7 kernel `Step`.
Closure: one-step on dependency-pair terms.
Strategy: not applicable.
Trust: kernel-only. No `sorry`, no `admit`, no new `axiom`, no native reduction.
-/

set_option autoImplicit false

open OperatorKO7
open OperatorKO7.Trace

universe u

namespace OperatorKO7.ReverseMath.SizeChangeSoundness

open FirstOrder Language

/-! ### Exact arithmetical sentence for the singleton dependency-pair bound -/

/-- Quantifier-free matrix saying that a number-coded counter has a strictly larger
number-coded bound. The set guards relativize the single-sorted `L2` carrier to naturals. -/
def dupDPBoundMatrix : L2.BoundedFormula Empty 2 :=
  (∼ (isSetBd (&0))) ⟹ ((∼ (isSetBd (&1))) ⊓ ltBd (&0) (&1))

theorem dupDPBoundMatrix_isQF : dupDPBoundMatrix.IsQF := by
  unfold dupDPBoundMatrix
  exact (Relations.isQF _ _).not.imp ((Relations.isQF _ _).not.inf (ltBd_isQF _ _))

/-- The explicit `forall counter, exists bound` sentence. -/
def DupDPBoundedSNSentence : L2.Sentence := ∀' ∃' dupDPBoundMatrix

theorem dupDPBoundedSNSentence_isPi02 :
    Complexity.IsPi02 DupDPBoundedSNSentence :=
  Complexity.IsQF.all_ex_isPi02 dupDPBoundMatrix_isQF

theorem dupDPBoundedSNSentence_isPrenex : DupDPBoundedSNSentence.IsPrenex :=
  Complexity.IsPi02.isPrenex dupDPBoundedSNSentence_isPi02

/-- Natural-number content of the explicit sentence. -/
def DupDPCounterBound : Prop := ∀ c : Nat, ∃ n : Nat, c < n

theorem dupDPCounterBound_holds : DupDPCounterBound :=
  fun c => ⟨c + 1, Nat.lt_succ_self c⟩

/-- Standard-model faithfulness of the explicit arithmetic sentence. -/
theorem dupDPBoundedSNSentence_faithful :
    (StdCarrier ⊨ DupDPBoundedSNSentence) ↔ DupDPCounterBound := by
  simp only [DupDPBoundedSNSentence, DupDPCounterBound, dupDPBoundMatrix, ltBd, isSetBd,
    Sentence.Realize, Formula.Realize, BoundedFormula.realize_all, BoundedFormula.realize_ex,
    BoundedFormula.realize_imp, BoundedFormula.realize_inf, BoundedFormula.realize_not,
    BoundedFormula.realize_rel₁, BoundedFormula.realize_rel₂]
  constructor
  · intro h c
    obtain ⟨b, hb⟩ := h (Sum.inl c)
    obtain ⟨hbnum, hlt⟩ := hb (id : ¬ stdStructure.RelMap Rel.isSet ![Sum.inl c])
    cases b with
    | inr S => exact absurd (trivial : stdStructure.RelMap Rel.isSet ![Sum.inr S]) hbnum
    | inl n => exact ⟨n, hlt⟩
  · intro h a
    cases a with
    | inr S =>
        exact ⟨Sum.inl 0,
          fun hcon => absurd (trivial : stdStructure.RelMap Rel.isSet ![Sum.inr S]) hcon⟩
    | inl c =>
        obtain ⟨n, hcn⟩ := h c
        exact ⟨Sum.inl n,
          fun _ => ⟨(id : ¬ stdStructure.RelMap Rel.isSet ![Sum.inl n]), hcn⟩⟩

/-! ### One-thread size-change graphs -/

/--
Intent: a size-change graph with a single strict descent thread. `call` is the call
relation of the dependency-pair problem, `proj` is the simple projection onto the
descending argument, and `strict_descent` is the single strict self-arc.

This is the one-node, one-arc configuration the subterm criterion produces on the
step-duplicating recursor.
-/
structure SizeChangeGraph (State : Type u) where
  /-- The call relation of the dependency-pair problem. -/
  call : State → State → Prop
  /-- The simple projection onto the descending argument. -/
  proj : State → Nat
  /-- The strict self-arc: every call strictly decreases the projection. -/
  strict_descent : ∀ s t, call s t → proj t < proj s

variable {State : Type u}

/--
Proves: along any chain of `n` consecutive calls the projection drops by at least `n`.
This is the descent-thread accounting the soundness argument runs on.
-/
theorem SizeChangeGraph.proj_drops_along_chain
    (G : SizeChangeGraph State) (f : Nat → State)
    (n : Nat) (hchain : ∀ i, i < n → G.call (f i) (f (i + 1))) :
    G.proj (f n) + n ≤ G.proj (f 0) := by
  induction n with
  | zero => simp
  | succ k ih =>
      have hk : ∀ i, i < k → G.call (f i) (f (i + 1)) := fun i hi =>
        hchain i (Nat.lt_succ_of_lt hi)
      have hstep : G.proj (f (k + 1)) < G.proj (f k) :=
        G.strict_descent _ _ (hchain k (Nat.lt_succ_self k))
      have := ih hk
      omega

/--
Intent: **one-thread size-change soundness**. A call relation carrying an everywhere-strict
descent thread admits no infinite chain.

Does not prove: the general multi-graph size-change theorem, which needs the Ramsey-style
closure argument. The configuration extracted from the step-duplicating recursor is the
single-graph, single-thread case, and that case is what this theorem covers.
Trust: kernel-only.
-/
theorem sizeChangeGraph_has_no_infinite_call_chain
    (G : SizeChangeGraph State) (f : Nat → State)
    (hchain : ∀ i, G.call (f i) (f (i + 1))) : False := by
  have := G.proj_drops_along_chain f (G.proj (f 0) + 1) (fun i _ => hchain i)
  omega

/-! ### The bounded presentation used by the `Π⁰₂` proposition -/

/-- No chain of exactly `n` consecutive calls issues from `s`. -/
def NoChainOfLength (call : State → State → Prop) (s : State) (n : Nat) : Prop :=
  ∀ f : Nat → State, f 0 = s → ¬ (∀ i, i < n → call (f i) (f (i + 1)))

/-- The bounded strong-normalization predicate, in the `∀∃` shape whose matrix is a
decidable condition on finite chains. This is the presentation `SN_b` of the manuscript's
`Π⁰₂` proposition. -/
def BoundedSN (call : State → State → Prop) : Prop :=
  ∀ s, ∃ n, NoChainOfLength call s n

/--
Intent: one-thread size-change soundness in the bounded `∀∃` presentation, with the
descent value at the start state as the explicit length bound.

Proves: every chain issuing from `s` has length at most `proj s`.
Trust: kernel-only.
-/
theorem sizeChangeGraph_boundedSN (G : SizeChangeGraph State) :
    BoundedSN G.call := by
  intro s
  refine ⟨G.proj s + 1, ?_⟩
  intro f hf0 hchain
  have hdrop := G.proj_drops_along_chain f (G.proj s + 1) hchain
  rw [hf0] at hdrop
  omega

/--
Proves: the call relation of a one-thread size-change graph is well founded, so the
dependency-pair problem is strongly normalizing.
-/
theorem sizeChangeGraph_wellFounded (G : SizeChangeGraph State) :
    WellFounded (fun t s => G.call s t) := by
  have h : ∀ (n : Nat) (s : State), G.proj s ≤ n → Acc (fun t s => G.call s t) s := by
    intro n
    induction n with
    | zero =>
        intro s hs
        refine Acc.intro s ?_
        intro t hts
        have := G.strict_descent s t hts
        omega
    | succ k ih =>
        intro s _
        refine Acc.intro s ?_
        intro t hts
        have hlt := G.strict_descent s t hts
        exact ih t (by omega)
  exact WellFounded.intro fun s => h (G.proj s) s (Nat.le_refl _)

/-! ### The dependency pair extracted from the step-duplicating recursor -/

/--
The marked term `recΔ♯ b s c`. The base and step arguments are carried unchanged; the
counter argument is carried as its successor height, which is the coordinate the subterm
criterion projects onto.
-/
structure DupDPTerm : Type where
  /-- The base argument, inert for the dependency-pair problem. -/
  base : Trace
  /-- The step argument, the dimension the confession projects away. -/
  step : Trace
  /-- The counter height, the retained descending coordinate. -/
  counter : Nat
deriving DecidableEq, Repr

/--
The singleton dependency pair extracted from the recursive rule
`recΔ b s (delta n) → app s (recΔ b s n)`: the marked pair
`recΔ♯ b s (delta n) → recΔ♯ b s n`.
-/
inductive DupDPStep : DupDPTerm → DupDPTerm → Prop
  | pair : ∀ (b s : Trace) (n : Nat),
      DupDPStep ⟨b, s, n + 1⟩ ⟨b, s, n⟩

/-- The simple projection `π` of the subterm criterion: select the counter argument. -/
def dupDPProjection (t : DupDPTerm) : Nat := t.counter

/--
Proves: the projection strictly descends across the extracted pair, which is the
subterm-criterion condition `π(l) = S(n) ▷ n = π(r)`.
-/
theorem dupDPStep_projection_strict :
    ∀ s t : DupDPTerm, DupDPStep s t → dupDPProjection t < dupDPProjection s := by
  intro s t h
  cases h with
  | pair b s' n => exact Nat.lt_succ_self n

/-- The step-duplicating recursor's dependency-pair problem as a one-thread size-change
graph: one node, one strict self-arc on the projected counter. -/
def dupSizeChangeGraph : SizeChangeGraph DupDPTerm where
  call := DupDPStep
  proj := dupDPProjection
  strict_descent := dupDPStep_projection_strict

/--
Intent: **the instance closure**. The dependency-pair problem of the step-duplicating
recursor is chain free.

Relation: the extracted pair relation `DupDPStep`.
Trust: kernel-only.
-/
theorem dupDP_has_no_infinite_chain (f : Nat → DupDPTerm)
    (hchain : ∀ i, DupDPStep (f i) (f (i + 1))) : False :=
  sizeChangeGraph_has_no_infinite_call_chain dupSizeChangeGraph f hchain

/--
Proves: the extracted dependency-pair problem satisfies the bounded `∀∃` presentation,
with the counter height as the explicit chain-length bound.
-/
theorem dupDP_boundedSN : BoundedSN DupDPStep :=
  sizeChangeGraph_boundedSN dupSizeChangeGraph

/--
Proves: the extracted dependency-pair relation is well founded, so the residual problem
the confession hands back is strongly normalizing.
-/
theorem dupDPStep_wellFounded : WellFounded (fun t s => DupDPStep s t) :=
  sizeChangeGraph_wellFounded dupSizeChangeGraph

local instance dupDPStep_isWellFounded :
    IsWellFounded DupDPTerm (fun t s => DupDPStep s t) :=
  ⟨dupDPStep_wellFounded⟩

/--
Proves: the chain-length bound is attained, so the instance measure has order type exactly
`ω` rather than any smaller ordinal. The projection is onto `Nat`.
Non-vacuity witness (Gate R5) for the instance measure.
-/
theorem dupDPProjection_surjective (n : Nat) :
    ∃ t : DupDPTerm, dupDPProjection t = n :=
  ⟨⟨void, void, n⟩, rfl⟩

/--
Proves: chains of every finite length exist, so the bound of `dupDP_boundedSN` is tight
and the problem is genuinely infinite in extent while chain free.
Non-vacuity witness (Gate R5) for `DupDPStep`.
-/
theorem dupDPStep_chain_of_every_length (b s : Trace) (n : Nat) :
    ∀ i, i < n → DupDPStep ⟨b, s, n - i⟩ ⟨b, s, n - (i + 1)⟩ := by
  intro i hi
  have hsucc : n - i = (n - (i + 1)) + 1 := by omega
  rw [hsucc]
  exact DupDPStep.pair b s (n - (i + 1))

/-- Exact finite-chain matrix: a chain of length `n` is impossible from counter `c` exactly
when `n` is strictly larger than `c`. -/
theorem dupDP_noChain_iff_counter_lt (b s : Trace) (c n : Nat) :
    NoChainOfLength DupDPStep ⟨b, s, c⟩ n ↔ c < n := by
  constructor
  · intro hno
    by_contra hnot
    have hnc : n ≤ c := Nat.le_of_not_gt hnot
    let f : Nat → DupDPTerm := fun i => ⟨b, s, c - i⟩
    apply hno f (by simp [f])
    intro i hi
    exact dupDPStep_chain_of_every_length b s c i (lt_of_lt_of_le hi hnc)
  · intro hcn f hf0 hchain
    have hdrop := dupSizeChangeGraph.proj_drops_along_chain f n hchain
    rw [hf0] at hdrop
    simp [dupSizeChangeGraph, dupDPProjection] at hdrop
    omega

/-- Exact reduction of bounded strong normalization for the extracted dependency-pair problem to
the number-only counter-bound statement. -/
theorem dupDP_boundedSN_iff_counterBound :
    BoundedSN DupDPStep ↔ DupDPCounterBound := by
  constructor
  · intro h c
    obtain ⟨n, hn⟩ := h ⟨void, void, c⟩
    exact ⟨n, (dupDP_noChain_iff_counter_lt void void c n).mp hn⟩
  · intro h t
    rcases t with ⟨b, s, c⟩
    obtain ⟨n, hcn⟩ := h c
    exact ⟨n, (dupDP_noChain_iff_counter_lt b s c n).mpr hcn⟩

/-- Full arithmetization bridge: the Lean bounded-SN proposition for `DupDPStep` is equivalent
to satisfaction of the displayed `Pi-zero-two` sentence in the standard model. -/
theorem dupDP_boundedSN_iff_stdModel_formula :
    BoundedSN DupDPStep ↔ StdCarrier ⊨ DupDPBoundedSNSentence :=
  dupDP_boundedSN_iff_counterBound.trans dupDPBoundedSNSentence_faithful.symm

/--
Proves: the step argument is inert for the residual problem. Two dependency-pair terms
differing only in the step argument have the same projection, so the confession discards
exactly the coordinate the descent never reads.
-/
theorem dupDPProjection_ignores_step_argument
    (b s s' : Trace) (n : Nat) :
    dupDPProjection ⟨b, s, n⟩ = dupDPProjection ⟨b, s', n⟩ := rfl

/--
Proves: the projection is the *only* coordinate carrying the descent, in the sense that
the base and step coordinates are preserved by every call.
-/
theorem dupDPStep_preserves_base_and_step :
    ∀ s t : DupDPTerm, DupDPStep s t → t.base = s.base ∧ t.step = s.step := by
  intro s t h
  cases h with
  | pair b s' n => exact ⟨rfl, rfl⟩

/-! ### Exact ordinal rank of the residual dependency-pair relation -/

/-- No residual dependency-pair step leaves a term whose counter is zero. -/
theorem dupDPStep_from_zero_false (b s : Trace) (t : DupDPTerm) :
    ¬ DupDPStep ⟨b, s, 0⟩ t := by
  intro h
  cases h

/-- A term with successor counter has exactly one residual successor. -/
theorem dupDPStep_from_succ_iff (b s : Trace) (n : Nat) (t : DupDPTerm) :
    DupDPStep ⟨b, s, n + 1⟩ t ↔ t = ⟨b, s, n⟩ := by
  constructor
  · intro h
    cases h
    rfl
  · rintro rfl
    exact DupDPStep.pair b s n

/-- The intrinsic well-founded rank of a residual dependency-pair term. -/
noncomputable def dupDPStepRank (t : DupDPTerm) : Ordinal :=
  IsWellFounded.rank (r := fun t s : DupDPTerm => DupDPStep s t) t

/--
Proves: the intrinsic rank of every residual term is exactly its counter, not merely bounded
by the counter projection. This computes the rank of the actual `DupDPStep` relation.
-/
theorem dupDPStepRank_eq_counter (t : DupDPTerm) :
    dupDPStepRank t = (t.counter : Ordinal) := by
  rcases t with ⟨b, s, n⟩
  induction n with
  | zero =>
      rw [dupDPStepRank, IsWellFounded.rank_eq]
      apply le_antisymm
      · refine Ordinal.iSup_le ?_
        intro t
        exact False.elim (dupDPStep_from_zero_false b s t.1 t.2)
      · exact bot_le
  | succ n ih =>
      rw [dupDPStepRank, IsWellFounded.rank_eq]
      calc
        (⨆ t : { t // DupDPStep ⟨b, s, n + 1⟩ t },
            Order.succ (IsWellFounded.rank
              (r := fun t s : DupDPTerm => DupDPStep s t) t.1)) =
            Order.succ (IsWellFounded.rank
              (r := fun t s : DupDPTerm => DupDPStep s t) ⟨b, s, n⟩) := by
              apply le_antisymm
              · refine Ordinal.iSup_le ?_
                rintro ⟨t, htstep⟩
                have ht : t = ⟨b, s, n⟩ :=
                  (dupDPStep_from_succ_iff b s n t).mp htstep
                subst t
                exact le_rfl
              · exact Ordinal.le_iSup
                  (fun t : { t // DupDPStep ⟨b, s, n + 1⟩ t } =>
                    Order.succ (IsWellFounded.rank
                      (r := fun t s : DupDPTerm => DupDPStep s t) t.1))
                  ⟨⟨b, s, n⟩, DupDPStep.pair b s n⟩
        _ = Order.succ (n : Ordinal) := by
              exact congrArg Order.succ ih
        _ = (n + 1 : Nat) := by
              exact (Ordinal.natCast_succ n).symm

/-- The ordinal height of the residual relation: the supremum of successor ranks. -/
noncomputable def dupDPStepHeight : Ordinal :=
  ⨆ t : DupDPTerm, Order.succ (dupDPStepRank t)

/--
Proves: the actual residual dependency-pair relation has ordinal height exactly `ω`.
The upper bound follows from the exact finite rank of every term; the lower bound is attained
by the terms `⟨void, void, n⟩` for all natural `n`.
-/
theorem dupDPStepHeight_eq_omega :
    dupDPStepHeight = Ordinal.omega0 := by
  apply le_antisymm
  · rw [dupDPStepHeight]
    refine Ordinal.iSup_le ?_
    intro t
    rw [dupDPStepRank_eq_counter, ← Ordinal.natCast_succ]
    exact (Ordinal.nat_lt_omega0 (t.counter + 1)).le
  · rw [← Ordinal.iSup_natCast]
    refine Ordinal.iSup_le ?_
    intro n
    have hle :
        Order.succ (dupDPStepRank ⟨void, void, n⟩) ≤ dupDPStepHeight :=
      Ordinal.le_iSup (fun t : DupDPTerm => Order.succ (dupDPStepRank t))
        ⟨void, void, n⟩
    rw [dupDPStepRank_eq_counter] at hle
    exact (Order.lt_succ (n : Ordinal)).le.trans hle

/-- Exact pointwise rank and exact global height of the residual relation. -/
theorem dupDPStep_exact_ordinal_height :
    dupDPStepHeight = Ordinal.omega0
      ∧ ∀ t : DupDPTerm, dupDPStepRank t = (t.counter : Ordinal) :=
  ⟨dupDPStepHeight_eq_omega, dupDPStepRank_eq_counter⟩

/--
Proves: the chosen *measure codomain* has order type `ω` and the projection is onto it.
The stronger intrinsic statement about the residual relation is
`dupDPStep_exact_ordinal_height` above.
-/
theorem dupDP_measure_orderType_omega :
    Ordinal.type ((· < ·) : Nat → Nat → Prop) = Ordinal.omega0
      ∧ Function.Surjective dupDPProjection :=
  ⟨Ordinal.type_nat_lt, fun n => ⟨⟨void, void, n⟩, rfl⟩⟩

end OperatorKO7.ReverseMath.SizeChangeSoundness
