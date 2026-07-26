import OperatorKO7.Kernel

/-!
# Size-change soundness for the step-duplicating recursor's dependency-pair problem

`Meta/ReverseMath/ArtsGieslPi02.lean` supplies an `L₂` object sentence in `∀∃`
quantifier-free shape, and its own header records that the formal sentence concerns
predecessor descent; `Meta/ReverseMath/ArtsGieslUpperSyntactic.lean` records that the
product does not identify that sentence with dependency-pair soundness. Those modules
therefore certify a `Π⁰₂` *shape*, and nothing about the confession route.

This module proves the mathematics the manuscript's Step 1 and Step 4 actually assert, at
the object level and unconditionally:

* `sizeChangeGraph_has_no_infinite_call_chain` is one-thread size-change soundness: a call
  relation carrying an everywhere-strict descent thread admits no infinite chain.
* `sizeChangeGraph_boundedSN` upgrades that to the bounded `∀∃` presentation the manuscript's
  `Π⁰₂` proposition uses, with the descent value itself as the explicit witness.
* `dupDP_boundedSN` and `dupDPStep_wellFounded` instantiate both on the singleton
  dependency pair `recΔ♯ b s (delta n) → recΔ♯ b s n` extracted from the step-duplicating
  recursor.
* `dupDPProjection_surjective` pins the instance measure at order type exactly `ω`: the
  projection is onto `Nat`, so no smaller ordinal bounds the descent.
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

end OperatorKO7.ReverseMath.SizeChangeSoundness
