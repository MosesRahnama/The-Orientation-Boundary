import Mathlib.Tactic
import OperatorKO7.Meta.Methods.OrientationClosure.SchemaCore
import OperatorKO7.Meta.Methods.OrientationClosure.FreePolynomialTermination
import OperatorKO7.Meta.Methods.OrientationClosure.MethodRowsTypedCalculi

/-!
# Method rows for the other-calculi group (W4)

Two rows: `infinitaryRewritingTermination` (Kennaway, Klop, Sleep and de Vries, "Transfinite
reductions in orthogonal term rewriting systems", Information and Computation 119(1), 1995) and
`higherOrderTupleInterpretation` (Kop and Vale, "Tuple interpretations for higher-order
complexity", FSCD 2021, LIPIcs 195, article 31). The higher-order row carries the native Kop and
Vale cost-size tuple data and laws, not the ambient affine first component on the ground image.

Every row follows the P5 row contract: `Data`, `Laws`, `Accepts`, `Result` with a verdict line, a
`Witness` with `_laws`, `_result`, `_feature`, and `_mutation`, plus `_sound` or `_universal`, and
a `_scope` definition for the fragment.

External trust: none.  Mathlib only.
-/

set_option autoImplicit false

namespace OperatorKO7.Methods.OrientationClosure.MethodRowsOtherCalculi

open OperatorKO7.Meta.Rewriting
open OperatorKO7.Methods.OrientationClosure.SchemaCore
open OperatorKO7.Methods.OrientationClosure.FreePolynomialTermination
open OperatorKO7.Methods.OrientationClosure.MethodRowsTypedCalculi

universe u

section InfinitaryRewriting

variable {ν : Type u}

/-! ## 1. Row `infinitaryRewritingTermination` -/

/-- Depth-indexed truncation of a free term: subterms at depth `k` are cut and replaced by the
hole `.var 0` of the one-variable skeleton carrier. -/
def truncAt : Nat → FreeTerm ν → FreeTerm (Fin 1)
  | 0, _ => .var 0
  | _ + 1, .var _ => .var 0
  | _ + 1, .zero => .zero
  | k + 1, .succ t => .succ (truncAt k t)
  | k + 1, .wrap a b => .wrap (truncAt k a) (truncAt k b)
  | k + 1, .recur a b c => .recur (truncAt k a) (truncAt k b) (truncAt k c)

@[simp] theorem truncAt_zero_view (t : FreeTerm ν) : truncAt 0 t = .var (0 : Fin 1) := rfl

@[simp] theorem truncAt_var (k : Nat) (x : ν) :
    truncAt k (.var x : FreeTerm ν) = .var (0 : Fin 1) := by
  cases k <;> rfl

@[simp] theorem truncAt_zero_const (k : Nat) :
    truncAt (k + 1) (.zero : FreeTerm ν) = .zero := rfl

@[simp] theorem truncAt_succ_view (k : Nat) (t : FreeTerm ν) :
    truncAt (k + 1) (.succ t) = .succ (truncAt k t) := rfl

@[simp] theorem truncAt_wrap_view (k : Nat) (a b : FreeTerm ν) :
    truncAt (k + 1) (.wrap a b) = .wrap (truncAt k a) (truncAt k b) := rfl

@[simp] theorem truncAt_recur_view (k : Nat) (a b c : FreeTerm ν) :
    truncAt (k + 1) (.recur a b c) =
      .recur (truncAt k a) (truncAt k b) (truncAt k c) := rfl

/-- Truncating at a shallower depth after a deeper truncation forgets nothing. -/
theorem truncAt_truncAt_of_le {k m : Nat} (h : k ≤ m) (t : FreeTerm ν) :
    truncAt k (truncAt m t) = truncAt k t := by
  induction t generalizing k m with
  | var x =>
      rcases k with _ | k <;> rcases m with _ | m <;> rfl
  | zero =>
      rcases k with _ | k
      · rfl
      · rcases m with _ | m
        · omega
        · rfl
  | succ t ih =>
      rcases k with _ | k
      · rfl
      · rcases m with _ | m
        · omega
        · simp only [truncAt]
          rw [ih (Nat.le_of_succ_le_succ h)]
  | wrap a b iha ihb =>
      rcases k with _ | k
      · rfl
      · rcases m with _ | m
        · omega
        · simp only [truncAt]
          rw [iha (Nat.le_of_succ_le_succ h), ihb (Nat.le_of_succ_le_succ h)]
  | recur a b c iha ihb ihc =>
      rcases k with _ | k
      · rfl
      · rcases m with _ | m
        · omega
        · simp only [truncAt]
          rw [iha (Nat.le_of_succ_le_succ h), ihb (Nat.le_of_succ_le_succ h),
            ihc (Nat.le_of_succ_le_succ h)]

/-- A depth-indexed tower of wraps over the hole. -/
def wrapIter : Nat → FreeTerm (Fin 1) → FreeTerm (Fin 1)
  | 0, t => t
  | k + 1, t => .wrap (.var 0) (wrapIter k t)

/-- A depth-indexed chain of successors over the hole. -/
def succIter : Nat → FreeTerm (Fin 1) → FreeTerm (Fin 1)
  | 0, t => t
  | k + 1, t => .succ (succIter k t)

/-- Truncating a depth-`k` tower at depth `k` leaves the tower. -/
theorem truncAt_wrapIter_self (k : Nat) (t : FreeTerm (Fin 1)) :
    truncAt k (wrapIter k t) = wrapIter k (.var 0) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [wrapIter, truncAt]
      rw [truncAt_var, ih]

/-- Truncating a tower at a depth at most the tower height leaves that depth's tower. -/
theorem truncAt_wrapIter_of_le {k n : Nat} (h : k ≤ n) (t : FreeTerm (Fin 1)) :
    truncAt k (wrapIter n t) = wrapIter k (.var 0) := by
  induction n generalizing k with
  | zero =>
      have hk : k = 0 := Nat.eq_zero_of_le_zero h
      subst hk
      rfl
  | succ n ih =>
      rcases lt_or_eq_of_le h with hlt | hEq
      · rcases k with _ | k
        · rfl
        · simp only [wrapIter, truncAt]
          rw [truncAt_var, ih (by omega : k ≤ n)]
      · subst hEq
        exact truncAt_wrapIter_self (n + 1) t

/-- Truncating a successor chain at depth `k` leaves the depth-`k` successor chain. -/
theorem truncAt_succIter_self (k : Nat) (t : FreeTerm (Fin 1)) :
    truncAt k (succIter k t) = succIter k (.var 0) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [succIter, truncAt]
      rw [ih]

/-- Truncating a successor chain at a depth at most its height leaves that depth's chain. -/
theorem truncAt_succIter_of_le {k n : Nat} (h : k ≤ n) (t : FreeTerm (Fin 1)) :
    truncAt k (succIter n t) = succIter k (.var 0) := by
  induction n generalizing k with
  | zero =>
      have hk : k = 0 := Nat.eq_zero_of_le_zero h
      subst hk
      rfl
  | succ n ih =>
      rcases lt_or_eq_of_le h with hlt | hEq
      · rcases k with _ | k
        · rfl
        · simp only [succIter, truncAt]
          rw [ih (by omega : k ≤ n)]
      · subst hEq
        exact truncAt_succIter_self (n + 1) t

/-- Truncations of two successor chains agree once the depth is at most both heights. -/
theorem truncAt_succIter_eq_of_le {j m m' : Nat} (h : j ≤ m) (h' : j ≤ m') :
    truncAt j (succIter m (.var (0 : Fin 1))) =
      truncAt j (succIter m' (.var (0 : Fin 1))) := by
  rw [truncAt_succIter_of_le h, truncAt_succIter_of_le h']

/-- Wrapping the argument and shifting the tower by one agree. -/
theorem wrapIter_wrap (n : Nat) (t : FreeTerm (Fin 1)) :
    wrapIter n (.wrap (.var 0) t) = wrapIter (n + 1) t := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [wrapIter] at *
      rw [ih]

/-- A depth-indexed coherent presentation of an infinite term: the depth-`k` trunk is a one-hole
skeleton and the depth-`k` view of the depth-`k+1` trunk is the depth-`k` trunk. -/
structure InfinitaryTerm where
  trunks : Nat → FreeTerm (Fin 1)
  trunk_zero : trunks 0 = .var 0
  coherent : ∀ k, truncAt k (trunks (k + 1)) = trunks k

/-- The infinite tower of wraps. -/
def omegaTower : InfinitaryTerm where
  trunks := fun k => wrapIter k (.var 0)
  trunk_zero := rfl
  coherent := by
    intro k
    exact truncAt_wrapIter_of_le (Nat.le_succ k) (.var 0)

/-- Congruence used for the coherence of the depth-indexed duplicating stages: truncation at
depth `k` cannot see the difference between two successor chains of height at least `k`. -/
theorem truncAt_dupStage_congruent : ∀ k n m m', k ≤ m → k ≤ m' →
    truncAt k (wrapIter n (.recur (.var 0) (.var 0) (succIter m (.var 0)))) =
      truncAt k (wrapIter n (.recur (.var 0) (.var 0) (succIter m' (.var 0)))) := by
  intro k
  induction k with
  | zero => intro n m m' _ _; rfl
  | succ k ih =>
      intro n m m' hm hm'
      rcases n with _ | n
      · simp only [wrapIter, truncAt]
        exact congrArg
          (fun z => (.recur (truncAt k (.var 0)) (truncAt k (.var 0)) z :
            FreeTerm (Fin 1)))
          (by rw [truncAt_succIter_of_le (by omega : k ≤ m),
            truncAt_succIter_of_le (by omega : k ≤ m')])
      · simp only [wrapIter, truncAt]
        exact congrArg
          (fun z => (.wrap (truncAt k (.var 0)) z : FreeTerm (Fin 1)))
          (ih n m m' (by omega : k ≤ m) (by omega : k ≤ m'))

/-- The `n`-th stage of the infinite duplicating reduction on the counter spine. -/
def dupStage (n : Nat) : InfinitaryTerm where
  trunks := fun k =>
    truncAt k (wrapIter n (.recur (.var 0) (.var 0) (succIter k (.var 0))))
  trunk_zero := rfl
  coherent := by
    intro k
    show truncAt k (truncAt (k + 1)
        (wrapIter n (.recur (.var 0) (.var 0) (succIter (k + 1) (.var 0))))) =
      truncAt k (wrapIter n (.recur (.var 0) (.var 0) (succIter k (.var 0))))
    rw [truncAt_truncAt_of_le (Nat.le_succ k)]
    exact truncAt_dupStage_congruent k n (k + 1) k (Nat.le_succ k) le_rfl

@[simp] theorem dupStage_trunks (n k : Nat) :
    (dupStage n).trunks k =
      truncAt k (wrapIter n (.recur (.var 0) (.var 0) (succIter k (.var 0)))) := rfl

/-- Constructor tag used to separate the tower shape from a recursor shape. -/
@[simp] def ctorTag : FreeTerm ν → Nat
  | .var _ => 0
  | .zero => 1
  | .succ _ => 2
  | .wrap _ _ => 3
  | .recur _ _ _ => 4

/-- Trunks distinguish the first two duplicating stages. -/
theorem dupStage_zero_ne_one : dupStage 0 ≠ dupStage 1 := by
  intro h
  have h1 := congrArg (fun T : InfinitaryTerm => T.trunks 1) h
  simp only [dupStage_trunks, truncAt, wrapIter, succIter] at h1
  have h2 := congrArg ctorTag h1
  simp [ctorTag] at h2

/-- One native step of the duplicating rule on the trunk fragment at redex depth `d`: below the
redex depth the two presentations are the tower, at and below larger depths they are the
presentation of `recur b s (succ n)` and of its contractum `wrap s (recur b s n)`. -/
def InfDupStepAt (d : Nat) (t u : InfinitaryTerm) : Prop :=
  (∀ k, k ≤ d →
    t.trunks k = wrapIter k (.var 0) ∧ u.trunks k = wrapIter k (.var 0)) ∧
  (∀ k, d < k →
    t.trunks k =
        truncAt k (wrapIter d (.recur (.var 0) (.var 0) (succIter k (.var 0)))) ∧
      u.trunks k =
        truncAt k (wrapIter d
          (.wrap (.var 0) (.recur (.var 0) (.var 0) (succIter k (.var 0))))))

/-- The standard stage family is an accepted infinite reduction: each stage is the native
contractum of the previous one. -/
theorem dupStage_step (n : Nat) : InfDupStepAt n (dupStage n) (dupStage (n + 1)) := by
  constructor
  · intro k hk
    constructor
    · rw [dupStage_trunks]
      exact truncAt_wrapIter_of_le hk _
    · rw [dupStage_trunks]
      exact truncAt_wrapIter_of_le (le_trans hk (Nat.le_succ n)) _
  · intro k hk
    constructor
    · rw [dupStage_trunks]
    · rw [dupStage_trunks]
      rw [wrapIter_wrap]

/-- A presentation converges to a limit presentation when every finite trunk stabilizes. -/
def ConvergesTo (u : Nat → InfinitaryTerm) (L : InfinitaryTerm) : Prop :=
  ∀ k, ∃ N, ∀ n, N ≤ n → (u n).trunks k = L.trunks k

/-- Native data of the row: the stage presentation, the certified redex depth of each step, and
the source stage. -/
structure infinitaryRewritingTerminationData where
  /-- Depth-indexed stage presentations. -/
  stages : Nat → InfinitaryTerm
  /-- Certified redex depth of each step. -/
  depths : Nat → Nat
  /-- Source stage of the reduction. -/
  source : InfinitaryTerm

/-- Admissibility laws. Pinned to Kennaway, Klop, Sleep, de Vries, "Transfinite reductions in orthogonal term rewriting systems",
Information and Computation 119(1), 1995, Definitions 2.1-2.6 (infinitary terms, reduction
sequences, convergence): the sequence starts at the source, each step is the duplicating root
rule at the certified depth, and the depths are unbounded (strong convergence). -/
def infinitaryRewritingTerminationLaws
    (M : infinitaryRewritingTerminationData) : Prop :=
  M.stages 0 = M.source ∧
  (∀ n, InfDupStepAt (M.depths n) (M.stages n) (M.stages (n + 1))) ∧
  (∀ d, ∃ N, ∀ n, N ≤ n → d ≤ M.depths n)

/-- The method's acceptance of the free duplicating rule: every stage is the certified contractum
of the previous one, so the infinite reduction is a reduction by `RootStep.recurSucc`. -/
def infinitaryRewritingTerminationAccepts
    (M : infinitaryRewritingTerminationData) : Prop :=
  ∀ n, InfDupStepAt (M.depths n) (M.stages n) (M.stages (n + 1))

/-- The method accepts the free two-rule system on the trunk fragment and the yield is
convergence of the accepted infinite reduction to the infinite tower; the finite fragment is a
separate well-foundedness theorem. The omitted general statement is named in
`infinitaryRewritingTermination_scope`.
Verdict: fragment escape. -/
def infinitaryRewritingTerminationResult
    (M : infinitaryRewritingTerminationData) : Prop :=
  infinitaryRewritingTerminationAccepts M ∧ ConvergesTo M.stages omegaTower

/-- Strong convergence of the certified depths yields convergence of the trunk presentations to
the infinite tower. -/
theorem infinitaryRewritingTermination_sound :
    ∀ M, infinitaryRewritingTerminationLaws M →
      infinitaryRewritingTerminationAccepts M → infinitaryRewritingTerminationResult M := by
  intro M hL hA
  refine ⟨hA, ?_⟩
  intro k
  obtain ⟨N, hN⟩ := hL.2.2 k
  refine ⟨N + 1, fun n hn => ?_⟩
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hj : N ≤ j := by omega
  exact ((hL.2.1 j).1 k (hN j hj)).2

/-- The witness reduction: the duplicating rule at redex depth `n` at stage `n`. -/
def infinitaryRewritingTerminationWitness : infinitaryRewritingTerminationData where
  stages := dupStage
  depths := fun n => n
  source := dupStage 0

theorem infinitaryRewritingTerminationWitness_laws :
    infinitaryRewritingTerminationLaws infinitaryRewritingTerminationWitness :=
  ⟨rfl, dupStage_step, fun d => ⟨d, fun _ hn => hn⟩⟩

theorem infinitaryRewritingTerminationWitness_result :
    infinitaryRewritingTerminationResult infinitaryRewritingTerminationWitness :=
  infinitaryRewritingTermination_sound _ infinitaryRewritingTerminationWitness_laws
    infinitaryRewritingTerminationWitness_laws.2.1

/-- Finite terms admit no infinite forward contextual reduction. -/
theorem finiteFragment_wellFounded :
    WellFounded (fun u t : FreeTerm Empty => ContextStep t u) :=
  main_free_contextual_termination Empty

/-- The stage family converges to the infinite tower. -/
theorem infiniteTree_converges : ConvergesTo dupStage omegaTower := by
  intro k
  refine ⟨k, fun n hn => ?_⟩
  rw [dupStage_trunks]
  exact truncAt_wrapIter_of_le hn _

/-- The root-active control relation: a term steps to itself. -/
def RootActiveStep (t u : InfinitaryTerm) : Prop := u = t

/-- A root-active loop is a convergent infinite sequence whose every stage is a redex, so
trunk convergence does not deliver normalization. -/
theorem rootActive_loop_control :
    ConvergesTo (fun _ => omegaTower) omegaTower ∧ RootActiveStep omegaTower omegaTower :=
  ⟨fun _ => ⟨0, fun _ _ => rfl⟩, rfl⟩

/-- The feature of the witness: the finite fragment is well founded, the infinite reduction
converges, every stage has a next step, and the root-active loop control separates convergence
from normalization. -/
theorem infinitaryRewritingTerminationWitness_feature :
    WellFounded (fun u t : FreeTerm Empty => ContextStep t u) ∧
    ConvergesTo dupStage omegaTower ∧
    (∀ n, InfDupStepAt n (dupStage n) (dupStage (n + 1))) ∧
    (ConvergesTo (fun _ => omegaTower) omegaTower ∧ RootActiveStep omegaTower omegaTower) :=
  ⟨finiteFragment_wellFounded, infiniteTree_converges, dupStage_step, rootActive_loop_control⟩

/-- The mutation shifts the stage family by one while keeping the anchored source: the start law
then fails. -/
theorem infinitaryRewritingTermination_mutation :
    ¬ infinitaryRewritingTerminationLaws
      { infinitaryRewritingTerminationWitness with stages := fun n => dupStage (n + 1) } := by
  intro h
  exact dupStage_zero_ne_one h.1.symm

/-- The scope of the fragment: the step conditions alone, without the unbounded certified depth
schedule, do not bound convergence; the general infinitary termination theorem for arbitrary
infinite-term presentations and root-active systems is not claimed. -/
def infinitaryRewritingTermination_scope : Prop :=
  ∀ (M : infinitaryRewritingTerminationData),
    (∀ n, InfDupStepAt (M.depths n) (M.stages n) (M.stages (n + 1))) →
      ConvergesTo M.stages omegaTower

/-- The unindexed infinitary duplicator relation: one contraction may occur at any certified
finite depth. -/
def InfDupStep (t u : InfinitaryTerm) : Prop :=
  ∃ d, InfDupStepAt d t u

/-- The standard stages form an infinite reduction of the unindexed relation. -/
theorem dupStage_infDupStep (n : Nat) : InfDupStep (dupStage n) (dupStage (n + 1)) :=
  ⟨n, dupStage_step n⟩

/-- Strong convergence is not termination: the infinitary duplicator relation is not well
founded because the certified stage family supplies an infinite reduction. -/
theorem infDupStep_not_wellFounded :
    ¬ WellFounded (fun u t : InfinitaryTerm => InfDupStep t u) := by
  intro hwf
  exact (WellFounded.wellFounded_iff_no_descending_seq.1 hwf).elim
    ⟨dupStage, fun n => dupStage_infDupStep n⟩

/-- Exact infinitary-rewriting classification. Finite terms terminate, while the infinitary
extension admits a genuine infinite strongly convergent reduction. Thus convergence and strong
normalization are distinct properties, and the witness establishes the former rather than
mislabeling it as the latter. -/
theorem infinitaryRewritingTermination_methodIdentity :
    WellFounded (fun u t : FreeTerm Empty => ContextStep t u) ∧
      infinitaryRewritingTerminationResult infinitaryRewritingTerminationWitness ∧
      ¬ WellFounded (fun u t : InfinitaryTerm => InfDupStep t u) :=
  ⟨finiteFragment_wellFounded, infinitaryRewritingTerminationWitness_result,
    infDupStep_not_wellFounded⟩

end InfinitaryRewriting

section HigherOrderTuple

variable {ν : Type}

/-- Native cost-size tuple data of the higher-order tuple interpretation: the cost coefficients
of the System T symbols and the coupling of the iterator clause. Pinned to Kop and Vale, "Tuple
interpretations for higher-order complexity", FSCD 2021, LIPIcs 195, article 31, Definition 8 and
Theorem 3.2 (a type-level cost-size assignment with monotone symbol interpretations and a
recursive clause that couples the step and counter costs); the data carry the method's native
higher-order constants, not the ambient affine first component on the ground image. -/
structure higherOrderTupleInterpretationData where
  costBase : Nat
  costSuccBias : Nat
  costSuccScale : Nat
  costAppLeft : Nat
  costAppRight : Nat
  costIterBase : Nat
  costIterStep : Nat
  costIterCounter : Nat
  costIterCouple : Nat

/-- Cost of a symbol application from the costs of its arguments. -/
def hotiSymCost (M : higherOrderTupleInterpretationData) : ASym TSym → List Nat → Nat
  | .fn .zero, _ => M.costBase
  | .fn .succ, [c] => M.costSuccBias + M.costSuccScale * c
  | .fn (.iter _), [cb, cs, cn] =>
      M.costIterBase * cb + M.costIterStep * cs + M.costIterCounter * cn +
        M.costIterCouple * (cs * cn)
  | .fn (.grec _), [cb, cs, cn] =>
      M.costIterBase * cb + M.costIterStep * cs + M.costIterCounter * cn +
        M.costIterCouple * (cs * cn)
  | .ap, [cf, ca] => M.costAppLeft * cf + M.costAppRight * ca
  | _, _ => 0

mutual
  /-- Native cost of a simply typed applicative term. -/
  def hotiCost (M : higherOrderTupleInterpretationData) : TTerm ν → Nat
    | .var _ => 0
    | .app f args => hotiSymCost M f (hotiCostList M args)
  /-- Native cost of an argument list. -/
  def hotiCostList (M : higherOrderTupleInterpretationData) : List (TTerm ν) → List Nat
    | [] => []
    | a :: as => hotiCost M a :: hotiCostList M as
end

@[simp] theorem hotiCost_var (M : higherOrderTupleInterpretationData) (x : ν) :
    hotiCost M (.var x : TTerm ν) = 0 := rfl

@[simp] theorem hotiCost_app (M : higherOrderTupleInterpretationData) (f : ASym TSym)
    (args : List (TTerm ν)) :
    hotiCost M (.app f args) = hotiSymCost M f (hotiCostList M args) := rfl

@[simp] theorem hotiCostList_nil (M : higherOrderTupleInterpretationData) :
    hotiCostList M ([] : List (TTerm ν)) = [] := rfl

@[simp] theorem hotiCostList_cons (M : higherOrderTupleInterpretationData) (a : TTerm ν)
    (as : List (TTerm ν)) :
    hotiCostList M (a :: as) = hotiCost M a :: hotiCostList M as := rfl

/-- Cost of a free term under the native higher-order semantics. -/
def hotiFreeCost (M : higherOrderTupleInterpretationData) : FreeTerm ν → Nat
  | .var _ => 0
  | .zero => M.costBase
  | .succ t => M.costSuccBias + M.costSuccScale * hotiFreeCost M t
  | .wrap x y => M.costAppLeft * hotiFreeCost M x + M.costAppRight * hotiFreeCost M y
  | .recur b s n =>
      M.costIterBase * hotiFreeCost M b + M.costIterStep * hotiFreeCost M s +
        M.costIterCounter * hotiFreeCost M n +
        M.costIterCouple * (hotiFreeCost M s * hotiFreeCost M n)

/-- Admissibility laws. Pinned to Kop and Vale, "Tuple interpretations for higher-order
complexity", FSCD 2021, LIPIcs 195, article 31, Definition 8 (a cost-size tuple interpretation:
the cost of `succ` is `bias + scale * c` with `scale = 1`, the cost of `@` is the sum of the two
component costs, and the iterator clause couples the step and counter costs) with the
strict-monotonicity conditions of the orientation theorem: the base, the iterator base and the
successor drift are positive, and the iterator counter and coupling coefficients are positive. -/
def higherOrderTupleInterpretationLaws (M : higherOrderTupleInterpretationData) : Prop :=
  1 ≤ M.costBase ∧ 1 ≤ M.costSuccBias ∧ M.costSuccScale = 1 ∧
    M.costAppLeft = 1 ∧ M.costAppRight = 1 ∧ 1 ≤ M.costIterBase ∧
    1 ≤ M.costIterStep ∧ 1 ≤ M.costIterCounter ∧ 1 ≤ M.costIterCouple

/-- The method's own acceptance of the free two-rule system through the adapter `toA`: the native
cost strictly decreases on the embedded zero rule and duplicating rule at every result type. -/
def higherOrderTupleInterpretationAccepts (M : higherOrderTupleInterpretationData) : Prop :=
  (∀ (A : TTy) (μ : Type) (b s : FreeTerm μ),
    hotiCost M (toA A b) < hotiCost M (toA A (.recur b s .zero))) ∧
  (∀ (A : TTy) (μ : Type) (b s n : FreeTerm μ),
    hotiCost M (toA A (.wrap s (.recur b s n))) <
      hotiCost M (toA A (.recur b s (.succ n))))

/-- Verdict: escape. The native cost-size tuple interpretation accepts the free two-rule system
through `toA`, and its soundness theorem yields termination of the contextual relation
`SchemaCore.ContextStep` over every variable type. The typed iterator relation and the polynomial
derivation-length bound of the source are named in `higherOrderTupleInterpretation_scope`. -/
def higherOrderTupleInterpretationResult (M : higherOrderTupleInterpretationData) : Prop :=
  higherOrderTupleInterpretationAccepts M ∧
    ∀ μ : Type, WellFounded (fun u t : FreeTerm μ => ContextStep t u)

/-- The native cost of the higher-order image is the free cost. -/
theorem hotiCost_toA (M : higherOrderTupleInterpretationData) (A : TTy) (t : FreeTerm ν) :
    hotiCost M (toA A t) = hotiFreeCost M t := by
  induction t with
  | var x => rfl
  | zero => rfl
  | succ t ih =>
      simp only [toA, hotiCost_app, hotiCostList_cons, hotiCostList_nil, hotiSymCost,
        hotiFreeCost, ih]
  | wrap x y ihx ihy =>
      simp only [toA, hotiCost_app, hotiCostList_cons, hotiCostList_nil, hotiSymCost,
        hotiFreeCost, ihx, ihy]
  | recur b s n ihb ihs ihn =>
      simp only [toA, hotiCost_app, hotiCostList_cons, hotiCostList_nil, hotiSymCost,
        hotiFreeCost, ihb, ihs, ihn]

/-- The zero rule strictly decreases the native cost. -/
theorem hotiFreeCost_zero (M : higherOrderTupleInterpretationData)
    (hL : higherOrderTupleInterpretationLaws M) (b s : FreeTerm ν) :
    hotiFreeCost M b < hotiFreeCost M (.recur b s .zero) := by
  obtain ⟨hbase, hbias, hscale, haL, haR, hiB, hiS, hiC, hiQ⟩ := hL
  simp only [hotiFreeCost]
  have h1 : hotiFreeCost M b ≤ M.costIterBase * hotiFreeCost M b :=
    Nat.le_mul_of_pos_left _ (by omega)
  have h2 : 1 ≤ M.costIterCounter * M.costBase := by
    simpa using Nat.mul_le_mul hiC hbase
  omega

/-- The duplicating rule strictly decreases the native cost: the coupling pays for the wrapper's
copy of the step argument and leaves one unit over. -/
theorem hotiFreeCost_dup (M : higherOrderTupleInterpretationData)
    (hL : higherOrderTupleInterpretationLaws M) (b s n : FreeTerm ν) :
    hotiFreeCost M (.wrap s (.recur b s n)) <
      hotiFreeCost M (.recur b s (.succ n)) := by
  obtain ⟨hbase, hbias, hscale, haL, haR, hiB, hiS, hiC, hiQ⟩ := hL
  simp only [hotiFreeCost, hscale, haL, haR, Nat.one_mul]
  have h1 : 1 ≤ M.costIterCounter * M.costSuccBias := by
    simpa using Nat.mul_le_mul hiC hbias
  have h2 : hotiFreeCost M s ≤ M.costIterCouple * (hotiFreeCost M s * M.costSuccBias) := by
    calc hotiFreeCost M s ≤ M.costIterCouple * hotiFreeCost M s :=
          Nat.le_mul_of_pos_left _ (by omega)
      _ = M.costIterCouple * (hotiFreeCost M s * 1) := by ring
      _ ≤ M.costIterCouple * (hotiFreeCost M s * M.costSuccBias) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hbias)
  have hkey1 : M.costIterCounter * (M.costSuccBias + hotiFreeCost M n) =
      M.costIterCounter * M.costSuccBias + M.costIterCounter * hotiFreeCost M n := by ring
  have hkey2 : M.costIterCouple * (hotiFreeCost M s * (M.costSuccBias + hotiFreeCost M n)) =
      M.costIterCouple * (hotiFreeCost M s * M.costSuccBias) +
        M.costIterCouple * (hotiFreeCost M s * hotiFreeCost M n) := by ring
  rw [hkey1, hkey2]
  omega

/-- The successor context preserves the strict cost decrease. -/
theorem hotiFreeCost_succ_lt (M : higherOrderTupleInterpretationData)
    (hL : higherOrderTupleInterpretationLaws M) {x y : FreeTerm ν}
    (h : hotiFreeCost M x < hotiFreeCost M y) :
    hotiFreeCost M (.succ x) < hotiFreeCost M (.succ y) := by
  obtain ⟨_, _, hscale, _, _, _, _, _, _⟩ := hL
  simp only [hotiFreeCost, hscale]
  omega

/-- The left wrapping context preserves the strict cost decrease. -/
theorem hotiFreeCost_wrapLeft_lt (M : higherOrderTupleInterpretationData)
    (hL : higherOrderTupleInterpretationLaws M) (r : FreeTerm ν) {x y : FreeTerm ν}
    (h : hotiFreeCost M x < hotiFreeCost M y) :
    hotiFreeCost M (.wrap x r) < hotiFreeCost M (.wrap y r) := by
  obtain ⟨_, _, _, haL, _, _, _, _, _⟩ := hL
  simp only [hotiFreeCost, haL]
  omega

/-- The right wrapping context preserves the strict cost decrease. -/
theorem hotiFreeCost_wrapRight_lt (M : higherOrderTupleInterpretationData)
    (hL : higherOrderTupleInterpretationLaws M) (l : FreeTerm ν) {x y : FreeTerm ν}
    (h : hotiFreeCost M x < hotiFreeCost M y) :
    hotiFreeCost M (.wrap l x) < hotiFreeCost M (.wrap l y) := by
  obtain ⟨_, _, _, _, haR, _, _, _, _⟩ := hL
  simp only [hotiFreeCost, haR]
  omega

/-- The base position of `recur` preserves the strict cost decrease. -/
theorem hotiFreeCost_recurBase_lt (M : higherOrderTupleInterpretationData)
    (hL : higherOrderTupleInterpretationLaws M) (s n : FreeTerm ν) {x y : FreeTerm ν}
    (h : hotiFreeCost M x < hotiFreeCost M y) :
    hotiFreeCost M (.recur x s n) < hotiFreeCost M (.recur y s n) := by
  obtain ⟨_, _, _, _, _, hiB, _, _, _⟩ := hL
  simp only [hotiFreeCost]
  have hB : M.costIterBase * hotiFreeCost M x < M.costIterBase * hotiFreeCost M y :=
    Nat.mul_lt_mul_of_pos_left h (by omega)
  omega

/-- The step position of `recur` preserves the strict cost decrease. -/
theorem hotiFreeCost_recurStep_lt (M : higherOrderTupleInterpretationData)
    (hL : higherOrderTupleInterpretationLaws M) (b n : FreeTerm ν) {x y : FreeTerm ν}
    (h : hotiFreeCost M x < hotiFreeCost M y) :
    hotiFreeCost M (.recur b x n) < hotiFreeCost M (.recur b y n) := by
  obtain ⟨_, _, _, _, _, _, hiS, _, _⟩ := hL
  simp only [hotiFreeCost]
  have hS : M.costIterStep * hotiFreeCost M x < M.costIterStep * hotiFreeCost M y :=
    Nat.mul_lt_mul_of_pos_left h (by omega)
  have hQ : M.costIterCouple * (hotiFreeCost M x * hotiFreeCost M n) ≤
      M.costIterCouple * (hotiFreeCost M y * hotiFreeCost M n) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (le_of_lt h))
  omega

/-- The counter position of `recur` preserves the strict cost decrease. -/
theorem hotiFreeCost_recurCounter_lt (M : higherOrderTupleInterpretationData)
    (hL : higherOrderTupleInterpretationLaws M) (b s : FreeTerm ν) {x y : FreeTerm ν}
    (h : hotiFreeCost M x < hotiFreeCost M y) :
    hotiFreeCost M (.recur b s x) < hotiFreeCost M (.recur b s y) := by
  obtain ⟨_, _, _, _, _, _, _, hiC, _⟩ := hL
  simp only [hotiFreeCost]
  have hC : M.costIterCounter * hotiFreeCost M x < M.costIterCounter * hotiFreeCost M y :=
    Nat.mul_lt_mul_of_pos_left h (by omega)
  have hQ : M.costIterCouple * (hotiFreeCost M s * hotiFreeCost M x) ≤
      M.costIterCouple * (hotiFreeCost M s * hotiFreeCost M y) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (le_of_lt h))
  omega

/-- Every free context preserves the strict cost decrease. -/
theorem hotiFreeCost_context_lt (M : higherOrderTupleInterpretationData)
    (hL : higherOrderTupleInterpretationLaws M) {t u : FreeTerm ν}
    (h : hotiFreeCost M u < hotiFreeCost M t) :
    ∀ C : FreeContext ν, hotiFreeCost M (C.plug u) < hotiFreeCost M (C.plug t) := by
  intro C
  induction C with
  | hole => exact h
  | succ C ih => exact hotiFreeCost_succ_lt M hL ih
  | wrapLeft C r ih => exact hotiFreeCost_wrapLeft_lt M hL r ih
  | wrapRight l C ih => exact hotiFreeCost_wrapRight_lt M hL l ih
  | recurBase C s n ih => exact hotiFreeCost_recurBase_lt M hL s n ih
  | recurStep b C n ih => exact hotiFreeCost_recurStep_lt M hL b n ih
  | recurCounter b s C ih => exact hotiFreeCost_recurCounter_lt M hL b s ih

/-- Every root step of the free schema strictly decreases the native cost. -/
theorem hotiFreeCost_root_lt (M : higherOrderTupleInterpretationData)
    (hA : higherOrderTupleInterpretationAccepts M) {t u : FreeTerm ν} (h : RootStep t u) :
    hotiFreeCost M u < hotiFreeCost M t := by
  cases h with
  | recurZero =>
      simpa only [hotiCost_toA] using hA.1 natTy ν _ _
  | recurSucc =>
      simpa only [hotiCost_toA] using hA.2 natTy ν _ _ _

/-- Every contextual step of the free schema strictly decreases the native cost. -/
theorem hotiFreeCost_contextStep_lt (M : higherOrderTupleInterpretationData)
    (hL : higherOrderTupleInterpretationLaws M)
    (hA : higherOrderTupleInterpretationAccepts M) {t u : FreeTerm ν}
    (h : ContextStep t u) : hotiFreeCost M u < hotiFreeCost M t := by
  cases h with
  | lift C hr => exact hotiFreeCost_context_lt M hL (hotiFreeCost_root_lt M hA hr) C

/-- **Soundness** of the native cost-size tuple interpretation: acceptance and the admissibility
laws give termination of the contextual relation of the free recursor. -/
theorem higherOrderTupleInterpretation_sound :
    ∀ M, higherOrderTupleInterpretationLaws M → higherOrderTupleInterpretationAccepts M →
      higherOrderTupleInterpretationResult M := by
  intro M hL hA
  refine ⟨hA, fun μ => ?_⟩
  exact Subrelation.wf (fun {u t} h => hotiFreeCost_contextStep_lt M hL hA h)
    (InvImage.wf (hotiFreeCost M) Nat.lt_wfRel.wf)

/-- Witness: the coupled cost with unit coefficients. -/
def higherOrderTupleInterpretationWitness : higherOrderTupleInterpretationData where
  costBase := 1
  costSuccBias := 1
  costSuccScale := 1
  costAppLeft := 1
  costAppRight := 1
  costIterBase := 1
  costIterStep := 1
  costIterCounter := 1
  costIterCouple := 1

theorem higherOrderTupleInterpretationWitness_laws :
    higherOrderTupleInterpretationLaws higherOrderTupleInterpretationWitness :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide⟩

theorem higherOrderTupleInterpretationWitness_accepts :
    higherOrderTupleInterpretationAccepts higherOrderTupleInterpretationWitness := by
  constructor
  · intro A μ b s
    rw [hotiCost_toA, hotiCost_toA]
    exact hotiFreeCost_zero _ higherOrderTupleInterpretationWitness_laws b s
  · intro A μ b s n
    rw [hotiCost_toA, hotiCost_toA]
    exact hotiFreeCost_dup _ higherOrderTupleInterpretationWitness_laws b s n

theorem higherOrderTupleInterpretationWitness_result :
    higherOrderTupleInterpretationResult higherOrderTupleInterpretationWitness :=
  higherOrderTupleInterpretation_sound _ higherOrderTupleInterpretationWitness_laws
    higherOrderTupleInterpretationWitness_accepts

/-- **Defining feature.** The native higher-order clauses and the coupling: the cost of an
application is the sum of the two component costs, and the coupled iterator clause orients the
duplicating rule on the free image. -/
theorem higherOrderTupleInterpretationWitness_feature :
    higherOrderTupleInterpretationAccepts higherOrderTupleInterpretationWitness ∧
    (∀ x y : TTerm Empty,
      hotiCost higherOrderTupleInterpretationWitness (.app .ap [x, y]) =
        hotiCost higherOrderTupleInterpretationWitness x +
          hotiCost higherOrderTupleInterpretationWitness y) ∧
    (∀ b s n : FreeTerm Empty,
      hotiFreeCost higherOrderTupleInterpretationWitness (.wrap s (.recur b s n)) <
        hotiFreeCost higherOrderTupleInterpretationWitness (.recur b s (.succ n))) := by
  refine ⟨higherOrderTupleInterpretationWitness_accepts, ?_, ?_⟩
  · intro x y
    simp only [hotiCost_app, hotiCostList_cons, hotiCostList_nil, hotiSymCost,
      higherOrderTupleInterpretationWitness, Nat.one_mul]
  · intro b s n
    exact hotiFreeCost_dup _ higherOrderTupleInterpretationWitness_laws b s n

/-- **Mutation.** Dropping the coupling, everything else fixed, breaks the admissibility law. -/
theorem higherOrderTupleInterpretation_mutation :
    ¬ higherOrderTupleInterpretationLaws
      { higherOrderTupleInterpretationWitness with costIterCouple := 0 } := by
  intro h
  obtain ⟨_, _, _, _, _, _, _, _, hQ⟩ := h
  simp only [Nat.one_le_iff_ne_zero] at hQ
  omega

/-- Scope of the tuple method: every admissible accepted tuple interpretation strictly decreases
on the typed image of every free contextual step and proves termination of that source relation. -/
def higherOrderTupleInterpretation_scope : Prop :=
  ∀ (M : higherOrderTupleInterpretationData), higherOrderTupleInterpretationLaws M →
    higherOrderTupleInterpretationAccepts M → ∀ (A : TTy) (μ : Type),
      (∀ {t u : FreeTerm μ}, ContextStep t u →
        AStep (iterRules A) (toA A t) (toA A u) ∧
          hotiCost M (toA A u) < hotiCost M (toA A t)) ∧
      WellFounded (fun u t : FreeTerm μ => ContextStep t u)

/-- A general cost-size tuple certificate for an arbitrary relation. A step decreases
lexicographically in the cost component and then in the size component. -/
structure CostSizeTupleCertificate (α : Type) (R : α → α → Prop) where
  tuple : α → Nat × Nat
  decreases : ∀ {x y}, R x y →
    Prod.Lex (fun a b : Nat => a < b) (fun a b : Nat => a < b) (tuple y) (tuple x)

/-- Every cost-size tuple certificate proves termination, for every carrier and relation. -/
theorem CostSizeTupleCertificate.wellFounded {α : Type} {R : α → α → Prop}
    (C : CostSizeTupleCertificate α R) : WellFounded (fun y x => R x y) :=
  Subrelation.wf (fun {_ _} h => C.decreases h)
    (InvImage.wf C.tuple (WellFounded.prod_lex Nat.lt_wfRel.wf Nat.lt_wfRel.wf))

/-- The coupled higher-order cost supplies a cost-size tuple certificate for the complete
contextual free-recursor relation. -/
def higherOrderTupleInterpretationCertificate
    (M : higherOrderTupleInterpretationData) (hL : higherOrderTupleInterpretationLaws M)
    (hA : higherOrderTupleInterpretationAccepts M) (μ : Type) :
    CostSizeTupleCertificate (FreeTerm μ) ContextStep where
  tuple t := (hotiFreeCost M t, 0)
  decreases h := Prod.lex_def.2 (Or.inl (hotiFreeCost_contextStep_lt M hL hA h))

/-- The tuple interpretation itself proves its complete scope. The first conjunct records the
actual typed rewrite step and its tuple decrease; the second is the induced source termination. -/
theorem higherOrderTupleInterpretation_scope_proven : higherOrderTupleInterpretation_scope := by
  intro M hL hA A μ
  refine ⟨?_, (higherOrderTupleInterpretation_sound M hL hA).2 μ⟩
  intro t u h
  exact ⟨toA_contextStep A h, by
    rw [hotiCost_toA, hotiCost_toA]
    exact hotiFreeCost_contextStep_lt M hL hA h⟩

/-- The unrestricted applicative iterator relation also terminates. This theorem is kept separate
because its proof is the recursive path order, not the tuple certificate. -/
theorem typedIteratorRelation_wellFounded (A : TTy) (μ : Type) :
    WellFounded (fun u t : TTerm μ => AStep (iterRules A) t u) :=
  horpoAdmittanceWitness_result.2.1 A μ

/-- Exact method identity for the row: tuple descent proves termination for arbitrary relations,
and the catalogue witness supplies typed image simulation, strict tuple descent, and source
termination. The unrestricted typed iterator theorem is recorded separately above. -/
theorem higherOrderTupleInterpretation_methodIdentity :
    (∀ {α : Type} {R : α → α → Prop}, CostSizeTupleCertificate α R →
      WellFounded (fun y x => R x y)) ∧
      (∀ μ : Type, WellFounded (fun u t : FreeTerm μ => ContextStep t u)) ∧
      higherOrderTupleInterpretation_scope := by
  refine ⟨fun C => C.wellFounded, ?_, higherOrderTupleInterpretation_scope_proven⟩
  intro μ
  exact (higherOrderTupleInterpretationCertificate higherOrderTupleInterpretationWitness
    higherOrderTupleInterpretationWitness_laws
    higherOrderTupleInterpretationWitness_accepts μ).wellFounded

end HigherOrderTuple

end OperatorKO7.Methods.OrientationClosure.MethodRowsOtherCalculi
