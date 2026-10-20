import OperatorKO7.Meta.OperationalInexpressibility.BethDefinability
import OperatorKO7.Meta.BoundaryObserver.GodelPairSideSymbol
import OperatorKO7.Meta.BoundaryObserver.RiceBoundary
import OperatorKO7.Meta.BoundaryObserver.BoundaryPole
import OperatorKO7.Meta.BoundaryObserver.SelfEvaluationBounds
import OperatorKO7.Meta.BoundaryObserver.DemandDetector
import OperatorKO7.Meta.SafeStep.EqWVoidAnomaly
import OperatorKO7.Meta.OperationalInexpressibility.FaithfulRecursorRealization

set_option autoImplicit false

/-!
# Logic, computability and rewriting sentences of the Boundary-Observation Principle

The statements of the sections on languages, self-reference, computability and the calculus that
no earlier declaration states in the words of the paper: the language license without an
inhabitance hypothesis on the verdicts, the maximal licensed subsets of the Gödel pair, the zero
discrimination of bounded-record readings at the merged pair of an extensional test and the
failure of the uniform-evaluation hypothesis for the codes under their semantics, the fair coin
readout at the value zero, the constant targets of the uncounted run, the observers that factor
through the content of the counted passes, the chain of passes to counter zero, the two normal
forms of the fork, the contextual path of a delta diagonal, the counted unrolling of the recursor,
the bounded records of opposite statuses, the budget report of a resource halt, and the faithful
transport along an arbitrary injective encoding.

Relation: the kernel root relation `Step`, its full context closure `StepCtxFull`, the counted pass
relation, and arbitrary relations on the source and ambient types.
Trust: kernel-only. No `sorry`, `admit`, `axiom`, `native_decide`.
-/

namespace OperatorKO7.Meta.BoundaryObserver.ObservationPrincipleLogic

/-! ## Theorem `thm:language-license`: no inhabitance hypothesis -/

open OperatorKO7.Meta.OperationalInexpressibility.DefinitionUnification
open OperatorKO7.Meta.OperationalInexpressibility.LicenseCriterion

/-- A complete language closed under every postcomposition has the Beth property for every target,
with no hypothesis that the verdict type is inhabited: an empty verdict type forces empty worlds,
and the completeness statement then defines every target. -/
theorem bethPropertyOn_of_complete_general (L : ObservedLanguage) (hcomplete : L.Complete)
    (hclosed : L.PostcompositionClosed) : L.BethPropertyOn fun _ => True := by
  by_cases hV : Nonempty L.Verdict
  · exact ObservedLanguage.bethPropertyOn_of_complete hcomplete hclosed
  · obtain ⟨ψ, hψ, -⟩ := hcomplete
    intro P _ _
    exact ⟨ψ, hψ, fun w => absurd ⟨L.denotes ψ w⟩ hV⟩

/-- For a sound and complete language closed under every postcomposition, a target is defined by a
derivable statement if and only if the observer determines it. -/
theorem explicitlyDefines_iff_licensed (L : ObservedLanguage) (hsound : L.Sound)
    (hcomplete : L.Complete) (hclosed : L.PostcompositionClosed) (P : L.World → L.Verdict) :
    L.ExplicitlyDefines P ↔ Licensed L.observe P :=
  ⟨ObservedLanguage.licensed_of_explicitlyDefines hsound,
    fun h => bethPropertyOn_of_complete_general L hcomplete hclosed P trivial h⟩

/-! ## Corollary `cor:godel`(ii): the maximal licensed subsets of the pair -/

open OperatorKO7.Meta.DistinctionBoundary.GodelArith
open OperatorKO7.Meta.DistinctionBoundary.GodelObserverCollision
open OperatorKO7.Meta.BoundaryObserver.GodelPairSideSymbol
open OperatorKO7.Meta.OperationalInexpressibility

/-- On the pair of the Gödel sentence and its negation, the subsets on which provability determines
truth and that are maximal among such subsets of the pair are exactly the two singletons. -/
theorem godel_pair_maximal_licensed (S : Set Formula) (hS : S ⊆ godelPair) :
    (LiftOrRefuse.LicensedOn S provabilityObserver truthTarget ∧
        ∀ T : Set Formula, S ⊆ T → T ⊆ godelPair →
          LiftOrRefuse.LicensedOn T provabilityObserver truthTarget → T = S) ↔
      S = {arithGodelSentence} ∨ S = {Formula.not arithGodelSentence} := by
  obtain ⟨hq, hP⟩ := godel_provability_collision
  have hpair : ∀ x, x ∈ godelPair ↔ x = arithGodelSentence ∨ x = Formula.not arithGodelSentence :=
    fun x => by simp [godelPair]
  have hsingle : ∀ z : Formula,
      LiftOrRefuse.LicensedOn ({z} : Set Formula) provabilityObserver truthTarget := by
    intro z x hx y hy _
    rw [Set.mem_singleton_iff] at hx hy
    rw [hx, hy]
  have hboth : ∀ T : Set Formula, arithGodelSentence ∈ T → Formula.not arithGodelSentence ∈ T →
      ¬ LiftOrRefuse.LicensedOn T provabilityObserver truthTarget :=
    fun T hγ hν hlic => hP (hlic _ hγ _ hν hq)
  have hsub : ∀ z, z ∈ godelPair → ({z} : Set Formula) ⊆ godelPair := by
    intro z hz x hx
    rw [Set.mem_singleton_iff.1 hx]
    exact hz
  constructor
  · rintro ⟨hlic, hmax⟩
    by_cases hγ : arithGodelSentence ∈ S <;> by_cases hν : Formula.not arithGodelSentence ∈ S
    · exact absurd hlic (hboth S hγ hν)
    · left
      ext x
      constructor
      · intro hx
        rcases (hpair x).1 (hS hx) with rfl | rfl
        · exact Set.mem_singleton _
        · exact absurd hx hν
      · intro hx
        rw [Set.mem_singleton_iff.1 hx]
        exact hγ
    · right
      ext x
      constructor
      · intro hx
        rcases (hpair x).1 (hS hx) with rfl | rfl
        · exact absurd hx hγ
        · exact Set.mem_singleton _
      · intro hx
        rw [Set.mem_singleton_iff.1 hx]
        exact hν
    · exfalso
      have hS0 : S = ∅ := by
        ext x
        constructor
        · intro hx
          rcases (hpair x).1 (hS hx) with rfl | rfl
          · exact absurd hx hγ
          · exact absurd hx hν
        · intro hx
          simp at hx
      have hT := hmax {arithGodelSentence} (by rw [hS0]; exact Set.empty_subset _)
        (hsub _ ((hpair _).2 (Or.inl rfl))) (hsingle _)
      rw [hS0] at hT
      exact Set.singleton_ne_empty _ hT
  · rintro (rfl | rfl)
    · refine ⟨hsingle _, fun T hST hT hlic => ?_⟩
      ext x
      constructor
      · intro hx
        rcases (hpair x).1 (hT hx) with rfl | rfl
        · exact Set.mem_singleton _
        · exact absurd hlic (hboth T (hST (Set.mem_singleton _)) hx)
      · intro hx
        exact hST hx
    · refine ⟨hsingle _, fun T hST hT hlic => ?_⟩
      ext x
      constructor
      · intro hx
        rcases (hpair x).1 (hT hx) with rfl | rfl
        · exact absurd hlic (hboth T hx (hST (Set.mem_singleton _)))
        · exact Set.mem_singleton _
      · intro hx
        exact hST hx

/-! ## Theorem `thm:rice`(ii) and (iii) -/

open OperatorKO7.Meta.BoundaryObserver.RiceBoundary
open OperatorKO7.Meta.BoundaryObserver.BoundaryPole
open OperatorKO7.Meta.BoundaryObserver.MergedPair

/-- For a nonconstant extensional test and every bound `b`, the codes of the bounded record with
opposite values of the test are a merged pair of the bounded record, and every reading determined
by the bounded record has discrimination zero at them. -/
theorem rice_bounded_pair_zero_discrimination (P : Nat.Partrec.Code → Bool)
    (hExt : ∀ c c', c.eval = c'.eval → P c = P c')
    (hNon : ¬ ((∀ c, P c = true) ∨ (∀ c, P c = false))) (b : ℕ) :
    ∃ cPos cNeg : Nat.Partrec.Code, P cPos = true ∧ P cNeg = false ∧
      IsMergedPair (boundedRecord b) cPos cNeg ∧
      ∀ (Y : Type) [Fintype Y] (K : Reading Nat.Partrec.Code Y),
        RecordDetermined (boundedRecord b) K → readingDiscrimination K cPos cNeg = 0 := by
  obtain ⟨cPos, cNeg, hp, hn, heq⟩ := bounded_record_merged_pair P hExt hNon b
  have hne : cPos ≠ cNeg := by
    intro h
    rw [h, hn] at hp
    exact Bool.false_ne_true hp
  exact ⟨cPos, cNeg, hp, hn, ⟨hne, heq⟩, fun Y _ K hK =>
    recordPoleGoal Nat.Partrec.Code (Fin (b + 1) → Option ℕ) Y (boundedRecord b) K cPos cNeg hK
      ⟨hne, heq⟩⟩

/-- The hypothesis of the uniform self-evaluation obstruction fails for the codes under their
semantics: no total computable code transformation `n` and fixed-point-free `j` on the values
satisfy `φ_{n(c)}(x) = j(φ_c(x))` for all codes `c` and inputs `x`, since the recursion theorem
gives a code `e` with `φ_{n(e)} = φ_e`. -/
theorem semantic_uniform_evaluation_hypothesis_fails :
    ¬ ∃ (n : Nat.Partrec.Code → Nat.Partrec.Code) (j : Part ℕ → Part ℕ),
      Computable n ∧ (∀ v, j v ≠ v) ∧ ∀ c x, (n c).eval x = j (c.eval x) := by
  rintro ⟨n, j, hn, hj, hnj⟩
  obtain ⟨e, he⟩ := (no_fixed_point_free_code_map n hn).1
  apply hj (e.eval 0)
  rw [← hnj e 0, he]

/-! ## Proposition `prop:readouts`(iii): the fair coin at the value zero -/

open OperatorKO7.Meta.BoundaryObserver.SelfEvaluationBounds

/-- The readout that returns a fair coin at every value differs from the readout of `(ii)` at the
value zero. -/
theorem constantHalf_differs_at_zero :
    (constantHalfRealReadout (some false) : ℝ) ≠ (realFairReadout (some false) : ℝ) := by
  norm_num [constantHalfRealReadout, realFairReadout]

/-! ## Proposition `prop:uncounted`(ii) and Theorem `thm:recursor-decidability` -/

open OperatorKO7.Meta.BoundaryObserver.RecursorDecidability

/-- Every target on the passes that the state observer of the uncounted run determines is
constant. -/
theorem constantRun_determined_const {T V : Type*} (t : T) (P : ℕ → V)
    (h : Determines (constantRun t) P) (n m : ℕ) : P n = P m :=
  h n m rfl

/-- For nonempty contents, no observer that factors through the content determines a measure that
falls at every pass. -/
theorem factors_through_content_not_measure {T Q' : Type*} [Nonempty T] (q' : T × ℕ → Q')
    (hq' : ∀ x y, content x = content y → q' x = q' y)
    (M : T × ℕ → ℕ) (hM : ∀ x y, Pass x y → M y < M x) : ¬ Determines q' M :=
  fun h => orienting_measure_not_content_determined M hM (fun x y hxy => h x y (hq' x y hxy))

/-- For nonempty contents, no observer that factors through the content determines the test
`[k = 0]`. -/
theorem factors_through_content_not_observed {T Q' : Type*} [Nonempty T] (q' : T × ℕ → Q')
    (hq' : ∀ x y, content x = content y → q' x = q' y) :
    ¬ Determines q' (observed (T := T)) :=
  fun h => observed_not_content_determined (fun x y hxy => h x y (hq' x y hxy))

/-- The counter determines the test `[k = 0]` for every content type. -/
theorem counter_determines_observed {T : Type*} :
    Determines (counter (T := T)) (observed (T := T)) := by
  intro x y h
  simp only [observed, counter] at h ⊢
  rw [h]

/-- From `(R, k)` the passes reach `(R, 0)`. -/
theorem pass_chain_exists {T : Type*} (R : T) (k : ℕ) :
    Relation.ReflTransGen Pass (R, k) (R, 0) := by
  induction k with
  | zero => exact .refl
  | succ k ih => exact Relation.ReflTransGen.head (b := (R, k)) ⟨rfl, rfl⟩ ih

/-! ## Theorems `thm:fork` and `thm:object`(ii), Proposition `prop:recursor-calculus`(ii) -/

open OperatorKO7 Trace
open OperatorKO7.Meta.BoundaryObserver.KernelCases

/-- `void` is a normal form of the root relation. -/
theorem void_normalForm : NormalForm void := by
  rintro ⟨u, hu⟩
  cases hu

/-- `integrate (merge void void)` is a normal form of the root relation. -/
theorem integrate_merge_void_void_normalForm : NormalForm (integrate (merge void void)) := by
  rintro ⟨u, hu⟩
  cases hu

/-- The two root reducts of `eqW void void` are distinct normal forms of the root relation. -/
theorem fork_distinct_normal_forms :
    NormalForm void ∧ NormalForm (integrate (merge void void)) ∧
      void ≠ integrate (merge void void) :=
  ⟨void_normalForm, integrate_merge_void_void_normalForm, fun h => Trace.noConfusion h⟩

/-- The explicit two-step path `integrate (merge (delta t) (delta t)) → integrate (delta t) → void`
of the full context closure. -/
theorem delta_diagonal_ctx_path (t : Trace) :
    MetaSN_KO7.StepCtxFull (integrate (merge (delta t) (delta t))) (integrate (delta t)) ∧
      MetaSN_KO7.StepCtxFull (integrate (delta t)) void :=
  ⟨MetaSN_KO7.StepCtxFull.integrate (MetaSN_KO7.StepCtxFull.root (Step.R_merge_cancel (delta t))),
    MetaSN_KO7.StepCtxFull.root (Step.R_int_delta t)⟩

/-- The counted unrolling of the recursor: the chain from `recΔ R s (numeral k)` to `spine s k R`
has `k + 1` steps of the full context closure, the first `k` of them context instances of the root
step rule and the last a context instance of the root base rule. -/
theorem recursor_unroll_counted (R s : Trace) (k : ℕ) :
    (∀ i, i < k →
      Step (recΔ R s (numeral (k - i))) (app s (recΔ R s (numeral (k - (i + 1))))) ∧
        MetaSN_KO7.StepCtxFull (spine s i (recΔ R s (numeral (k - i))))
          (spine s (i + 1) (recΔ R s (numeral (k - (i + 1)))))) ∧
      Step (recΔ R s (numeral (k - k))) R ∧
      MetaSN_KO7.StepCtxFull (spine s k (recΔ R s (numeral (k - k)))) (spine s k R) := by
  refine ⟨fun i hi => ?_, ?_, ?_⟩
  · have hk : k - i = (k - (i + 1)) + 1 := by omega
    have hstep : Step (recΔ R s (numeral (k - i))) (app s (recΔ R s (numeral (k - (i + 1))))) := by
      rw [hk]
      exact Step.R_rec_succ R s _
    refine ⟨hstep, ?_⟩
    rw [← spine_app]
    exact spine_ctx_step s i (MetaSN_KO7.StepCtxFull.root hstep)
  · rw [Nat.sub_self]
    exact Step.R_rec_zero R s
  · rw [Nat.sub_self]
    exact spine_ctx_step s k (MetaSN_KO7.StepCtxFull.root (Step.R_rec_zero R s))

/-! ## Proposition `prop:m44-bounded-records` and Remark `prop:m44-budget-reports`(a) -/

open UniversalObservation.Completion
open UniversalObservation.Demand

/-- For every bound `b` there are codes with `φ_{c₊}(b)` defined and `φ_{c₋}(b)` undefined whose
bounded evaluations at `b` are both `none`. -/
theorem bounded_records_opposite_statuses (b : ℕ) :
    ∃ cPos cNeg : Nat.Partrec.Code, (cPos.eval b).Dom ∧ ¬ (cNeg.eval b).Dom ∧
      Nat.Partrec.Code.evaln b cPos b = none ∧ Nat.Partrec.Code.evaln b cNeg b = none := by
  obtain ⟨c₁, c₂, h₁, h₂, e₁, e₂⟩ := finite_budget_same_record_opposite_statuses b
  exact ⟨c₁, c₂, (boundedHaltingSourceAt_good_iff c₁ b).1 h₁,
    fun h => h₂ ((boundedHaltingSourceAt_good_iff c₂ b).2 h), e₁, e₂⟩

/-- The budget reported by a certificate: the budget of a resource halt, and nothing otherwise. -/
def budgetReport {I W : Type*} {P : Problem I W} {D : Set I} : Certificate P D → Option ℕ
  | .resourceHalt b => some b
  | _ => none

/-- A budget report is separated from feasibility: for every budget value, a feasible problem and
an infeasible problem have certificates reporting that budget. -/
theorem budget_report_separated (budget : ℕ) :
    ∃ (c₁ : Certificate (⟨fun _ _ => True⟩ : Problem Unit Unit) Set.univ)
      (c₂ : Certificate (⟨fun _ _ => False⟩ : Problem Unit Unit) Set.univ),
      budgetReport c₁ = some budget ∧ budgetReport c₂ = some budget ∧
        Good (⟨fun _ _ => True⟩ : Problem Unit Unit) Set.univ ∧
        ¬ Good (⟨fun _ _ => False⟩ : Problem Unit Unit) Set.univ := by
  obtain ⟨-, -, h₁, h₂⟩ := resource_halt_has_both_source_statuses budget
  exact ⟨.resourceHalt budget, .resourceHalt budget, rfl, rfl, h₁, h₂⟩

/-! ## Theorem `thm:faithful-outgoing` for an arbitrary injective encoding -/

open OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile
open OperatorKO7.Meta.OperationalInexpressibility.FaithfulRecursorRealization
open OperatorKO7.Meta.Rewriting

section FaithfulGeneral

variable {A B : Type*}

/-- The relation generated on the attained image of an encoding: it relates two encoded states
exactly at related sources. -/
def generatedRelation (e : A → B) (R : A → A → Prop) (x y : Set.range e) : Prop :=
  ∃ a a', e a = x.1 ∧ e a' = y.1 ∧ R a a'

/-- For an injective encoding, the bijection of the sources onto the attained image is a relation
isomorphism for the generated relation. -/
theorem generated_relation_iso (e : A → B) (he : Function.Injective e) (R : A → A → Prop)
    (a a' : A) :
    R a a' ↔ generatedRelation e R (Equiv.ofInjective e he a) (Equiv.ofInjective e he a') := by
  constructor
  · intro h
    exact ⟨a, a', rfl, rfl, h⟩
  · rintro ⟨b, b', hb, hb', h⟩
    rw [Equiv.ofInjective_apply] at hb hb'
    obtain rfl := he hb
    obtain rfl := he hb'
    exact h

/-- Exact outgoing transport: the ambient successors of an encoded state are the encodings of its
source successors if and only if the ambient relation reflects and preserves the source relation on
encoded states and every ambient successor of an encoded state is encoded. -/
theorem exact_outgoing_iff (e : A → B) (he : Function.Injective e) (R : A → A → Prop)
    (S : B → B → Prop) :
    (∀ a b, S (e a) b ↔ ∃ a', b = e a' ∧ R a a') ↔
      (∀ a a', S (e a) (e a') ↔ R a a') ∧ ∀ a b, S (e a) b → ∃ a', e a' = b := by
  constructor
  · intro h
    refine ⟨fun a a' => ?_, fun a b hab => ?_⟩
    · rw [h]
      constructor
      · rintro ⟨a'', h1, h2⟩
        rwa [he h1]
      · intro h2
        exact ⟨a', rfl, h2⟩
    · obtain ⟨a', rfl, -⟩ := (h a b).1 hab
      exact ⟨a', rfl⟩
  · rintro ⟨h1, h2⟩ a b
    constructor
    · intro hab
      obtain ⟨a', rfl⟩ := h2 a b hab
      exact ⟨a', rfl, (h1 a a').1 hab⟩
    · rintro ⟨a', rfl, h⟩
      exact (h1 a a').2 h

/-- The closed relation embedding of an exact outgoing encoding. -/
def exactEmbedding (e : A → B) (he : Function.Injective e) (R : A → A → Prop) (S : B → B → Prop)
    (h : ∀ a b, S (e a) b ↔ ∃ a', b = e a' ∧ R a a') : ClosedRelationEmbedding R S where
  map := ⟨e, he⟩
  step_iff := fun {x y} => (((exact_outgoing_iff e he R S).1 h).1 x y).symm
  forward_closed := fun {x y} hxy => ((exact_outgoing_iff e he R S).1 h).2 x y hxy

/-- Under exact outgoing transport every finite ambient path from an encoded state lifts to a
source path. -/
theorem exact_outgoing_path_lift (e : A → B) (he : Function.Injective e) (R : A → A → Prop)
    (S : B → B → Prop) (h : ∀ a b, S (e a) b ↔ ∃ a', b = e a' ∧ R a a') {a : A} {y : B}
    (hp : Relation.ReflTransGen S (e a) y) :
    ∃ a', e a' = y ∧ Relation.ReflTransGen R a a' :=
  closedEmbedding_star_pull (exactEmbedding e he R S h) hp

/-- Under exact outgoing transport accessibility is equivalent at a source state and at its
encoding. -/
theorem exact_outgoing_acc_iff (e : A → B) (he : Function.Injective e) (R : A → A → Prop)
    (S : B → B → Prop) (h : ∀ a b, S (e a) b ↔ ∃ a', b = e a' ∧ R a a') (a : A) :
    Acc (fun b a => R a b) a ↔ Acc (fun b a => S a b) (e a) :=
  closedEmbedding_acc_iff (exactEmbedding e he R S h) a

/-- Under exact outgoing transport confluence of the source transports to every ambient start that
encodes a source start. -/
theorem exact_outgoing_confluent_at (e : A → B) (he : Function.Injective e) (R : A → A → Prop)
    (S : B → B → Prop) (h : ∀ a b, S (e a) b ↔ ∃ a', b = e a' ∧ R a a')
    (hc : ∀ {x a b}, Relation.ReflTransGen R x a → Relation.ReflTransGen R x b →
      ∃ z, Relation.ReflTransGen R a z ∧ Relation.ReflTransGen R b z)
    {x : A} {a b : B} (ha : Relation.ReflTransGen S (e x) a)
    (hb : Relation.ReflTransGen S (e x) b) :
    ∃ z, Relation.ReflTransGen S a z ∧ Relation.ReflTransGen S b z :=
  closedEmbedding_confluent_at (exactEmbedding e he R S h) hc ha hb

/-- A ranked next-step machine conjugated by a bijection. -/
def conjMachine {C : Type*} (M : RankedMachine A) (E : A ≃ C) : RankedMachine C where
  next c := (M.next (E.symm c)).map E
  rank c := M.rank (E.symm c)
  decreases := by
    intro a b h
    obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp h
    simpa using M.decreases hc

/-- The conjugated machine sends the image of a state to the image of its normal form, with the
same step count. -/
theorem conjMachine_normalize_cost {C : Type*} (M : RankedMachine A) (E : A ≃ C) (a : A) :
    (conjMachine M E).normalize (E a) = E (M.normalize a) ∧
      (conjMachine M E).cost (E a) = M.cost a := by
  induction n : M.rank a using Nat.strong_induction_on generalizing a with
  | h n ih =>
    cases hn : M.next a with
    | none =>
      have hc : (conjMachine M E).next (E a) = none := by simp [conjMachine, hn]
      rw [(conjMachine M E).normalize_terminal hc, M.normalize_terminal hn,
        (conjMachine M E).cost_terminal hc, M.cost_terminal hn]
      exact ⟨rfl, rfl⟩
    | some b =>
      have hc : (conjMachine M E).Step (E a) (E b) := by
        show (conjMachine M E).next (E a) = some (E b)
        simp [conjMachine, hn]
      rw [(conjMachine M E).normalize_step hc, M.normalize_step hn,
        (conjMachine M E).cost_step hc, M.cost_step hn]
      obtain ⟨h1, h2⟩ := ih (M.rank b) (by simpa [n] using M.decreases hn) b rfl
      exact ⟨h1, by rw [h2]⟩

/-- For an injective encoding, a ranked machine on the sources conjugated by the bijection onto the
attained image is a ranked machine on the image; the normal form of an encoded state is the image of
the normal form of its source, and the two step counts are equal. -/
theorem encoded_machine_transport (e : A → B) (he : Function.Injective e) (M : RankedMachine A)
    (a : A) :
    (conjMachine M (Equiv.ofInjective e he)).normalize (Equiv.ofInjective e he a) =
        Equiv.ofInjective e he (M.normalize a) ∧
      (conjMachine M (Equiv.ofInjective e he)).cost (Equiv.ofInjective e he a) = M.cost a :=
  conjMachine_normalize_cost M (Equiv.ofInjective e he) a

end FaithfulGeneral

/-! ## Theorem `thm:rice`(iv): the bounded halting sets are computably decided by their records -/

section BoundedHalting

open OperatorKO7.Meta.BoundaryObserver.RiceBoundary

/-- Theorem `thm:rice`(iv), the bounded sets: for every budget `b`, the set of codes whose bounded
record has an entry at input zero is a computable predicate of the code, and two codes with one
bounded record lie both in it or both outside it. The zero-input halting set is the union of
these sets over `b` by `halting_one_sided`. -/
theorem bounded_halting_decided (b : ℕ) :
    ComputablePred (fun c : Nat.Partrec.Code =>
        boundedRecord b c ⟨0, Nat.zero_lt_succ b⟩ ≠ none) ∧
      ∀ c c' : Nat.Partrec.Code, boundedRecord b c = boundedRecord b c' →
        (boundedRecord b c ⟨0, Nat.zero_lt_succ b⟩ ≠ none ↔
          boundedRecord b c' ⟨0, Nat.zero_lt_succ b⟩ ≠ none) := by
  have hprim : Primrec fun c : Nat.Partrec.Code => (Nat.Partrec.Code.evaln b c 0).isSome :=
    Primrec.option_isSome.comp (Nat.Partrec.Code.evaln_prim.comp
      ((Primrec.pair (Primrec.const b) Primrec.id).pair (Primrec.const 0)))
  refine ⟨ComputablePred.computable_iff.2 ⟨_, hprim.to_comp, ?_⟩, fun c c' h => by rw [h]⟩
  funext c
  simp [boundedRecord, Option.ne_none_iff_isSome]

end BoundedHalting

end OperatorKO7.Meta.BoundaryObserver.ObservationPrincipleLogic
