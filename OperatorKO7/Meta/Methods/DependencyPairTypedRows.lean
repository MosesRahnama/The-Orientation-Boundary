import OperatorKO7.Meta.DependencyPairs_Works
import OperatorKO7.Meta.ConfessionMethod_ArgumentFiltering
import OperatorKO7.Meta.ManySortedBarrierSurvival
import OperatorKO7.Meta.SymbolicComparatorBarrier_Weighted_Schema
import OperatorKO7.Meta.NonlinearUnconstrainedExactLaw
import OperatorKO7.Meta.ContextClosed_SN_Full
import OperatorKO7.Meta.HigherOrderRewriting_Syntax

/-!
# Carriers for the dependency-pair and typed rows of the RDRS coverage ledger (lane E4)

Sixteen rows sit in the dependency-pair and typed-transformation layer. They divide into four
groups, each carried by one compiled fact.

**The counter projection.** KO7 extracts one dependency pair, `recΔ b s (delta n) → recΔ b s n`,
and the projection that keeps only the counter depth strictly decreases along it
(`dpPair_decreases`). Every DP-side row is that projection wearing a different name: the classifier
row, argument filtering, the reduction-pair processor, the reduction-triple processor, the
order-sorted variant, the context-sensitive variant, and the two-dimensional CTRS variant.

**The pair is not unique.** The reduction-pair rows are import dependent because the ledger does
not fix the pair. Two different pairs both succeed, which is the compiled reason.

**The typed image is exact.** Type introduction and many-sorted persistence now use an independent
typed relation, an injective erasure into the KO7 relation, an exact source/target shape theorem,
and inherited well-foundedness. This is the specialized KO7 transport; no unrestricted literature
theorem about arbitrary type introduction is claimed.

**Unconditional rules.** KO7 has no conditional rule, so operational termination for conditional
systems and the two-dimensional CTRS notion both collapse to the unconditional case.

Relation: the extracted dependency pair and the KO7 root relation. Closure: root.
External trust: none. Mathlib only.
-/

namespace OperatorKO7.Methods.DependencyPairTypedRows

open OperatorKO7
open OperatorKO7.Trace
open OperatorKO7.StepDuplicating
open OperatorKO7.StepDuplicating.StepDuplicatingSchema
open OperatorKO7.SymbolicComparatorBarrier
open OperatorKO7.MetaDependencyPairs
open OperatorKO7.ConfessionMethodFamily
open OperatorKO7.CompositionalImpossibility

/-! ## The counter projection -/

/-- Exact shape theorem for the extracted KO7 dependency-pair relation.  This closes the
"exactly one schema" clause rather than merely exhibiting its constructor. -/
theorem dppair_iff_recSucc_shape {a b : Trace} :
    DPPair a b ↔
      ∃ base payload counter : Trace,
        a = recΔ base payload (delta counter) ∧
          b = recΔ base payload counter := by
  constructor
  · intro h
    cases h with
    | rec_succ base payload counter => exact ⟨base, payload, counter, rfl, rfl⟩
  · rintro ⟨base, payload, counter, rfl, rfl⟩
    exact DPPair.rec_succ base payload counter

/-- The compiled content shared by every dependency-pair row: KO7 has exactly one extracted pair,
the counter projection strictly decreases along it, and the reverse pair relation is well
founded. -/
abbrev CounterProjectionCore : Prop :=
  (∀ a b : Trace, DPPair a b ↔
      ∃ base payload counter : Trace,
        a = recΔ base payload (delta counter) ∧ b = recΔ base payload counter)
    ∧ (∀ {a b : Trace}, DPPair a b → dpRank b < dpRank a)
    ∧ (∀ (b s n : Trace), DPPair (recΔ b s (delta n)) (recΔ b s n))
    ∧ WellFounded DPPairRev

theorem counterProjectionCore_holds : CounterProjectionCore :=
  ⟨fun _ _ => dppair_iff_recSucc_shape, dpPair_decreases, DPPair.rec_succ, wf_DPPairRev⟩

/-- **dpProcessorClassification.** -/
abbrev DPProcessorClassificationRowClaim : Prop := CounterProjectionCore

theorem dpProcessorClassification_row_anchor : DPProcessorClassificationRowClaim :=
  counterProjectionCore_holds

/-- **dpArgumentFiltering.** The filter that keeps only the counter position yields the same rank
as the dependency-pair projection, so the escape is the same one. -/
abbrev DPArgumentFilteringRowClaim : Prop :=
  CounterProjectionCore
    ∧ OperatorKO7.ConfessionMethodFamily.argumentFilteringRankFn = dpProjection
    ∧ OperatorKO7.ConfessionMethodFamily.schemaArgumentFilteringWitness.keepRecurCoordinate
        = ⟨2, by decide⟩

theorem dpArgumentFiltering_row_anchor : DPArgumentFilteringRowClaim :=
  ⟨counterProjectionCore_holds,
    OperatorKO7.ConfessionMethodFamily.argumentFilteringRankFn_eq_dpProjection,
    OperatorKO7.ConfessionMethodFamily.schemaArgumentFilteringWitness.keepRecurCoordinate_is_counter⟩

/-! ### The reduction pair is not unique -/

/-- A reduction pair for the extracted problem: a rank into the naturals that strictly decreases
along every dependency pair. -/
structure ReductionPair where
  rank : Trace → Nat
  decreases : ∀ {a b : Trace}, DPPair a b → rank b < rank a

/-- The canonical pair: the counter projection with the strict order on the naturals. -/
def counterReductionPair : ReductionPair where
  rank := dpRank
  decreases := dpPair_decreases

/-- A second, different pair: twice the counter depth. It succeeds on the same problem, which is
why the row is import dependent and not theorem-backed on its own. -/
def doubledCounterReductionPair : ReductionPair where
  rank := fun t => 2 * dpRank t
  decreases := fun h => by
    have := dpPair_decreases h
    omega

/-- A countable family of successful reduction pairs.  Index `k` scales the counter projection by
the positive coefficient `k + 1`. -/
def scaledCounterReductionPair (k : Nat) : ReductionPair where
  rank := fun t => (k + 1) * dpRank t
  decreases := fun h =>
    Nat.mul_lt_mul_of_pos_left (dpPair_decreases h) (Nat.succ_pos k)

@[simp] theorem scaledCounterReductionPair_probe (k : Nat) :
    (scaledCounterReductionPair k).rank (recΔ void void (delta void)) = k + 1 := by
  simp [scaledCounterReductionPair, dpRank, dpProjection]

/-- Distinct indices give extensionally distinct successful ranking functions. -/
theorem scaledCounterReductionPair_rank_injective :
    Function.Injective (fun k : Nat => (scaledCounterReductionPair k).rank) := by
  intro k l h
  have hprobe := congrFun h (recΔ void void (delta void))
  simpa using hprobe

theorem reductionPairs_differ :
    counterReductionPair.rank ≠ doubledCounterReductionPair.rank := by
  intro h
  have := congrFun h (recΔ void void (delta void))
  simp [counterReductionPair, doubledCounterReductionPair, dpRank, dpProjection] at this

/-- **dpReductionPairProcessor.** Import dependent: a pair exists and succeeds, and it is not
unique, so the row's outcome depends on the pairing the caller fixes. -/
abbrev DPReductionPairProcessorRowClaim : Prop :=
  (∀ {a b : Trace}, DPPair a b → counterReductionPair.rank b < counterReductionPair.rank a)
    ∧ (∀ {a b : Trace},
        DPPair a b → doubledCounterReductionPair.rank b < doubledCounterReductionPair.rank a)
    ∧ counterReductionPair.rank ≠ doubledCounterReductionPair.rank
    ∧ Function.Injective (fun k : Nat => (scaledCounterReductionPair k).rank)

theorem dpReductionPairProcessor_row_anchor : DPReductionPairProcessorRowClaim :=
  ⟨counterReductionPair.decreases, doubledCounterReductionPair.decreases, reductionPairs_differ,
    scaledCounterReductionPair_rank_injective⟩

/-- A reduction triple adds a weak component used for the rules that are not pairs. -/
structure ReductionTriple extends ReductionPair where
  weak : Trace → Nat
  weak_nonincreasing : ∀ {a b : Trace}, Step a b → weak b ≤ weak a

def counterReductionTriple : ReductionTriple where
  toReductionPair := counterReductionPair
  weak := OperatorKO7.PolyInterpretation.W
  weak_nonincreasing := fun h =>
    Nat.le_of_lt (OperatorKO7.PolyInterpretation.W_orients_step h)

/-- **dpReductionTriples.** Import dependent for the same reason as the pair row. -/
abbrev DPReductionTriplesRowClaim : Prop :=
  (∀ {a b : Trace},
      DPPair a b → counterReductionTriple.rank b < counterReductionTriple.rank a)
    ∧ (∀ {a b : Trace}, Step a b → counterReductionTriple.weak b ≤ counterReductionTriple.weak a)
    ∧ counterReductionPair.rank ≠ doubledCounterReductionPair.rank
    ∧ Function.Injective (fun k : Nat => (scaledCounterReductionPair k).rank)

theorem dpReductionTriples_row_anchor : DPReductionTriplesRowClaim :=
  ⟨counterReductionTriple.decreases, counterReductionTriple.weak_nonincreasing,
    reductionPairs_differ, scaledCounterReductionPair_rank_injective⟩

/-- A dependency-pair processor on the concrete KO7 pair relation. -/
structure ConcreteDPProcessor where
  output : Trace → Trace → Prop

/-- A neutral processor is extensionally the identity on the pair problem. -/
def IsNeutralDPProcessor (P : ConcreteDPProcessor) : Prop :=
  ∀ a b : Trace, P.output a b ↔ DPPair a b

def identityDPProcessor : ConcreteDPProcessor where
  output := DPPair

theorem identityDPProcessor_neutral : IsNeutralDPProcessor identityDPProcessor := by
  intro a b
  rfl

/-- **dpNeutralProcessors.** The processor is exhibited, its output is extensionally the original
pair relation, and well-foundedness is preserved in both directions by that equality. -/
abbrev DPNeutralProcessorsRowClaim : Prop :=
  ∃ P : ConcreteDPProcessor,
    IsNeutralDPProcessor P
      ∧ (WellFounded (fun t s => P.output s t) ↔ WellFounded DPPairRev)

theorem dpNeutralProcessors_row_anchor : DPNeutralProcessorsRowClaim := by
  refine ⟨identityDPProcessor, identityDPProcessor_neutral, ?_⟩
  rfl

/-- The finite formative-pair catalog of the KO7 dependency-pair problem. -/
inductive FormativePairTag where
  | recSucc
  deriving DecidableEq, Repr

/-- The tag-indexed formative relation, defined independently of `DPPair`. -/
inductive FormativePair : FormativePairTag → Trace → Trace → Prop
  | recSucc (b s n : Trace) :
      FormativePair .recSucc (recΔ b s (delta n)) (recΔ b s n)

theorem formativePair_iff_dppair {a b : Trace} :
    (∃ tag, FormativePair tag a b) ↔ DPPair a b := by
  constructor
  · rintro ⟨tag, h⟩
    cases h with
    | recSucc base payload counter => exact DPPair.rec_succ base payload counter
  · intro h
    cases h with
    | rec_succ base payload counter =>
        exact ⟨.recSucc, FormativePair.recSucc base payload counter⟩

theorem formativePair_decreases {tag : FormativePairTag} {a b : Trace}
    (h : FormativePair tag a b) : dpRank b < dpRank a := by
  apply dpPair_decreases
  exact formativePair_iff_dppair.mp ⟨tag, h⟩

theorem wf_FormativePairRev :
    WellFounded (fun y x : Trace => ∃ tag, FormativePair tag x y) := by
  refine Subrelation.wf ?_ wf_DPPairRev
  intro y x h
  exact formativePair_iff_dppair.mp h

/-- **formativeRules.** Exact closure of the singleton formative-pair catalog: erasing its tag is
extensionally the complete KO7 pair relation, its rank strictly decreases, and its reverse is
well founded. -/
abbrev FormativeRulesRowClaim : Prop :=
  (∀ a b : Trace, (∃ tag, FormativePair tag a b) ↔ DPPair a b)
    ∧ (∀ {tag : FormativePairTag} {a b : Trace},
      FormativePair tag a b → dpRank b < dpRank a)
    ∧ WellFounded (fun y x : Trace => ∃ tag, FormativePair tag x y)

theorem formativeRules_row_anchor : FormativeRulesRowClaim :=
  ⟨fun _ _ => formativePair_iff_dppair, formativePair_decreases, wf_FormativePairRev⟩

/-! ## Sorted transformations -/

namespace SortedTransport

open OperatorKO7.TypedBarrierSurvival

/-- Sort-preserving erasure of counter terms into the KO7 constructor algebra. -/
@[simp] def eraseCnt : Term .cnt → Trace
  | .zero => .void
  | .succ n => .delta (eraseCnt n)

/-- Sort-preserving erasure of step terms. -/
@[simp] def eraseStep : Term .step → Trace
  | .stepZero => .void
  | .stepSucc s => .delta (eraseStep s)

/-- Sort-preserving erasure of result terms. -/
@[simp] def eraseRes : Term .res → Trace
  | .base => .void
  | .wrap s t => .app (eraseStep s) (eraseRes t)
  | .recur b s n => .recΔ (eraseRes b) (eraseStep s) (eraseCnt n)

/-- The typed recursor-successor relation, independently generated on sorted terms. -/
inductive TypedRecSuccStep : Term .res → Term .res → Prop
  | recSucc (b : Term .res) (s : Term .step) (n : Term .cnt) :
      TypedRecSuccStep (.recur b s (.succ n)) (.wrap s (.recur b s n))

theorem typedRecSuccStep_iff {a b : Term .res} :
    TypedRecSuccStep a b ↔
      ∃ (baseArg : Term .res) (payload : Term .step) (counter : Term .cnt),
        a = .recur baseArg payload (.succ counter) ∧
          b = .wrap payload (.recur baseArg payload counter) := by
  constructor
  · intro h
    cases h with
    | recSucc baseArg payload counter => exact ⟨baseArg, payload, counter, rfl, rfl⟩
  · rintro ⟨baseArg, payload, counter, rfl, rfl⟩
    exact .recSucc baseArg payload counter

/-- Every typed recursive step erases to the actual KO7 recursor-successor rule. -/
theorem eraseRes_typedRecSuccStep {a b : Term .res} (h : TypedRecSuccStep a b) :
    Step (eraseRes a) (eraseRes b) := by
  cases h with
  | recSucc baseArg payload counter =>
      simpa using Step.R_rec_succ (eraseRes baseArg) (eraseStep payload) (eraseCnt counter)

/-- Specialized many-sorted type introduction preserves strong normalization internally. -/
theorem typedRecSuccStep_wellFounded :
    WellFounded (fun y x : Term .res => TypedRecSuccStep x y) := by
  refine Subrelation.wf ?_
    (InvImage.wf eraseRes OperatorKO7.PolyInterpretation.wf_StepRev_poly)
  intro y x h
  exact eraseRes_typedRecSuccStep h

/-- Every typed recursor-successor instance exists, so the relation is nonempty. -/
theorem typedRecSuccStep_nonempty :
    TypedRecSuccStep (.recur .base .stepZero (.succ .zero))
      (.wrap .stepZero (.recur .base .stepZero .zero)) :=
  .recSucc .base .stepZero .zero

/-- The transformed recursive-call pair on the typed carrier.  This is distinct
from `TypedRecSuccStep`: dependency-pair extraction removes the emitted wrapper
and retains only the recursive call. -/
inductive TypedDPPair : Term .res → Term .res → Prop
  | recSucc (b : Term .res) (s : Term .step) (n : Term .cnt) :
      TypedDPPair (.recur b s (.succ n)) (.recur b s n)

/-- Typed dependency-pair erasure lands in the actual KO7 dependency-pair
relation, not in the source rewrite relation. -/
theorem eraseRes_typedDPPair :
    ∀ {a b : Term .res}, TypedDPPair a b → DPPair (eraseRes a) (eraseRes b)
  | _, _, TypedDPPair.recSucc b s n => by
      simpa using DPPair.rec_succ (eraseRes b) (eraseStep s) (eraseCnt n)

/-- The typed transformed-call relation is well founded by exact erasure into
the KO7 dependency-pair relation. -/
theorem typedDPPair_wellFounded :
    WellFounded (fun y x : Term .res => TypedDPPair x y) := by
  refine Subrelation.wf ?_ (InvImage.wf eraseRes wf_DPPairRev)
  intro y x h
  exact eraseRes_typedDPPair h

end SortedTransport

/-- **typeIntroduction.** The many-sorted carrier keeps the additive barrier, its independently
generated recursive step erases to the KO7 rule, the typed relation is nonempty, and its reverse
is well founded.  This is an internal persistence theorem for the specialized recursor fragment. -/
abbrev TypeIntroductionRowClaim : Prop :=
  (∀ M : OperatorKO7.ManySortedBarrierSurvival.AdditiveMeasure,
    ¬ (∀ (b : OperatorKO7.TypedBarrierSurvival.Term .res)
        (s : OperatorKO7.TypedBarrierSurvival.Term .step)
        (n : OperatorKO7.TypedBarrierSurvival.Term .cnt),
      M.evalRes (OperatorKO7.TypedBarrierSurvival.Term.wrap s
          (OperatorKO7.TypedBarrierSurvival.Term.recur b s n)) <
        M.evalRes (OperatorKO7.TypedBarrierSurvival.Term.recur b s
          (OperatorKO7.TypedBarrierSurvival.Term.succ n))))
    ∧ (∀ {a b}, SortedTransport.TypedRecSuccStep a b →
      Step (SortedTransport.eraseRes a) (SortedTransport.eraseRes b))
    ∧ WellFounded
      (fun y x : OperatorKO7.TypedBarrierSurvival.Term .res =>
        SortedTransport.TypedRecSuccStep x y)
    ∧ ∃ a b : OperatorKO7.TypedBarrierSurvival.Term .res,
        SortedTransport.TypedRecSuccStep a b

theorem typeIntroduction_row_anchor : TypeIntroductionRowClaim :=
  ⟨OperatorKO7.ManySortedBarrierSurvival.no_additive_orients_manySorted_recSucc,
    SortedTransport.eraseRes_typedRecSuccStep,
    SortedTransport.typedRecSuccStep_wellFounded,
    ⟨.recur .base .stepZero (.succ .zero),
      .wrap .stepZero (.recur .base .stepZero .zero),
      SortedTransport.typedRecSuccStep_nonempty⟩⟩

/-- **manySortedPersistence.** The specialized many-sorted presentation is definitionally the
typed presentation and therefore carries the same exact operational and termination theorem. -/
abbrev ManySortedPersistenceRowClaim : Prop :=
  TypeIntroductionRowClaim
    ∧ OperatorKO7.ManySortedBarrierSurvival.MSort =
      OperatorKO7.TypedBarrierSurvival.Ty

theorem manySortedPersistence_row_anchor : ManySortedPersistenceRowClaim :=
  ⟨typeIntroduction_row_anchor, rfl⟩

/-! ### Order-sorted dependency pairs -/

/-- A closed order-sorted carrier.  Unlike the plain typed relation above, the sort is data and
therefore remains visible to processors that range over the whole carrier. -/
inductive OrderSortedTerm where
  | cnt : OperatorKO7.TypedBarrierSurvival.Term .cnt → OrderSortedTerm
  | step : OperatorKO7.TypedBarrierSurvival.Term .step → OrderSortedTerm
  | res : OperatorKO7.TypedBarrierSurvival.Term .res → OrderSortedTerm

/-- The declared subsort order `cnt < step < res`.  The KO7 dependency pair itself is homogeneous
at result sort, while the ambient carrier retains the proper lower sorts. -/
def orderSortRank : OperatorKO7.TypedBarrierSurvival.Ty → Nat
  | .cnt => 0
  | .step => 1
  | .res => 2

def OrderSubsort (σ τ : OperatorKO7.TypedBarrierSurvival.Ty) : Prop :=
  orderSortRank σ ≤ orderSortRank τ

theorem orderSubsort_refl (σ : OperatorKO7.TypedBarrierSurvival.Ty) :
    OrderSubsort σ σ :=
  le_rfl

theorem orderSubsort_trans : Transitive OrderSubsort := by
  intro σ τ υ hστ hτυ
  exact hστ.trans hτυ

theorem orderSubsort_cnt_step : OrderSubsort .cnt .step := by
  simp [OrderSubsort, orderSortRank]

theorem orderSubsort_step_res : OrderSubsort .step .res := by
  simp [OrderSubsort, orderSortRank]

/-- Sort projection on the closed carrier. -/
def orderSortOf : OrderSortedTerm → OperatorKO7.TypedBarrierSurvival.Ty
  | .cnt _ => .cnt
  | .step _ => .step
  | .res _ => .res

/-- The order-sorted dependency-pair relation is generated independently on the
closed carrier.  Its target is the transformed recursive call itself; the source
rewrite target with its emitted wrapper belongs to `TypedRecSuccStep` and is
deliberately not conflated with this relation. -/
inductive OrderSortedDPPair : OrderSortedTerm → OrderSortedTerm → Prop
  | recSucc
      (b : OperatorKO7.TypedBarrierSurvival.Term .res)
      (s : OperatorKO7.TypedBarrierSurvival.Term .step)
      (n : OperatorKO7.TypedBarrierSurvival.Term .cnt) :
      OrderSortedDPPair
        (.res (.recur b s (.succ n)))
        (.res (.recur b s n))

/-- The order-sorted relation is exactly the typed transformed-call relation on
result terms. -/
theorem orderSortedDPPair_res_iff
    {a b : OperatorKO7.TypedBarrierSurvival.Term .res} :
    OrderSortedDPPair (.res a) (.res b) ↔ SortedTransport.TypedDPPair a b := by
  constructor
  · intro h
    cases h with
    | recSucc baseArg payload counter =>
        exact SortedTransport.TypedDPPair.recSucc baseArg payload counter
  · intro h
    cases h with
    | recSucc baseArg payload counter =>
        exact OrderSortedDPPair.recSucc baseArg payload counter

/-- Every order-sorted dependency pair is homogeneous at result sort. -/
theorem orderSortedDPPair_result_sorted {a b : OrderSortedTerm}
    (h : OrderSortedDPPair a b) :
    orderSortOf a = .res ∧ orderSortOf b = .res := by
  cases h
  exact ⟨rfl, rfl⟩

/-- Read an order-sorted term back into the untyped KO7 carrier without identifying its sort. -/
def eraseOrderSorted : OrderSortedTerm → Trace
  | .cnt t => SortedTransport.eraseCnt t
  | .step t => SortedTransport.eraseStep t
  | .res t => SortedTransport.eraseRes t

/-- Exact erasure of the independently generated order-sorted relation into
the actual KO7 dependency-pair relation. -/
theorem eraseOrderSorted_pair {a b : OrderSortedTerm}
    (h : OrderSortedDPPair a b) :
    DPPair (eraseOrderSorted a) (eraseOrderSorted b) := by
  cases h with
  | recSucc baseArg payload counter =>
      simpa [eraseOrderSorted] using
        DPPair.rec_succ (SortedTransport.eraseRes baseArg)
          (SortedTransport.eraseStep payload) (SortedTransport.eraseCnt counter)

/-- Counter rank on the complete order-sorted carrier. Lower-sort terms receive rank zero because
the dependency-pair relation has no edge at those sorts. -/
def orderSortedDPRank : OrderSortedTerm → Nat
  | .res t => dpRank (SortedTransport.eraseRes t)
  | _ => 0

theorem orderSortedDPPair_decreases {a b : OrderSortedTerm}
    (h : OrderSortedDPPair a b) :
    orderSortedDPRank b < orderSortedDPRank a := by
  cases h with
  | recSucc baseArg payload counter =>
      exact dpPair_decreases
        (eraseOrderSorted_pair (OrderSortedDPPair.recSucc baseArg payload counter))

theorem orderSortedDPPair_wellFounded :
    WellFounded (fun y x : OrderSortedTerm => OrderSortedDPPair x y) := by
  refine Subrelation.wf ?_ (InvImage.wf orderSortedDPRank Nat.lt_wfRel.wf)
  intro y x h
  exact orderSortedDPPair_decreases h

theorem orderSortedDPPair_nonempty :
    OrderSortedDPPair
      (.res (.recur .base .stepZero (.succ .zero)))
      (.res (.recur .base .stepZero .zero)) :=
  .recSucc .base .stepZero .zero

/-- **orderSortedDP.** The row carries an actual order-sorted dependency-pair
syntax and transformed-call relation.  The pair is homogeneous at result sort,
exact on the typed dependency-pair presentation, erases to the real KO7
`DPPair`, is nonempty, strictly decreasing, and globally well founded. -/
abbrev OrderSortedDPRowClaim : Prop :=
  OrderSubsort .cnt .step
    ∧ OrderSubsort .step .res
    ∧ (∀ {a b : OperatorKO7.TypedBarrierSurvival.Term .res},
      OrderSortedDPPair (.res a) (.res b) ↔ SortedTransport.TypedDPPair a b)
    ∧ (∀ {a b : OrderSortedTerm}, OrderSortedDPPair a b →
      orderSortOf a = .res ∧ orderSortOf b = .res)
    ∧ (∀ {a b : OrderSortedTerm}, OrderSortedDPPair a b →
      DPPair (eraseOrderSorted a) (eraseOrderSorted b))
    ∧ (∀ {a b : OrderSortedTerm}, OrderSortedDPPair a b →
      orderSortedDPRank b < orderSortedDPRank a)
    ∧ WellFounded (fun y x : OrderSortedTerm => OrderSortedDPPair x y)
    ∧ ∃ a b : OrderSortedTerm, OrderSortedDPPair a b

theorem orderSortedDP_row_anchor : OrderSortedDPRowClaim :=
  ⟨orderSubsort_cnt_step, orderSubsort_step_res,
    fun {_ _} => orderSortedDPPair_res_iff,
    orderSortedDPPair_result_sorted, eraseOrderSorted_pair,
    orderSortedDPPair_decreases, orderSortedDPPair_wellFounded,
    ⟨.res (.recur .base .stepZero (.succ .zero)),
      .res (.recur .base .stepZero .zero),
      orderSortedDPPair_nonempty⟩⟩

/-! ### Context-sensitive rewriting -/

/-- Replacement map on the filtered signature used by the KO7 dependency-pair processor.
The other KO7 constructors have no active argument in this filtered signature. -/
structure ReplacementMap where
  deltaAllows : Bool
  recurAllows : Fin 3 → Bool
  wrapAllows : Fin 2 → Bool

/-- The exact counter route: descend through `delta`, the recursive-call position of `app`, and
the counter position of `recΔ`; freeze the duplicated payload at both of its occurrences. -/
def counterOnlyReplacement : ReplacementMap where
  deltaAllows := true
  recurAllows := fun i => decide (i.val = 2)
  wrapAllows := fun i => decide (i.val = 1)

/-- Context-sensitive closure for the filtered signature. Root contraction is always available;
congruence is available exactly at positions selected by the replacement map. -/
inductive ContextSensitiveStep (μ : ReplacementMap) (R : Trace → Trace → Prop) :
    Trace → Trace → Prop
  | root {a b : Trace} : R a b → ContextSensitiveStep μ R a b
  | delta {a b : Trace} (enabled : μ.deltaAllows = true) :
      ContextSensitiveStep μ R a b →
        ContextSensitiveStep μ R (.delta a) (.delta b)
  | appL {a a' b : Trace} (enabled : μ.wrapAllows 0 = true) :
      ContextSensitiveStep μ R a a' →
        ContextSensitiveStep μ R (.app a b) (.app a' b)
  | appR {a b b' : Trace} (enabled : μ.wrapAllows 1 = true) :
      ContextSensitiveStep μ R b b' →
        ContextSensitiveStep μ R (.app a b) (.app a b')
  | recB {b b' s n : Trace} (enabled : μ.recurAllows 0 = true) :
      ContextSensitiveStep μ R b b' →
        ContextSensitiveStep μ R (.recΔ b s n) (.recΔ b' s n)
  | recS {b s s' n : Trace} (enabled : μ.recurAllows 1 = true) :
      ContextSensitiveStep μ R s s' →
        ContextSensitiveStep μ R (.recΔ b s n) (.recΔ b s' n)
  | recN {b s n n' : Trace} (enabled : μ.recurAllows 2 = true) :
      ContextSensitiveStep μ R n n' →
        ContextSensitiveStep μ R (.recΔ b s n) (.recΔ b s n')

/-- Every context-sensitive KO7 step in the filtered signature is a full contextual step. -/
theorem contextSensitiveStep_sub_stepCtxFull (μ : ReplacementMap) :
    ∀ {a b : Trace}, ContextSensitiveStep μ Step a b → MetaSN_KO7.StepCtxFull a b
  | _, _, .root h => MetaSN_KO7.StepCtxFull.root h
  | _, _, .delta _ h =>
      MetaSN_KO7.StepCtxFull.delta (contextSensitiveStep_sub_stepCtxFull μ h)
  | _, _, .appL _ h =>
      MetaSN_KO7.StepCtxFull.appL (contextSensitiveStep_sub_stepCtxFull μ h)
  | _, _, .appR _ h =>
      MetaSN_KO7.StepCtxFull.appR (contextSensitiveStep_sub_stepCtxFull μ h)
  | _, _, .recB _ h =>
      MetaSN_KO7.StepCtxFull.recB (contextSensitiveStep_sub_stepCtxFull μ h)
  | _, _, .recS _ h =>
      MetaSN_KO7.StepCtxFull.recS (contextSensitiveStep_sub_stepCtxFull μ h)
  | _, _, .recN _ h =>
      MetaSN_KO7.StepCtxFull.recN (contextSensitiveStep_sub_stepCtxFull μ h)

/-- Every replacement-map instance on the filtered signature is strongly normalizing because it
is a subrelation of the already terminating full contextual KO7 relation. -/
theorem contextSensitiveStep_wellFounded (μ : ReplacementMap) :
    WellFounded (fun a b : Trace => ContextSensitiveStep μ Step b a) := by
  have hsub :
      Subrelation
        (fun a b : Trace => ContextSensitiveStep μ Step b a)
        MetaSN_KO7.StepCtxFullRev := by
    intro a b h
    exact contextSensitiveStep_sub_stepCtxFull μ h
  exact Subrelation.wf hsub MetaSN_KO7.wf_StepCtxFullRev_poly

@[simp] theorem counterOnly_delta_active :
    counterOnlyReplacement.deltaAllows = true := rfl

@[simp] theorem counterOnly_recur_counter_active :
    counterOnlyReplacement.recurAllows 2 = true := rfl

@[simp] theorem counterOnly_recur_base_frozen :
    counterOnlyReplacement.recurAllows 0 = false := rfl

@[simp] theorem counterOnly_recur_payload_frozen :
    counterOnlyReplacement.recurAllows 1 = false := rfl

@[simp] theorem counterOnly_wrap_payload_frozen :
    counterOnlyReplacement.wrapAllows 0 = false := rfl

@[simp] theorem counterOnly_wrap_continuation_active :
    counterOnlyReplacement.wrapAllows 1 = true := rfl

/-- Exact outer-shape theorem for the counter-only closure. Besides a root contraction, only
`delta`, the right `app` continuation, and the `recΔ` counter can propagate a contraction. -/
theorem counterOnly_contextSensitiveStep_cases {a b : Trace}
    (h : ContextSensitiveStep counterOnlyReplacement Step a b) :
    Step a b ∨
      (∃ x y, a = .delta x ∧ b = .delta y ∧
        ContextSensitiveStep counterOnlyReplacement Step x y) ∨
      (∃ f x y, a = .app f x ∧ b = .app f y ∧
        ContextSensitiveStep counterOnlyReplacement Step x y) ∨
      (∃ base payload x y, a = .recΔ base payload x ∧ b = .recΔ base payload y ∧
        ContextSensitiveStep counterOnlyReplacement Step x y) := by
  cases h with
  | root h => exact Or.inl h
  | delta _ h => exact Or.inr (Or.inl ⟨_, _, rfl, rfl, h⟩)
  | appL enabled _ => simp [counterOnlyReplacement] at enabled
  | appR _ h => exact Or.inr (Or.inr (Or.inl ⟨_, _, _, rfl, rfl, h⟩))
  | recB enabled _ => simp [counterOnlyReplacement] at enabled
  | recS enabled _ => simp [counterOnlyReplacement] at enabled
  | recN _ h => exact Or.inr (Or.inr (Or.inr ⟨_, _, _, _, rfl, rfl, h⟩))

/-- **contextSensitiveDP.** Under the counter-only replacement map the payload position is frozen,
the recursive continuation remains active, the resulting source relation is strongly normalizing,
and the pair problem is discharged by the counter projection. -/
abbrev ContextSensitiveDPRowClaim : Prop :=
  counterOnlyReplacement.deltaAllows = true
    ∧ counterOnlyReplacement.recurAllows 2 = true
    ∧ counterOnlyReplacement.recurAllows 0 = false
    ∧ counterOnlyReplacement.recurAllows 1 = false
    ∧ counterOnlyReplacement.wrapAllows 0 = false
    ∧ counterOnlyReplacement.wrapAllows 1 = true
    ∧ WellFounded
      (fun a b : Trace => ContextSensitiveStep counterOnlyReplacement Step b a)
    ∧ CounterProjectionCore

theorem contextSensitiveDP_row_anchor : ContextSensitiveDPRowClaim :=
  ⟨counterOnly_delta_active, counterOnly_recur_counter_active,
    counterOnly_recur_base_frozen, counterOnly_recur_payload_frozen,
    counterOnly_wrap_payload_frozen, counterOnly_wrap_continuation_active,
    contextSensitiveStep_wellFounded counterOnlyReplacement,
    counterProjectionCore_holds⟩

/-- The eight root-rule schemas generating `Step`. -/
inductive KO7RootRuleTag where
  | intDelta | mergeVoidLeft | mergeVoidRight | mergeCancel
  | recZero | recSucc | eqRefl | eqDiff
  deriving DecidableEq, Repr

/-- KO7 rule schemas carry no condition list. -/
def rootRuleConditions (_ : KO7RootRuleTag) : List (Trace × Trace) := []

/-- Parameterized instance relation for the eight KO7 root-rule schemas.  Keeping this relation
in `Prop` is essential: `Step` itself is proposition-valued, so Lean correctly forbids eliminating
a `Step` proof into a data-valued rule tag.  The indexed relation records the same rule identity
without violating proof irrelevance. -/
inductive KO7RuleInstance : KO7RootRuleTag → Trace → Trace → Prop
  | intDelta (t : Trace) :
      KO7RuleInstance .intDelta (.integrate (.delta t)) .void
  | mergeVoidLeft (t : Trace) :
      KO7RuleInstance .mergeVoidLeft (.merge .void t) t
  | mergeVoidRight (t : Trace) :
      KO7RuleInstance .mergeVoidRight (.merge t .void) t
  | mergeCancel (t : Trace) :
      KO7RuleInstance .mergeCancel (.merge t t) t
  | recZero (b s : Trace) :
      KO7RuleInstance .recZero (.recΔ b s .void) b
  | recSucc (b s n : Trace) :
      KO7RuleInstance .recSucc (.recΔ b s (.delta n)) (.app s (.recΔ b s n))
  | eqRefl (a : Trace) :
      KO7RuleInstance .eqRefl (.eqW a a) .void
  | eqDiff (a b : Trace) :
      KO7RuleInstance .eqDiff (.eqW a b) (.integrate (.merge a b))

/-- Every actual KO7 root step is an instance of one of the eight finite rule schemas. -/
theorem step_to_KO7RuleInstance :
    ∀ {a b : Trace}, Step a b → ∃ tag : KO7RootRuleTag, KO7RuleInstance tag a b
  | _, _, Step.R_int_delta t => ⟨.intDelta, .intDelta t⟩
  | _, _, Step.R_merge_void_left t => ⟨.mergeVoidLeft, .mergeVoidLeft t⟩
  | _, _, Step.R_merge_void_right t => ⟨.mergeVoidRight, .mergeVoidRight t⟩
  | _, _, Step.R_merge_cancel t => ⟨.mergeCancel, .mergeCancel t⟩
  | _, _, Step.R_rec_zero b s => ⟨.recZero, .recZero b s⟩
  | _, _, Step.R_rec_succ b s n => ⟨.recSucc, .recSucc b s n⟩
  | _, _, Step.R_eq_refl a => ⟨.eqRefl, .eqRefl a⟩
  | _, _, Step.R_eq_diff a b => ⟨.eqDiff, .eqDiff a b⟩

/-- Every finite rule-schema instance is an actual KO7 root step. -/
theorem KO7RuleInstance_to_step :
    ∀ {tag : KO7RootRuleTag} {a b : Trace}, KO7RuleInstance tag a b → Step a b
  | _, _, _, KO7RuleInstance.intDelta t => Step.R_int_delta t
  | _, _, _, KO7RuleInstance.mergeVoidLeft t => Step.R_merge_void_left t
  | _, _, _, KO7RuleInstance.mergeVoidRight t => Step.R_merge_void_right t
  | _, _, _, KO7RuleInstance.mergeCancel t => Step.R_merge_cancel t
  | _, _, _, KO7RuleInstance.recZero b s => Step.R_rec_zero b s
  | _, _, _, KO7RuleInstance.recSucc b s n => Step.R_rec_succ b s n
  | _, _, _, KO7RuleInstance.eqRefl a => Step.R_eq_refl a
  | _, _, _, KO7RuleInstance.eqDiff a b => Step.R_eq_diff a b

/-- Exact finite-schema characterization of the KO7 root relation. -/
theorem step_iff_KO7RuleInstance {a b : Trace} :
    Step a b ↔ ∃ tag : KO7RootRuleTag, KO7RuleInstance tag a b :=
  ⟨step_to_KO7RuleInstance, fun h => by
    rcases h with ⟨_, htag⟩
    exact KO7RuleInstance_to_step htag⟩

/-- KO7 is unconditional in the literal rule-schema sense: every actual step is an instance of
one of the eight named generators, and the matched generator has an empty condition list.  The
matched tag is proof-relevant data produced *inside an existential proposition*, so this theorem
respects Lean's elimination restriction for `Prop`-valued `Step`. -/
def KO7IsUnconditional : Prop :=
  ∀ {a b : Trace}, Step a b →
    ∃ tag : KO7RootRuleTag,
      KO7RuleInstance tag a b ∧ rootRuleConditions tag = []

theorem ko7_is_unconditional : KO7IsUnconditional := by
  intro a b h
  rcases step_iff_KO7RuleInstance.mp h with ⟨tag, htag⟩
  exact ⟨tag, htag, rfl⟩

/-- The two dimensions of a conditional dependency-pair problem. -/
inductive TwoDDimension where
  | dependency
  | condition
  deriving DecidableEq, Repr

/-- Concrete two-dimensional dependency-pair relation for KO7. The dependency dimension is the
ordinary extracted pair. A condition-dimensional pair can only be generated by a member of a
matched rule's condition list. -/
inductive KO7TwoDDP : TwoDDimension → Trace → Trace → Prop
  | dependency {a b : Trace} : DPPair a b → KO7TwoDDP .dependency a b
  | condition (tag : KO7RootRuleTag) {lhs rhs c d : Trace} :
      KO7RuleInstance tag lhs rhs →
      (c, d) ∈ rootRuleConditions tag →
      KO7TwoDDP .condition c d

theorem ko7TwoDDP_dependency_iff {a b : Trace} :
    KO7TwoDDP .dependency a b ↔ DPPair a b := by
  constructor
  · intro h
    cases h with
    | dependency hpair => exact hpair
  · exact KO7TwoDDP.dependency

theorem ko7TwoDDP_condition_empty {a b : Trace} :
    ¬ KO7TwoDDP .condition a b := by
  intro h
  cases h with
  | condition tag hinstance hmem =>
      simp [rootRuleConditions] at hmem

/-- Dimension-erased two-dimensional pair relation. -/
def KO7TwoDDPAny (a b : Trace) : Prop :=
  ∃ dimension : TwoDDimension, KO7TwoDDP dimension a b

theorem ko7TwoDDPAny_iff_DPPair {a b : Trace} :
    KO7TwoDDPAny a b ↔ DPPair a b := by
  constructor
  · rintro ⟨dimension, h⟩
    cases dimension with
    | dependency => exact ko7TwoDDP_dependency_iff.mp h
    | condition => exact False.elim (ko7TwoDDP_condition_empty h)
  · intro h
    exact ⟨.dependency, KO7TwoDDP.dependency h⟩

theorem wf_KO7TwoDDPAnyRev :
    WellFounded (fun a b : Trace => KO7TwoDDPAny b a) := by
  have hsub :
      Subrelation (fun a b : Trace => KO7TwoDDPAny b a) DPPairRev := by
    intro a b h
    exact ko7TwoDDPAny_iff_DPPair.mp h
  exact Subrelation.wf hsub wf_DPPairRev

/-- **twoDDPForCTRS.** The condition dimension is proved empty, erasing the dimension recovers
exactly the ordinary pair relation, and the resulting reverse relation is well founded. -/
abbrev TwoDDPForCTRSRowClaim : Prop :=
  KO7IsUnconditional
    ∧ (∀ a b : Trace, ¬ KO7TwoDDP .condition a b)
    ∧ (∀ a b : Trace, KO7TwoDDPAny a b ↔ DPPair a b)
    ∧ WellFounded (fun a b : Trace => KO7TwoDDPAny b a)
    ∧ CounterProjectionCore

theorem twoDDPForCTRS_row_anchor : TwoDDPForCTRSRowClaim :=
  ⟨ko7_is_unconditional, fun _ _ => ko7TwoDDP_condition_empty,
    fun _ _ => ko7TwoDDPAny_iff_DPPair, wf_KO7TwoDDPAnyRev,
    counterProjectionCore_holds⟩

/-- Satisfaction of every condition in a finite condition list. The predicate is abstract so the
empty-condition theorem below applies to reachability, joinability, normalization, or any other
operational condition semantics. -/
def ConditionsHold (satisfies : Trace × Trace → Prop)
    (conditions : List (Trace × Trace)) : Prop :=
  ∀ condition ∈ conditions, satisfies condition

/-- Operational root relation induced by the finite KO7 rule-schema catalog under an arbitrary
condition-satisfaction semantics. -/
def KO7ConditionalOperationalStep (satisfies : Trace × Trace → Prop)
    (a b : Trace) : Prop :=
  ∃ tag : KO7RootRuleTag,
    KO7RuleInstance tag a b ∧ ConditionsHold satisfies (rootRuleConditions tag)

/-- Empty condition lists make the operational relation independent of the chosen condition
semantics and extensionally identical to the KO7 root relation. -/
theorem ko7ConditionalOperationalStep_iff_step
    (satisfies : Trace × Trace → Prop) {a b : Trace} :
    KO7ConditionalOperationalStep satisfies a b ↔ Step a b := by
  constructor
  · rintro ⟨tag, hinstance, _⟩
    exact KO7RuleInstance_to_step hinstance
  · intro hstep
    rcases step_to_KO7RuleInstance hstep with ⟨tag, hinstance⟩
    refine ⟨tag, hinstance, ?_⟩
    simp [ConditionsHold, rootRuleConditions]

theorem ko7ConditionalOperationalStep_eq_step
    (satisfies : Trace × Trace → Prop) :
    KO7ConditionalOperationalStep satisfies = Step := by
  funext a b
  exact propext (ko7ConditionalOperationalStep_iff_step satisfies)

theorem ko7ConditionalOperationalTermination_iff
    (satisfies : Trace × Trace → Prop) :
    WellFounded
        (fun a b : Trace => KO7ConditionalOperationalStep satisfies b a) ↔
      WellFounded (fun a b : Trace => Step b a) := by
  rw [ko7ConditionalOperationalStep_eq_step satisfies]

theorem ko7ConditionalOperationalTermination
    (satisfies : Trace × Trace → Prop) :
    WellFounded
      (fun a b : Trace => KO7ConditionalOperationalStep satisfies b a) := by
  rw [ko7ConditionalOperationalStep_eq_step satisfies]
  exact OperatorKO7.PolyInterpretation.wf_StepRev_poly

/-- **operationalTerminationCTRS.** For every possible interpretation of condition satisfaction,
the operational relation is exactly `Step`; termination is therefore equivalent and both sides
are proved well founded. -/
abbrev OperationalTerminationCTRSRowClaim : Prop :=
  KO7IsUnconditional
    ∧ WellFounded (fun a b : Trace => Step b a)
    ∧ ∀ satisfies : Trace × Trace → Prop,
      (∀ a b : Trace, KO7ConditionalOperationalStep satisfies a b ↔ Step a b)
        ∧ (WellFounded
              (fun a b : Trace => KO7ConditionalOperationalStep satisfies b a) ↔
            WellFounded (fun a b : Trace => Step b a))
        ∧ WellFounded
            (fun a b : Trace => KO7ConditionalOperationalStep satisfies b a)

theorem operationalTerminationCTRS_row_anchor : OperationalTerminationCTRSRowClaim :=
  ⟨ko7_is_unconditional, OperatorKO7.PolyInterpretation.wf_StepRev_poly, fun satisfies =>
    ⟨fun _ _ => ko7ConditionalOperationalStep_iff_step satisfies,
      ko7ConditionalOperationalTermination_iff satisfies,
      ko7ConditionalOperationalTermination satisfies⟩⟩

/-! ## Constrained rewriting -/

/-- An integer-valued constrained counter certificate on the concrete pair relation. -/
structure ConstrainedCounterCertificate where
  counter : Trace → Int
  constraint : Trace → Prop
  source_constrained : ∀ b s n : Trace, constraint (recΔ b s (delta n))
  decreases : ∀ {a b : Trace}, DPPair a b → counter b < counter a

def ko7ConstrainedCertificate : ConstrainedCounterCertificate where
  counter := fun t => (dpRank t : Int)
  constraint := fun t => 0 < (dpRank t : Int)
  source_constrained := fun b s n => by simp [dpRank, dpProjection]
  decreases := fun h => Int.ofNat_lt.mpr (dpPair_decreases h)

/-- Logically constrained pair relation: an extracted pair whose source satisfies the integer
positivity constraint. -/
def ConstrainedDPPair (a b : Trace) : Prop :=
  DPPair a b ∧ ko7ConstrainedCertificate.constraint a

theorem constrainedDPPair_iff_DPPair {a b : Trace} :
    ConstrainedDPPair a b ↔ DPPair a b := by
  constructor
  · exact And.left
  · intro h
    cases h with
    | rec_succ base payload counter =>
        exact ⟨DPPair.rec_succ base payload counter,
          ko7ConstrainedCertificate.source_constrained base payload counter⟩

theorem constrainedDPPair_decreases {a b : Trace}
    (h : ConstrainedDPPair a b) :
    ko7ConstrainedCertificate.counter b < ko7ConstrainedCertificate.counter a :=
  ko7ConstrainedCertificate.decreases h.1

theorem wf_ConstrainedDPPairRev :
    WellFounded (fun a b : Trace => ConstrainedDPPair b a) := by
  have hsub :
      Subrelation (fun a b : Trace => ConstrainedDPPair b a) DPPairRev := by
    intro a b h
    exact h.1
  exact Subrelation.wf hsub wf_DPPairRev

/-- **integerTermRewriting.** The counter is encoded as an integer with a positivity constraint,
the constrained relation is exactly the KO7 pair relation, and its reverse is well founded. -/
abbrev IntegerTermRewritingRowClaim : Prop :=
  (∀ (b s n : Trace), ko7ConstrainedCertificate.constraint (recΔ b s (delta n)))
    ∧ (∀ {a b : Trace},
        DPPair a b → ko7ConstrainedCertificate.counter b < ko7ConstrainedCertificate.counter a)
    ∧ (∀ a b : Trace, ConstrainedDPPair a b ↔ DPPair a b)
    ∧ WellFounded (fun a b : Trace => ConstrainedDPPair b a)

theorem integerTermRewriting_row_anchor : IntegerTermRewritingRowClaim :=
  ⟨ko7ConstrainedCertificate.source_constrained, ko7ConstrainedCertificate.decreases,
    fun _ _ => constrainedDPPair_iff_DPPair, wf_ConstrainedDPPairRev⟩

/-- **lctrs.** Exact logically constrained pair semantics, including constraint erasure and strong
normalization of the constrained reverse relation. -/
abbrev LCTRSRowClaim : Prop :=
  (∀ a b : Trace, ConstrainedDPPair a b ↔ DPPair a b)
    ∧ (∀ {a b : Trace}, ConstrainedDPPair a b →
      ko7ConstrainedCertificate.counter b < ko7ConstrainedCertificate.counter a)
    ∧ WellFounded (fun a b : Trace => ConstrainedDPPair b a)

theorem lctrs_row_anchor : LCTRSRowClaim :=
  ⟨fun _ _ => constrainedDPPair_iff_DPPair, constrainedDPPair_decreases,
    wf_ConstrainedDPPairRev⟩

/-- Closed, binder-free translation of every KO7 trace into the repository's higher-order syntax.
Distinct closed tags retain the four constructors whose counter projection resets to zero. -/
@[simp] def encodeTraceHO : Trace → OperatorKO7.HigherOrderRewritingSyntax.HOTerm
  | .void => .atom
  | .delta t => .succ (encodeTraceHO t)
  | .integrate t => .app (.app .atom (encodeTraceHO t)) .atom
  | .merge a b =>
      .app (.app (.app (.succ .atom) (encodeTraceHO a)) (encodeTraceHO b)) .atom
  | .app a b =>
      .app (.app (.app (.succ (.succ .atom)) (encodeTraceHO a)) (encodeTraceHO b)) .atom
  | .recΔ b s n => .recur (encodeTraceHO b) (encodeTraceHO s) (encodeTraceHO n)
  | .eqW a b =>
      .app
        (.app (.app (.succ (.succ (.succ .atom))) (encodeTraceHO a)) (encodeTraceHO b))
        .atom

/-- Partial inverse of `encodeTraceHO`. -/
@[simp] def decodeTraceHO :
    OperatorKO7.HigherOrderRewritingSyntax.HOTerm → Option Trace
  | .atom => some .void
  | .succ t => Option.map .delta (decodeTraceHO t)
  | .app (.app .atom t) .atom => Option.map .integrate (decodeTraceHO t)
  | .app (.app (.app (.succ .atom) a) b) .atom =>
      match decodeTraceHO a, decodeTraceHO b with
      | some a', some b' => some (.merge a' b')
      | _, _ => none
  | .app (.app (.app (.succ (.succ .atom)) a) b) .atom =>
      match decodeTraceHO a, decodeTraceHO b with
      | some a', some b' => some (.app a' b')
      | _, _ => none
  | .recur b s n =>
      match decodeTraceHO b, decodeTraceHO s, decodeTraceHO n with
      | some b', some s', some n' => some (.recΔ b' s' n')
      | _, _, _ => none
  | .app (.app (.app (.succ (.succ (.succ .atom))) a) b) .atom =>
      match decodeTraceHO a, decodeTraceHO b with
      | some a', some b' => some (.eqW a' b')
      | _, _ => none
  | _ => none

@[simp] theorem decodeTraceHO_encodeTraceHO (t : Trace) :
    decodeTraceHO (encodeTraceHO t) = some t := by
  induction t <;> simp [encodeTraceHO, decodeTraceHO, *]

theorem encodeTraceHO_injective : Function.Injective encodeTraceHO := by
  intro a b h
  have hDecoded := congrArg decodeTraceHO h
  simpa using hDecoded

/-- The translated image lies in the closed, binder-free higher-order fragment. -/
theorem encodeTraceHO_closed :
    ∀ t : Trace,
      OperatorKO7.HigherOrderRewritingSyntax.ClosedFragment (encodeTraceHO t)
  | .void => .atom
  | .delta t => .succ (encodeTraceHO_closed t)
  | .integrate t =>
      .app (.app .atom (encodeTraceHO_closed t)) .atom
  | .merge a b =>
      .app
        (.app (.app (.succ .atom) (encodeTraceHO_closed a)) (encodeTraceHO_closed b))
        .atom
  | .app a b =>
      .app
        (.app
          (.app (.succ (.succ .atom)) (encodeTraceHO_closed a))
          (encodeTraceHO_closed b))
        .atom
  | .recΔ b s n =>
      .recur (encodeTraceHO_closed b) (encodeTraceHO_closed s) (encodeTraceHO_closed n)
  | .eqW a b =>
      .app
        (.app
          (.app (.succ (.succ (.succ .atom))) (encodeTraceHO_closed a))
          (encodeTraceHO_closed b))
        .atom

/-- Higher-order counter retaining only successor depth and the recursor counter coordinate. -/
@[simp] def higherOrderCounter :
    OperatorKO7.HigherOrderRewritingSyntax.HOTerm → Nat
  | .succ t => higherOrderCounter t + 1
  | .recur _ _ n => higherOrderCounter n
  | _ => 0

@[simp] theorem higherOrderCounter_encodeTraceHO (t : Trace) :
    higherOrderCounter (encodeTraceHO t) = dpRank t := by
  induction t <;> simp [encodeTraceHO, higherOrderCounter, dpRank, dpProjection, *]

/-- The first-order constrained pair transported to the closed higher-order image. -/
def HigherOrderConstrainedDPPair
    (a b : OperatorKO7.HigherOrderRewritingSyntax.HOTerm) : Prop :=
  ∃ x y : Trace,
    ConstrainedDPPair x y ∧ encodeTraceHO x = a ∧ encodeTraceHO y = b

theorem higherOrderConstrainedDPPair_on_image_iff {a b : Trace} :
    HigherOrderConstrainedDPPair (encodeTraceHO a) (encodeTraceHO b) ↔
      ConstrainedDPPair a b := by
  constructor
  · rintro ⟨x, y, hxy, hxa, hyb⟩
    have hx : x = a := encodeTraceHO_injective hxa
    have hy : y = b := encodeTraceHO_injective hyb
    simpa [hx, hy] using hxy
  · intro h
    exact ⟨a, b, h, rfl, rfl⟩

theorem higherOrderConstrainedDPPair_decreases {a b}
    (h : HigherOrderConstrainedDPPair a b) :
    higherOrderCounter b < higherOrderCounter a := by
  rcases h with ⟨x, y, hxy, hxa, hyb⟩
  calc
    higherOrderCounter b = higherOrderCounter (encodeTraceHO y) :=
      congrArg higherOrderCounter hyb.symm
    _ = dpRank y := higherOrderCounter_encodeTraceHO y
    _ < dpRank x := dpPair_decreases hxy.1
    _ = higherOrderCounter (encodeTraceHO x) :=
      (higherOrderCounter_encodeTraceHO x).symm
    _ = higherOrderCounter a := congrArg higherOrderCounter hxa

def HigherOrderConstraint
    (t : OperatorKO7.HigherOrderRewritingSyntax.HOTerm) : Prop :=
  0 < higherOrderCounter t

theorem higherOrderConstrainedDPPair_source_constrained {a b}
    (h : HigherOrderConstrainedDPPair a b) : HigherOrderConstraint a := by
  have hdec := higherOrderConstrainedDPPair_decreases h
  exact Nat.zero_lt_of_lt hdec

theorem wf_HigherOrderConstrainedDPPairRev :
    WellFounded
      (fun a b : OperatorKO7.HigherOrderRewritingSyntax.HOTerm =>
        HigherOrderConstrainedDPPair b a) := by
  have hsub :
      Subrelation
        (fun a b : OperatorKO7.HigherOrderRewritingSyntax.HOTerm =>
          HigherOrderConstrainedDPPair b a)
        (fun a b => higherOrderCounter a < higherOrderCounter b) := by
    intro a b h
    exact higherOrderConstrainedDPPair_decreases h
  exact Subrelation.wf hsub (InvImage.wf higherOrderCounter Nat.lt_wfRel.wf)

/-- **higherOrderLCTRS.** Faithful closed-fragment transport of the exact constrained KO7 pair,
with rank preservation, constraint soundness, and strong normalization on the full translated
relation. -/
abbrev HigherOrderLCTRSRowClaim : Prop :=
  Function.Injective encodeTraceHO
    ∧ (∀ t : Trace, decodeTraceHO (encodeTraceHO t) = some t)
    ∧ (∀ t : Trace,
      OperatorKO7.HigherOrderRewritingSyntax.ClosedFragment (encodeTraceHO t))
    ∧ (∀ t : Trace, higherOrderCounter (encodeTraceHO t) = dpRank t)
    ∧ (∀ a b : Trace,
      HigherOrderConstrainedDPPair (encodeTraceHO a) (encodeTraceHO b) ↔
        ConstrainedDPPair a b)
    ∧ (∀ {a b}, HigherOrderConstrainedDPPair a b → HigherOrderConstraint a)
    ∧ (∀ {a b}, HigherOrderConstrainedDPPair a b →
      higherOrderCounter b < higherOrderCounter a)
    ∧ WellFounded
      (fun a b : OperatorKO7.HigherOrderRewritingSyntax.HOTerm =>
        HigherOrderConstrainedDPPair b a)

theorem higherOrderLCTRS_row_anchor : HigherOrderLCTRSRowClaim :=
  ⟨encodeTraceHO_injective, decodeTraceHO_encodeTraceHO, encodeTraceHO_closed,
    higherOrderCounter_encodeTraceHO,
    fun _ _ => higherOrderConstrainedDPPair_on_image_iff,
    higherOrderConstrainedDPPair_source_constrained,
    higherOrderConstrainedDPPair_decreases,
    wf_HigherOrderConstrainedDPPairRev⟩

/-! ## The safe/normal split -/

/-- Bellantoni-Cook tier assignment on the recursor: each argument position is normal or safe. -/
inductive Tier where
  | normal
  | safe
  deriving DecidableEq, Repr

/-- The KO7 assignment: the counter is normal, the base and step arguments are safe. -/
def ko7Tier : Fin 3 → Tier
  | ⟨2, _⟩ => Tier.normal
  | _ => Tier.safe

/-- The occurrence-level Bellantoni-Cook obligation for the displayed rule.  The counter must be
normal, the payload must be safe, and a safe payload may not be duplicated by the recursive clause. -/
def BellantoniCookAdmissible (τ : Fin 3 → Tier) : Prop :=
  τ 2 = .normal ∧ τ 1 = .safe ∧
    countVar SchemaVar.s dupTgt ≤ countVar SchemaVar.s dupSrc

/-- No tier assignment can satisfy the Bellantoni-Cook obligation for the duplicating rule.  The
obstruction is assignment-independent: the resource inequality is numerically false. -/
theorem no_bellantoniCookAdmissible :
    ∀ τ : Fin 3 → Tier, ¬ BellantoniCookAdmissible τ := by
  intro τ h
  have hcount := h.2.2
  rw [countVar_dupSrc_s, countVar_dupTgt_s] at hcount
  omega

/-- **bellantoniCookSplit.** The barrier is universal over tier assignments, not merely a failure
of the displayed assignment.  The concrete KO7 assignment records the intended safe/normal split,
while the universal theorem shows that no reassignment can repair the duplicated payload. -/
abbrev BellantoniCookSplitRowClaim : Prop :=
  (∀ τ : Fin 3 → Tier, ¬ BellantoniCookAdmissible τ)
    ∧ ko7Tier 2 = Tier.normal
    ∧ ko7Tier 1 = Tier.safe
    ∧ ko7Tier 0 = Tier.safe
    ∧ countVar SchemaVar.s dupSrc = 1
    ∧ countVar SchemaVar.s dupTgt = 2
    ∧ ¬ (countVar SchemaVar.s dupTgt ≤ countVar SchemaVar.s dupSrc)

theorem bellantoniCookSplit_row_anchor : BellantoniCookSplitRowClaim := by
  refine ⟨no_bellantoniCookAdmissible, rfl, rfl, rfl,
    countVar_dupSrc_s, countVar_dupTgt_s, ?_⟩
  rw [countVar_dupSrc_s, countVar_dupTgt_s]
  omega

end OperatorKO7.Methods.DependencyPairTypedRows
