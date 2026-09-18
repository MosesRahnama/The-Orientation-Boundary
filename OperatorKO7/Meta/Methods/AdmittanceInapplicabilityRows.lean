import OperatorKO7.Meta.ConfessionMethod_SCT
import OperatorKO7.Meta.LPO_KO7
import OperatorKO7.Meta.SymbolicComparatorBarrier_Weighted_Schema
import OperatorKO7.Meta.Methods.PathOrderRows
import OperatorKO7.Meta.ContextClosed_SN_Full

/-!
# Carriers for the admittance and inapplicability rows of the RDRS coverage ledger (lane E5)

Ten rows record what a definitional criterion says about the duplicating recursor: whether it
admits the definition at all, rather than whether it orients the rewrite step. Five are
admitters, two are typing barriers, one is an abstraction, one is an inapplicability marker, and
one is the size-change escape.

The five admitters share one fact: the recursive call sits on the strict subterm `n` of the
counter `delta n`, so structural descent holds and every criterion built on it, HORPO's
first-order fragment, the computability-path order, the general schema, sized types, and the Coq
guard, admits the definition. `counterDescent` is that fact, compiled once.

The two typing barriers share the opposite fact: the payload variable occurs twice on the
right-hand side, so no linear typing exists and the tier assignment cannot be predicative.

Relation: the schema duplicating rule and the KO7 root relation. Closure: root.
External trust: none. Mathlib only.
-/

namespace OperatorKO7.Methods.AdmittanceInapplicabilityRows

open OperatorKO7
open OperatorKO7.Trace
open OperatorKO7.SymbolicComparatorBarrier
open OperatorKO7.ConfessionMethodFamily

/-! ## Structural descent on the counter -/

/-- Structural depth of the counter argument. -/
def counterDepth : STerm → Nat
  | STerm.var _ => 0
  | STerm.base => 0
  | STerm.succ t => 1 + counterDepth t
  | STerm.wrap _ _ => 0
  | STerm.recur _ _ n => counterDepth n

/-- Counter constructor matched by the duplicating recursor rule. -/
def matchedCounter : STerm := STerm.succ (STerm.var SchemaVar.n)

/-- Counter passed to the recursive call in the duplicating recursor rule. -/
def recursiveCallCounter : STerm := STerm.var SchemaVar.n

/-- The source exposes `matchedCounter` as its recursion argument. -/
theorem dupSrc_matchedCounter :
    dupSrc = STerm.recur (STerm.var SchemaVar.b) (STerm.var SchemaVar.s) matchedCounter := rfl

/-- The target's unique recursive call receives `recursiveCallCounter`. -/
theorem dupTgt_recursiveCallCounter :
    dupTgt =
      STerm.wrap (STerm.var SchemaVar.s)
        (STerm.recur (STerm.var SchemaVar.b) (STerm.var SchemaVar.s) recursiveCallCounter) := rfl

/-- Proper syntactic subterm relation on the schema term algebra. -/
inductive StrictSubterm : STerm → STerm → Prop
  | succ (t : STerm) : StrictSubterm t (.succ t)
  | wrapLeft (x y : STerm) : StrictSubterm x (.wrap x y)
  | wrapRight (x y : STerm) : StrictSubterm y (.wrap x y)
  | recurBase (b s n : STerm) : StrictSubterm b (.recur b s n)
  | recurStep (b s n : STerm) : StrictSubterm s (.recur b s n)
  | recurCounter (b s n : STerm) : StrictSubterm n (.recur b s n)
  | trans {x y z : STerm} : StrictSubterm x y → StrictSubterm y z → StrictSubterm x z

/-- Proper subterms have smaller structural size. -/
theorem strictSubterm_size_lt {x y : STerm} (h : StrictSubterm x y) :
    OperatorKO7.Methods.PathOrderRows.stermSize x <
      OperatorKO7.Methods.PathOrderRows.stermSize y := by
  induction h with
  | succ t =>
      simp only [OperatorKO7.Methods.PathOrderRows.stermSize]
      omega
  | wrapLeft x y =>
      simp only [OperatorKO7.Methods.PathOrderRows.stermSize]
      omega
  | wrapRight x y =>
      simp only [OperatorKO7.Methods.PathOrderRows.stermSize]
      omega
  | recurBase b s n =>
      simp only [OperatorKO7.Methods.PathOrderRows.stermSize]
      omega
  | recurStep b s n =>
      simp only [OperatorKO7.Methods.PathOrderRows.stermSize]
      omega
  | recurCounter b s n =>
      simp only [OperatorKO7.Methods.PathOrderRows.stermSize]
      omega
  | trans hxy hyz ihxy ihyz => exact Nat.lt_trans ihxy ihyz

/-- The proper-subterm relation is well founded, not merely irreflexive on the displayed call. -/
theorem strictSubterm_wellFounded : WellFounded StrictSubterm := by
  have hsub :
      Subrelation StrictSubterm
        (fun x y : STerm =>
          OperatorKO7.Methods.PathOrderRows.stermSize x <
            OperatorKO7.Methods.PathOrderRows.stermSize y) := by
    intro x y h
    exact strictSubterm_size_lt h
  exact Subrelation.wf hsub
    (InvImage.wf OperatorKO7.Methods.PathOrderRows.stermSize Nat.lt_wfRel.wf)

/-- Exact recursive-call certificate: the KO7 counter call is on the constructor predecessor. -/
theorem ko7_recursive_counter_strict_subterm :
    StrictSubterm recursiveCallCounter matchedCounter :=
  StrictSubterm.succ _

/-- **The shared admittance fact.** In the duplicating rule the recursive call is made on the
strict structural predecessor of the counter, so the counter depth strictly drops. Every
definitional criterion that admits structurally descending recursion admits this definition. -/
theorem counterDescent : counterDepth recursiveCallCounter < counterDepth matchedCounter := by
  simp [recursiveCallCounter, matchedCounter, counterDepth]

/-- A definitional admittance criterion: a predicate on the recursive call that the criterion
requires, together with the fact that the KO7 recursor satisfies it. -/
structure AdmittanceCriterion where
  admits : Prop
  ko7Satisfies : admits

/-- The criterion every admitter row instantiates. -/
def structuralDescentCriterion : AdmittanceCriterion where
  admits := StrictSubterm recursiveCallCounter matchedCounter
  ko7Satisfies := ko7_recursive_counter_strict_subterm

/-- **horpoAdmittance.** The first-order fragment of HORPO is a recursive path order, and the
recursive call descends structurally, so the definition is admitted. The KO7 path order supplies
the orientation the criterion pairs with. -/
abbrev HorpoAdmittanceRowClaim : Prop :=
  StrictSubterm recursiveCallCounter matchedCounter
    ∧ WellFounded StrictSubterm
    ∧ counterDepth recursiveCallCounter < counterDepth matchedCounter
    ∧ (∀ {a b : Trace}, Step a b → OperatorKO7.MetaLPO.LPO_KO7 a b)

theorem horpoAdmittance_row_anchor : HorpoAdmittanceRowClaim :=
  ⟨ko7_recursive_counter_strict_subterm, strictSubterm_wellFounded,
    counterDescent, OperatorKO7.MetaLPO.lpo_orients_all_root_rules⟩

/-- The accessible-subterm fragment of the computability closure used by CPO on this first-order
schema. This is a distinct proof object, not a second name for the HORPO proposition. -/
inductive FirstOrderComputabilityClosure : STerm → STerm → Prop
  | accessibleArgument {x y : STerm} :
      StrictSubterm x y → FirstOrderComputabilityClosure x y

theorem firstOrderComputabilityClosure_iff {x y : STerm} :
    FirstOrderComputabilityClosure x y ↔ StrictSubterm x y := by
  constructor
  · intro h
    cases h with
    | accessibleArgument hsub => exact hsub
  · exact FirstOrderComputabilityClosure.accessibleArgument

/-- The specialized computability closure is well founded on the whole schema syntax. -/
theorem firstOrderComputabilityClosure_wellFounded :
    WellFounded FirstOrderComputabilityClosure := by
  have hsub : Subrelation FirstOrderComputabilityClosure StrictSubterm := by
    intro x y h
    exact firstOrderComputabilityClosure_iff.mp h
  exact Subrelation.wf hsub strictSubterm_wellFounded

/-- The recursive counter belongs to the computability closure of the matched constructor. -/
theorem ko7_recursive_counter_in_computabilityClosure :
    FirstOrderComputabilityClosure recursiveCallCounter matchedCounter :=
  FirstOrderComputabilityClosure.accessibleArgument ko7_recursive_counter_strict_subterm

/-- **cpoAdmittance.** The first-order computability closure contains the recursive counter,
is globally well founded on schema terms, and is paired with the compiled KO7 path-order
orientation. -/
abbrev CpoAdmittanceRowClaim : Prop :=
  FirstOrderComputabilityClosure recursiveCallCounter matchedCounter
    ∧ WellFounded FirstOrderComputabilityClosure
    ∧ counterDepth recursiveCallCounter < counterDepth matchedCounter
    ∧ (∀ {a b : Trace}, Step a b → OperatorKO7.MetaLPO.LPO_KO7 a b)

theorem cpoAdmittance_row_anchor : CpoAdmittanceRowClaim :=
  ⟨ko7_recursive_counter_in_computabilityClosure,
    firstOrderComputabilityClosure_wellFounded, counterDescent,
    OperatorKO7.MetaLPO.lpo_orients_all_root_rules⟩

/-- **generalSchemaAdmittance.** The general schema on the first-order recursor requires the
recursive call to be on a strict subterm of a constructor argument; `delta n` has `n` as its
strict subterm. -/
abbrev GeneralSchemaAdmittanceRowClaim : Prop :=
  StrictSubterm recursiveCallCounter matchedCounter
    ∧ WellFounded StrictSubterm
    ∧ counterDepth recursiveCallCounter < counterDepth matchedCounter
    ∧ counterDepth matchedCounter = 1 + counterDepth recursiveCallCounter

theorem generalSchemaAdmittance_row_anchor : GeneralSchemaAdmittanceRowClaim :=
  ⟨ko7_recursive_counter_strict_subterm, strictSubterm_wellFounded, counterDescent, rfl⟩

/-- A sized-type predicate: the counter carries a size index that strictly decreases along the
recursive call. -/
def SizedDescent (size : STerm → Nat) : Prop :=
  size recursiveCallCounter < size matchedCounter

/-- **sizedTypesAdmittance.** The counter depth is a size index witnessing the descent. -/
abbrev SizedTypesAdmittanceRowClaim : Prop := SizedDescent counterDepth

theorem sizedTypesAdmittance_row_anchor : SizedTypesAdmittanceRowClaim := counterDescent

/-- The Coq guard condition on the recursor: the recursive call's counter argument is a strict
structural subterm of the pattern-matched counter. -/
def guardSatisfied : Prop := StrictSubterm recursiveCallCounter matchedCounter

/-- **coqGuardAdmittance.** -/
abbrev CoqGuardAdmittanceRowClaim : Prop := guardSatisfied

theorem coqGuardAdmittance_row_anchor : CoqGuardAdmittanceRowClaim :=
  ko7_recursive_counter_strict_subterm

/-! ## Typing barriers -/

/-- The rule is resource-linear when its left side is left-linear and its right side does not use
any variable more often than the left side. This is the exact multiplicity discipline of an
exponential-free linear rule, not an absolute right-side occurrence cap. -/
def LinearTypable : Prop :=
  (∀ v : SchemaVar, countVar v dupSrc ≤ 1) ∧
    ∀ v : SchemaVar, countVar v dupTgt ≤ countVar v dupSrc

/-- An arbitrary rule-typing discipline whose derivations are sound for exponential-free resource
use.  No syntax or proof rules are fixed here; the only required law is the occurrence inequality
that every contraction-free derivation must satisfy. -/
structure ResourceSoundRuleTyping where
  Derivable : STerm → STerm → Prop
  occurrence_sound :
    ∀ {source target : STerm}, Derivable source target →
      ∀ v : SchemaVar, countVar v target ≤ countVar v source

/-- Every resource-sound rule-typing discipline rejects the duplicating KO7 schema rule. -/
theorem no_resourceSoundRuleTyping_derives_dup
    (T : ResourceSoundRuleTyping) :
    ¬ T.Derivable dupSrc dupTgt := by
  intro h
  have hs := T.occurrence_sound h SchemaVar.s
  rw [countVar_dupSrc_s, countVar_dupTgt_s] at hs
  omega

/-- The universal quantification is non-vacuous: the maximal occurrence-sound discipline accepts
exactly the rules satisfying all resource inequalities. -/
def maximalResourceSoundRuleTyping : ResourceSoundRuleTyping where
  Derivable := fun source target =>
    ∀ v : SchemaVar, countVar v target ≤ countVar v source
  occurrence_sound := fun h => h

theorem maximalResourceSoundRuleTyping_accepts_identity (t : STerm) :
    maximalResourceSoundRuleTyping.Derivable t t := by
  intro v
  exact le_rfl

/-- The duplicating rule's source is left-linear. -/
theorem dupSrc_leftLinear : ∀ v : SchemaVar, countVar v dupSrc ≤ 1 := by
  intro v
  cases v <;> simp [dupSrc, countVar]

/-- **linearLogicTypingBarrier.** The payload occurs twice on the right-hand side, so no
exponential-free linear typing exists for the duplicating rule. -/
theorem dup_not_linearTypable : ¬ LinearTypable := by
  intro h
  have hs := h.2 SchemaVar.s
  rw [countVar_dupSrc_s, countVar_dupTgt_s] at hs
  omega

abbrev LinearLogicTypingBarrierRowClaim : Prop :=
  (∀ v : SchemaVar, countVar v dupSrc ≤ 1)
    ∧ ¬ LinearTypable
    ∧ countVar SchemaVar.s dupSrc = 1
    ∧ countVar SchemaVar.s dupTgt = 2
    ∧ (∀ T : ResourceSoundRuleTyping, ¬ T.Derivable dupSrc dupTgt)
    ∧ (∀ t : STerm, maximalResourceSoundRuleTyping.Derivable t t)

theorem linearLogicTypingBarrier_row_anchor : LinearLogicTypingBarrierRowClaim :=
  ⟨dupSrc_leftLinear, dup_not_linearTypable, countVar_dupSrc_s, countVar_dupTgt_s,
    no_resourceSoundRuleTyping_derives_dup,
    maximalResourceSoundRuleTyping_accepts_identity⟩

/-- A Leivant tier assignment on the recursor's three arguments. -/
def LeivantTier := Fin 3 → Nat

/-- A ramified assignment requires the recursive result to sit at a strictly lower tier than the
recursion argument, and forbids a tier-raising duplication of a lower-tier variable. -/
def RamifiedAdmissible (τ : LeivantTier) : Prop :=
  τ 0 < τ 2 ∧ τ 1 < τ 2 ∧ countVar SchemaVar.s dupTgt ≤ countVar SchemaVar.s dupSrc

/-- **ramifiedRecursionTypingBarrier.** No tier assignment is admissible, because the third clause
fails for every assignment: the payload count doubles. -/
theorem no_ramified_assignment : ∀ τ : LeivantTier, ¬ RamifiedAdmissible τ := by
  intro τ h
  have := h.2.2
  rw [countVar_dupSrc_s, countVar_dupTgt_s] at this
  omega

abbrev RamifiedRecursionTypingBarrierRowClaim : Prop :=
  (∀ τ : LeivantTier, ¬ RamifiedAdmissible τ) ∧ countVar SchemaVar.s dupTgt = 2

theorem ramifiedRecursionTypingBarrier_row_anchor : RamifiedRecursionTypingBarrierRowClaim :=
  ⟨no_ramified_assignment, countVar_dupTgt_s⟩

/-! ## Abstraction and inapplicability -/

/-- **abstractInterpretationAdmittance.** The abstraction a size analyser computes on this
definition is the size-change graph of the recursive call: the counter coordinate descends and the
other two are nonincreasing. That graph is already compiled. -/
abbrev AbstractInterpretationAdmittanceRowClaim : Prop :=
  schemaRecCallGraph.arcs ⟨2, by omega⟩ ⟨2, by omega⟩ = SCArc.strictDecrease
    ∧ schemaRecCallGraph.arcs ⟨0, by omega⟩ ⟨0, by omega⟩ = SCArc.nonIncreasing
    ∧ schemaRecCallGraph.arcs ⟨1, by omega⟩ ⟨1, by omega⟩ = SCArc.nonIncreasing
    ∧ sctSatisfied schemaRecCallGraph

theorem abstractInterpretationAdmittance_row_anchor :
    AbstractInterpretationAdmittanceRowClaim :=
  ⟨schemaRecCallGraph_counter_descent, schemaRecCallGraph_base_nonincreasing,
    schemaRecCallGraph_step_nonincreasing, schema_sct_satisfied⟩

/-- **sizeChangeTerminationEscape.** The size-change route succeeds: the unique descent is the
counter coordinate, and the derived rank is the dependency-pair projection. -/
abbrev SizeChangeTerminationEscapeRowClaim : Prop :=
  sctSatisfied schemaRecCallGraph
    ∧ sctRankFn = OperatorKO7.CompositionalImpossibility.dpProjection
    ∧ (∀ b s n : Trace,
        sctDerivedRank.rank
            (OperatorKO7.CompositionalImpossibility.ko7Schema.wrap s
              (OperatorKO7.CompositionalImpossibility.ko7Schema.recur b s n)) <
          sctDerivedRank.rank
            (OperatorKO7.CompositionalImpossibility.ko7Schema.recur b s
              (OperatorKO7.CompositionalImpossibility.ko7Schema.succ n)))

theorem sizeChangeTerminationEscape_row_anchor : SizeChangeTerminationEscapeRowClaim :=
  ⟨schema_sct_satisfied, sctRankFn_eq_dpProjection, sctDerivedRank_orients_dup_step⟩

/-- Structural-induction principle for the finite trace carrier. -/
abbrev FiniteTraceInduction : Prop :=
  ∀ (P : Trace → Prop),
    P void →
    (∀ t, P t → P (delta t)) →
    (∀ t, P t → P (integrate t)) →
    (∀ x y, P x → P y → P (merge x y)) →
    (∀ x y, P x → P y → P (app x y)) →
    (∀ b s n, P b → P s → P n → P (recΔ b s n)) →
    (∀ x y, P x → P y → P (eqW x y)) →
    ∀ t, P t

/-- The finite trace induction principle is inhabited. -/
theorem finiteTraceInduction_holds : FiniteTraceInduction := by
  intro P hv hd hi hm ha hr he t
  induction t with
  | void => exact hv
  | delta t ih => exact hd t ih
  | integrate t ih => exact hi t ih
  | merge x y ihx ihy => exact hm x y ihx ihy
  | app x y ihx ihy => exact ha x y ihx ihy
  | recΔ b s n ihb ihs ihn => exact hr b s n ihb ihs ihn
  | eqW x y ihx ihy => exact he x y ihx ihy

/-- An infinite forward reduction in a relation. -/
def InfiniteForwardReduction {α : Type} (R : α → α → Prop) : Prop :=
  Nonempty {f : Nat → α // ∀ n, R (f n) (f (n + 1))}

/-- Full contextual strong normalization excludes every infinite KO7 reduction sequence. -/
theorem no_infinite_stepCtxFull_reduction :
    ¬ InfiniteForwardReduction MetaSN_KO7.StepCtxFull := by
  rintro ⟨f, hf⟩
  exact
    (WellFounded.wellFounded_iff_no_descending_seq.1
      MetaSN_KO7.wf_StepCtxFullRev_poly).elim ⟨f, hf⟩

/-- **infinitaryRewritingTermination.** The exact result is stronger than mere finiteness of syntax:
the full contextual relation is well founded and admits no infinite forward reduction. -/
abbrev InfinitaryRewritingTerminationRowClaim : Prop :=
  FiniteTraceInduction
    ∧ WellFounded MetaSN_KO7.StepCtxFullRev
    ∧ ¬ InfiniteForwardReduction MetaSN_KO7.StepCtxFull

theorem infinitaryRewritingTermination_row_anchor : InfinitaryRewritingTerminationRowClaim :=
  ⟨finiteTraceInduction_holds, MetaSN_KO7.wf_StepCtxFullRev_poly,
    no_infinite_stepCtxFull_reduction⟩

end OperatorKO7.Methods.AdmittanceInapplicabilityRows
