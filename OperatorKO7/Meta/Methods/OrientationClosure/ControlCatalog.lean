import OperatorKO7.Meta.Methods.OrientationClosure.MethodRowsDependencyPairs
import OperatorKO7.Meta.Methods.OrientationClosure.CouplingTheorem
import OperatorKO7.Meta.Methods.OrientationClosure.FreePolynomialTermination
import OperatorKO7.Meta.Methods.OrientationClosure.ScalarGrammarDecision
import OperatorKO7.Meta.Methods.OrientationClosure.ObserverRanks
import Mathlib.Tactic

/-!
# Control catalog

Controls of the closeout catalog that no earlier module proves. Each theorem states the expected
outcome of one control.

C01: on the singleton schema the duplicating rule is a self-loop, no measure orients it, and the
unbounded-payload hypothesis of the coupling barrier fails for every measure. C04: the product
`payload * counter` is classified as payload-reading with a failed duplicating-step instance. C05:
the zero multiple of the payload is payload-blind and fails orientation. C07: every strictly
increasing recoding of the counter orients. C11: a strictly decreasing rational measure exists on a
nonterminating relation, and the comparison separated by `1` is well founded on the nonnegative
rationals. C21: adding a self-loop rule to the free system keeps every coupling barrier and loses
termination. C22: the certificate `counterLinear` fails once the source rule is altered. C24: a well
founded relation with finite branches of every length from one state has no natural rank. C25: the
empty system has an empty dependency-pair problem and terminates.
-/

set_option autoImplicit false

namespace OperatorKO7.Methods.OrientationClosure.ControlCatalog

open OperatorKO7.StepDuplicating
open OperatorKO7.Meta.Rewriting
open OperatorKO7.Meta.BoundaryGeneral.DirectMeasureGrammarClosure
open OperatorKO7.Methods.OrientationClosure.SchemaCore
open OperatorKO7.Methods.OrientationClosure.DependencyPairSoundness
open OperatorKO7.Methods.OrientationClosure.ProcessorSemantics
open OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs
open OperatorKO7.Methods.OrientationClosure.ScalarGrammarDecision

/-! ## C01: singleton schema -/

/-- The schema whose carrier has one element. -/
def unitSchema : StepDuplicatingSchema where
  T := Unit
  base := ()
  succ := fun _ => ()
  wrap := fun _ _ => ()
  recur := fun _ _ _ => ()

/-- C01: on the singleton schema both sides of the duplicating rule coincide, no measure orients
it, and the unbounded-payload hypothesis of the coupling barrier fails for every measure. -/
theorem singleton_schema_control :
    (∀ b s n : unitSchema.T,
      unitSchema.wrap s (unitSchema.recur b s n) = unitSchema.recur b s (unitSchema.succ n)) ∧
      (∀ M : unitSchema.T → Nat, ¬ ∀ b s n : unitSchema.T,
        M (unitSchema.wrap s (unitSchema.recur b s n)) < M (unitSchema.recur b s (unitSchema.succ n))) ∧
      (∀ M : unitSchema.T → Nat, ¬ ∀ K : Nat, ∃ s : unitSchema.T, K ≤ M s) := by
  refine ⟨fun _ _ _ => rfl, fun M h => ?_, fun M h => ?_⟩
  · exact lt_irrefl _ (h () () ())
  · obtain ⟨s, hs⟩ := h (M () + 1)
    have e : M s = M () := rfl
    omega

/-! ## C04, C05, C07: the scalar grammar -/

/-- C04: `payload * counter` is classified as payload-reading, with a failed instance. -/
theorem payload_mul_counter_classified :
    ∃ w : FailedDupWitness (.mul .payload .counter),
      classify (.mul .payload .counter) = .blockedPayload w := by
  unfold classify
  simp [readsPayload?, positiveAtUnit?, MeasureExpr.eval]

/-- C05: the zero multiple of the payload is payload-blind and fails orientation. -/
theorem zero_smul_payload_control :
    PayloadBlind (MeasureExpr.smul 0 .payload).eval ∧
      ¬ OrientsDupStep (MeasureExpr.smul 0 .payload).eval := by
  refine ⟨fun c p p' => by simp [MeasureExpr.eval], fun h => ?_⟩
  have := h 0 0 1 le_rfl
  simp [MeasureExpr.eval] at this

/-- C07: every strictly increasing recoding of the counter orients the duplicating step. -/
theorem counter_recoding_orients (g : Nat → Nat) (hg : StrictMono g) :
    OrientsDupStep (fun c _ => g c) :=
  payloadBlind_and_counterStrict_implies_orients (fun _ _ _ => rfl)
    (fun c _ => hg (Nat.lt_succ_self c))

/-! ## C11: rational shrinking steps -/

/-- The successor relation: every `x` has the smaller element `x + 1`. -/
def AscendingStep (y x : Nat) : Prop := y = x + 1

theorem ascendingStep_not_wellFounded : ¬ WellFounded AscendingStep := by
  intro h
  have key : ∀ x, Acc AscendingStep x → False := by
    intro x hx
    induction hx with
    | intro x _ ih => exact ih (x + 1) rfl
  exact key 0 (h.apply 0)

/-- C11: the rational measure `1 / (x + 1)` strictly decreases along a relation that does not
terminate, so strict decrease in the rationals certifies nothing; the comparison separated by `1`
is well founded on the nonnegative rationals. -/
theorem rational_shrinking_control :
    (∀ x : Nat, (1 : ℚ) / ((x + 1 : Nat) + 1) < 1 / ((x : Nat) + 1)) ∧
      ¬ WellFounded AscendingStep ∧
      WellFounded (fun y x : {q : ℚ // 0 ≤ q} => y.1 + 1 ≤ x.1) := by
  refine ⟨fun x => ?_, ascendingStep_not_wellFounded, ?_⟩
  · apply one_div_lt_one_div_of_lt
    · positivity
    · push_cast
      linarith
  · apply Subrelation.wf (r := InvImage (· < ·) (fun x : {q : ℚ // 0 ≤ q} => ⌊x.1⌋₊))
    · intro y x h
      show ⌊y.1⌋₊ < ⌊x.1⌋₊
      have h2 : ⌊y.1 + 1⌋₊ ≤ ⌊x.1⌋₊ := Nat.floor_mono h
      rw [Nat.floor_add_one y.2] at h2
      omega
    · exact InvImage.wf _ Nat.lt_wfRel.wf

/-! ## C21: an added self-loop rule -/

/-- The free root relation extended by the self-loop `zero → zero`. -/
inductive LoopExtStep : FreeTerm Empty → FreeTerm Empty → Prop
  | root {t u : FreeTerm Empty} : RootStep t u → LoopExtStep t u
  | loop : LoopExtStep .zero .zero

/-- C21, negative part: every coupling barrier of the free system survives the extension, since an
orienter of the extension orients the duplicating rule. -/
theorem added_self_loop_keeps_barrier (M : FreeTerm Empty → Nat) (c_w g : Nat)
    (hretain : ∀ x y : FreeTerm Empty, c_w + M x + M y ≤ M (.wrap x y))
    (hgain : ∀ b s n : FreeTerm Empty, M (.recur b s (.succ n)) ≤ M (.recur b s n) + g)
    (hunb : ∀ K : Nat, ∃ s : FreeTerm Empty, K ≤ M s) :
    ¬ ∀ {t u : FreeTerm Empty}, LoopExtStep t u → M u < M t := by
  intro h
  exact CouplingTheorem.no_orientation_of_retention_bounded_gain_unbounded_payload
    (S := freeSchema Empty) M c_w g hretain hgain hunb
    (fun b s n => h (.root (.recurSucc b s n)))

/-- C21, positive part: the extension does not terminate while the free root relation does. -/
theorem added_self_loop_loses_termination :
    ¬ WellFounded (fun u t => LoopExtStep t u) ∧
      WellFounded (fun u t : FreeTerm Empty => RootStep t u) :=
  ⟨fun h => (h.asymmetric _ _ LoopExtStep.loop) LoopExtStep.loop,
    FreePolynomialTermination.main_free_root_termination Empty⟩

/-! ## C22: altered source under the same certificate -/

/-- The successor rule with a recursive call that keeps `succ n`. -/
def alteredSuccRule : Rule FreeSym Nat where
  lhs := .app .recur [.var 0, .var 1, .app .succ [.var 2]]
  rhs := .app .wrap [.var 1, .app .recur [.var 0, .var 1, .app .succ [.var 2]]]
  lhs_isApp := rfl

/-- The free recursor with the altered successor rule. -/
def alteredTRS : TRS FreeSym Nat := [zeroRule, alteredSuccRule]

/-- C22: the same certificate `counterLinear` fails on the altered source: its pair no longer
decreases. The unaltered source is accepted. -/
theorem altered_source_certificate_fails :
    PairsStrict counterLinear freeRecursorTRS ∧ ¬ PairsStrict counterLinear alteredTRS := by
  refine ⟨counterLinear_pairsStrict, fun h => ?_⟩
  have hsub : IsSubterm (.app FreeSym.recur [.var 0, .var 1, .app .succ [.var 2]] : FTerm)
      alteredSuccRule.rhs := by
    show IsSubterm _ (Term.app FreeSym.wrap
      [Term.var 1, Term.app FreeSym.recur [Term.var 0, Term.var 1, Term.app FreeSym.succ [Term.var 2]]])
    exact IsSubterm.arg FreeSym.wrap _ (by simp) (IsSubterm.refl _)
  have hdef : IsDefined alteredTRS FreeSym.recur := ⟨zeroRule, by simp [alteredTRS], _, rfl⟩
  have := h alteredSuccRule (by simp [alteredTRS]) Subst.id FreeSym.recur
    [.var 0, .var 1, .app .succ [.var 2]] rfl FreeSym.recur
    [.var 0, .var 1, .app .succ [.var 2]] hsub hdef
  exact lt_irrefl _ this

/-! ## C24: unbounded finite branches -/

/-- From `none` to every `some k`, and down from `some (k + 1)` to `some k`. -/
inductive FanStep : Option Nat → Option Nat → Prop
  | fan (k : Nat) : FanStep none (some k)
  | down (k : Nat) : FanStep (some (k + 1)) (some k)

theorem fan_acc_some : ∀ k : Nat, Acc (fun y x => FanStep x y) (some k)
  | 0 => Acc.intro _ fun y h => by cases h
  | k + 1 => Acc.intro _ fun y h => by
      cases h
      exact fan_acc_some k

theorem fan_wellFounded : WellFounded (fun y x => FanStep x y) := by
  refine ⟨fun x => ?_⟩
  cases x with
  | none =>
    refine Acc.intro _ fun y h => ?_
    cases h
    exact fan_acc_some _
  | some k => exact fan_acc_some k

/-- C24: the fan relation is well founded, has finite paths of every length from `none`, and has no
natural-valued rank. -/
theorem fan_no_natRank :
    WellFounded (fun y x => FanStep x y) ∧ ¬ Nonempty (ObserverRanks.NatRank FanStep) := by
  refine ⟨fan_wellFounded, ?_⟩
  rintro ⟨r⟩
  have hk : ∀ k, k ≤ r.rank (some k) := by
    intro k
    induction k with
    | zero => exact Nat.zero_le _
    | succ k ih =>
      have := r.decreases (FanStep.down k)
      omega
  have h1 := r.decreases (FanStep.fan (r.rank none))
  have h2 := hk (r.rank none)
  omega

/-! ## C25: boundary outcome -/

/-- C25: the empty rewrite system has an empty dependency-pair problem, a finite one, and every term
terminates. -/
theorem empty_system_boundary :
    (∀ c d : Call Unit Nat, ¬ dpPairs emptyTRS c d) ∧ FiniteDP emptyTRS (dpPairs emptyTRS) ∧
      ∀ t : Term Unit Nat, SN emptyTRS t := by
  have hno : ∀ c d : Call Unit Nat, ¬ dpPairs emptyTRS c d := by
    rintro c d ⟨rule, hrule, -⟩
    simp [emptyTRS] at hrule
  refine ⟨hno, ⟨fun _ => Acc.intro _ fun _ hd => absurd hd.2.2.choose_spec.2 (hno _ _)⟩,
    emptyTRS_sn⟩

end OperatorKO7.Methods.OrientationClosure.ControlCatalog
