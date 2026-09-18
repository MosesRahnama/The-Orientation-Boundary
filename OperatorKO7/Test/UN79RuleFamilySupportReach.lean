import OperatorKO7.Meta.UniqueNormalization.RuleFamilySupport
import Mathlib.Data.Set.Finite.Basic

/-!
# Rule-family finite-support checks
-/

#check @OperatorKO7.Meta.UniqueNormalization.RuleFamily
#print axioms OperatorKO7.Meta.UniqueNormalization.RuleFamily
#check @OperatorKO7.Meta.UniqueNormalization.RuleFamily.ofList
#print axioms OperatorKO7.Meta.UniqueNormalization.RuleFamily.ofList
#check @OperatorKO7.Meta.UniqueNormalization.RuleFamily.FinitePart
#print axioms OperatorKO7.Meta.UniqueNormalization.RuleFamily.FinitePart
#check @OperatorKO7.Meta.UniqueNormalization.RuleFamily.rootStep
#print axioms OperatorKO7.Meta.UniqueNormalization.RuleFamily.rootStep
#check @OperatorKO7.Meta.UniqueNormalization.RuleFamily.Step
#print axioms OperatorKO7.Meta.UniqueNormalization.RuleFamily.Step
#check @OperatorKO7.Meta.UniqueNormalization.RuleFamily.Step.root
#print axioms OperatorKO7.Meta.UniqueNormalization.RuleFamily.Step.root
#check @OperatorKO7.Meta.UniqueNormalization.RuleFamily.Step.arg
#print axioms OperatorKO7.Meta.UniqueNormalization.RuleFamily.Step.arg
#check @OperatorKO7.Meta.UniqueNormalization.RuleFamily.Conv
#print axioms OperatorKO7.Meta.UniqueNormalization.RuleFamily.Conv
#check @OperatorKO7.Meta.UniqueNormalization.RuleFamily.NormalForm
#print axioms OperatorKO7.Meta.UniqueNormalization.RuleFamily.NormalForm
#check @OperatorKO7.Meta.UniqueNormalization.RuleFamily.UNconv
#print axioms OperatorKO7.Meta.UniqueNormalization.RuleFamily.UNconv
#check @OperatorKO7.Meta.UniqueNormalization.RuleFamily.rootStep_ofList_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.RuleFamily.rootStep_ofList_iff
#check @OperatorKO7.Meta.UniqueNormalization.RuleFamily.step_of_finite
#print axioms OperatorKO7.Meta.UniqueNormalization.RuleFamily.step_of_finite
#check @OperatorKO7.Meta.UniqueNormalization.RuleFamily.step_ofList_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.RuleFamily.step_ofList_iff
#check @OperatorKO7.Meta.UniqueNormalization.RuleFamily.step_mono
#print axioms OperatorKO7.Meta.UniqueNormalization.RuleFamily.step_mono
#check @OperatorKO7.Meta.UniqueNormalization.RuleFamily.finite_step_mono
#print axioms OperatorKO7.Meta.UniqueNormalization.RuleFamily.finite_step_mono
#check @OperatorKO7.Meta.UniqueNormalization.RuleFamily.step_singleton
#print axioms OperatorKO7.Meta.UniqueNormalization.RuleFamily.step_singleton
#check @OperatorKO7.Meta.UniqueNormalization.RuleFamily.step_iff_singleton
#print axioms OperatorKO7.Meta.UniqueNormalization.RuleFamily.step_iff_singleton
#check @OperatorKO7.Meta.UniqueNormalization.RuleFamily.conv_of_finite
#print axioms OperatorKO7.Meta.UniqueNormalization.RuleFamily.conv_of_finite
#check @OperatorKO7.Meta.UniqueNormalization.RuleFamily.conv_ofList_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.RuleFamily.conv_ofList_iff
#check @OperatorKO7.Meta.UniqueNormalization.RuleFamily.conv_mono
#print axioms OperatorKO7.Meta.UniqueNormalization.RuleFamily.conv_mono
#check @OperatorKO7.Meta.UniqueNormalization.RuleFamily.finite_conv_mono
#print axioms OperatorKO7.Meta.UniqueNormalization.RuleFamily.finite_conv_mono
#check @OperatorKO7.Meta.UniqueNormalization.RuleFamily.conv_exists_finite
#print axioms OperatorKO7.Meta.UniqueNormalization.RuleFamily.conv_exists_finite
#check @OperatorKO7.Meta.UniqueNormalization.RuleFamily.conv_iff_finite
#print axioms OperatorKO7.Meta.UniqueNormalization.RuleFamily.conv_iff_finite
#check @OperatorKO7.Meta.UniqueNormalization.RuleFamily.normal_ofList_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.RuleFamily.normal_ofList_iff
#check @OperatorKO7.Meta.UniqueNormalization.RuleFamily.normal_finite
#print axioms OperatorKO7.Meta.UniqueNormalization.RuleFamily.normal_finite
#check @OperatorKO7.Meta.UniqueNormalization.RuleFamily.normal_iff_finite
#print axioms OperatorKO7.Meta.UniqueNormalization.RuleFamily.normal_iff_finite
#check @OperatorKO7.Meta.UniqueNormalization.RuleFamily.un_ofList_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.RuleFamily.un_ofList_iff
#check @OperatorKO7.Meta.UniqueNormalization.RuleFamily.un_of_finite_parts
#print axioms OperatorKO7.Meta.UniqueNormalization.RuleFamily.un_of_finite_parts
#check @OperatorKO7.Meta.UniqueNormalization.RuleFamily.not_un_iff_finite_witness
#print axioms OperatorKO7.Meta.UniqueNormalization.RuleFamily.not_un_iff_finite_witness
#check @OperatorKO7.Meta.UniqueNormalization.RuleFamily.NonOmegaOverlapping
#print axioms OperatorKO7.Meta.UniqueNormalization.RuleFamily.NonOmegaOverlapping
#check @OperatorKO7.Meta.UniqueNormalization.RuleFamily.RhsDetermined
#print axioms OperatorKO7.Meta.UniqueNormalization.RuleFamily.RhsDetermined
#check @OperatorKO7.Meta.UniqueNormalization.RuleFamily.nonOmega_ofList_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.RuleFamily.nonOmega_ofList_iff
#check @OperatorKO7.Meta.UniqueNormalization.RuleFamily.rhsDetermined_ofList_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.RuleFamily.rhsDetermined_ofList_iff
#check @OperatorKO7.Meta.UniqueNormalization.RuleFamily.nonOmega_finite
#print axioms OperatorKO7.Meta.UniqueNormalization.RuleFamily.nonOmega_finite
#check @OperatorKO7.Meta.UniqueNormalization.RuleFamily.rhsDetermined_finite
#print axioms OperatorKO7.Meta.UniqueNormalization.RuleFamily.rhsDetermined_finite
#check @OperatorKO7.Meta.UniqueNormalization.RuleFamily.finite_un_theorem_iff_rule_families
#print axioms OperatorKO7.Meta.UniqueNormalization.RuleFamily.finite_un_theorem_iff_rule_families

open OperatorKO7.Meta.Rewriting OperatorKO7.Meta.UniqueNormalization

/-- With no rules, conversion is equality on the actual term carrier. -/
example {sigma nu : Type} (s t : Term sigma nu) :
    RuleFamily.Conv (fun _ => False) s t ↔ s = t := by
  constructor
  · intro h
    induction h with
    | refl => rfl
    | tail _ hlast _ =>
        rcases hlast with hstep | hstep
        all_goals
          obtain ⟨_, hfalse, _⟩ := RuleFamily.step_singleton hstep
          exact hfalse.elim
  · intro h
    subst t
    exact Relation.ReflTransGen.refl

/-- No decidable equality or nonempty variable carrier is required. -/
example {sigma nu : Type} :
    RuleFamily.UNconv (fun _ : Rule sigma nu => False) := by
  apply RuleFamily.un_of_finite_parts
  intro R hR s t _ _ h
  have hnil : R = [] := by
    cases R with
    | nil => rfl
    | cons r rs => exact (hR r (List.mem_cons_self)).elim
  subst R
  have noStep : ∀ x y, ¬ Step ([] : TRS sigma nu) x y := by
    intro x y hstep
    have h := RuleFamily.step_of_finite
      (P := fun _ : Rule sigma nu => False) (by intro r hr; cases hr) hstep
    obtain ⟨_, hf, _⟩ := RuleFamily.step_singleton h
    exact hf
  induction h with
  | refl => rfl
  | tail _ hlast _ =>
      rcases hlast with hstep | hstep
      · exact (noStep _ _ hstep).elim
      · exact (noStep _ _ hstep).elim

namespace InfiniteRulesControl

def rule (n : Nat) : Rule Nat PUnit.{1} :=
  ⟨.app (n + 1) [], .app n [], rfl⟩

def rules : RuleFamily Nat PUnit.{1} := fun r => ∃ n, r = rule n

theorem rule_injective : Function.Injective rule := by
  intro n m h
  have hl := congrArg Rule.lhs h
  change Term.app (n + 1) [] = Term.app (m + 1) [] at hl
  exact Nat.add_right_cancel (Term.app.inj hl).1

theorem rules_infinite : Set.Infinite {r | rules r} := by
  apply Set.infinite_of_injective_forall_mem rule_injective
  intro n
  exact ⟨n, rfl⟩

theorem step (n : Nat) :
    RuleFamily.Step rules (.app (n + 1) []) (.app n []) :=
  RuleFamily.Step.root ⟨rule n, ⟨n, rfl⟩, (fun x => .var x), rfl, rfl⟩

/-- The rule-family relation rewrites at an actual non-root position. -/
example : RuleFamily.Step rules (.app 10 [.app 2 []]) (.app 10 [.app 1 []]) := by
  exact RuleFamily.Step.arg 10 [] [] (step 1)

/-- An infinite rule collection has a finite support for a two-step conversion. -/
example : ∃ R : TRS Nat PUnit.{1}, RuleFamily.FinitePart rules R ∧
    conv R (.app 3 []) (.app 1 []) := by
  apply RuleFamily.conv_exists_finite
  exact Relation.ReflTransGen.tail
    (Relation.ReflTransGen.single (Or.inl (step 2))) (Or.inl (step 1))

/-- Each variable is normal for this infinite collection, as for finite TRSs. -/
example : RuleFamily.NormalForm rules (.var PUnit.unit) := by
  intro t h
  obtain ⟨r, _, hstep⟩ := RuleFamily.step_singleton h
  exact Step.not_var hstep

end InfiniteRulesControl

#check @InfiniteRulesControl.rule
#print axioms InfiniteRulesControl.rule
#check @InfiniteRulesControl.rules
#print axioms InfiniteRulesControl.rules
#check @InfiniteRulesControl.rule_injective
#print axioms InfiniteRulesControl.rule_injective
#check @InfiniteRulesControl.rules_infinite
#print axioms InfiniteRulesControl.rules_infinite
#check @InfiniteRulesControl.step
#print axioms InfiniteRulesControl.step

/-- The finite source counterexample transfers with its failed RHS law intact. -/
example :
    RuleFamily.NonOmegaOverlapping (RuleFamily.ofList FreshRhs.trs) ∧
      ¬ RuleFamily.RhsDetermined (RuleFamily.ofList FreshRhs.trs) ∧
      ¬ RuleFamily.UNconv (RuleFamily.ofList FreshRhs.trs) := by
  have h := FreshRhs.variable_condition_necessary
  refine ⟨RuleFamily.nonOmega_ofList_iff.mpr h.1, ?_, ?_⟩
  · intro hv
    exact h.2.1 (RuleFamily.rhsDetermined_ofList_iff.mp hv)
  · intro hu
    exact h.2.2.1 (RuleFamily.un_ofList_iff.mp hu)
