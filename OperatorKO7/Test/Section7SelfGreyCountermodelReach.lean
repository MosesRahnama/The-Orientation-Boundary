import OperatorKO7.Meta.UniqueNormalization.Section7SelfGreyCountermodel

set_option autoImplicit false

open OperatorKO7.Meta.Rewriting
open OperatorKO7.Meta.UniqueNormalization
open OperatorKO7.Meta.UniqueNormalization.Section7SelfGreyCountermodel

#check @T
#print axioms T
#check @p
#print axioms p
#check @q
#print axioms q
#check @d
#print axioms d
#check @c
#print axioms c
#check @dp
#print axioms dp
#check @dq
#print axioms dq
#check @cdp
#print axioms cdp
#check @cdq
#print axioms cdq
#check @rule
#print axioms rule
#check @rules
#print axioms rules
#check @terms
#print axioms terms
#check @terms_eq
#print axioms terms_eq
#check @terms_coalgebra
#print axioms terms_coalgebra
#check @terms_length
#print axioms terms_length
#check @terms_nodup
#print axioms terms_nodup
#check @mem_terms
#print axioms mem_terms
#check @p_ne_q
#print axioms p_ne_q
#check @cdp_ne_cdq
#print axioms cdp_ne_cdq
#check @rules_constructor
#print axioms rules_constructor
#check @rule_rhs_determined
#print axioms rule_rhs_determined
#check @rules_strong
#print axioms rules_strong
#check @root_d
#print axioms root_d
#check @rootStep_iff
#print axioms rootStep_iff
#check @rootStep_on_terms_iff
#print axioms rootStep_on_terms_iff
#check @parent
#print axioms parent
#check @parent_edge
#print axioms parent_edge
#check @parent_edge_iff
#print axioms parent_edge_iff
#check @parent_mem
#print axioms parent_mem
#check @rank
#print axioms rank
#check @parent_rank_decreases
#print axioms parent_rank_decreases
#check @parent_terminating
#print axioms parent_terminating
#check @parent_of_root
#print axioms parent_of_root
#check @rootSteps_represented
#print axioms rootSteps_represented
#check @eqv_dp_dq
#print axioms eqv_dp_dq
#check @eqv_cdp_cdq
#print axioms eqv_cdp_cdq
#check @hat_cdp_cdq
#print axioms hat_cdp_cdq
#check @parent_grey
#print axioms parent_grey
#check @SameVars
#print axioms SameVars
#check @vars_d
#print axioms vars_d
#check @vars_c
#print axioms vars_c
#check @rootStep_preserves_vars
#print axioms rootStep_preserves_vars
#check @forall₂_varsList_eq
#print axioms forall₂_varsList_eq
#check @sameVars_app
#print axioms sameVars_app
#check @sameVars_closed
#print axioms sameVars_closed
#check @downOn_preserves_vars
#print axioms downOn_preserves_vars
#check @vars_cdp
#print axioms vars_cdp
#check @vars_cdq
#print axioms vars_cdq
#check @vars_cdp_ne_cdq
#print axioms vars_cdp_ne_cdq
#check @not_down_cdp_cdq
#print axioms not_down_cdp_cdq
#check @not_down_dp_dq
#print axioms not_down_dp_dq
#check @no_proofGraph_same_parent
#print axioms no_proofGraph_same_parent
#check @selfGrey_countermodel
#print axioms selfGrey_countermodel
#check @not_selfGrey_strong_terminating_soundness
#print axioms not_selfGrey_strong_terminating_soundness
#check @reflexiveSeed
#print axioms reflexiveSeed
#check @reflexiveSeed_sound
#print axioms reflexiveSeed_sound
#check @constructor_support_self_cycle
#print axioms constructor_support_self_cycle
#check @reflexiveSeed_support_not_wellFounded
#print axioms reflexiveSeed_support_not_wellFounded
#check @no_sound_support_certificate
#print axioms no_sound_support_certificate

example : parent p = none ∧ parent q = none ∧
    parent dp = some cdp ∧ parent dq = some cdq ∧
    parent cdp = some cdq ∧ parent cdq = none := by decide

example : rootStep rules dp cdp ∧ rootStep rules dq cdq ∧
    ¬ rootStep rules cdp cdq := by
  refine ⟨root_d p, root_d q, ?_⟩
  intro h
  obtain ⟨t, ht, _⟩ := (rootStep_iff cdp cdq).mp h
  cases (Term.app.inj ht).1

example : parent cdp = some cdq ∧ Grey terms rules (EqvOn terms parent) cdp cdq ∧
    ¬ DownOn terms rules cdp cdq :=
  ⟨by decide, parent_grey (by decide), not_down_cdp_cdq⟩

example : Term.vars cdp = {false} ∧ Term.vars cdq = {true} ∧
    Term.vars cdp ≠ Term.vars cdq :=
  ⟨vars_cdp, vars_cdq, vars_cdp_ne_cdq⟩

example : EqvOn terms parent cdp cdq ∧
    ∀ A : List T, ¬ DownOn A rules cdp cdq :=
  ⟨eqv_cdp_cdq, fun _ h => vars_cdp_ne_cdq (downOn_preserves_vars h)⟩

example : ¬ ∃ rho : PGraph terms rules, rho.par = parent :=
  no_proofGraph_same_parent

example : ConstructorSupportDependency terms parent reflexiveSeed (cdp, cdq) (cdp, cdq) ∧
    ¬ WellFounded (ConstructorSupportDependency terms parent reflexiveSeed) :=
  ⟨constructor_support_self_cycle, reflexiveSeed_support_not_wellFounded⟩

example : ¬ ∃ seed : CRel Unit Bool,
    (∀ {x y}, seed x y → DownOn terms rules x y) ∧
    WellFounded (ConstructorSupportDependency terms parent seed) :=
  no_sound_support_certificate
