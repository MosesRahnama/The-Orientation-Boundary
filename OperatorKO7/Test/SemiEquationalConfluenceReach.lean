import OperatorKO7.Meta.UniqueNormalization.SemiEquationalConfluence

/-!
# Reach and axiom check for semi-equational confluence

Pins every explicit public declaration of
`OperatorKO7/Meta/UniqueNormalization/SemiEquationalConfluence.lean`,
and the constructors of `CPar` and `CParList`, each with a paired axiom query.
Baseline axioms only.
-/

#check @OperatorKO7.Meta.UniqueNormalization.varOccurrences_var_eq
#print axioms OperatorKO7.Meta.UniqueNormalization.varOccurrences_var_eq
#check @OperatorKO7.Meta.UniqueNormalization.varOccurrences_app_eq
#print axioms OperatorKO7.Meta.UniqueNormalization.varOccurrences_app_eq
#check @OperatorKO7.Meta.UniqueNormalization.varOccurs_iff_mem_varOccurrences
#print axioms OperatorKO7.Meta.UniqueNormalization.varOccurs_iff_mem_varOccurrences
#check @OperatorKO7.Meta.UniqueNormalization.agree_on_occurs_of_apply_eq
#print axioms OperatorKO7.Meta.UniqueNormalization.agree_on_occurs_of_apply_eq
#check @OperatorKO7.Meta.UniqueNormalization.varOccurs_mapVar_inv
#print axioms OperatorKO7.Meta.UniqueNormalization.varOccurs_mapVar_inv
#check @OperatorKO7.Meta.UniqueNormalization.exists_level_of_cconv
#print axioms OperatorKO7.Meta.UniqueNormalization.exists_level_of_cconv
#check @OperatorKO7.Meta.UniqueNormalization.exists_level_of_conds
#print axioms OperatorKO7.Meta.UniqueNormalization.exists_level_of_conds
#check @OperatorKO7.Meta.UniqueNormalization.cstepE_cconv_of_cstep
#print axioms OperatorKO7.Meta.UniqueNormalization.cstepE_cconv_of_cstep
#check @OperatorKO7.Meta.UniqueNormalization.cstep_of_cstepE_cconv
#print axioms OperatorKO7.Meta.UniqueNormalization.cstep_of_cstepE_cconv
#check @OperatorKO7.Meta.UniqueNormalization.cstep_iff_cstepE_cconv
#print axioms OperatorKO7.Meta.UniqueNormalization.cstep_iff_cstepE_cconv
#check @OperatorKO7.Meta.UniqueNormalization.cconv_of_cstepEStar
#print axioms OperatorKO7.Meta.UniqueNormalization.cconv_of_cstepEStar
#check @OperatorKO7.Meta.UniqueNormalization.cstepEStar_arg
#print axioms OperatorKO7.Meta.UniqueNormalization.cstepEStar_arg
#check @OperatorKO7.Meta.UniqueNormalization.cstepEStar_args_append
#print axioms OperatorKO7.Meta.UniqueNormalization.cstepEStar_args_append
#check @OperatorKO7.Meta.UniqueNormalization.cstepEStar_apply_pointwise
#print axioms OperatorKO7.Meta.UniqueNormalization.cstepEStar_apply_pointwise
#check @OperatorKO7.Meta.UniqueNormalization.CPar
#print axioms OperatorKO7.Meta.UniqueNormalization.CPar
#check @OperatorKO7.Meta.UniqueNormalization.CPar.var
#print axioms OperatorKO7.Meta.UniqueNormalization.CPar.var
#check @OperatorKO7.Meta.UniqueNormalization.CPar.app
#print axioms OperatorKO7.Meta.UniqueNormalization.CPar.app
#check @OperatorKO7.Meta.UniqueNormalization.CPar.root
#print axioms OperatorKO7.Meta.UniqueNormalization.CPar.root
#check @OperatorKO7.Meta.UniqueNormalization.CParList
#print axioms OperatorKO7.Meta.UniqueNormalization.CParList
#check @OperatorKO7.Meta.UniqueNormalization.CParList.nil
#print axioms OperatorKO7.Meta.UniqueNormalization.CParList.nil
#check @OperatorKO7.Meta.UniqueNormalization.CParList.cons
#print axioms OperatorKO7.Meta.UniqueNormalization.CParList.cons
#check @OperatorKO7.Meta.UniqueNormalization.CPar.refl
#print axioms OperatorKO7.Meta.UniqueNormalization.CPar.refl
#check @OperatorKO7.Meta.UniqueNormalization.CParList.refl
#print axioms OperatorKO7.Meta.UniqueNormalization.CParList.refl
#check @OperatorKO7.Meta.UniqueNormalization.CParList.of_slot
#print axioms OperatorKO7.Meta.UniqueNormalization.CParList.of_slot
#check @OperatorKO7.Meta.UniqueNormalization.CParList.of_map
#print axioms OperatorKO7.Meta.UniqueNormalization.CParList.of_map
#check @OperatorKO7.Meta.UniqueNormalization.CPar.of_cstepE
#print axioms OperatorKO7.Meta.UniqueNormalization.CPar.of_cstepE
#check @OperatorKO7.Meta.UniqueNormalization.CPar.var_inv
#print axioms OperatorKO7.Meta.UniqueNormalization.CPar.var_inv
#check @OperatorKO7.Meta.UniqueNormalization.CPar.app_inv
#print axioms OperatorKO7.Meta.UniqueNormalization.CPar.app_inv
#check @OperatorKO7.Meta.UniqueNormalization.CParList.nil_inv
#print axioms OperatorKO7.Meta.UniqueNormalization.CParList.nil_inv
#check @OperatorKO7.Meta.UniqueNormalization.CParList.cons_inv
#print axioms OperatorKO7.Meta.UniqueNormalization.CParList.cons_inv
#check @OperatorKO7.Meta.UniqueNormalization.CPar.apply_pointwise
#print axioms OperatorKO7.Meta.UniqueNormalization.CPar.apply_pointwise
#check @OperatorKO7.Meta.UniqueNormalization.cstepEStar_of_cpar
#print axioms OperatorKO7.Meta.UniqueNormalization.cstepEStar_of_cpar
#check @OperatorKO7.Meta.UniqueNormalization.cstepEStar_of_cparStar
#print axioms OperatorKO7.Meta.UniqueNormalization.cstepEStar_of_cparStar
#check @OperatorKO7.Meta.UniqueNormalization.IsOracleRedex
#print axioms OperatorKO7.Meta.UniqueNormalization.IsOracleRedex
#check @OperatorKO7.Meta.UniqueNormalization.CLeftLinear
#print axioms OperatorKO7.Meta.UniqueNormalization.CLeftLinear
#check @OperatorKO7.Meta.UniqueNormalization.CVarCondition
#print axioms OperatorKO7.Meta.UniqueNormalization.CVarCondition
#check @OperatorKO7.Meta.UniqueNormalization.NoFeasibleOverlap
#print axioms OperatorKO7.Meta.UniqueNormalization.NoFeasibleOverlap
#check @OperatorKO7.Meta.UniqueNormalization.CNonOverlapping
#print axioms OperatorKO7.Meta.UniqueNormalization.CNonOverlapping
#check @OperatorKO7.Meta.UniqueNormalization.OracleStable
#print axioms OperatorKO7.Meta.UniqueNormalization.OracleStable
#check @OperatorKO7.Meta.UniqueNormalization.noFeasibleOverlap_of_nonOverlapping
#print axioms OperatorKO7.Meta.UniqueNormalization.noFeasibleOverlap_of_nonOverlapping
#check @OperatorKO7.Meta.UniqueNormalization.oracleStable_cconv
#print axioms OperatorKO7.Meta.UniqueNormalization.oracleStable_cconv
#check @OperatorKO7.Meta.UniqueNormalization.cLeftLinear_of_isMethodLinearization
#print axioms OperatorKO7.Meta.UniqueNormalization.cLeftLinear_of_isMethodLinearization
#check @OperatorKO7.Meta.UniqueNormalization.cVarCondition_of_isLinearization
#print axioms OperatorKO7.Meta.UniqueNormalization.cVarCondition_of_isLinearization
#check @OperatorKO7.Meta.UniqueNormalization.cparList_pattern_decompose
#print axioms OperatorKO7.Meta.UniqueNormalization.cparList_pattern_decompose
#check @OperatorKO7.Meta.UniqueNormalization.cpar_pattern_decompose
#print axioms OperatorKO7.Meta.UniqueNormalization.cpar_pattern_decompose
#check @OperatorKO7.Meta.UniqueNormalization.cparList_exists_target
#print axioms OperatorKO7.Meta.UniqueNormalization.cparList_exists_target
#check @OperatorKO7.Meta.UniqueNormalization.cpar_exists_target
#print axioms OperatorKO7.Meta.UniqueNormalization.cpar_exists_target
#check @OperatorKO7.Meta.UniqueNormalization.cstepE_relConfluent
#print axioms OperatorKO7.Meta.UniqueNormalization.cstepE_relConfluent
#check @OperatorKO7.Meta.UniqueNormalization.cconfluent_of_noFeasibleOverlap
#print axioms OperatorKO7.Meta.UniqueNormalization.cconfluent_of_noFeasibleOverlap
#check @OperatorKO7.Meta.UniqueNormalization.cconfluent_of_nonOverlapping
#print axioms OperatorKO7.Meta.UniqueNormalization.cconfluent_of_nonOverlapping
#check @OperatorKO7.Meta.UniqueNormalization.UNconv_of_linearization_noFeasibleOverlap
#print axioms OperatorKO7.Meta.UniqueNormalization.UNconv_of_linearization_noFeasibleOverlap
#check @OperatorKO7.Meta.UniqueNormalization.UNred_of_linearization_noFeasibleOverlap
#print axioms OperatorKO7.Meta.UniqueNormalization.UNred_of_linearization_noFeasibleOverlap
#check @OperatorKO7.Meta.UniqueNormalization.UNconv_of_linHub_noFeasibleOverlap
#print axioms OperatorKO7.Meta.UniqueNormalization.UNconv_of_linHub_noFeasibleOverlap
#check @OperatorKO7.Meta.UniqueNormalization.UNred_of_linHub_noFeasibleOverlap
#print axioms OperatorKO7.Meta.UniqueNormalization.UNred_of_linHub_noFeasibleOverlap
#check @OperatorKO7.Meta.UniqueNormalization.UNconv_of_linHub_nonOverlapping
#print axioms OperatorKO7.Meta.UniqueNormalization.UNconv_of_linHub_nonOverlapping
#check @OperatorKO7.Meta.UniqueNormalization.lhs_flat_of_linearizesRule
#print axioms OperatorKO7.Meta.UniqueNormalization.lhs_flat_of_linearizesRule
#check @OperatorKO7.Meta.UniqueNormalization.cNonOverlapping_of_flat
#print axioms OperatorKO7.Meta.UniqueNormalization.cNonOverlapping_of_flat
#check @OperatorKO7.Meta.UniqueNormalization.cNonOverlapping_linHub_of_flat
#print axioms OperatorKO7.Meta.UniqueNormalization.cNonOverlapping_linHub_of_flat
#check @OperatorKO7.Meta.UniqueNormalization.KlopSystem.linKlop
#print axioms OperatorKO7.Meta.UniqueNormalization.KlopSystem.linKlop
#check @OperatorKO7.Meta.UniqueNormalization.KlopSystem.isLin_klop
#print axioms OperatorKO7.Meta.UniqueNormalization.KlopSystem.isLin_klop
#check @OperatorKO7.Meta.UniqueNormalization.KlopSystem.linKlop_leftLinear
#print axioms OperatorKO7.Meta.UniqueNormalization.KlopSystem.linKlop_leftLinear
#check @OperatorKO7.Meta.UniqueNormalization.KlopSystem.linKlop_nonOverlapping
#print axioms OperatorKO7.Meta.UniqueNormalization.KlopSystem.linKlop_nonOverlapping
#check @OperatorKO7.Meta.UniqueNormalization.KlopSystem.trs_varCondition
#print axioms OperatorKO7.Meta.UniqueNormalization.KlopSystem.trs_varCondition
#check @OperatorKO7.Meta.UniqueNormalization.KlopSystem.linKlop_varCondition
#print axioms OperatorKO7.Meta.UniqueNormalization.KlopSystem.linKlop_varCondition
#check @OperatorKO7.Meta.UniqueNormalization.KlopSystem.linKlop_cconfluent
#print axioms OperatorKO7.Meta.UniqueNormalization.KlopSystem.linKlop_cconfluent
#check @OperatorKO7.Meta.UniqueNormalization.KlopSystem.trs_lhs_flat
#print axioms OperatorKO7.Meta.UniqueNormalization.KlopSystem.trs_lhs_flat
#check @OperatorKO7.Meta.UniqueNormalization.KlopSystem.trs_lhs_head_injective
#print axioms OperatorKO7.Meta.UniqueNormalization.KlopSystem.trs_lhs_head_injective
#check @OperatorKO7.Meta.UniqueNormalization.KlopSystem.linHub_trs_nonOverlapping
#print axioms OperatorKO7.Meta.UniqueNormalization.KlopSystem.linHub_trs_nonOverlapping
#check @OperatorKO7.Meta.UniqueNormalization.KlopSystem.linHub_trs_cconfluent
#print axioms OperatorKO7.Meta.UniqueNormalization.KlopSystem.linHub_trs_cconfluent
#check @OperatorKO7.Meta.UniqueNormalization.KlopSystem.UNconv_trs
#print axioms OperatorKO7.Meta.UniqueNormalization.KlopSystem.UNconv_trs
#check @OperatorKO7.Meta.UniqueNormalization.KlopSystem.UNconv_trs_and_not_confluent
#print axioms OperatorKO7.Meta.UniqueNormalization.KlopSystem.UNconv_trs_and_not_confluent
#check @OperatorKO7.Meta.UniqueNormalization.InfeasibleOverlap.trs
#print axioms OperatorKO7.Meta.UniqueNormalization.InfeasibleOverlap.trs
#check @OperatorKO7.Meta.UniqueNormalization.InfeasibleOverlap.lin
#print axioms OperatorKO7.Meta.UniqueNormalization.InfeasibleOverlap.lin
#check @OperatorKO7.Meta.UniqueNormalization.InfeasibleOverlap.isLin
#print axioms OperatorKO7.Meta.UniqueNormalization.InfeasibleOverlap.isLin
#check @OperatorKO7.Meta.UniqueNormalization.InfeasibleOverlap.trs_lhs_not_unifiable
#print axioms OperatorKO7.Meta.UniqueNormalization.InfeasibleOverlap.trs_lhs_not_unifiable
#check @OperatorKO7.Meta.UniqueNormalization.InfeasibleOverlap.lin_leftLinear
#print axioms OperatorKO7.Meta.UniqueNormalization.InfeasibleOverlap.lin_leftLinear
#check @OperatorKO7.Meta.UniqueNormalization.InfeasibleOverlap.lin_varCondition
#print axioms OperatorKO7.Meta.UniqueNormalization.InfeasibleOverlap.lin_varCondition
#check @OperatorKO7.Meta.UniqueNormalization.InfeasibleOverlap.lin_not_nonOverlapping
#print axioms OperatorKO7.Meta.UniqueNormalization.InfeasibleOverlap.lin_not_nonOverlapping
#check @OperatorKO7.Meta.UniqueNormalization.InfeasibleOverlap.subterm_cd_cases
#print axioms OperatorKO7.Meta.UniqueNormalization.InfeasibleOverlap.subterm_cd_cases
#check @OperatorKO7.Meta.UniqueNormalization.InfeasibleOverlap.no_cstep_c
#print axioms OperatorKO7.Meta.UniqueNormalization.InfeasibleOverlap.no_cstep_c
#check @OperatorKO7.Meta.UniqueNormalization.InfeasibleOverlap.not_cconv_c_d
#print axioms OperatorKO7.Meta.UniqueNormalization.InfeasibleOverlap.not_cconv_c_d
#check @OperatorKO7.Meta.UniqueNormalization.InfeasibleOverlap.lin_noFeasibleOverlap
#print axioms OperatorKO7.Meta.UniqueNormalization.InfeasibleOverlap.lin_noFeasibleOverlap
#check @OperatorKO7.Meta.UniqueNormalization.InfeasibleOverlap.lin_cconfluent
#print axioms OperatorKO7.Meta.UniqueNormalization.InfeasibleOverlap.lin_cconfluent
#check @OperatorKO7.Meta.UniqueNormalization.InfeasibleOverlap.UNconv_trs
#print axioms OperatorKO7.Meta.UniqueNormalization.InfeasibleOverlap.UNconv_trs
#check @OperatorKO7.Meta.UniqueNormalization.Controls.linHuet_leftLinear
#print axioms OperatorKO7.Meta.UniqueNormalization.Controls.linHuet_leftLinear
#check @OperatorKO7.Meta.UniqueNormalization.Controls.linHuet_varCondition
#print axioms OperatorKO7.Meta.UniqueNormalization.Controls.linHuet_varCondition
#check @OperatorKO7.Meta.UniqueNormalization.Controls.linHuet_feasibleOverlap
#print axioms OperatorKO7.Meta.UniqueNormalization.Controls.linHuet_feasibleOverlap
#check @OperatorKO7.Meta.UniqueNormalization.Controls.linKO7_leftLinear
#print axioms OperatorKO7.Meta.UniqueNormalization.Controls.linKO7_leftLinear
#check @OperatorKO7.Meta.UniqueNormalization.Controls.linKO7_varCondition
#print axioms OperatorKO7.Meta.UniqueNormalization.Controls.linKO7_varCondition
#check @OperatorKO7.Meta.UniqueNormalization.Controls.linKO7_feasibleOverlap
#print axioms OperatorKO7.Meta.UniqueNormalization.Controls.linKO7_feasibleOverlap

/-! ## Exercised statements -/

open OperatorKO7.Meta.UniqueNormalization in
/-- Klop's system has unique normal forms and is not confluent. -/
example : UNconv KlopSystem.trs ∧ ¬ confluent KlopSystem.trs :=
  KlopSystem.UNconv_trs_and_not_confluent

open OperatorKO7.Meta.UniqueNormalization in
/-- The theorem for hub linearizations applies at its own domain: Klop's system. -/
example : UNconv KlopSystem.trs :=
  UNconv_of_linHub_nonOverlapping KlopSystem.trs_varCondition
    KlopSystem.linHub_trs_nonOverlapping

open OperatorKO7.Meta.UniqueNormalization in
/-- A linearization with an overlap that never fires is confluent. -/
example : cconfluent InfeasibleOverlap.lin ∧ ¬ CNonOverlapping InfeasibleOverlap.lin :=
  ⟨InfeasibleOverlap.lin_cconfluent, InfeasibleOverlap.lin_not_nonOverlapping⟩

open OperatorKO7.Meta.UniqueNormalization in
/-- The hypothesis fails on Huet's linearization, whose system has no UN=. -/
example : ¬ NoFeasibleOverlap Controls.linHuet (cconv Controls.linHuet) :=
  Controls.linHuet_feasibleOverlap
