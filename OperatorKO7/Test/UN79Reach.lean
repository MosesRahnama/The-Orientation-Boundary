import OperatorKO7.Meta.UniqueNormalization.Theorem69
import OperatorKO7.Meta.UniqueNormalization.Examples
import OperatorKO7.Meta.UniqueNormalization.CommonGeneralisation
import OperatorKO7.Meta.UniqueNormalization.ConstructorTranslation
import OperatorKO7.Meta.UniqueNormalization.RationalUnification
import OperatorKO7.Meta.UniqueNormalization.OverlapClasses
import OperatorKO7.Meta.UniqueNormalization.UNStatement
import OperatorKO7.Meta.UniqueNormalization.RewriteAux
import OperatorKO7.Meta.UniqueNormalization.TermMaps
import OperatorKO7.Meta.UniqueNormalization.Proposition22

/-!
# Reach test: the RTA open problem #79 campaign

Campaign: `KO7-LLM-Benchmark\Distinction_Boundary\Roadmaps\klop\ROADMAP.md`.

This file checks declaration names, prints their axioms and tests theorem types
on stated fixtures. Source freshness requires a separate dependency-build receipt.
-/

set_option autoImplicit false

namespace UN79Reach

open OperatorKO7.Meta.Rewriting
open OperatorKO7.Meta.UniqueNormalization

/-! ## Term maps and rewriting auxiliaries -/

#check @Term.mapSym
#check @Term.mapSymList
#check @Term.mapSym_var
#check @Term.mapSym_app
#check @Term.mapSymList_nil
#check @Term.mapSymList_cons
#check @Term.mapSymList_eq_map
#check @Term.mapSym_id
#check @Term.mapSym_mapSym
#check @Term.mapSubstSym
#check @Term.mapSym_apply
#check @Term.isApp_mapSym
#check @Term.mapVar
#check @Term.mapVarList
#check @Term.mapVar_var
#check @Term.mapVar_app
#check @Term.mapVarList_nil
#check @Term.mapVarList_cons
#check @Term.mapVarList_eq_map
#check @Term.apply_mapVar_of
#check @Term.mapVar_injective
#check @Step.subst
#check @StepStar.subst
#check @StepStar.args_append
#check @StepStar.args
#check @forall₂_map_map

#print axioms OperatorKO7.Meta.Rewriting.Term.mapSym
#print axioms OperatorKO7.Meta.Rewriting.Term.mapSymList
#print axioms OperatorKO7.Meta.Rewriting.Term.mapSym_var
#print axioms OperatorKO7.Meta.Rewriting.Term.mapSym_app
#print axioms OperatorKO7.Meta.Rewriting.Term.mapSymList_nil
#print axioms OperatorKO7.Meta.Rewriting.Term.mapSymList_cons
#print axioms OperatorKO7.Meta.Rewriting.Term.mapSymList_eq_map
#print axioms OperatorKO7.Meta.Rewriting.Term.mapSym_id
#print axioms OperatorKO7.Meta.Rewriting.Term.mapSym_mapSym
#print axioms OperatorKO7.Meta.Rewriting.Term.mapSubstSym
#print axioms OperatorKO7.Meta.Rewriting.Term.mapSym_apply
#print axioms OperatorKO7.Meta.Rewriting.Term.isApp_mapSym
#print axioms OperatorKO7.Meta.Rewriting.Term.mapVar
#print axioms OperatorKO7.Meta.Rewriting.Term.mapVarList
#print axioms OperatorKO7.Meta.Rewriting.Term.mapVar_var
#print axioms OperatorKO7.Meta.Rewriting.Term.mapVar_app
#print axioms OperatorKO7.Meta.Rewriting.Term.mapVarList_nil
#print axioms OperatorKO7.Meta.Rewriting.Term.mapVarList_cons
#print axioms OperatorKO7.Meta.Rewriting.Term.mapVarList_eq_map
#print axioms OperatorKO7.Meta.Rewriting.Term.apply_mapVar_of
#print axioms OperatorKO7.Meta.Rewriting.Term.mapVar_injective
#print axioms OperatorKO7.Meta.Rewriting.Step.subst
#print axioms OperatorKO7.Meta.Rewriting.StepStar.subst
#print axioms OperatorKO7.Meta.Rewriting.StepStar.args_append
#print axioms OperatorKO7.Meta.Rewriting.StepStar.args
#print axioms OperatorKO7.Meta.Rewriting.forall₂_map_map

/-! ## Statement layer -/

#check @convStep
#check @conv
#check @NormalForm
#check @UNconv
#check @UNred
#check @NFP
#check @confluent
#check @Consistent
#check @Step.app_inv
#check @Step.not_var
#check @convStep_symm
#check @conv.refl
#check @conv.single
#check @conv.of_step
#check @conv.trans
#check @conv.symm
#check @conv.of_stepStar
#check @conv.of_joinable
#check @conv.arg_congr
#check @NormalForm.eq_of_stepStar
#check @UNred_of_UNconv
#check @UNconv_of_NFP
#check @joinable_of_conv
#check @NFP_of_confluent
#check @UNconv_of_confluent
#check @Consistent_of_UNconv
#check @not_UNconv_of_not_Consistent
#check @NormalForm.var
#check @Example.no_rootStep_of_head_ne
#check @Example.const_normalForm
#check @Example.tgt_normalForm
#check @Example.demo_conv
#check @Example.demo_normalizes

#print axioms OperatorKO7.Meta.UniqueNormalization.Step.app_inv
#print axioms OperatorKO7.Meta.UniqueNormalization.Step.not_var
#print axioms OperatorKO7.Meta.UniqueNormalization.convStep
#print axioms OperatorKO7.Meta.UniqueNormalization.conv
#print axioms OperatorKO7.Meta.UniqueNormalization.convStep_symm
#print axioms OperatorKO7.Meta.UniqueNormalization.conv.refl
#print axioms OperatorKO7.Meta.UniqueNormalization.conv.single
#print axioms OperatorKO7.Meta.UniqueNormalization.conv.of_step
#print axioms OperatorKO7.Meta.UniqueNormalization.conv.trans
#print axioms OperatorKO7.Meta.UniqueNormalization.conv.symm
#print axioms OperatorKO7.Meta.UniqueNormalization.conv.of_stepStar
#print axioms OperatorKO7.Meta.UniqueNormalization.conv.of_joinable
#print axioms OperatorKO7.Meta.UniqueNormalization.conv.arg_congr
#print axioms OperatorKO7.Meta.UniqueNormalization.NormalForm
#print axioms OperatorKO7.Meta.UniqueNormalization.NormalForm.var
#print axioms OperatorKO7.Meta.UniqueNormalization.NormalForm.eq_of_stepStar
#print axioms OperatorKO7.Meta.UniqueNormalization.UNconv
#print axioms OperatorKO7.Meta.UniqueNormalization.UNred
#print axioms OperatorKO7.Meta.UniqueNormalization.NFP
#print axioms OperatorKO7.Meta.UniqueNormalization.confluent
#print axioms OperatorKO7.Meta.UniqueNormalization.Consistent
#print axioms OperatorKO7.Meta.UniqueNormalization.UNred_of_UNconv
#print axioms OperatorKO7.Meta.UniqueNormalization.UNconv_of_NFP
#print axioms OperatorKO7.Meta.UniqueNormalization.joinable_of_conv
#print axioms OperatorKO7.Meta.UniqueNormalization.NFP_of_confluent
#print axioms OperatorKO7.Meta.UniqueNormalization.UNconv_of_confluent
#print axioms OperatorKO7.Meta.UniqueNormalization.Consistent_of_UNconv
#print axioms OperatorKO7.Meta.UniqueNormalization.not_UNconv_of_not_Consistent
#print axioms OperatorKO7.Meta.UniqueNormalization.Example.no_rootStep_of_head_ne
#print axioms OperatorKO7.Meta.UniqueNormalization.Example.const_normalForm
#print axioms OperatorKO7.Meta.UniqueNormalization.Example.tgt_normalForm
#print axioms OperatorKO7.Meta.UniqueNormalization.Example.demo_conv
#print axioms OperatorKO7.Meta.UniqueNormalization.Example.demo_normalizes

/-! ## Omega-unification -/

#check @UnifClosure
#check @OmegaUnifiableShared
#check @OmegaUnifiable
#check @leftCopy
#check @rightCopy
#check @classesRel
#check @UnifClosure.symbol_eq
#check @UnifClosure.args_forall₂
#check @omegaUnifiableShared_of_subst
#check @omegaUnifiable_of_unifier
#check @unifClosure_classesRel
#check @forall₂_classesRel_refl
#check @UnifClosure.mk
#check @UnifClosure.rfl'
#check @UnifClosure.symm'
#check @UnifClosure.trans'
#check @UnifClosure.decomp
#check @infTermP
#check @InfTerm
#check @InfTerm.var
#check @InfTerm.app
#check @InfTerm.dest_var
#check @InfTerm.dest_app
#check @InfTerm.app_inj
#check @InfSubst
#check @InfApply
#check @InfiniteOmegaUnifiableShared
#check @InfiniteOmegaUnifiable
#check @omegaUnifiableShared_of_infiniteSubst
#check @omegaUnifiableShared_of_infinite
#check @omegaUnifiable_of_infinite
#check @unifSetoid
#check @UClass
#check @QAppRep
#check @QAppRep.mk
#check @QAppRep.head
#check @QAppRep.args
#check @QAppRep.class_eq
#check @chooseQAppRep
#check @closureViewQ
#check @unfoldQ
#check @unfoldQ_eq_of_rel
#check @closureViewQ_app
#check @unfoldQ_app
#check @infApply_unfoldQ
#check @infinite_of_omegaUnifiableShared
#check @omegaUnifiableShared_iff_infinite
#check @omegaUnifiable_iff_infinite
#check @OccursCheck.xTm
#check @OccursCheck.fxTm
#check @OccursCheck.cert
#check @OccursCheck.cert_closure
#check @OccursCheck.omegaUnifiableShared
#check @OccursCheck.infiniteOmegaUnifiableShared
#check @OccursCheck.not_unifiable
#check @Huet.lhs₁
#check @Huet.lhs₂
#check @Huet.L
#check @Huet.Rt
#check @Huet.lowClass
#check @Huet.cert
#check @Huet.L_eq
#check @Huet.Rt_eq
#check @Huet.low_rel
#check @Huet.cert_closure
#check @Huet.lhs_omegaUnifiable
#check @Huet.lhs_infiniteOmegaUnifiable
#check @Huet.lhs_not_unifiable

#print axioms OperatorKO7.Meta.UniqueNormalization.UnifClosure
#print axioms OperatorKO7.Meta.UniqueNormalization.UnifClosure.mk
#print axioms OperatorKO7.Meta.UniqueNormalization.UnifClosure.rfl'
#print axioms OperatorKO7.Meta.UniqueNormalization.UnifClosure.symm'
#print axioms OperatorKO7.Meta.UniqueNormalization.UnifClosure.trans'
#print axioms OperatorKO7.Meta.UniqueNormalization.UnifClosure.decomp
#print axioms OperatorKO7.Meta.UniqueNormalization.OmegaUnifiableShared
#print axioms OperatorKO7.Meta.UniqueNormalization.leftCopy
#print axioms OperatorKO7.Meta.UniqueNormalization.rightCopy
#print axioms OperatorKO7.Meta.UniqueNormalization.OmegaUnifiable
#print axioms OperatorKO7.Meta.UniqueNormalization.infTermP
#print axioms OperatorKO7.Meta.UniqueNormalization.InfTerm.var
#print axioms OperatorKO7.Meta.UniqueNormalization.InfTerm.app
#print axioms OperatorKO7.Meta.UniqueNormalization.InfTerm.dest_var
#print axioms OperatorKO7.Meta.UniqueNormalization.InfTerm.dest_app
#print axioms OperatorKO7.Meta.UniqueNormalization.InfTerm.app_inj
#print axioms OperatorKO7.Meta.UniqueNormalization.InfApply
#print axioms OperatorKO7.Meta.UniqueNormalization.InfiniteOmegaUnifiableShared
#print axioms OperatorKO7.Meta.UniqueNormalization.InfiniteOmegaUnifiable
#print axioms OperatorKO7.Meta.UniqueNormalization.omegaUnifiableShared_of_infiniteSubst
#print axioms OperatorKO7.Meta.UniqueNormalization.omegaUnifiableShared_of_infinite
#print axioms OperatorKO7.Meta.UniqueNormalization.omegaUnifiable_of_infinite
#print axioms OperatorKO7.Meta.UniqueNormalization.unifSetoid
#print axioms OperatorKO7.Meta.UniqueNormalization.QAppRep
#print axioms OperatorKO7.Meta.UniqueNormalization.QAppRep.mk
#print axioms OperatorKO7.Meta.UniqueNormalization.QAppRep.head
#print axioms OperatorKO7.Meta.UniqueNormalization.QAppRep.args
#print axioms OperatorKO7.Meta.UniqueNormalization.QAppRep.class_eq
#print axioms OperatorKO7.Meta.UniqueNormalization.chooseQAppRep
#print axioms OperatorKO7.Meta.UniqueNormalization.closureViewQ
#print axioms OperatorKO7.Meta.UniqueNormalization.unfoldQ
#print axioms OperatorKO7.Meta.UniqueNormalization.unfoldQ_eq_of_rel
#print axioms OperatorKO7.Meta.UniqueNormalization.closureViewQ_app
#print axioms OperatorKO7.Meta.UniqueNormalization.unfoldQ_app
#print axioms OperatorKO7.Meta.UniqueNormalization.infApply_unfoldQ
#print axioms OperatorKO7.Meta.UniqueNormalization.infinite_of_omegaUnifiableShared
#print axioms OperatorKO7.Meta.UniqueNormalization.omegaUnifiableShared_iff_infinite
#print axioms OperatorKO7.Meta.UniqueNormalization.omegaUnifiable_iff_infinite
#print axioms OperatorKO7.Meta.UniqueNormalization.UnifClosure.symbol_eq
#print axioms OperatorKO7.Meta.UniqueNormalization.UnifClosure.args_forall₂
#print axioms OperatorKO7.Meta.UniqueNormalization.forall₂_of_map_eq
#print axioms OperatorKO7.Meta.UniqueNormalization.omegaUnifiableShared_of_subst
#print axioms OperatorKO7.Meta.UniqueNormalization.omegaUnifiable_of_unifier
#print axioms OperatorKO7.Meta.UniqueNormalization.classesRel
#print axioms OperatorKO7.Meta.UniqueNormalization.forall₂_classesRel_refl
#print axioms OperatorKO7.Meta.UniqueNormalization.unifClosure_classesRel
#print axioms OperatorKO7.Meta.UniqueNormalization.OccursCheck.xTm
#print axioms OperatorKO7.Meta.UniqueNormalization.OccursCheck.fxTm
#print axioms OperatorKO7.Meta.UniqueNormalization.OccursCheck.cert
#print axioms OperatorKO7.Meta.UniqueNormalization.OccursCheck.cert_closure
#print axioms OperatorKO7.Meta.UniqueNormalization.OccursCheck.omegaUnifiableShared
#print axioms OperatorKO7.Meta.UniqueNormalization.OccursCheck.infiniteOmegaUnifiableShared
#print axioms OperatorKO7.Meta.UniqueNormalization.OccursCheck.not_unifiable
#print axioms OperatorKO7.Meta.UniqueNormalization.Huet.lhs₁
#print axioms OperatorKO7.Meta.UniqueNormalization.Huet.lhs₂
#print axioms OperatorKO7.Meta.UniqueNormalization.Huet.L
#print axioms OperatorKO7.Meta.UniqueNormalization.Huet.Rt
#print axioms OperatorKO7.Meta.UniqueNormalization.Huet.lowClass
#print axioms OperatorKO7.Meta.UniqueNormalization.Huet.cert
#print axioms OperatorKO7.Meta.UniqueNormalization.Huet.L_eq
#print axioms OperatorKO7.Meta.UniqueNormalization.Huet.Rt_eq
#print axioms OperatorKO7.Meta.UniqueNormalization.Huet.low_rel
#print axioms OperatorKO7.Meta.UniqueNormalization.Huet.cert_closure
#print axioms OperatorKO7.Meta.UniqueNormalization.Huet.lhs_omegaUnifiable
#print axioms OperatorKO7.Meta.UniqueNormalization.Huet.lhs_infiniteOmegaUnifiable
#print axioms OperatorKO7.Meta.UniqueNormalization.Huet.lhs_not_unifiable

/-! ## Overlap classes -/

#check @Unifiable
#check @Subterm
#check @Subterm.refl
#check @Subterm.arg
#check @ProperSubterm
#check @Subterm.of_properSubterm
#check @Subterm.eq_of_var
#check @NonOverlapping
#check @NonOmegaOverlapping
#check @Deterministic
#check @AlmostNonOmegaOverlapping
#check @ConstructorNonOverlapping
#check @ConstructorNonOmegaOverlapping
#check @OmegaUnifiable.of_unifiable
#check @Subterm.size_le
#check @ProperSubterm.size_lt
#check @Subterm.eq_or_properSubterm
#check @NonOverlapping.of_nonOmegaOverlapping
#check @ConstructorNonOverlapping.of_nonOmegaOverlapping
#check @properSubterm_clause_of_nonOmegaOverlapping

#print axioms OperatorKO7.Meta.UniqueNormalization.Unifiable
#print axioms OperatorKO7.Meta.UniqueNormalization.OmegaUnifiable.of_unifiable
#print axioms OperatorKO7.Meta.UniqueNormalization.Subterm
#print axioms OperatorKO7.Meta.UniqueNormalization.Subterm.refl
#print axioms OperatorKO7.Meta.UniqueNormalization.Subterm.arg
#print axioms OperatorKO7.Meta.UniqueNormalization.ProperSubterm
#print axioms OperatorKO7.Meta.UniqueNormalization.Subterm.of_properSubterm
#print axioms OperatorKO7.Meta.UniqueNormalization.Subterm.eq_of_var
#print axioms OperatorKO7.Meta.UniqueNormalization.Subterm.size_le
#print axioms OperatorKO7.Meta.UniqueNormalization.ProperSubterm.size_lt
#print axioms OperatorKO7.Meta.UniqueNormalization.Subterm.eq_or_properSubterm
#print axioms OperatorKO7.Meta.UniqueNormalization.NonOverlapping
#print axioms OperatorKO7.Meta.UniqueNormalization.NonOmegaOverlapping
#print axioms OperatorKO7.Meta.UniqueNormalization.Deterministic
#print axioms OperatorKO7.Meta.UniqueNormalization.AlmostNonOmegaOverlapping
#print axioms OperatorKO7.Meta.UniqueNormalization.ConstructorNonOverlapping
#print axioms OperatorKO7.Meta.UniqueNormalization.ConstructorNonOmegaOverlapping
#print axioms OperatorKO7.Meta.UniqueNormalization.NonOverlapping.of_nonOmegaOverlapping
#print axioms OperatorKO7.Meta.UniqueNormalization.ConstructorNonOverlapping.of_nonOmegaOverlapping
#print axioms OperatorKO7.Meta.UniqueNormalization.properSubterm_clause_of_nonOmegaOverlapping

/-! ## Common generalisation and Proposition 21 -/

#check @Term.DeterminedBy
#check @Rule.RhsDetermined
#check @TRS.RhsDetermined
#check @CommonGeneralisation
#check @CommonGeneralisation.mk
#check @CommonGeneralisation.gl
#check @CommonGeneralisation.gr
#check @CommonGeneralisation.s₁
#check @CommonGeneralisation.s₂
#check @CommonGeneralisation.apply_gl₁
#check @CommonGeneralisation.apply_gl₂
#check @CommonGeneralisation.apply_gr₁
#check @CommonGeneralisation.apply_gr₂
#check @CommonGeneralisation.determined
#check @CommonGeneralisation.self
#check @apply_eq_of_agree
#check @agree_of_apply_eq
#check @Term.determinedBy_of_vars_subset
#check @Term.vars_subset_of_determinedBy
#check @Term.determinedBy_iff_vars_subset
#check @Rule.rhsDetermined_iff_vars_subset
#check @TRS.rhsDetermined_iff_vars_subset
#check @rootStep_eq_of_commonGeneralisation
#check @Deterministic.of_nonOmegaOverlapping
#check @AlmostNonOmegaOverlapping.of_nonOmegaOverlapping
#check @FreshRhs.rule
#check @FreshRhs.trs
#check @FreshRhs.subterm_app_eq
#check @FreshRhs.nonOmegaOverlapping
#check @FreshRhs.sub
#check @FreshRhs.step_to_var
#check @FreshRhs.not_consistent
#check @FreshRhs.not_UNconv
#check @FreshRhs.not_rhsDetermined
#check @FreshRhs.variable_condition_necessary

#print axioms OperatorKO7.Meta.UniqueNormalization.apply_eq_of_agree
#print axioms OperatorKO7.Meta.UniqueNormalization.agree_of_apply_eq
#print axioms OperatorKO7.Meta.UniqueNormalization.Term.DeterminedBy
#print axioms OperatorKO7.Meta.UniqueNormalization.Term.determinedBy_of_vars_subset
#print axioms OperatorKO7.Meta.UniqueNormalization.Term.vars_subset_of_determinedBy
#print axioms OperatorKO7.Meta.UniqueNormalization.Term.determinedBy_iff_vars_subset
#print axioms OperatorKO7.Meta.UniqueNormalization.Rule.RhsDetermined
#print axioms OperatorKO7.Meta.UniqueNormalization.Rule.rhsDetermined_iff_vars_subset
#print axioms OperatorKO7.Meta.UniqueNormalization.TRS.RhsDetermined
#print axioms OperatorKO7.Meta.UniqueNormalization.TRS.rhsDetermined_iff_vars_subset
#print axioms OperatorKO7.Meta.UniqueNormalization.CommonGeneralisation
#print axioms OperatorKO7.Meta.UniqueNormalization.CommonGeneralisation.mk
#print axioms OperatorKO7.Meta.UniqueNormalization.CommonGeneralisation.gl
#print axioms OperatorKO7.Meta.UniqueNormalization.CommonGeneralisation.gr
#print axioms OperatorKO7.Meta.UniqueNormalization.CommonGeneralisation.s₁
#print axioms OperatorKO7.Meta.UniqueNormalization.CommonGeneralisation.s₂
#print axioms OperatorKO7.Meta.UniqueNormalization.CommonGeneralisation.apply_gl₁
#print axioms OperatorKO7.Meta.UniqueNormalization.CommonGeneralisation.apply_gl₂
#print axioms OperatorKO7.Meta.UniqueNormalization.CommonGeneralisation.apply_gr₁
#print axioms OperatorKO7.Meta.UniqueNormalization.CommonGeneralisation.apply_gr₂
#print axioms OperatorKO7.Meta.UniqueNormalization.CommonGeneralisation.determined
#print axioms OperatorKO7.Meta.UniqueNormalization.CommonGeneralisation.self
#print axioms OperatorKO7.Meta.UniqueNormalization.rootStep_eq_of_commonGeneralisation
#print axioms OperatorKO7.Meta.UniqueNormalization.Deterministic.of_nonOmegaOverlapping
#print axioms OperatorKO7.Meta.UniqueNormalization.AlmostNonOmegaOverlapping.of_nonOmegaOverlapping
#print axioms OperatorKO7.Meta.UniqueNormalization.FreshRhs.rule
#print axioms OperatorKO7.Meta.UniqueNormalization.FreshRhs.trs
#print axioms OperatorKO7.Meta.UniqueNormalization.FreshRhs.subterm_app_eq
#print axioms OperatorKO7.Meta.UniqueNormalization.FreshRhs.nonOmegaOverlapping
#print axioms OperatorKO7.Meta.UniqueNormalization.FreshRhs.sub
#print axioms OperatorKO7.Meta.UniqueNormalization.FreshRhs.step_to_var
#print axioms OperatorKO7.Meta.UniqueNormalization.FreshRhs.not_consistent
#print axioms OperatorKO7.Meta.UniqueNormalization.FreshRhs.not_UNconv
#print axioms OperatorKO7.Meta.UniqueNormalization.FreshRhs.not_rhsDetermined
#print axioms OperatorKO7.Meta.UniqueNormalization.FreshRhs.variable_condition_necessary

/-! ## Constructor translation -/

#check @gammaSym
#check @constructorLabel
#check @destructorLabel
#check @eraseLabel
#check @constructorLabel_app
#check @destructorLabel_app
#check @constructorLabel_var
#check @destructorLabel_var
#check @eraseLabel_constructorLabel
#check @eraseLabel_destructorLabel
#check @eraseLabelList_constructorLabelList
#check @constructorLabel_apply
#check @destructorLabel_apply
#check @eraseLabel_apply
#check @destructorPattern
#check @destructorPattern_app
#check @destructorPattern_isApp
#check @eraseLabel_destructorPattern
#check @appNodes
#check @appNodesList
#check @appNodes_var
#check @appNodes_app
#check @appNodesList_nil
#check @appNodesList_cons
#check @mem_appNodesList_of_mem
#check @properAppNodes
#check @properAppNodes_app
#check @patternNodes
#check @mem_patternNodes
#check @transRule
#check @patternRuleOf
#check @constructorTranslation
#check @transRule_mem
#check @patternRuleOf_mem
#check @mem_constructorTranslation
#check @lemma13
#check @appNodes_subset_patternNodes
#check @lemma14_forward_strict
#check @lemma14_forward
#check @lemma14_back
#check @prop15_forward
#check @prop15_back
#check @cor16

#print axioms OperatorKO7.Meta.UniqueNormalization.gammaSym
#print axioms OperatorKO7.Meta.UniqueNormalization.constructorLabel
#print axioms OperatorKO7.Meta.UniqueNormalization.destructorLabel
#print axioms OperatorKO7.Meta.UniqueNormalization.eraseLabel
#print axioms OperatorKO7.Meta.UniqueNormalization.constructorLabel_app
#print axioms OperatorKO7.Meta.UniqueNormalization.destructorLabel_app
#print axioms OperatorKO7.Meta.UniqueNormalization.constructorLabel_var
#print axioms OperatorKO7.Meta.UniqueNormalization.destructorLabel_var
#print axioms OperatorKO7.Meta.UniqueNormalization.eraseLabel_constructorLabel
#print axioms OperatorKO7.Meta.UniqueNormalization.eraseLabel_destructorLabel
#print axioms OperatorKO7.Meta.UniqueNormalization.eraseLabelList_constructorLabelList
#print axioms OperatorKO7.Meta.UniqueNormalization.constructorLabel_apply
#print axioms OperatorKO7.Meta.UniqueNormalization.destructorLabel_apply
#print axioms OperatorKO7.Meta.UniqueNormalization.eraseLabel_apply
#print axioms OperatorKO7.Meta.UniqueNormalization.destructorPattern
#print axioms OperatorKO7.Meta.UniqueNormalization.destructorPattern_app
#print axioms OperatorKO7.Meta.UniqueNormalization.destructorPattern_isApp
#print axioms OperatorKO7.Meta.UniqueNormalization.eraseLabel_destructorPattern
#print axioms OperatorKO7.Meta.UniqueNormalization.appNodes
#print axioms OperatorKO7.Meta.UniqueNormalization.appNodesList
#print axioms OperatorKO7.Meta.UniqueNormalization.appNodes_var
#print axioms OperatorKO7.Meta.UniqueNormalization.appNodes_app
#print axioms OperatorKO7.Meta.UniqueNormalization.appNodesList_nil
#print axioms OperatorKO7.Meta.UniqueNormalization.appNodesList_cons
#print axioms OperatorKO7.Meta.UniqueNormalization.mem_appNodesList_of_mem
#print axioms OperatorKO7.Meta.UniqueNormalization.properAppNodes
#print axioms OperatorKO7.Meta.UniqueNormalization.properAppNodes_app
#print axioms OperatorKO7.Meta.UniqueNormalization.patternNodes
#print axioms OperatorKO7.Meta.UniqueNormalization.mem_patternNodes
#print axioms OperatorKO7.Meta.UniqueNormalization.transRule
#print axioms OperatorKO7.Meta.UniqueNormalization.patternRuleOf
#print axioms OperatorKO7.Meta.UniqueNormalization.constructorTranslation
#print axioms OperatorKO7.Meta.UniqueNormalization.transRule_mem
#print axioms OperatorKO7.Meta.UniqueNormalization.patternRuleOf_mem
#print axioms OperatorKO7.Meta.UniqueNormalization.mem_constructorTranslation
#print axioms OperatorKO7.Meta.UniqueNormalization.lemma13
#print axioms OperatorKO7.Meta.UniqueNormalization.appNodes_subset_patternNodes
#print axioms OperatorKO7.Meta.UniqueNormalization.lemma14_forward_strict
#print axioms OperatorKO7.Meta.UniqueNormalization.lemma14_forward
#print axioms OperatorKO7.Meta.UniqueNormalization.lemma14_back
#print axioms OperatorKO7.Meta.UniqueNormalization.prop15_forward
#print axioms OperatorKO7.Meta.UniqueNormalization.prop15_back
#print axioms OperatorKO7.Meta.UniqueNormalization.cor16

/-! ## Theorem 69 -/

#check @Step.mono
#check @conv.mono
#check @extRuleL
#check @extRuleR
#check @extendedTRS
#check @mem_extendedTRS
#check @SymbolAbsent
#check @SymbolAbsent.arg
#check @step_of_step_extended
#check @normalForm_extended
#check @step_extL
#check @step_extR
#check @conv_var_var
#check @not_consistent_extended
#check @symbolAbsent_all_normalForms_false
#check @UNconv_of_consistency_of_extensions
#check @UNred_of_consistency_of_extensions
#check @FreezingNeeded.ruleGA
#check @FreezingNeeded.trs
#check @FreezingNeeded.tGx
#check @FreezingNeeded.tGx_normalForm
#check @FreezingNeeded.tGx_unifiable
#check @FreezingNeeded.tGx_omegaUnifiable
#check @FreezingNeeded.extension_not_nonOmegaOverlapping
#check @FreezingNeeded.freezing_step_required

#print axioms OperatorKO7.Meta.UniqueNormalization.Step.mono
#print axioms OperatorKO7.Meta.UniqueNormalization.conv.mono
#print axioms OperatorKO7.Meta.UniqueNormalization.extRuleL
#print axioms OperatorKO7.Meta.UniqueNormalization.extRuleR
#print axioms OperatorKO7.Meta.UniqueNormalization.extendedTRS
#print axioms OperatorKO7.Meta.UniqueNormalization.mem_extendedTRS
#print axioms OperatorKO7.Meta.UniqueNormalization.SymbolAbsent
#print axioms OperatorKO7.Meta.UniqueNormalization.SymbolAbsent.arg
#print axioms OperatorKO7.Meta.UniqueNormalization.step_of_step_extended
#print axioms OperatorKO7.Meta.UniqueNormalization.normalForm_extended
#print axioms OperatorKO7.Meta.UniqueNormalization.step_extL
#print axioms OperatorKO7.Meta.UniqueNormalization.step_extR
#print axioms OperatorKO7.Meta.UniqueNormalization.conv_var_var
#print axioms OperatorKO7.Meta.UniqueNormalization.not_consistent_extended
#print axioms OperatorKO7.Meta.UniqueNormalization.symbolAbsent_all_normalForms_false
#print axioms OperatorKO7.Meta.UniqueNormalization.UNconv_of_consistency_of_extensions
#print axioms OperatorKO7.Meta.UniqueNormalization.UNred_of_consistency_of_extensions
#print axioms OperatorKO7.Meta.UniqueNormalization.FreezingNeeded.ruleGA
#print axioms OperatorKO7.Meta.UniqueNormalization.FreezingNeeded.trs
#print axioms OperatorKO7.Meta.UniqueNormalization.FreezingNeeded.tGx
#print axioms OperatorKO7.Meta.UniqueNormalization.FreezingNeeded.tGx_normalForm
#print axioms OperatorKO7.Meta.UniqueNormalization.FreezingNeeded.tGx_unifiable
#print axioms OperatorKO7.Meta.UniqueNormalization.FreezingNeeded.tGx_omegaUnifiable
#print axioms OperatorKO7.Meta.UniqueNormalization.FreezingNeeded.extension_not_nonOmegaOverlapping
#print axioms OperatorKO7.Meta.UniqueNormalization.FreezingNeeded.freezing_step_required

/-! ## Example battery: complete public surface -/

#check @HuetSystem.ruleAA
#check @HuetSystem.ruleAB
#check @HuetSystem.ruleC
#check @HuetSystem.trs
#check @HuetSystem.tA
#check @HuetSystem.tB
#check @HuetSystem.tC
#check @HuetSystem.tGC
#check @HuetSystem.tFCC
#check @HuetSystem.tFCGC
#check @HuetSystem.subC
#check @HuetSystem.step_FCC_A
#check @HuetSystem.step_C_GC
#check @HuetSystem.step_FCC_FCGC
#check @HuetSystem.step_FCGC_B
#check @HuetSystem.no_rootStep_of_head
#check @HuetSystem.tA_normalForm
#check @HuetSystem.tB_normalForm
#check @HuetSystem.conv_A_B
#check @HuetSystem.not_UNconv
#check @HuetSystem.not_UNred
#check @HuetSystem.rhsDetermined
#check @HuetSystem.hypothesis_required
#check @KlopSystem.ruleA
#check @KlopSystem.ruleC
#check @KlopSystem.ruleD
#check @KlopSystem.trs
#check @KlopSystem.tA
#check @KlopSystem.tE
#check @KlopSystem.tCA
#check @KlopSystem.tCE
#check @KlopSystem.tDACA
#check @KlopSystem.tDCACA
#check @KlopSystem.tCCA
#check @KlopSystem.subA
#check @KlopSystem.subCA
#check @KlopSystem.step_A_CA
#check @KlopSystem.step_CA_DACA
#check @KlopSystem.step_DACA_DCACA
#check @KlopSystem.step_DCACA_E
#check @KlopSystem.stepStar_A_E
#check @KlopSystem.stepStar_CA_E
#check @KlopSystem.stepStar_A_CE
#check @KlopSystem.klop_both_reductions
#check @KlopSystem.conv_E_CE
#check @KlopSystem.tE_normalForm
#check @KlopSystem.FromCE
#check @KlopSystem.FromCE.base
#check @KlopSystem.FromCE.nest
#check @KlopSystem.FromCE.ne_tE
#check @KlopSystem.FromCE.step
#check @KlopSystem.fromCE_of_stepStar
#check @KlopSystem.not_stepStar_tCE_tE
#check @KlopSystem.not_joinable_tE_tCE
#check @KlopSystem.not_confluent
#check @KlopSystem.klop_example_three

#print axioms OperatorKO7.Meta.UniqueNormalization.HuetSystem.ruleAA
#print axioms OperatorKO7.Meta.UniqueNormalization.HuetSystem.ruleAB
#print axioms OperatorKO7.Meta.UniqueNormalization.HuetSystem.ruleC
#print axioms OperatorKO7.Meta.UniqueNormalization.HuetSystem.trs
#print axioms OperatorKO7.Meta.UniqueNormalization.HuetSystem.tA
#print axioms OperatorKO7.Meta.UniqueNormalization.HuetSystem.tB
#print axioms OperatorKO7.Meta.UniqueNormalization.HuetSystem.tC
#print axioms OperatorKO7.Meta.UniqueNormalization.HuetSystem.tGC
#print axioms OperatorKO7.Meta.UniqueNormalization.HuetSystem.tFCC
#print axioms OperatorKO7.Meta.UniqueNormalization.HuetSystem.tFCGC
#print axioms OperatorKO7.Meta.UniqueNormalization.HuetSystem.subC
#print axioms OperatorKO7.Meta.UniqueNormalization.HuetSystem.step_FCC_A
#print axioms OperatorKO7.Meta.UniqueNormalization.HuetSystem.step_C_GC
#print axioms OperatorKO7.Meta.UniqueNormalization.HuetSystem.step_FCC_FCGC
#print axioms OperatorKO7.Meta.UniqueNormalization.HuetSystem.step_FCGC_B
#print axioms OperatorKO7.Meta.UniqueNormalization.HuetSystem.no_rootStep_of_head
#print axioms OperatorKO7.Meta.UniqueNormalization.HuetSystem.tA_normalForm
#print axioms OperatorKO7.Meta.UniqueNormalization.HuetSystem.tB_normalForm
#print axioms OperatorKO7.Meta.UniqueNormalization.HuetSystem.conv_A_B
#print axioms OperatorKO7.Meta.UniqueNormalization.HuetSystem.not_UNconv
#print axioms OperatorKO7.Meta.UniqueNormalization.HuetSystem.not_UNred
#print axioms OperatorKO7.Meta.UniqueNormalization.HuetSystem.rhsDetermined
#print axioms OperatorKO7.Meta.UniqueNormalization.HuetSystem.hypothesis_required
#print axioms OperatorKO7.Meta.UniqueNormalization.KlopSystem.ruleA
#print axioms OperatorKO7.Meta.UniqueNormalization.KlopSystem.ruleC
#print axioms OperatorKO7.Meta.UniqueNormalization.KlopSystem.ruleD
#print axioms OperatorKO7.Meta.UniqueNormalization.KlopSystem.trs
#print axioms OperatorKO7.Meta.UniqueNormalization.KlopSystem.tA
#print axioms OperatorKO7.Meta.UniqueNormalization.KlopSystem.tE
#print axioms OperatorKO7.Meta.UniqueNormalization.KlopSystem.tCA
#print axioms OperatorKO7.Meta.UniqueNormalization.KlopSystem.tCE
#print axioms OperatorKO7.Meta.UniqueNormalization.KlopSystem.tDACA
#print axioms OperatorKO7.Meta.UniqueNormalization.KlopSystem.tDCACA
#print axioms OperatorKO7.Meta.UniqueNormalization.KlopSystem.tCCA
#print axioms OperatorKO7.Meta.UniqueNormalization.KlopSystem.subA
#print axioms OperatorKO7.Meta.UniqueNormalization.KlopSystem.subCA
#print axioms OperatorKO7.Meta.UniqueNormalization.KlopSystem.step_A_CA
#print axioms OperatorKO7.Meta.UniqueNormalization.KlopSystem.step_CA_DACA
#print axioms OperatorKO7.Meta.UniqueNormalization.KlopSystem.step_DACA_DCACA
#print axioms OperatorKO7.Meta.UniqueNormalization.KlopSystem.step_DCACA_E
#print axioms OperatorKO7.Meta.UniqueNormalization.KlopSystem.stepStar_A_E
#print axioms OperatorKO7.Meta.UniqueNormalization.KlopSystem.stepStar_CA_E
#print axioms OperatorKO7.Meta.UniqueNormalization.KlopSystem.stepStar_A_CE
#print axioms OperatorKO7.Meta.UniqueNormalization.KlopSystem.klop_both_reductions
#print axioms OperatorKO7.Meta.UniqueNormalization.KlopSystem.conv_E_CE
#print axioms OperatorKO7.Meta.UniqueNormalization.KlopSystem.tE_normalForm
#print axioms OperatorKO7.Meta.UniqueNormalization.KlopSystem.FromCE
#print axioms OperatorKO7.Meta.UniqueNormalization.KlopSystem.FromCE.base
#print axioms OperatorKO7.Meta.UniqueNormalization.KlopSystem.FromCE.nest
#print axioms OperatorKO7.Meta.UniqueNormalization.KlopSystem.FromCE.ne_tE
#print axioms OperatorKO7.Meta.UniqueNormalization.KlopSystem.FromCE.step
#print axioms OperatorKO7.Meta.UniqueNormalization.KlopSystem.fromCE_of_stepStar
#print axioms OperatorKO7.Meta.UniqueNormalization.KlopSystem.not_stepStar_tCE_tE
#print axioms OperatorKO7.Meta.UniqueNormalization.KlopSystem.not_joinable_tE_tCE
#print axioms OperatorKO7.Meta.UniqueNormalization.KlopSystem.not_confluent
#print axioms OperatorKO7.Meta.UniqueNormalization.KlopSystem.klop_example_three

/-! ## The six campaign results, each on its fixture -/

/-- Result 1. Huet's system: finite non-overlap is insufficient, explicit
infinite-term omega-overlap is present, and UN= fails.
This shows the hypothesis of RTA open problem #79 is required. -/
example :
    TRS.RhsDetermined HuetSystem.trs ∧ ¬ UNconv HuetSystem.trs ∧
      ¬ UNred HuetSystem.trs ∧
      OmegaUnifiable HuetSystem.ruleAA.lhs HuetSystem.ruleAB.lhs ∧
      InfiniteOmegaUnifiable HuetSystem.ruleAA.lhs HuetSystem.ruleAB.lhs ∧
      ¬ Unifiable HuetSystem.ruleAA.lhs HuetSystem.ruleAB.lhs :=
  HuetSystem.hypothesis_required

/-- Result 2. The variable condition on right-hand sides is a hypothesis of the
problem, not a convention: without it, `F(x) -> y` is non-omega-overlapping and
still identifies every pair of variables. -/
example :
    NonOmegaOverlapping FreshRhs.trs ∧ ¬ TRS.RhsDetermined FreshRhs.trs ∧
      ¬ UNconv FreshRhs.trs ∧ ¬ Consistent FreshRhs.trs :=
  FreshRhs.variable_condition_necessary

/-- Result 3. Proposition 21, in the form Theorem 68 consumes. -/
example {sigma nu : Type} (R : TRS sigma nu)
    (hno : NonOmegaOverlapping R) (hvar : TRS.RhsDetermined R) :
    AlmostNonOmegaOverlapping R :=
  AlmostNonOmegaOverlapping.of_nonOmegaOverlapping hno hvar

/-- Result 4. Corollary 16: the constructor translation preserves and reflects
consistency. -/
example {sigma nu : Type} (R : TRS sigma nu) :
    Consistent R ↔ Consistent (constructorTranslation R) :=
  cor16 R

/-- Result 5. Theorem 69's reduction: a general consistency theorem for the class,
together with membership of each extension in that class, gives UN=. -/
example {sigma nu : Type} {R : TRS sigma nu} {x y : nu} (hxy : x ≠ y)
    (hCON : ∀ S : TRS sigma nu,
      NonOmegaOverlapping S → TRS.RhsDetermined S → Consistent S)
    (hclass : ∀ t u : Term sigma nu, NormalForm R t → NormalForm R u →
      conv R t u → t ≠ u →
      ∃ F : sigma, NonOmegaOverlapping (extendedTRS R F t u x y) ∧
        TRS.RhsDetermined (extendedTRS R F t u x y)) :
    UNconv R :=
  UNconv_of_consistency_of_extensions hxy hCON hclass

/-- Result 6. The variable-freezing half of the paper's signature extension is
required: with a fresh symbol alone, the extension can leave the class. -/
example :
    NormalForm FreezingNeeded.trs FreezingNeeded.tGx ∧
      OmegaUnifiable FreezingNeeded.tGx FreezingNeeded.ruleGA.lhs ∧
      ¬ NonOmegaOverlapping
        (extendedTRS FreezingNeeded.trs 9 FreezingNeeded.tGx FreezingNeeded.tGx 5 6) :=
  FreezingNeeded.freezing_step_required

/-- Sanity: Lemma 13 fires on a concrete pattern, `g(x)` inside the left-hand
side of `f(g(x)) -> x`. -/
example : StepStar
    (constructorTranslation
      [({ lhs := .app 0 [.app 1 [.var 0]], rhs := .var 0, lhs_isApp := rfl } :
        Rule Nat Nat)])
    (destructorLabel (.app 1 [.var 0])) (constructorLabel (.app 1 [.var 0])) := by
  refine lemma13 _ _ ?_
  intro n hn
  simp only [appNodes_app, appNodesList_cons, appNodes_var, appNodesList_nil,
    List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hn
  subst hn
  exact List.mem_append_left _ (List.Mem.head _)

/-! ## Ranked-signature transport -/

#check @Term.ArityCorrect
#print axioms OperatorKO7.Meta.Rewriting.Term.ArityCorrect
#check @Term.ArityCorrect.var
#print axioms OperatorKO7.Meta.Rewriting.Term.ArityCorrect.var
#check @Term.ArityCorrect.app
#print axioms OperatorKO7.Meta.Rewriting.Term.ArityCorrect.app
#check @Term.arityCorrect_var
#print axioms OperatorKO7.Meta.Rewriting.Term.arityCorrect_var
#check @Term.arityCorrect_app_iff
#print axioms OperatorKO7.Meta.Rewriting.Term.arityCorrect_app_iff
#check @Term.arityCorrect_mapSym_iff
#print axioms OperatorKO7.Meta.Rewriting.Term.arityCorrect_mapSym_iff
#check @Term.arityCorrect_mapVar_iff
#print axioms OperatorKO7.Meta.Rewriting.Term.arityCorrect_mapVar_iff
#check @Term.arityCorrect_apply_iff
#print axioms OperatorKO7.Meta.Rewriting.Term.arityCorrect_apply_iff
#check @Term.ArityCorrect.apply
#print axioms OperatorKO7.Meta.Rewriting.Term.ArityCorrect.apply
#check @Term.ArityCorrect.of_apply
#print axioms OperatorKO7.Meta.Rewriting.Term.ArityCorrect.of_apply
#check @Term.arityProbe
#print axioms OperatorKO7.Meta.Rewriting.Term.arityProbe
#check @Term.arityProbe_correct
#print axioms OperatorKO7.Meta.Rewriting.Term.arityProbe_correct
#check @Term.arity_preserving_iff_probes
#print axioms OperatorKO7.Meta.Rewriting.Term.arity_preserving_iff_probes
#check @Term.arity_preserving_iff_all_terms
#print axioms OperatorKO7.Meta.Rewriting.Term.arity_preserving_iff_all_terms
#check @Term.Ranked
#print axioms OperatorKO7.Meta.Rewriting.Term.Ranked
#check @Term.mapRankedSym
#print axioms OperatorKO7.Meta.Rewriting.Term.mapRankedSym
#check @Term.mapRankedVar
#print axioms OperatorKO7.Meta.Rewriting.Term.mapRankedVar
#check @Term.applyRanked
#print axioms OperatorKO7.Meta.Rewriting.Term.applyRanked
#check @Term.mapRankedSym_id
#print axioms OperatorKO7.Meta.Rewriting.Term.mapRankedSym_id
#check @Term.mapRankedSym_comp
#print axioms OperatorKO7.Meta.Rewriting.Term.mapRankedSym_comp
#check @Term.mapRankedSym_applyRanked
#print axioms OperatorKO7.Meta.Rewriting.Term.mapRankedSym_applyRanked
#check @Term.list_length_preservation_not_arity_preservation
#print axioms OperatorKO7.Meta.Rewriting.Term.list_length_preservation_not_arity_preservation

example {sigma tau nu : Type} (a : sigma → Nat) (b : tau → Nat)
    (f : sigma → tau) (hf : ∀ s, b (f s) = a s) (t : Term sigma nu) :
    Term.ArityCorrect b (Term.mapSym f t) ↔ Term.ArityCorrect a t :=
  Term.arityCorrect_mapSym_iff a b f hf t

example :
    Term.ArityCorrect (fun _ : Unit => 0) (Term.app () [] : Term Unit Unit) ∧
      ¬ Term.ArityCorrect (fun _ : Unit => 1)
        (Term.mapSym (id : Unit → Unit) (Term.app () [] : Term Unit Unit)) :=
  Term.list_length_preservation_not_arity_preservation.2


/-! ## Whole-system overlap classes and translated rule obstruction -/

#check @ClassExamples.omega_head_eq
#print axioms OperatorKO7.Meta.UniqueNormalization.ClassExamples.omega_head_eq
#check @ClassExamples.finite_head_eq
#print axioms OperatorKO7.Meta.UniqueNormalization.ClassExamples.finite_head_eq
#check @ClassExamples.flat_app_subterm_eq
#print axioms OperatorKO7.Meta.UniqueNormalization.ClassExamples.flat_app_subterm_eq
#check @ClassExamples.deterministic_of_nonOverlapping
#print axioms OperatorKO7.Meta.UniqueNormalization.ClassExamples.deterministic_of_nonOverlapping
#check @ClassExamples.substituted_variable_is_subterm
#print axioms OperatorKO7.Meta.UniqueNormalization.ClassExamples.substituted_variable_is_subterm
#check @ClassExamples.noCommonGeneralisation_of_distinct_nullary_rhs
#print axioms OperatorKO7.Meta.UniqueNormalization.ClassExamples.noCommonGeneralisation_of_distinct_nullary_rhs
#check @HuetSystem.subterm_ruleAA_eq
#print axioms OperatorKO7.Meta.UniqueNormalization.HuetSystem.subterm_ruleAA_eq
#check @HuetSystem.subterm_ruleC_eq
#print axioms OperatorKO7.Meta.UniqueNormalization.HuetSystem.subterm_ruleC_eq
#check @HuetSystem.subterm_ruleAB_cases
#print axioms OperatorKO7.Meta.UniqueNormalization.HuetSystem.subterm_ruleAB_cases
#check @HuetSystem.nonvariable_subterm_cases
#print axioms OperatorKO7.Meta.UniqueNormalization.HuetSystem.nonvariable_subterm_cases
#check @HuetSystem.proper_pattern_not_omega_unifiable
#print axioms OperatorKO7.Meta.UniqueNormalization.HuetSystem.proper_pattern_not_omega_unifiable
#check @HuetSystem.critical_lhs_not_unifiable
#print axioms OperatorKO7.Meta.UniqueNormalization.HuetSystem.critical_lhs_not_unifiable
#check @HuetSystem.unifiable_lhs_eq
#print axioms OperatorKO7.Meta.UniqueNormalization.HuetSystem.unifiable_lhs_eq
#check @HuetSystem.nonOverlapping
#print axioms OperatorKO7.Meta.UniqueNormalization.HuetSystem.nonOverlapping
#check @HuetSystem.proper_omega_overlaps_absent
#print axioms OperatorKO7.Meta.UniqueNormalization.HuetSystem.proper_omega_overlaps_absent
#check @HuetSystem.root_deterministic
#print axioms OperatorKO7.Meta.UniqueNormalization.HuetSystem.root_deterministic
#check @HuetSystem.almostNonOmegaOverlapping
#print axioms OperatorKO7.Meta.UniqueNormalization.HuetSystem.almostNonOmegaOverlapping
#check @HuetSystem.not_nonOmegaOverlapping
#print axioms OperatorKO7.Meta.UniqueNormalization.HuetSystem.not_nonOmegaOverlapping
#check @HuetSystem.whole_system_class_certificate
#print axioms OperatorKO7.Meta.UniqueNormalization.HuetSystem.whole_system_class_certificate
#check @HuetSystem.no_common_generalisation
#print axioms OperatorKO7.Meta.UniqueNormalization.HuetSystem.no_common_generalisation
#check @HuetSystem.finite_root_condition_not_common_generalisation
#print axioms OperatorKO7.Meta.UniqueNormalization.HuetSystem.finite_root_condition_not_common_generalisation
#check @KlopSystem.nonvariable_subterm_eq
#print axioms OperatorKO7.Meta.UniqueNormalization.KlopSystem.nonvariable_subterm_eq
#check @KlopSystem.omega_unifiable_lhs_eq
#print axioms OperatorKO7.Meta.UniqueNormalization.KlopSystem.omega_unifiable_lhs_eq
#check @KlopSystem.nonOmegaOverlapping
#print axioms OperatorKO7.Meta.UniqueNormalization.KlopSystem.nonOmegaOverlapping
#check @KlopSystem.rhsDetermined
#print axioms OperatorKO7.Meta.UniqueNormalization.KlopSystem.rhsDetermined
#check @KlopSystem.whole_system_class_certificate
#print axioms OperatorKO7.Meta.UniqueNormalization.KlopSystem.whole_system_class_certificate
#check @HuetTranslation.rootRoleLabel
#print axioms OperatorKO7.Meta.UniqueNormalization.HuetTranslation.rootRoleLabel
#check @HuetTranslation.map_lhs_AA
#print axioms OperatorKO7.Meta.UniqueNormalization.HuetTranslation.map_lhs_AA
#check @HuetTranslation.map_lhs_AB
#print axioms OperatorKO7.Meta.UniqueNormalization.HuetTranslation.map_lhs_AB
#check @HuetTranslation.translated_lhs_omegaUnifiable
#print axioms OperatorKO7.Meta.UniqueNormalization.HuetTranslation.translated_lhs_omegaUnifiable
#check @HuetTranslation.translated_rules_no_common_generalisation
#print axioms OperatorKO7.Meta.UniqueNormalization.HuetTranslation.translated_rules_no_common_generalisation
#check @HuetTranslation.not_stronglyAlmostNonOmegaOverlapping
#print axioms OperatorKO7.Meta.UniqueNormalization.HuetTranslation.not_stronglyAlmostNonOmegaOverlapping
#check @HuetTranslation.finite_root_almost_counterexample
#print axioms OperatorKO7.Meta.UniqueNormalization.HuetTranslation.finite_root_almost_counterexample
#check @HuetTranslation.current_almost_translation_implication_false
#print axioms OperatorKO7.Meta.UniqueNormalization.HuetTranslation.current_almost_translation_implication_false

example :
    NonOverlapping HuetSystem.trs ∧ AlmostNonOmegaOverlapping HuetSystem.trs ∧
      TRS.RhsDetermined HuetSystem.trs ∧ ¬ NonOmegaOverlapping HuetSystem.trs ∧
      ¬ UNconv HuetSystem.trs ∧ ¬ UNred HuetSystem.trs :=
  HuetSystem.whole_system_class_certificate

example :
    NonOmegaOverlapping KlopSystem.trs ∧ TRS.RhsDetermined KlopSystem.trs ∧
      ¬ confluent KlopSystem.trs :=
  KlopSystem.whole_system_class_certificate

example :
    AlmostNonOmegaOverlapping HuetSystem.trs ∧ TRS.RhsDetermined HuetSystem.trs ∧
      ¬ StronglyAlmostNonOmegaOverlapping (constructorTranslation HuetSystem.trs) :=
  HuetTranslation.finite_root_almost_counterexample

end UN79Reach
