import OperatorKO7.Meta.UniqueNormalization.Transfer
import OperatorKO7.Meta.UniqueNormalization.Linearization
import OperatorKO7.Meta.UniqueNormalization.ConditionalTRS
import OperatorKO7.Meta.UniqueNormalization.Examples

/-!
# Reach test: the conditional-linearization transfer theorem

Campaign: `Roadmaps\klop\ROADMAP.md`, WP-K2, route R2.

This check imports every module it names, so each declaration resolves against
the current source of its owning module. It asserts that the conditional layer,
the linearization specification, and the transfer theorem all elaborate
verbatim, and it exercises the transfer theorem, the equational-coincidence
corollary, the negative control, and one genuine level-2 conditional step.

Axiom reports live in the owning modules.
-/

set_option autoImplicit false

namespace UN79TransferReach

open OperatorKO7.Meta.Rewriting
open OperatorKO7.Meta.UniqueNormalization

/-! ## Abstract rewriting layer -/

#check @relStar
#check @relConv
#check @relJoinable
#check @relConfluent
#check @relConv.refl
#check @relConv.single
#check @relConv.trans
#check @relConv.symm
#check @relConv.mono
#check @conv_of_relConv
#check @relJoinable_of_relConv

/-! ## Conditional systems -/

#check @CRule
#check @CRule.mk
#check @CRule.lhs
#check @CRule.rhs
#check @CRule.conds
#check @CRule.lhs_isApp
#check @CTRS
#check @crootStepE
#check @CStepE
#check @CStepE.root
#check @CStepE.arg
#check @CStepE.app_inv
#check @CStepE.mono
#check @CStepLevel
#check @CStepLevel_zero
#check @CStepLevel_succ
#check @CStepLevel.mono
#check @CStepLevel.mono_of_le
#check @CStep
#check @CStepStar
#check @cconv
#check @cconfluent
#check @CStep.of_level
#check @CStep.arg
#check @CondExample.crB
#check @CondExample.crF
#check @CondExample.demoCTRS
#check @CondExample.subBC
#check @CondExample.step_b_c
#check @CondExample.step_fbc_a
#check @CondExample.cstepStar_fbc_a
#check @CondExample.step_fbb_a

/-! ## Linearization -/

#check @VarOccurs
#check @VarOccurs.app_inv
#check @VarOccurs.size_apply_le
#check @VarOccurs.size_apply_lt_of_isApp
#check @VarOccurs.subterm_apply
#check @apply_eq_of_occurs_agree
#check @mapVar_id
#check @apply_mapVar
#check @mapVar_id_on
#check @LinearizesRule
#check @IsLinearization
#check @Term.varOccurrences
#check @Term.LeftLinear
#check @MethodLinearizesRule
#check @MethodLinearizesRule.mk
#check @MethodLinearizesRule.transfer
#check @MethodLinearizesRule.leftLinear
#check @IsMethodLinearization
#check @IsMethodLinearization.toIsLinearization
#check @linearizesRule_self
#check @linearizesRule_binaryDiagonal
#check @methodLinearizesRule_self
#check @leftLinear_binarySplit
#check @methodLinearizesRule_binaryDiagonal

/-! ## Transfer -/

#check @conv.args_append
#check @conv.args
#check @conv_apply_pointwise
#check @NormalForm.subterm
#check @cconv_of_relConv_level
#check @cstepLevel_one_of_rootStep
#check @cstepLevel_one_of_step
#check @cstepLevel_of_step
#check @cstep_of_step
#check @cconv_of_conv
#check @conv_of_cstepLevel
#check @conv_of_cstep
#check @cconv_iff_conv
#check @nf_no_cstep
#check @UNconv_of_cconfluent_linearization
#check @UNred_of_cconfluent_linearization
#check @Controls.linHuet
#check @Controls.isLin_huet
#check @Controls.linHuet_not_cconfluent
#check @Controls.linKO7
#check @Controls.nine_not_in_var_zero
#check @Controls.nine_not_in_void
#check @Controls.isLin_ko7
#check @Controls.linKO7_not_cconfluent

/-! ## Axiom parity -/

#print axioms relStar
#print axioms relConv
#print axioms relJoinable
#print axioms relConfluent
#print axioms relConv.refl
#print axioms relConv.single
#print axioms relConv.trans
#print axioms relConv.symm
#print axioms relConv.mono
#print axioms conv_of_relConv
#print axioms relJoinable_of_relConv
#print axioms CRule
#print axioms CRule.mk
#print axioms CRule.lhs
#print axioms CRule.rhs
#print axioms CRule.conds
#print axioms CRule.lhs_isApp
#print axioms CTRS
#print axioms crootStepE
#print axioms CStepE
#print axioms CStepE.root
#print axioms CStepE.arg
#print axioms CStepE.app_inv
#print axioms CStepE.mono
#print axioms CStepLevel
#print axioms CStepLevel_zero
#print axioms CStepLevel_succ
#print axioms CStepLevel.mono
#print axioms CStepLevel.mono_of_le
#print axioms CStep
#print axioms CStepStar
#print axioms cconv
#print axioms cconfluent
#print axioms CStep.of_level
#print axioms CStep.arg
#print axioms CondExample.crB
#print axioms CondExample.crF
#print axioms CondExample.demoCTRS
#print axioms CondExample.subBC
#print axioms CondExample.step_b_c
#print axioms CondExample.step_fbc_a
#print axioms CondExample.cstepStar_fbc_a
#print axioms CondExample.step_fbb_a
#print axioms Term.varOccurrences
#print axioms Term.LeftLinear
#print axioms MethodLinearizesRule
#print axioms MethodLinearizesRule.mk
#print axioms MethodLinearizesRule.transfer
#print axioms MethodLinearizesRule.leftLinear
#print axioms IsMethodLinearization
#print axioms IsMethodLinearization.toIsLinearization
#print axioms methodLinearizesRule_self
#print axioms leftLinear_binarySplit
#print axioms methodLinearizesRule_binaryDiagonal
#print axioms conv.args_append
#print axioms conv.args
#print axioms conv_apply_pointwise
#print axioms NormalForm.subterm
#print axioms cconv_of_relConv_level
#print axioms cstepLevel_one_of_rootStep
#print axioms cstepLevel_one_of_step
#print axioms cstepLevel_of_step
#print axioms cstep_of_step
#print axioms cconv_of_conv
#print axioms conv_of_cstepLevel
#print axioms conv_of_cstep
#print axioms cconv_iff_conv
#print axioms nf_no_cstep
#print axioms UNconv_of_cconfluent_linearization
#print axioms UNred_of_cconfluent_linearization
#print axioms Controls.linHuet
#print axioms Controls.isLin_huet
#print axioms Controls.linHuet_not_cconfluent
#print axioms Controls.linKO7
#print axioms Controls.nine_not_in_var_zero
#print axioms Controls.nine_not_in_void
#print axioms Controls.isLin_ko7
#print axioms Controls.linKO7_not_cconfluent

/-! ## The results, each on its fixture -/

/-- The transfer theorem: confluence of a conditional linearization gives unique
normal forms with respect to conversion. -/
example {sigma nu : Type} {R : TRS sigma nu} {C : CTRS sigma nu}
    (hlin : IsLinearization R C) (hconf : cconfluent C) : UNconv R :=
  UNconv_of_cconfluent_linearization hlin hconf

/-- The same hypotheses give unique normal forms with respect to reduction. -/
example {sigma nu : Type} {R : TRS sigma nu} {C : CTRS sigma nu}
    (hlin : IsLinearization R C) (hconf : cconfluent C) : UNred R :=
  UNred_of_cconfluent_linearization hlin hconf

/-- A linearization has the same equational theory as the system it linearizes,
with no confluence hypothesis. -/
example {sigma nu : Type} {R : TRS sigma nu} {C : CTRS sigma nu}
    (hlin : IsLinearization R C) (s t : Term sigma nu) :
    cconv C s t ↔ conv R s t :=
  cconv_iff_conv hlin s t

/-- The negative control: Huet's system fails unique normal forms, so its
conditional linearization fails confluence. -/
example : ¬ cconfluent Controls.linHuet := Controls.linHuet_not_cconfluent

/-- The linearization of Huet's system really is one. -/
example : IsLinearization HuetSystem.trs Controls.linHuet := Controls.isLin_huet

/-- A conditional step at level 2, with its condition discharged by a level-1
conversion rather than by syntactic equality. -/
example :
    CStepLevel CondExample.demoCTRS 2
      (.app 2 [.app 0 [], .app 1 []]) (.app 3 []) :=
  CondExample.step_fbc_a

/-- The diagonal rule linearizes to the conditional rule, with the target kept
as the original right-hand side. -/
example : LinearizesRule CondExample.diagRule CondExample.crF :=
  CondExample.diagRule_linearizes

end UN79TransferReach
