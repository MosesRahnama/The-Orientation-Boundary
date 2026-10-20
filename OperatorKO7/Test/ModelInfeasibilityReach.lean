import OperatorKO7.Meta.UniqueNormalization.ModelInfeasibility

/-!
# Reach and axiom check for model certificates

Pins every explicit public declaration of
`OperatorKO7/Meta/UniqueNormalization/ModelInfeasibility.lean`, and the constructor
and projection of `SymbolInterp`, each with a paired axiom query. Baseline axioms only.
-/

#check @OperatorKO7.Meta.UniqueNormalization.SymbolInterp
#print axioms OperatorKO7.Meta.UniqueNormalization.SymbolInterp
#check @OperatorKO7.Meta.UniqueNormalization.SymbolInterp.mk
#print axioms OperatorKO7.Meta.UniqueNormalization.SymbolInterp.mk
#check @OperatorKO7.Meta.UniqueNormalization.SymbolInterp.op
#print axioms OperatorKO7.Meta.UniqueNormalization.SymbolInterp.op
#check @OperatorKO7.Meta.UniqueNormalization.SymbolInterp.eval
#print axioms OperatorKO7.Meta.UniqueNormalization.SymbolInterp.eval
#check @OperatorKO7.Meta.UniqueNormalization.SymbolInterp.evalList
#print axioms OperatorKO7.Meta.UniqueNormalization.SymbolInterp.evalList
#check @OperatorKO7.Meta.UniqueNormalization.SymbolInterp.eval_var
#print axioms OperatorKO7.Meta.UniqueNormalization.SymbolInterp.eval_var
#check @OperatorKO7.Meta.UniqueNormalization.SymbolInterp.eval_app
#print axioms OperatorKO7.Meta.UniqueNormalization.SymbolInterp.eval_app
#check @OperatorKO7.Meta.UniqueNormalization.SymbolInterp.evalList_nil
#print axioms OperatorKO7.Meta.UniqueNormalization.SymbolInterp.evalList_nil
#check @OperatorKO7.Meta.UniqueNormalization.SymbolInterp.evalList_cons
#print axioms OperatorKO7.Meta.UniqueNormalization.SymbolInterp.evalList_cons
#check @OperatorKO7.Meta.UniqueNormalization.SymbolInterp.evalList_eq_map
#print axioms OperatorKO7.Meta.UniqueNormalization.SymbolInterp.evalList_eq_map
#check @OperatorKO7.Meta.UniqueNormalization.SymbolInterp.eval_apply
#print axioms OperatorKO7.Meta.UniqueNormalization.SymbolInterp.eval_apply
#check @OperatorKO7.Meta.UniqueNormalization.SymbolInterp.RulesHold
#print axioms OperatorKO7.Meta.UniqueNormalization.SymbolInterp.RulesHold
#check @OperatorKO7.Meta.UniqueNormalization.SymbolInterp.eval_eq_of_step
#print axioms OperatorKO7.Meta.UniqueNormalization.SymbolInterp.eval_eq_of_step
#check @OperatorKO7.Meta.UniqueNormalization.SymbolInterp.eval_eq_of_conv
#print axioms OperatorKO7.Meta.UniqueNormalization.SymbolInterp.eval_eq_of_conv
#check @OperatorKO7.Meta.UniqueNormalization.ModelRefutesOverlaps
#print axioms OperatorKO7.Meta.UniqueNormalization.ModelRefutesOverlaps
#check @OperatorKO7.Meta.UniqueNormalization.noFeasibleOverlap_of_model
#print axioms OperatorKO7.Meta.UniqueNormalization.noFeasibleOverlap_of_model
#check @OperatorKO7.Meta.UniqueNormalization.UNconv_of_model
#print axioms OperatorKO7.Meta.UniqueNormalization.UNconv_of_model
#check @OperatorKO7.Meta.UniqueNormalization.UNconv_of_linHub_model
#print axioms OperatorKO7.Meta.UniqueNormalization.UNconv_of_linHub_model
#check @OperatorKO7.Meta.UniqueNormalization.convSetoid
#print axioms OperatorKO7.Meta.UniqueNormalization.convSetoid
#check @OperatorKO7.Meta.UniqueNormalization.quotientInterp
#print axioms OperatorKO7.Meta.UniqueNormalization.quotientInterp
#check @OperatorKO7.Meta.UniqueNormalization.quotientInterp_eval
#print axioms OperatorKO7.Meta.UniqueNormalization.quotientInterp_eval
#check @OperatorKO7.Meta.UniqueNormalization.quotientInterp_rulesHold
#print axioms OperatorKO7.Meta.UniqueNormalization.quotientInterp_rulesHold
#check @OperatorKO7.Meta.UniqueNormalization.quotientInterp_eval_canonical
#print axioms OperatorKO7.Meta.UniqueNormalization.quotientInterp_eval_canonical
#check @OperatorKO7.Meta.UniqueNormalization.noFeasibleOverlap_iff_quotient_refutes
#print axioms OperatorKO7.Meta.UniqueNormalization.noFeasibleOverlap_iff_quotient_refutes
#check @OperatorKO7.Meta.UniqueNormalization.Controls.huet_no_model_certificate
#print axioms OperatorKO7.Meta.UniqueNormalization.Controls.huet_no_model_certificate
#check @OperatorKO7.Meta.UniqueNormalization.Controls.ko7_no_model_certificate
#print axioms OperatorKO7.Meta.UniqueNormalization.Controls.ko7_no_model_certificate
#check @OperatorKO7.Meta.UniqueNormalization.F45Certificate.trs
#print axioms OperatorKO7.Meta.UniqueNormalization.F45Certificate.trs
#check @OperatorKO7.Meta.UniqueNormalization.F45Certificate.lin
#print axioms OperatorKO7.Meta.UniqueNormalization.F45Certificate.lin
#check @OperatorKO7.Meta.UniqueNormalization.F45Certificate.collapse
#print axioms OperatorKO7.Meta.UniqueNormalization.F45Certificate.collapse
#check @OperatorKO7.Meta.UniqueNormalization.F45Certificate.linearizes_first
#print axioms OperatorKO7.Meta.UniqueNormalization.F45Certificate.linearizes_first
#check @OperatorKO7.Meta.UniqueNormalization.F45Certificate.linearizes_second
#print axioms OperatorKO7.Meta.UniqueNormalization.F45Certificate.linearizes_second
#check @OperatorKO7.Meta.UniqueNormalization.F45Certificate.isLin
#print axioms OperatorKO7.Meta.UniqueNormalization.F45Certificate.isLin
#check @OperatorKO7.Meta.UniqueNormalization.F45Certificate.lin_leftLinear
#print axioms OperatorKO7.Meta.UniqueNormalization.F45Certificate.lin_leftLinear
#check @OperatorKO7.Meta.UniqueNormalization.F45Certificate.trs_varCondition
#print axioms OperatorKO7.Meta.UniqueNormalization.F45Certificate.trs_varCondition
#check @OperatorKO7.Meta.UniqueNormalization.F45Certificate.lin_not_nonOverlapping
#print axioms OperatorKO7.Meta.UniqueNormalization.F45Certificate.lin_not_nonOverlapping
#check @OperatorKO7.Meta.UniqueNormalization.F45Certificate.model
#print axioms OperatorKO7.Meta.UniqueNormalization.F45Certificate.model
#check @OperatorKO7.Meta.UniqueNormalization.F45Certificate.model_op_F
#print axioms OperatorKO7.Meta.UniqueNormalization.F45Certificate.model_op_F
#check @OperatorKO7.Meta.UniqueNormalization.F45Certificate.model_op_G
#print axioms OperatorKO7.Meta.UniqueNormalization.F45Certificate.model_op_G
#check @OperatorKO7.Meta.UniqueNormalization.F45Certificate.model_rulesHold
#print axioms OperatorKO7.Meta.UniqueNormalization.F45Certificate.model_rulesHold
#check @OperatorKO7.Meta.UniqueNormalization.F45Certificate.lhs2_subterm_cases
#print axioms OperatorKO7.Meta.UniqueNormalization.F45Certificate.lhs2_subterm_cases
#check @OperatorKO7.Meta.UniqueNormalization.F45Certificate.model_refutes
#print axioms OperatorKO7.Meta.UniqueNormalization.F45Certificate.model_refutes
#check @OperatorKO7.Meta.UniqueNormalization.F45Certificate.UNconv_trs
#print axioms OperatorKO7.Meta.UniqueNormalization.F45Certificate.UNconv_trs

/-- Non-vacuity at the advertised domain: the F45 system itself has unique normal
forms, and its linearization overlaps. -/
example : OperatorKO7.Meta.UniqueNormalization.UNconv
      OperatorKO7.Meta.UniqueNormalization.F45Certificate.trs ∧
    ¬ OperatorKO7.Meta.UniqueNormalization.CNonOverlapping
      OperatorKO7.Meta.UniqueNormalization.F45Certificate.lin :=
  ⟨OperatorKO7.Meta.UniqueNormalization.F45Certificate.UNconv_trs,
    OperatorKO7.Meta.UniqueNormalization.F45Certificate.lin_not_nonOverlapping⟩
