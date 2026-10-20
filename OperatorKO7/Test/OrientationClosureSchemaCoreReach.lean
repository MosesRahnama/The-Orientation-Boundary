import OperatorKO7.Meta.Methods.OrientationClosure.SchemaCore

/-!
# SchemaCore reach and axiom check

Paired declaration reach and axiom checks for `SchemaCore.lean`.
-/

#check @OperatorKO7.Methods.OrientationClosure.SchemaCore.FreeTerm
#print axioms OperatorKO7.Methods.OrientationClosure.SchemaCore.FreeTerm
#check @OperatorKO7.Methods.OrientationClosure.SchemaCore.FreeTerm.subst
#print axioms OperatorKO7.Methods.OrientationClosure.SchemaCore.FreeTerm.subst
#check @OperatorKO7.Methods.OrientationClosure.SchemaCore.FreeTerm.subst_var
#print axioms OperatorKO7.Methods.OrientationClosure.SchemaCore.FreeTerm.subst_var
#check @OperatorKO7.Methods.OrientationClosure.SchemaCore.FreeTerm.subst_zero
#print axioms OperatorKO7.Methods.OrientationClosure.SchemaCore.FreeTerm.subst_zero
#check @OperatorKO7.Methods.OrientationClosure.SchemaCore.FreeTerm.subst_succ
#print axioms OperatorKO7.Methods.OrientationClosure.SchemaCore.FreeTerm.subst_succ
#check @OperatorKO7.Methods.OrientationClosure.SchemaCore.FreeTerm.subst_wrap
#print axioms OperatorKO7.Methods.OrientationClosure.SchemaCore.FreeTerm.subst_wrap
#check @OperatorKO7.Methods.OrientationClosure.SchemaCore.FreeTerm.subst_recur
#print axioms OperatorKO7.Methods.OrientationClosure.SchemaCore.FreeTerm.subst_recur
#check @OperatorKO7.Methods.OrientationClosure.SchemaCore.FreeTerm.subst_id
#print axioms OperatorKO7.Methods.OrientationClosure.SchemaCore.FreeTerm.subst_id
#check @OperatorKO7.Methods.OrientationClosure.SchemaCore.FreeTerm.subst_comp
#print axioms OperatorKO7.Methods.OrientationClosure.SchemaCore.FreeTerm.subst_comp
#check @OperatorKO7.Methods.OrientationClosure.SchemaCore.FreeContext
#print axioms OperatorKO7.Methods.OrientationClosure.SchemaCore.FreeContext
#check @OperatorKO7.Methods.OrientationClosure.SchemaCore.FreeContext.plug
#print axioms OperatorKO7.Methods.OrientationClosure.SchemaCore.FreeContext.plug
#check @OperatorKO7.Methods.OrientationClosure.SchemaCore.FreeContext.subst
#print axioms OperatorKO7.Methods.OrientationClosure.SchemaCore.FreeContext.subst
#check @OperatorKO7.Methods.OrientationClosure.SchemaCore.FreeContext.comp
#print axioms OperatorKO7.Methods.OrientationClosure.SchemaCore.FreeContext.comp
#check @OperatorKO7.Methods.OrientationClosure.SchemaCore.FreeContext.plug_hole
#print axioms OperatorKO7.Methods.OrientationClosure.SchemaCore.FreeContext.plug_hole
#check @OperatorKO7.Methods.OrientationClosure.SchemaCore.FreeContext.plug_comp
#print axioms OperatorKO7.Methods.OrientationClosure.SchemaCore.FreeContext.plug_comp
#check @OperatorKO7.Methods.OrientationClosure.SchemaCore.FreeContext.subst_plug
#print axioms OperatorKO7.Methods.OrientationClosure.SchemaCore.FreeContext.subst_plug
#check @OperatorKO7.Methods.OrientationClosure.SchemaCore.RootStep
#print axioms OperatorKO7.Methods.OrientationClosure.SchemaCore.RootStep
#check @OperatorKO7.Methods.OrientationClosure.SchemaCore.RootStep.subst
#print axioms OperatorKO7.Methods.OrientationClosure.SchemaCore.RootStep.subst
#check @OperatorKO7.Methods.OrientationClosure.SchemaCore.ContextStep
#print axioms OperatorKO7.Methods.OrientationClosure.SchemaCore.ContextStep
#check @OperatorKO7.Methods.OrientationClosure.SchemaCore.rootStep_contextStep
#print axioms OperatorKO7.Methods.OrientationClosure.SchemaCore.rootStep_contextStep
#check @OperatorKO7.Methods.OrientationClosure.SchemaCore.freeSchema
#print axioms OperatorKO7.Methods.OrientationClosure.SchemaCore.freeSchema
#check @OperatorKO7.Methods.OrientationClosure.SchemaCore.freeRootSystem
#print axioms OperatorKO7.Methods.OrientationClosure.SchemaCore.freeRootSystem
#check @OperatorKO7.Methods.OrientationClosure.SchemaCore.freeRootSystem_dup
#print axioms OperatorKO7.Methods.OrientationClosure.SchemaCore.freeRootSystem_dup
#check @OperatorKO7.Methods.OrientationClosure.SchemaCore.FreeTerm.var
#print axioms OperatorKO7.Methods.OrientationClosure.SchemaCore.FreeTerm.var
#check @OperatorKO7.Methods.OrientationClosure.SchemaCore.FreeTerm.zero
#print axioms OperatorKO7.Methods.OrientationClosure.SchemaCore.FreeTerm.zero
#check @OperatorKO7.Methods.OrientationClosure.SchemaCore.FreeTerm.succ
#print axioms OperatorKO7.Methods.OrientationClosure.SchemaCore.FreeTerm.succ
#check @OperatorKO7.Methods.OrientationClosure.SchemaCore.FreeTerm.wrap
#print axioms OperatorKO7.Methods.OrientationClosure.SchemaCore.FreeTerm.wrap
#check @OperatorKO7.Methods.OrientationClosure.SchemaCore.FreeTerm.recur
#print axioms OperatorKO7.Methods.OrientationClosure.SchemaCore.FreeTerm.recur
#check @OperatorKO7.Methods.OrientationClosure.SchemaCore.FreeContext.hole
#print axioms OperatorKO7.Methods.OrientationClosure.SchemaCore.FreeContext.hole
#check @OperatorKO7.Methods.OrientationClosure.SchemaCore.FreeContext.succ
#print axioms OperatorKO7.Methods.OrientationClosure.SchemaCore.FreeContext.succ
#check @OperatorKO7.Methods.OrientationClosure.SchemaCore.FreeContext.wrapLeft
#print axioms OperatorKO7.Methods.OrientationClosure.SchemaCore.FreeContext.wrapLeft
#check @OperatorKO7.Methods.OrientationClosure.SchemaCore.FreeContext.wrapRight
#print axioms OperatorKO7.Methods.OrientationClosure.SchemaCore.FreeContext.wrapRight
#check @OperatorKO7.Methods.OrientationClosure.SchemaCore.FreeContext.recurBase
#print axioms OperatorKO7.Methods.OrientationClosure.SchemaCore.FreeContext.recurBase
#check @OperatorKO7.Methods.OrientationClosure.SchemaCore.FreeContext.recurStep
#print axioms OperatorKO7.Methods.OrientationClosure.SchemaCore.FreeContext.recurStep
#check @OperatorKO7.Methods.OrientationClosure.SchemaCore.FreeContext.recurCounter
#print axioms OperatorKO7.Methods.OrientationClosure.SchemaCore.FreeContext.recurCounter
#check @OperatorKO7.Methods.OrientationClosure.SchemaCore.RootStep.recurZero
#print axioms OperatorKO7.Methods.OrientationClosure.SchemaCore.RootStep.recurZero
#check @OperatorKO7.Methods.OrientationClosure.SchemaCore.RootStep.recurSucc
#print axioms OperatorKO7.Methods.OrientationClosure.SchemaCore.RootStep.recurSucc
#check @OperatorKO7.Methods.OrientationClosure.SchemaCore.ContextStep.lift
#print axioms OperatorKO7.Methods.OrientationClosure.SchemaCore.ContextStep.lift
#check @OperatorKO7.Methods.OrientationClosure.SchemaCore.ContextStep.outer
#print axioms OperatorKO7.Methods.OrientationClosure.SchemaCore.ContextStep.outer
#check @OperatorKO7.Methods.OrientationClosure.SchemaCore.ContextStep.subst
#print axioms OperatorKO7.Methods.OrientationClosure.SchemaCore.ContextStep.subst
