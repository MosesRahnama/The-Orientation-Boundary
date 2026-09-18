import OperatorKO7.Meta.UniqueNormalization.Section7RootSufficiency
import OperatorKO7.Meta.UniqueNormalization.Section7FiberReduction

set_option autoImplicit false

open OperatorKO7.Meta.UniqueNormalization

#check @RootStepsRepresented
#check @TermTargetedPGraph.universal_of_rootStepsRepresented

#print axioms RootStepsRepresented
#print axioms TermTargetedPGraph.universal_of_rootStepsRepresented

#check @PGraph.universal_of_rootStepsRepresented
#check @PGraph.Universal.rootStepsRepresented
#check @PGraph.Universal.sigmaClosedOn
#check @PGraph.universal_iff_rootStepsRepresented_and_sigmaClosedOn
#check @PGraph.Universal.barClosed
#check @PGraph.Universal.equalityComplete
#check @PGraph.sigmaClosedOn_of_barClosed_complete
#check @PGraph.universal_iff_rootStepsRepresented_and_barClosed
#check @PGraph.universal_iff_rootStepsRepresented_of_barClosed_complete
#check @PGraph.EqualityComplete.universal_iff_rootStepsRepresented
#check @PGraph.exists_unrepresented_rootStep_of_not_universal
#check @RootStepsRepresented.iff_normalRoot

#print axioms PGraph.universal_of_rootStepsRepresented
#print axioms PGraph.Universal.rootStepsRepresented
#print axioms PGraph.Universal.sigmaClosedOn
#print axioms PGraph.universal_iff_rootStepsRepresented_and_sigmaClosedOn
#print axioms PGraph.Universal.barClosed
#print axioms PGraph.Universal.equalityComplete
#print axioms PGraph.sigmaClosedOn_of_barClosed_complete
#print axioms PGraph.universal_iff_rootStepsRepresented_and_barClosed
#print axioms PGraph.universal_iff_rootStepsRepresented_of_barClosed_complete
#print axioms PGraph.EqualityComplete.universal_iff_rootStepsRepresented
#print axioms PGraph.exists_unrepresented_rootStep_of_not_universal
#print axioms RootStepsRepresented.iff_normalRoot

open OperatorKO7.Meta.Rewriting

#check @PGraph.RootOnly
#print axioms PGraph.RootOnly

#check @PGraph.empty_rootOnly
#print axioms PGraph.empty_rootOnly

#check @PGraph.RootOnly.extend_root
#print axioms PGraph.RootOnly.extend_root

#check @RootStepsRepresented.mono
#print axioms RootStepsRepresented.mono

#check @exists_rootOnly_rootStepsRepresented
#print axioms exists_rootOnly_rootStepsRepresented

#check @exists_equalityComplete_rootStepsRepresented
#print axioms exists_equalityComplete_rootStepsRepresented

#check @exists_rootOnly_rootStepsRepresented_of_strong
#print axioms exists_rootOnly_rootStepsRepresented_of_strong

#check @exists_equalityComplete_rootStepsRepresented_of_strong
#print axioms exists_equalityComplete_rootStepsRepresented_of_strong

example : ∃ rho : PGraph Section7Active.terms Section7Active.rules,
    rho.RootOnly ∧ RootStepsRepresented Section7Active.terms Section7Active.rules rho :=
  exists_rootOnly_rootStepsRepresented_of_strong Section7Active.terms_coalgebra
    Section7Active.rules_constructor Section7Active.rules_strong

example : ∃ rho : PGraph Section7Active.terms Section7Active.rules,
    rho.EqualityComplete ∧
      RootStepsRepresented Section7Active.terms Section7Active.rules rho :=
  exists_equalityComplete_rootStepsRepresented_of_strong Section7Active.terms_coalgebra
    Section7Active.rules_constructor Section7Active.rules_strong

example : RootStepsRepresented Section7Active.terms Section7Active.rules
    Section7Active.graph := by
  intro a b ha hb _
  exact ⟨ha, hb, Section7Active.constant,
    Section7Active.reach_constant ha, Section7Active.reach_constant hb⟩

example : Section7Active.graph.Universal := by
  apply Section7Active.graph.universal_of_rootStepsRepresented
    (Section7Active.graph.sigmaClosedOn_of_barClosed_complete
      Section7Active.terms_coalgebra Section7Active.rules_constructor
      Section7Active.graph_barClosed Section7Active.graph_complete)
  intro a b ha hb _
  exact ⟨ha, hb, Section7Active.constant,
    Section7Active.reach_constant ha, Section7Active.reach_constant hb⟩

example : SigmaClosedOn Section7Active.terms
    (EqvOn Section7Active.terms Section7Active.Trap.graph.par) :=
  Section7Active.Trap.graph.sigmaClosedOn_of_barClosed_complete
    Section7Active.terms_coalgebra Section7Active.rules_constructor
    Section7Active.Trap.graph_barClosed Section7Active.Trap.graph_complete

example : ¬ RootStepsRepresented Section7Active.terms Section7Active.rules
    Section7Active.Trap.graph := by
  intro h
  exact Section7Active.Trap.once_not_eqv_constant
    (h (by simp [Section7Active.mem_terms]) (by simp [Section7Active.mem_terms])
      Section7Active.root_once)

example : ∃ a b, a ∈ Section7Active.terms ∧ b ∈ Section7Active.terms ∧
    rootStep Section7Active.rules a b ∧
      ¬ EqvOn Section7Active.terms Section7Active.Trap.graph.par a b := by
  apply Section7Active.Trap.graph.exists_unrepresented_rootStep_of_not_universal
    (Section7Active.Trap.graph.sigmaClosedOn_of_barClosed_complete
      Section7Active.terms_coalgebra Section7Active.rules_constructor
      Section7Active.Trap.graph_barClosed Section7Active.Trap.graph_complete)
  intro huniv
  exact Section7Active.Trap.once_not_eqv_constant
    (huniv.rootStepsRepresented (by simp [Section7Active.mem_terms])
      (by simp [Section7Active.mem_terms]) Section7Active.root_once)

#check @down_transitive_of_finite_context_models
#print axioms down_transitive_of_finite_context_models

#check @conv_iff_down_of_finite_context_models
#print axioms conv_iff_down_of_finite_context_models

#check @constructorCompatible_conv_of_finite_context_models
#print axioms constructorCompatible_conv_of_finite_context_models

#check @PGraph.ContextTransitive
#print axioms PGraph.ContextTransitive

#check @PGraph.ContextAbsorbs
#print axioms PGraph.ContextAbsorbs

#check @PGraph.contextTransitive_iff_contextAbsorbs
#print axioms PGraph.contextTransitive_iff_contextAbsorbs

#check @PGraph.context_subset_downOn
#print axioms PGraph.context_subset_downOn

#check @PGraph.context_iff_downOn_of_rootStepsRepresented
#print axioms PGraph.context_iff_downOn_of_rootStepsRepresented

#check @PGraph.downOn_transitive_of_contextAbsorbs
#print axioms PGraph.downOn_transitive_of_contextAbsorbs

#check @PGraph.Universal.contextAbsorbs
#print axioms PGraph.Universal.contextAbsorbs

example : Section7Active.graph.ContextAbsorbs := by
  intro a b c ha _ hc _ _
  exact CT.base ⟨ha, hc, Section7Active.constant,
    Section7Active.reach_constant ha, Section7Active.reach_constant hc⟩

example : ∀ a b c,
    DownOn Section7Active.terms Section7Active.rules a b →
    DownOn Section7Active.terms Section7Active.rules b c →
    DownOn Section7Active.terms Section7Active.rules a c := by
  apply Section7Active.graph.downOn_transitive_of_contextAbsorbs
    Section7Active.terms_coalgebra
  · intro a b ha hb _
    exact ⟨ha, hb, Section7Active.constant,
      Section7Active.reach_constant ha, Section7Active.reach_constant hb⟩
  · intro a b c ha _ hc _ _
    exact CT.base ⟨ha, hc, Section7Active.constant,
      Section7Active.reach_constant ha, Section7Active.reach_constant hc⟩
