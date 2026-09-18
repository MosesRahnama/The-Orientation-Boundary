import OperatorKO7.Meta.DistinctionBoundary.GodelRankTransport

/-!
# Reach and axiom gate for quotation/substitution/representation rank transport
-/


set_option autoImplicit false

namespace OperatorKO7.Meta.DistinctionBoundary.GodelPartial

#check @JustifPhase
#check @JustifPhase.quote
#check @JustifPhase.subst
#check @JustifPhase.represent
#check @phaseRank
#check @QuoteJustifState
#check @QuoteJustifState.mk
#check @QuoteJustifState.code
#check @QuoteJustifState.phase
#check @transportedBudget
#check @toMeta
#check @LicensedJustification
#check @LicensedJustification.quoteToSubst
#check @LicensedJustification.substToRepresent
#check @LicensedJustification.representToQuote
#check @QuoteJustifStep
#check @phaseRank_quoteToSubst
#check @phaseRank_substToRepresent
#check @phaseRank_representToQuote
#check @licensed_implies_budgetDrop
#check @licensed_to_reflective
#check @quoteJustif_of_licensed
#check @quoteJustif_strict_rank
#check @quoteJustif_identity_blocked
#check @quoteJustif_cycle_impossible
#check @every_licensed_edge_decreases_rank
#check @quote_self_license_is_identity_base
#check @quote_self_license_on_justif_state
#check @quotation_mediated_cycle_impossible
#check @quote_justif_wf
#print axioms JustifPhase
#print axioms JustifPhase.quote
#print axioms JustifPhase.subst
#print axioms JustifPhase.represent
#print axioms phaseRank
#print axioms QuoteJustifState
#print axioms QuoteJustifState.mk
#print axioms QuoteJustifState.code
#print axioms QuoteJustifState.phase
#print axioms transportedBudget
#print axioms toMeta
#print axioms LicensedJustification
#print axioms LicensedJustification.quoteToSubst
#print axioms LicensedJustification.substToRepresent
#print axioms LicensedJustification.representToQuote
#print axioms QuoteJustifStep
#print axioms phaseRank_quoteToSubst
#print axioms phaseRank_substToRepresent
#print axioms phaseRank_representToQuote
#print axioms licensed_implies_budgetDrop
#print axioms licensed_to_reflective
#print axioms quoteJustif_of_licensed
#print axioms quoteJustif_strict_rank
#print axioms quoteJustif_identity_blocked
#print axioms quoteJustif_cycle_impossible
#print axioms every_licensed_edge_decreases_rank
#print axioms quote_self_license_is_identity_base
#print axioms quote_self_license_on_justif_state
#print axioms quotation_mediated_cycle_impossible
#print axioms quote_justif_wf

end OperatorKO7.Meta.DistinctionBoundary.GodelPartial
