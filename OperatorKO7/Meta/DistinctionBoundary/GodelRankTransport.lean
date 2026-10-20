import OperatorKO7.Meta.DistinctionBoundary.GodelPartial
import OperatorKO7.Meta.DistinctionBoundary.GodelPartialClosure
import OperatorKO7.Meta.Decision.ReflectiveDependencyPairs

set_option autoImplicit false
set_option maxHeartbeats 400000

/-!
# Abstract justification-phase rank model (ROADMAP-12 §10.1.3 support)

States carry a code and a phase label named `quote`, `subst`, or `represent`.
The licensed edges in this file are administrative phase transitions plus a
strict encoded-size decrease on the return edge. They do **not** consume the
live quotation, substitution, or representability relations and therefore do
not by themselves prove semantic transport of those operations. For this
abstract phase machine, every edge strictly decreases the transported
reflective rank and every cycle is impossible. The frozen identity theorem
`quote_self_license_is_refused` is the identity base case.

NameGate: no `goedel_first`, no `incompleteness`, no `feferman_completeness`.
-/

namespace OperatorKO7.Meta.DistinctionBoundary.GodelPartial

open OperatorKO7
open OperatorKO7.Meta.Decision.ReflectiveDependencyPairs
open Multiset

inductive JustifPhase : Type
  | quote
  | subst
  | represent
deriving DecidableEq, Repr

def phaseRank : JustifPhase → Nat
  | .quote => 2
  | .subst => 1
  | .represent => 0

structure QuoteJustifState where
  code : PartialCode
  phase : JustifPhase
deriving DecidableEq

noncomputable def transportedBudget (s : QuoteJustifState) : Nat :=
  3 * sizeOf (encode s.code) + phaseRank s.phase

noncomputable def toMeta (s : QuoteJustifState) : MetaQueryState where
  metaState := sizeOf (encode s.code)
  activeQuery := phaseRank s.phase
  obligations := ({sizeOf (encode s.code)} : Multiset Obligation)
  budget := transportedBudget s

/-- Licensed administrative phase transition: quote-label to subst-label to
represent-label, then a return to quote-label only at a strictly smaller code. -/
inductive LicensedJustification : QuoteJustifState → QuoteJustifState → Prop
  | quoteToSubst (c : PartialCode) :
      LicensedJustification ⟨c, .quote⟩ ⟨c, .subst⟩
  | substToRepresent (c : PartialCode) :
      LicensedJustification ⟨c, .subst⟩ ⟨c, .represent⟩
  | representToQuote {c d : PartialCode}
      (h : sizeOf (encode d) < sizeOf (encode c)) :
      LicensedJustification ⟨c, .represent⟩ ⟨d, .quote⟩

def QuoteJustifStep (s t : QuoteJustifState) : Prop :=
  LicensedJustification s t ∧ ReflectiveStep (toMeta s) (toMeta t)

theorem phaseRank_quoteToSubst (c : PartialCode) :
    transportedBudget ⟨c, .subst⟩ < transportedBudget ⟨c, .quote⟩ := by
  simp [transportedBudget, phaseRank]

theorem phaseRank_substToRepresent (c : PartialCode) :
    transportedBudget ⟨c, .represent⟩ < transportedBudget ⟨c, .subst⟩ := by
  simp [transportedBudget, phaseRank]

theorem phaseRank_representToQuote {c d : PartialCode}
    (h : sizeOf (encode d) < sizeOf (encode c)) :
    transportedBudget ⟨d, .quote⟩ < transportedBudget ⟨c, .represent⟩ := by
  change 3 * sizeOf (encode d) + 2 < 3 * sizeOf (encode c)
  omega

theorem licensed_implies_budgetDrop {s t : QuoteJustifState}
    (h : LicensedJustification s t) :
    (toMeta t).budget < (toMeta s).budget := by
  cases h with
  | quoteToSubst c =>
    simpa [toMeta] using phaseRank_quoteToSubst c
  | substToRepresent c =>
    simpa [toMeta] using phaseRank_substToRepresent c
  | representToQuote hsz =>
    simpa [toMeta] using phaseRank_representToQuote hsz

theorem licensed_to_reflective {s t : QuoteJustifState}
    (h : LicensedJustification s t) :
    ReflectiveStep (toMeta s) (toMeta t) :=
  ReflectiveStep.budgetDrop (licensed_implies_budgetDrop h)

theorem quoteJustif_of_licensed {s t : QuoteJustifState}
    (h : LicensedJustification s t) : QuoteJustifStep s t :=
  ⟨h, licensed_to_reflective h⟩

theorem quoteJustif_strict_rank {s t : QuoteJustifState}
    (h : QuoteJustifStep s t) :
    RankLT (rank (toMeta t)) (rank (toMeta s)) :=
  reflective_pair_strict_rank h.2

theorem quoteJustif_identity_blocked (s : QuoteJustifState) :
    ¬ QuoteJustifStep s s := by
  intro h
  exact identity_reflective_pair_blocked (toMeta s) h.2

theorem quoteJustif_cycle_impossible {s : QuoteJustifState}
    (h : Relation.TransGen QuoteJustifStep s s) : False := by
  have hR : Relation.TransGen ReflectiveStep (toMeta s) (toMeta s) :=
    Relation.TransGen.lift toMeta (fun _ _ hab => hab.2) h
  exact mutual_reflective_cycle_requires_descent hR

/-- Every licensed administrative phase edge decreases the transported rank. -/
theorem every_licensed_edge_decreases_rank {s t : QuoteJustifState}
    (h : LicensedJustification s t) :
    RankLT (rank (toMeta t)) (rank (toMeta s)) :=
  reflective_pair_strict_rank (licensed_to_reflective h)

/-- Frozen identity base case: using a code to license that same code's
representability is an identity reflective pair and is refused. -/
theorem quote_self_license_is_identity_base (c : PartialCode) :
    ¬ ReflectiveStep (quoteTransportState c) (quoteTransportState c) ∧
      WellFounded RankLT :=
  quote_self_license_is_refused c

theorem quote_self_license_on_justif_state (c : PartialCode) :
    ¬ QuoteJustifStep ⟨c, .quote⟩ ⟨c, .quote⟩ :=
  quoteJustif_identity_blocked ⟨c, .quote⟩

theorem quotation_mediated_cycle_impossible (c : PartialCode) :
    ¬ Relation.TransGen QuoteJustifStep ⟨c, .quote⟩ ⟨c, .quote⟩ :=
  fun h => quoteJustif_cycle_impossible h

theorem quote_justif_wf : WellFounded RankLT :=
  wf_RankLT

end OperatorKO7.Meta.DistinctionBoundary.GodelPartial
