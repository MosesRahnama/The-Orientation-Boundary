/-!
This module defines two local finite enums and proves their list lengths, distinctness, and
constructor membership. Correspondence with an external catalog or legal doctrine requires a
separate generated check.












-/

namespace OperatorKO7.Meta.Plugs.LawUSStateCA

/-- Carrier with the constructors displayed below.




-/
inductive LawUSStateCAW1Route
  | AuerDeferenceCalifornia
  | ChevronStepOneCalifornia
  | SkidmoreDeferenceCalifornia
  | SlidingScaleBalancingCa
  | LenityRuleCalifornia
  deriving DecidableEq, Repr

/-- Carrier with the constructors displayed below.
-/
inductive LawUSStateCAW2Route
  | JudicialNoticeEscape
  | CertifiedQuestionToCaSupreme
  | CircuitSplitAcknowledgment
  deriving DecidableEq, Repr

/-- Definition with formal content given by the displayed type and body. -/
def lawUSStateCAW1Routes : List LawUSStateCAW1Route :=
  [ .AuerDeferenceCalifornia
  , .ChevronStepOneCalifornia
  , .SkidmoreDeferenceCalifornia
  , .SlidingScaleBalancingCa
  , .LenityRuleCalifornia
  ]

/-- Definition with formal content given by the displayed type and body. -/
def lawUSStateCAW2Routes : List LawUSStateCAW2Route :=
  [ .JudicialNoticeEscape
  , .CertifiedQuestionToCaSupreme
  , .CircuitSplitAcknowledgment
  ]

theorem lawUSStateCAW1Routes_length :
    lawUSStateCAW1Routes.length = 5 := by decide

theorem lawUSStateCAW2Routes_length :
    lawUSStateCAW2Routes.length = 3 := by decide

theorem lawUSStateCAW1Routes_nodup :
    lawUSStateCAW1Routes.Nodup := by decide

theorem lawUSStateCAW2Routes_nodup :
    lawUSStateCAW2Routes.Nodup := by decide

theorem lawUSStateCAW1Routes_complete_exact (r : LawUSStateCAW1Route) :
    r ∈ lawUSStateCAW1Routes ↔
      r = .AuerDeferenceCalifornia ∨
      r = .ChevronStepOneCalifornia ∨
      r = .SkidmoreDeferenceCalifornia ∨
      r = .SlidingScaleBalancingCa ∨
      r = .LenityRuleCalifornia := by
  cases r <;> decide

theorem lawUSStateCAW2Routes_complete_exact (r : LawUSStateCAW2Route) :
    r ∈ lawUSStateCAW2Routes ↔
      r = .JudicialNoticeEscape ∨
      r = .CertifiedQuestionToCaSupreme ∨
      r = .CircuitSplitAcknowledgment := by
  cases r <;> decide

end OperatorKO7.Meta.Plugs.LawUSStateCA
