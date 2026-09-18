import OperatorKO7.Meta.DistinctionBoundary.MinimalFork.EqW.Context

/-!
# Strong normalization and exact-length bounds for all four minimal EqW relations

Each relation is proved separately. The measure is purely structural: every
root contraction removes one `eqW`, and contextual lifting preserves that strict
decrease. The same fact gives an explicit upper bound on every exact-length path.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.DistinctionBoundary.MinimalFork

open OperatorKO7.Meta.DistinctionBoundary.Quantitative

/-- Roadmap-stable name for the number of equality-witness nodes. -/
abbrev eqWCount : MiniEqWTerm → Nat := miniEqWCount

/-- Every raw root contraction strictly lowers the query count. -/
theorem miniEqW_rawRoot_count_decreases {s t : MiniEqWTerm}
    (h : MiniEqWRootStep s t) : miniEqWCount t < miniEqWCount s := by
  cases h <;> simp [miniEqWCount]

/-- Every guarded root contraction strictly lowers the query count. -/
theorem miniEqW_guardedRoot_count_decreases {s t : MiniEqWTerm}
    (h : MiniEqWGuardedRootStep s t) : miniEqWCount t < miniEqWCount s := by
  cases h <;> simp [miniEqWCount]

/-- Every raw contextual contraction strictly lowers the query count. -/
theorem miniEqW_rawCtx_count_decreases {s t : MiniEqWTerm}
    (h : MiniEqWCtxStep s t) : miniEqWCount t < miniEqWCount s := by
  induction h with
  | root hr => exact miniEqW_rawRoot_count_decreases hr
  | left _ ih =>
      simp only [miniEqWCount]
      omega
  | right _ ih =>
      simp only [miniEqWCount]
      omega

/-- Every guarded contextual contraction strictly lowers the query count. -/
theorem miniEqW_guardedCtx_count_decreases {s t : MiniEqWTerm}
    (h : MiniEqWGuardedCtxStep s t) : miniEqWCount t < miniEqWCount s := by
  induction h with
  | root hr => exact miniEqW_guardedRoot_count_decreases hr
  | left _ ih =>
      simp only [miniEqWCount]
      omega
  | right _ ih =>
      simp only [miniEqWCount]
      omega

/-- Generic natural-measure termination constructor, explicitly oriented for
`WellFounded (flip R)`. -/
theorem wf_flip_of_nat_decrease
    {T : Type} {R : T → T → Prop} (m : T → Nat)
    (hdec : ∀ {s t}, R s t → m t < m s) :
    WellFounded (flip R) := by
  have hsub : Subrelation (flip R) (InvImage (· < ·) m) := by
    intro x y hxy
    exact hdec hxy
  exact hsub.wf (InvImage.wf m Nat.lt_wfRel.wf)

/-- Raw root strong normalization. -/
theorem minimalEqW_root_SN : WellFounded (flip MiniEqWRootStep) :=
  wf_flip_of_nat_decrease miniEqWCount miniEqW_rawRoot_count_decreases

/-- Roadmap-stable raw-root decrease theorem. -/
theorem root_count_decreases {s t : MiniEqWTerm}
    (h : MiniEqWRootStep s t) : eqWCount t < eqWCount s :=
  miniEqW_rawRoot_count_decreases h

/-- Roadmap-stable raw-context decrease theorem. -/
theorem ctx_count_decreases {s t : MiniEqWTerm}
    (h : MiniEqWCtxStep s t) : eqWCount t < eqWCount s :=
  miniEqW_rawCtx_count_decreases h

/-- Guarded root strong normalization. -/
theorem minimalEqW_guarded_root_SN : WellFounded (flip MiniEqWGuardedRootStep) :=
  wf_flip_of_nat_decrease miniEqWCount miniEqW_guardedRoot_count_decreases

/-- Raw unrestricted-context strong normalization. -/
theorem minimalEqW_context_SN : WellFounded (flip MiniEqWCtxStep) :=
  wf_flip_of_nat_decrease miniEqWCount miniEqW_rawCtx_count_decreases

/-- Guarded unrestricted-context strong normalization. -/
theorem minimalEqW_guarded_context_SN : WellFounded (flip MiniEqWGuardedCtxStep) :=
  wf_flip_of_nat_decrease miniEqWCount miniEqW_guardedCtx_count_decreases

/-- A strictly decreasing natural measure bounds the length of every exact path. -/
theorem steps_length_le_nat_measure
    {T : Type} {R : T → T → Prop} (m : T → Nat)
    (hdec : ∀ {s t}, R s t → m t < m s)
    {n : Nat} {s t : T} (h : Steps R n s t) : n ≤ m s := by
  induction h with
  | zero => simp
  | @succ n x y z hxy hyz ih =>
      have hd : m y < m x := hdec hxy
      omega

/-- Any exact path in a caller-specified minimal-term relation is bounded by
`eqWCount` whenever every one-step edge strictly lowers that count. -/
theorem steps_length_le_eqWCount
    {R : MiniEqWTerm → MiniEqWTerm → Prop}
    (hdec : ∀ {s t}, R s t → eqWCount t < eqWCount s)
    {n : Nat} {s t : MiniEqWTerm} (h : Steps R n s t) :
    n ≤ eqWCount s :=
  steps_length_le_nat_measure eqWCount hdec h

/-- Raw-root derivations are bounded by the initial query count. -/
theorem miniEqW_rawRoot_steps_length_le_count
    {n : Nat} {s t : MiniEqWTerm} (h : Steps MiniEqWRootStep n s t) :
    n ≤ miniEqWCount s :=
  steps_length_le_nat_measure miniEqWCount miniEqW_rawRoot_count_decreases h

/-- Guarded-root derivations are bounded by the initial query count. -/
theorem miniEqW_guardedRoot_steps_length_le_count
    {n : Nat} {s t : MiniEqWTerm} (h : Steps MiniEqWGuardedRootStep n s t) :
    n ≤ miniEqWCount s :=
  steps_length_le_nat_measure miniEqWCount miniEqW_guardedRoot_count_decreases h

/-- Raw-context derivations are bounded by the initial query count. -/
theorem miniEqW_rawCtx_steps_length_le_count
    {n : Nat} {s t : MiniEqWTerm} (h : Steps MiniEqWCtxStep n s t) :
    n ≤ miniEqWCount s :=
  steps_length_le_nat_measure miniEqWCount miniEqW_rawCtx_count_decreases h

/-- Guarded-context derivations are bounded by the initial query count. -/
theorem miniEqW_guardedCtx_steps_length_le_count
    {n : Nat} {s t : MiniEqWTerm} (h : Steps MiniEqWGuardedCtxStep n s t) :
    n ≤ miniEqWCount s :=
  steps_length_le_nat_measure miniEqWCount miniEqW_guardedCtx_count_decreases h

end OperatorKO7.Meta.DistinctionBoundary.MinimalFork
