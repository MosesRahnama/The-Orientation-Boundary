import OperatorKO7.Meta.UniqueNormalization.DecreasingDMCancellation

/-!
# RTA #79 route R2: residual measured-diagram algebra

The full `MeasuredJoin` inequalities contain a common input prefix.  Additive DM
cancellation turns them into the residual form used in the formal proof of
Lemma 3.5.  This module also proves that strict and non-strict DM comparison are
preserved by the whole-prefix downset filter.

Trust: kernel checked. No external certificate or new axiom.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniqueNormalization

/-- Filtering a strict DM comparison by a whole-prefix downset preserves the
comparison non-strictly. If all strict replacement witnesses are filtered away,
the two filtered multisets become equal; otherwise the surviving witnesses give
a strict DM comparison. -/
theorem dmLe_removeBelowList_of_dmLt
    {M N : Multiset LevelKey} (hMN : Multiset.IsDershowitzMannaLT M N)
    (labels : List LevelLabel) :
    DMLe (removeBelowList M labels) (removeBelowList N labels) := by
  classical
  rcases hMN with ⟨X, Y, Z, hZ, hM, hN, hYZ⟩
  let X' := removeBelowList X labels
  let Y' := removeBelowList Y labels
  let Z' := removeBelowList Z labels
  have hM' : removeBelowList M labels = X' + Y' := by
    rw [hM, removeBelowList_add]
  have hN' : removeBelowList N labels = X' + Z' := by
    rw [hN, removeBelowList_add]
  by_cases hZ' : Z' = 0
  · have hY' : Y' = 0 := by
      by_contra hneY
      obtain ⟨y, hy⟩ : ∃ y, y ∈ Y' := Multiset.exists_mem_of_ne_zero hneY
      have hyFilter : y ∈ Y ∧ ¬ BelowList labels y := by
        simpa [Y', removeBelowList] using hy
      obtain ⟨z, hzZ, hyz⟩ := hYZ y hyFilter.1
      have hzNot : z ∉ Z' := by
        rw [hZ']
        exact Multiset.notMem_zero z
      have hzRemoved : BelowList labels z := by
        by_contra hzBelow
        apply hzNot
        simp [Z', removeBelowList, hzZ, hzBelow]
      rcases hzRemoved with ⟨a, ha, hza⟩
      have hyRemoved : BelowList labels y := ⟨a, ha, hyz.trans hza⟩
      exact hyFilter.2 hyRemoved
    rw [hM', hN', hY', hZ']
  · have hYZ' : ∀ y ∈ Y', ∃ z ∈ Z', y < z := by
      intro y hy
      have hyFilter : y ∈ Y ∧ ¬ BelowList labels y := by
        simpa [Y', removeBelowList] using hy
      obtain ⟨z, hzZ, hyz⟩ := hYZ y hyFilter.1
      have hzKeep : ¬ BelowList labels z := by
        intro hzBelow
        rcases hzBelow with ⟨a, ha, hza⟩
        exact hyFilter.2 ⟨a, ha, hyz.trans hza⟩
      exact ⟨z, by simp [Z', removeBelowList, hzZ, hzKeep], hyz⟩
    apply DMLe.of_lt
    refine ⟨X', Y', Z', hZ', hM', hN', hYZ'⟩

/-- Whole-prefix filtering is monotone for the non-strict DM order. -/
theorem DMLe.removeBelowList {M N : Multiset LevelKey}
    (hMN : DMLe M N) (labels : List LevelLabel) :
    DMLe (removeBelowList M labels) (removeBelowList N labels) := by
  rcases dmLe_iff_eq_or_lt.mp hMN with hEq | hlt
  · subst N
    exact DMLe.refl _
  · exact dmLe_removeBelowList_of_dmLt hlt labels

/-- Residual left-arm form of a measured diagram. -/
theorem MeasuredJoin.leftResidual
    {State : Type*} {step : LabelledStep State LevelLabel}
    {tau sigma : List LevelLabel} {x y : State}
    (D : MeasuredJoin step tau sigma x y) :
    DMLe (removeBelowList (lexMax D.leftOutput) tau) (lexMax sigma) := by
  have h := D.leftMeasure
  rw [lexMax_append] at h
  change DMLe
    (lexMax tau + removeBelowList (lexMax D.leftOutput) tau)
    (lexMax tau + lexMax sigma) at h
  exact DMLe.cancel_left (lexMax tau) h

/-- Residual right-arm form of a measured diagram. -/
theorem MeasuredJoin.rightResidual
    {State : Type*} {step : LabelledStep State LevelLabel}
    {tau sigma : List LevelLabel} {x y : State}
    (D : MeasuredJoin step tau sigma x y) :
    DMLe (removeBelowList (lexMax D.rightOutput) sigma) (lexMax tau) := by
  have h := D.rightMeasure
  rw [lexMax_append] at h
  have h' : DMLe
      (lexMax sigma + removeBelowList (lexMax D.rightOutput) sigma)
      (lexMax sigma + lexMax tau) := by
    simpa [peakMeasure, add_comm] using h
  exact DMLe.cancel_left (lexMax sigma) h'

/-- Rebuild the full left-arm measured inequality from its residual form. -/
theorem measuredLeft_of_residual
    {tau sigma output : List LevelLabel}
    (h : DMLe (removeBelowList (lexMax output) tau) (lexMax sigma)) :
    DMLe (lexMax (tau ++ output)) (peakMeasure (tau, sigma)) := by
  have h' := DMLe.add_left (lexMax tau) h
  rw [lexMax_append]
  simpa [peakMeasure] using h'

/-- Rebuild the full right-arm measured inequality from its residual form. -/
theorem measuredRight_of_residual
    {tau sigma output : List LevelLabel}
    (h : DMLe (removeBelowList (lexMax output) sigma) (lexMax tau)) :
    DMLe (lexMax (sigma ++ output)) (peakMeasure (tau, sigma)) := by
  have h' := DMLe.add_left (lexMax sigma) h
  rw [lexMax_append]
  simpa [peakMeasure, add_comm] using h'

end OperatorKO7.Meta.UniqueNormalization

#check @OperatorKO7.Meta.UniqueNormalization.dmLe_removeBelowList_of_dmLt
#check @OperatorKO7.Meta.UniqueNormalization.DMLe.removeBelowList
#check @OperatorKO7.Meta.UniqueNormalization.MeasuredJoin.leftResidual
#check @OperatorKO7.Meta.UniqueNormalization.MeasuredJoin.rightResidual
#check @OperatorKO7.Meta.UniqueNormalization.measuredLeft_of_residual
#check @OperatorKO7.Meta.UniqueNormalization.measuredRight_of_residual

#print axioms OperatorKO7.Meta.UniqueNormalization.dmLe_removeBelowList_of_dmLt
#print axioms OperatorKO7.Meta.UniqueNormalization.DMLe.removeBelowList
#print axioms OperatorKO7.Meta.UniqueNormalization.MeasuredJoin.leftResidual
#print axioms OperatorKO7.Meta.UniqueNormalization.MeasuredJoin.rightResidual
#print axioms OperatorKO7.Meta.UniqueNormalization.measuredLeft_of_residual
#print axioms OperatorKO7.Meta.UniqueNormalization.measuredRight_of_residual
