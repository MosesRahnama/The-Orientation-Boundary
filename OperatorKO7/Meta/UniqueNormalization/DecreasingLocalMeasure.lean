import OperatorKO7.Meta.UniqueNormalization.DecreasingSequenceMeasure

/-!
# RTA #79 route R2: local decreasing valleys satisfy the global induction measure

This module is the Lean analogue of Proposition 3.4 in the valley proof of
decreasing diagrams.  It converts the exact local `DecreasingValley` carrier
into labelled joining paths and proves that each completed arm is below or equal
to the original two-label peak in the lexicographic-maximum multiset order.

Trust: kernel checked. No external certificate or new axiom.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniqueNormalization

universe u

variable {State : Type u}

/-- Reflexive-transitive closure of the Dershowitz-Manna strict multiset order. -/
abbrev DMLe (M N : Multiset LevelKey) : Prop :=
  Relation.ReflTransGen Multiset.IsDershowitzMannaLT M N

namespace DMLe

/-- Reflexivity of the multiset non-strict order. -/
theorem refl (M : Multiset LevelKey) : DMLe M M :=
  Relation.ReflTransGen.refl

/-- One strict Dershowitz-Manna decrease gives a non-strict decrease. -/
theorem of_lt {M N : Multiset LevelKey}
    (h : Multiset.IsDershowitzMannaLT M N) : DMLe M N :=
  Relation.ReflTransGen.single h

/-- Transitivity. -/
theorem trans {M N P : Multiset LevelKey} (hMN : DMLe M N) (hNP : DMLe N P) :
    DMLe M P :=
  Relation.ReflTransGen.trans hMN hNP

end DMLe

/-- Adding the same multiset on the left preserves a strict DM decrease. -/
theorem dmLt_add_left (K : Multiset LevelKey) {M N : Multiset LevelKey}
    (h : Multiset.IsDershowitzMannaLT M N) :
    Multiset.IsDershowitzMannaLT (K + M) (K + N) := by
  rcases h with ⟨X, Y, Z, hZ, hM, hN, hYZ⟩
  refine ⟨K + X, Y, Z, hZ, ?_, ?_, hYZ⟩
  · rw [hM]
    ac_rfl
  · rw [hN]
    ac_rfl

/-- Adding the same multiset on the right preserves a strict DM decrease. -/
theorem dmLt_add_right (K : Multiset LevelKey) {M N : Multiset LevelKey}
    (h : Multiset.IsDershowitzMannaLT M N) :
    Multiset.IsDershowitzMannaLT (M + K) (N + K) := by
  simpa [add_comm] using dmLt_add_left K h

/-- Adding the same multiset on the left preserves the reflexive-transitive DM
order. -/
theorem DMLe.add_left (K : Multiset LevelKey) {M N : Multiset LevelKey}
    (h : DMLe M N) : DMLe (K + M) (K + N) := by
  induction h with
  | refl => exact DMLe.refl _
  | tail _ hlast ih =>
      exact Relation.ReflTransGen.tail ih (dmLt_add_left K hlast)

/-- The strict multiset order below a singleton follows from pointwise strict
boundedness. -/
theorem dmLt_singleton_of_all_lt {M : Multiset LevelKey} {a : LevelKey}
    (h : ∀ x ∈ M, x < a) :
    Multiset.IsDershowitzMannaLT M ({a} : Multiset LevelKey) := by
  refine ⟨0, M, {a}, by simp, by simp, by simp, ?_⟩
  intro x hx
  exact ⟨a, by simp, h x hx⟩

/-- Filtering first below a smaller cutoff and then below a larger cutoff is the
same as filtering only below the larger cutoff. -/
theorem removeBelow_removeBelow_of_lt {M : Multiset LevelKey} {c a : LevelKey}
    (hca : c < a) :
    removeBelow (removeBelow M c) a = removeBelow M a := by
  ext x
  simp only [removeBelow, Multiset.count_filter]
  by_cases hxa : x < a
  · simp [hxa]
  · have hxc : ¬ x < c := by
      intro h
      exact hxa (h.trans hca)
    simp [hxa, hxc]

/-- A prefix consisting only of labels below `a` has no effect after the whole
suffix measure is filtered below `a`. -/
theorem removeBelow_lexMax_append_of_allBelow
    {a : LevelLabel} {low rest : List LevelLabel}
    (hlow : AllBelow a low) :
    removeBelow (lexMax (low ++ rest)) a.toKey =
      removeBelow (lexMax rest) a.toKey := by
  induction low with
  | nil => simp
  | cons c low ih =>
      have hca : c.toKey < a.toKey :=
        levelLabel_toKey_lt_iff.mpr (hlow c (by simp))
      have htail : AllBelow a low := by
        intro d hd
        exact hlow d (by simp [hd])
      rw [List.cons_append, lexMax_cons]
      simp only [removeBelow, Multiset.filter_add]
      have hsingle : Multiset.filter (fun x => ¬ x < a.toKey) ({c.toKey} : Multiset LevelKey) = 0 := by
        apply Multiset.filter_eq_nil.mpr
        intro x hx
        simp only [Multiset.mem_singleton] at hx
        subst x
        exact fun hnot => hnot hca
      rw [hsingle, zero_add]
      change removeBelow (removeBelow (lexMax (low ++ rest)) c.toKey) a.toKey = _
      rw [removeBelow_removeBelow_of_lt hca, ih htail]
      rfl

/-- If every source label is below `a` or `b`, nothing survives filtering below
both cutoffs. -/
theorem removeBelow_removeBelow_lexMax_eq_zero_of_allBelowEither
    {a b : LevelLabel} {labels : List LevelLabel}
    (h : AllBelowEither a b labels) :
    removeBelow (removeBelow (lexMax labels) b.toKey) a.toKey = 0 := by
  ext x
  simp only [removeBelow, Multiset.count_filter, Multiset.count_zero]
  by_cases hxa : x < a.toKey
  · simp [hxa]
  · by_cases hxb : x < b.toKey
    · simp [hxa, hxb]
    · have hxnot : x ∉ lexMax labels := by
        intro hx
        obtain ⟨c, hc, hxc⟩ := mem_lexMax_source hx
        subst hxc
        rcases h c hc with hca | hcb
        · exact hxa (levelLabel_toKey_lt_iff.mpr hca)
        · exact hxb (levelLabel_toKey_lt_iff.mpr hcb)
      have hcount : Multiset.count x (lexMax labels) = 0 :=
        Multiset.count_eq_zero.mpr hxnot
      simp [hxa, hxb, hcount]

/-- An optional exact-labelled step is represented by either the empty label
list or the singleton label list. -/
theorem exists_lPath_of_optionalLabelStep
    {step : LabelledStep State LevelLabel} {a : LevelLabel} {x y : State}
    (h : OptionalLabelStep step a x y) :
    ∃ labels : List LevelLabel,
      LPath step x y labels ∧ (labels = [] ∨ labels = [a]) := by
  rcases h with hxy | hstep
  · subst hxy
    exact ⟨[], LPath.refl _, Or.inl rfl⟩
  · exact ⟨[a], LPath.cons hstep (LPath.refl _), Or.inr rfl⟩

/-- The left local valley branch has measure at most the original two-label
peak. `opt = []` is a strict decrease; `opt = [b]` may be equality. -/
theorem local_left_measure_bound
    {a b : LevelLabel} {lowA opt lowBoth : List LevelLabel}
    (hA : AllBelow a lowA)
    (hopt : opt = [] ∨ opt = [b])
    (hBoth : AllBelowEither a b lowBoth) :
    DMLe
      (lexMax ([a] ++ (lowA ++ opt ++ lowBoth)))
      (peakMeasure ([a], [b])) := by
  have hignore := removeBelow_lexMax_append_of_allBelow
    (a := a) (low := lowA) (rest := opt ++ lowBoth) hA
  simp only [List.singleton_append, List.append_assoc, peakMeasure,
    lexMax_singleton]
  rw [lexMax_cons, hignore]
  rcases hopt with rfl | rfl
  · -- No optional b: every surviving lower label is below b.
    have hall : ∀ x ∈ removeBelow (lexMax lowBoth) a.toKey, x < b.toKey := by
      intro x hx
      simp only [removeBelow, Multiset.mem_filter] at hx
      obtain ⟨c, hc, rfl⟩ := mem_lexMax_source hx.1
      rcases hBoth c hc with hca | hcb
      · exact False.elim (hx.2 (levelLabel_toKey_lt_iff.mpr hca))
      · exact levelLabel_toKey_lt_iff.mpr hcb
    exact DMLe.of_lt <| dmLt_add_left {a.toKey} (dmLt_singleton_of_all_lt hall)
  · -- Optional b present: lower-both labels disappear after the two filters.
    change DMLe
      ({a.toKey} + removeBelow (lexMax (b :: lowBoth)) a.toKey)
      ({a.toKey} + {b.toKey})
    rw [lexMax_cons]
    simp only [removeBelow, Multiset.filter_add]
    have hzero := removeBelow_removeBelow_lexMax_eq_zero_of_allBelowEither hBoth
    change
      DMLe
        ({a.toKey} +
          (Multiset.filter (fun x => ¬ x < a.toKey) ({b.toKey} : Multiset LevelKey) +
            removeBelow (removeBelow (lexMax lowBoth) b.toKey) a.toKey))
        ({a.toKey} + {b.toKey})
    rw [hzero, add_zero]
    by_cases hba : b.toKey < a.toKey
    · have hfilter :
          Multiset.filter (fun x => ¬ x < a.toKey) ({b.toKey} : Multiset LevelKey) = 0 := by
        apply Multiset.filter_eq_nil.mpr
        intro x hx
        simp only [Multiset.mem_singleton] at hx
        subst x
        exact fun hnot => hnot hba
      rw [hfilter]
      exact DMLe.of_lt <| dmLt_add_left {a.toKey} (dmLt_singleton_of_all_lt (by simp))
    · have hfilter :
          Multiset.filter (fun x => ¬ x < a.toKey) ({b.toKey} : Multiset LevelKey) = {b.toKey} := by
        apply Multiset.filter_eq_self.mpr
        intro x hx
        simp only [Multiset.mem_singleton] at hx
        subst x
        exact hba
      rw [hfilter]

/-- Right-hand mirror of `local_left_measure_bound`. -/
theorem local_right_measure_bound
    {a b : LevelLabel} {lowB opt lowBoth : List LevelLabel}
    (hB : AllBelow b lowB)
    (hopt : opt = [] ∨ opt = [a])
    (hBoth : AllBelowEither a b lowBoth) :
    DMLe
      (lexMax ([b] ++ (lowB ++ opt ++ lowBoth)))
      (peakMeasure ([a], [b])) := by
  have h := local_left_measure_bound
    (a := b) (b := a) (lowA := lowB) (opt := opt) (lowBoth := lowBoth)
    hB hopt (by
      intro c hc
      rcases hBoth c hc with hca | hcb
      · exact Or.inr hca
      · exact Or.inl hcb)
  simpa [peakMeasure, add_comm] using h

/-- A measured joining diagram for two labelled input paths. -/
structure MeasuredJoin (step : LabelledStep State LevelLabel)
    (leftInput rightInput : List LevelLabel) (left right : State) where
  join : State
  leftOutput : List LevelLabel
  rightOutput : List LevelLabel
  leftPath : LPath step left join leftOutput
  rightPath : LPath step right join rightOutput
  leftMeasure : DMLe (lexMax (leftInput ++ leftOutput))
    (peakMeasure (leftInput, rightInput))
  rightMeasure : DMLe (lexMax (rightInput ++ rightOutput))
    (peakMeasure (leftInput, rightInput))

/-- **Local measured-diagram theorem.** Every route-R2 decreasing local valley
produces a measured join satisfying the global lexicographic-maximum induction
bound. -/
theorem LocalPeak.measuredJoin_of_decreasing
    {step : LabelledStep State LevelLabel} (peak : LocalPeak step)
    (hdec : peak.Decreasing LevelLabelLt) :
    Nonempty (MeasuredJoin step [peak.leftLabel] [peak.rightLabel]
      peak.left peak.right) := by
  rcases hdec with ⟨valley⟩
  obtain ⟨lowA, hLowA, hAllA⟩ :=
    exists_lPath_allBelow_of_star_stepBelow valley.leftLow
  obtain ⟨optB, hOptB, hOptBshape⟩ :=
    exists_lPath_of_optionalLabelStep valley.leftPeakLabel
  obtain ⟨lowBothL, hBothL, hAllBothL⟩ :=
    exists_lPath_allBelowEither_of_star_stepBelowEither valley.leftBoth
  obtain ⟨lowB, hLowB, hAllB⟩ :=
    exists_lPath_allBelow_of_star_stepBelow valley.rightLow
  obtain ⟨optA, hOptA, hOptAshape⟩ :=
    exists_lPath_of_optionalLabelStep valley.rightPeakLabel
  obtain ⟨lowBothR, hBothR, hAllBothR⟩ :=
    exists_lPath_allBelowEither_of_star_stepBelowEither valley.rightBoth
  refine ⟨{
    join := valley.join
    leftOutput := lowA ++ optB ++ lowBothL
    rightOutput := lowB ++ optA ++ lowBothR
    leftPath := by
      simpa [List.append_assoc] using hLowA.trans (hOptB.trans hBothL)
    rightPath := by
      simpa [List.append_assoc] using hLowB.trans (hOptA.trans hBothR)
    leftMeasure := local_left_measure_bound hAllA hOptBshape hAllBothL
    rightMeasure := local_right_measure_bound hAllB hOptAshape hAllBothR
  }⟩

end OperatorKO7.Meta.UniqueNormalization

#check @OperatorKO7.Meta.UniqueNormalization.DMLe
#check @OperatorKO7.Meta.UniqueNormalization.DMLe.refl
#check @OperatorKO7.Meta.UniqueNormalization.DMLe.of_lt
#check @OperatorKO7.Meta.UniqueNormalization.DMLe.trans
#check @OperatorKO7.Meta.UniqueNormalization.dmLt_add_left
#check @OperatorKO7.Meta.UniqueNormalization.dmLt_add_right
#check @OperatorKO7.Meta.UniqueNormalization.DMLe.add_left
#check @OperatorKO7.Meta.UniqueNormalization.dmLt_singleton_of_all_lt
#check @OperatorKO7.Meta.UniqueNormalization.removeBelow_removeBelow_of_lt
#check @OperatorKO7.Meta.UniqueNormalization.removeBelow_lexMax_append_of_allBelow
#check @OperatorKO7.Meta.UniqueNormalization.removeBelow_removeBelow_lexMax_eq_zero_of_allBelowEither
#check @OperatorKO7.Meta.UniqueNormalization.exists_lPath_of_optionalLabelStep
#check @OperatorKO7.Meta.UniqueNormalization.local_left_measure_bound
#check @OperatorKO7.Meta.UniqueNormalization.local_right_measure_bound
#check @OperatorKO7.Meta.UniqueNormalization.MeasuredJoin
#check @OperatorKO7.Meta.UniqueNormalization.LocalPeak.measuredJoin_of_decreasing

#print axioms OperatorKO7.Meta.UniqueNormalization.DMLe.refl
#print axioms OperatorKO7.Meta.UniqueNormalization.DMLe.of_lt
#print axioms OperatorKO7.Meta.UniqueNormalization.DMLe.trans
#print axioms OperatorKO7.Meta.UniqueNormalization.dmLt_add_left
#print axioms OperatorKO7.Meta.UniqueNormalization.dmLt_add_right
#print axioms OperatorKO7.Meta.UniqueNormalization.DMLe.add_left
#print axioms OperatorKO7.Meta.UniqueNormalization.dmLt_singleton_of_all_lt
#print axioms OperatorKO7.Meta.UniqueNormalization.removeBelow_removeBelow_of_lt
#print axioms OperatorKO7.Meta.UniqueNormalization.removeBelow_lexMax_append_of_allBelow
#print axioms OperatorKO7.Meta.UniqueNormalization.removeBelow_removeBelow_lexMax_eq_zero_of_allBelowEither
#print axioms OperatorKO7.Meta.UniqueNormalization.exists_lPath_of_optionalLabelStep
#print axioms OperatorKO7.Meta.UniqueNormalization.local_left_measure_bound
#print axioms OperatorKO7.Meta.UniqueNormalization.local_right_measure_bound
#print axioms OperatorKO7.Meta.UniqueNormalization.LocalPeak.measuredJoin_of_decreasing
