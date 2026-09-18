import OperatorKO7.Meta.UniqueNormalization.DecreasingLocalMeasure

/-!
# RTA #79 route R2: strict recursive subpeak decrease

This module proves the route-R2 specialization of Lemma 3.6 in the valley proof
of decreasing diagrams.  Because `LevelLabelLt` is a total lexicographic order,
the proof can use the exact structural shape of `DecreasingValley` instead of a
generic multiset-cancellation theorem.

For the left branch of a local peak labelled `a,b`, any continuation `tail`
forms a strictly smaller recursive peak against the local left joining path:

`measure(tail, localLeft) < measure(a :: tail, [b])`.

The right-hand theorem is the mirror image.  These are the strict induction
edges consumed by the global peak tiling theorem.

Trust: kernel checked. No external certificate or new axiom.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniqueNormalization

universe u

variable {State : Type u}

/-- The part of a multiset strictly below one peak label. -/
def belowPart (a : LevelLabel) (M : Multiset LevelKey) : Multiset LevelKey :=
  M.filter (fun x => x < a.toKey)

/-- Splitting at one peak label partitions a multiset into the below part and the
surviving `removeBelow` part. -/
theorem belowPart_add_removeBelow (a : LevelLabel) (M : Multiset LevelKey) :
    belowPart a M + removeBelow M a.toKey = M :=
  Multiset.filter_add_not (fun x => x < a.toKey) M

/-- If every source label is below `a`, nothing in its `lexMax` survives the
`removeBelow _ a` filter. -/
theorem removeBelow_lexMax_eq_zero_of_allBelow
    {a : LevelLabel} {labels : List LevelLabel} (h : AllBelow a labels) :
    removeBelow (lexMax labels) a.toKey = 0 := by
  apply Multiset.filter_eq_nil.mpr
  intro x hx
  obtain ⟨c, hc, rfl⟩ := mem_lexMax_source hx
  exact fun hnot => hnot (levelLabel_toKey_lt_iff.mpr (h c hc))

/-- If a low prefix and low suffix are both strictly below `b`, inserting `b`
between them makes `b` the only new lexicographic-maximum contribution after the
prefix. -/
theorem lexMax_low_append_peak_low
    {b : LevelLabel} {lowPrefix lowSuffix : List LevelLabel}
    (hpre : AllBelow b lowPrefix) (hsuf : AllBelow b lowSuffix) :
    lexMax (lowPrefix ++ [b] ++ lowSuffix) = lexMax lowPrefix + {b.toKey} := by
  induction lowPrefix with
  | nil =>
      simp only [List.nil_append, List.singleton_append, lexMax_cons, lexMax_nil, zero_add]
      rw [removeBelow_lexMax_eq_zero_of_allBelow hsuf]
      simp
  | cons c low ih =>
      have hcb : c.toKey < b.toKey :=
        levelLabel_toKey_lt_iff.mpr (hpre c (by simp))
      have htail : AllBelow b low := by
        intro d hd
        exact hpre d (by simp [hd])
      -- `List.append` recurses on its first argument, so peeling the head is
      -- definitional and keeps the left-associated shape the hypothesis has.
      have hpeel : ((c :: low) ++ [b]) ++ lowSuffix
          = c :: ((low ++ [b]) ++ lowSuffix) := rfl
      rw [hpeel, lexMax_cons, ih htail, lexMax_cons]
      simp only [removeBelow, Multiset.filter_add, Multiset.filter_singleton]
      have hnot : ¬ b.toKey < c.toKey := not_lt_of_ge (le_of_lt hcb)
      rw [if_pos hnot]
      ac_rfl

/-- Labels in `lowA ++ lowBoth` are below at least one of the two peak labels. -/
theorem allBelowEither_low_append
    {a b : LevelLabel} {lowA lowBoth : List LevelLabel}
    (hA : AllBelow a lowA) (hBoth : AllBelowEither a b lowBoth) :
    AllBelowEither a b (lowA ++ lowBoth) := by
  intro c hc
  simp only [List.mem_append] at hc
  rcases hc with hc | hc
  · exact Or.inl (hA c hc)
  · exact hBoth c hc

/-- If the optional opposite label `b` is itself below `a`, every label in the
whole left local output is below `a` or `b`. -/
theorem allBelowEither_low_peak_low_of_peak_lt
    {a b : LevelLabel} {lowA lowBoth : List LevelLabel}
    (hA : AllBelow a lowA) (hBoth : AllBelowEither a b lowBoth)
    (hba : LevelLabelLt b a) :
    AllBelowEither a b (lowA ++ [b] ++ lowBoth) := by
  intro c hc
  -- `(lowA ++ [b]) ++ lowBoth`, so membership splits left-associated.
  simp only [List.mem_append, List.mem_singleton] at hc
  rcases hc with (hc | rfl) | hc
  · exact Or.inl (hA c hc)
  · exact Or.inl hba
  · exact hBoth c hc

/-- If `b` is not below `a`, then all labels in the low prefix and low suffix are
strictly below `b`. -/
theorem allBelow_b_of_not_below
    {a b : LevelLabel} {lowA lowBoth : List LevelLabel}
    (hA : AllBelow a lowA) (hBoth : AllBelowEither a b lowBoth)
    (hba : ¬ LevelLabelLt b a) :
    AllBelow b lowA ∧ AllBelow b lowBoth := by
  have hab : a.toKey ≤ b.toKey := by
    exact le_of_not_gt (fun h => hba (levelLabel_toKey_lt_iff.mp h))
  constructor
  · intro c hc
    have hca : c.toKey < a.toKey := levelLabel_toKey_lt_iff.mpr (hA c hc)
    exact levelLabel_toKey_lt_iff.mp (hca.trans_le hab)
  · intro c hc
    rcases hBoth c hc with hca | hcb
    · have hca' : c.toKey < a.toKey := levelLabel_toKey_lt_iff.mpr hca
      exact levelLabel_toKey_lt_iff.mp (hca'.trans_le hab)
    · exact hcb

/-- Direct DM witness when every local-output lexicographic maximum is below one
of the two peak labels. -/
theorem strict_subpeak_of_allBelowEither
    {a b : LevelLabel} {tail output : List LevelLabel}
    (hout : AllBelowEither a b output) :
    PeakMeasureLt (tail, output) (a :: tail, [b]) := by
  let U := lexMax tail
  let B := belowPart a U
  let O := removeBelow U a.toKey
  have hpart : B + O = U := belowPart_add_removeBelow a U
  refine ⟨O, B + lexMax output, {a.toKey, b.toKey}, by simp, ?_, ?_, ?_⟩
  · change U + lexMax output = O + (B + lexMax output)
    rw [← hpart]
    ac_rfl
  · change ({a.toKey} + O) + {b.toKey} = O + {a.toKey, b.toKey}
    ac_rfl
  · intro y hy
    simp only [Multiset.mem_add] at hy
    rcases hy with hyB | hyOut
    · have hyB' : y < a.toKey := (Multiset.mem_filter.mp hyB).2
      exact ⟨a.toKey, by simp, hyB'⟩
    · obtain ⟨c, hc, rfl⟩ := mem_lexMax_source hyOut
      rcases hout c hc with hca | hcb
      · exact ⟨a.toKey, by simp, levelLabel_toKey_lt_iff.mpr hca⟩
      · exact ⟨b.toKey, by simp, levelLabel_toKey_lt_iff.mpr hcb⟩

/-- Direct DM witness in the only nontrivial cancellation case: `b` survives as
the unique optional opposite peak label, is put into the common multiset, and
`a` remains the nonempty removed multiset. -/
theorem strict_subpeak_of_surviving_peak
    {a b : LevelLabel} {tail lowA lowBoth : List LevelLabel}
    (hA : AllBelow a lowA) (hBoth : AllBelowEither a b lowBoth)
    (hba : ¬ LevelLabelLt b a) :
    PeakMeasureLt (tail, lowA ++ [b] ++ lowBoth) (a :: tail, [b]) := by
  obtain ⟨hpreB, hsufB⟩ := allBelow_b_of_not_below hA hBoth hba
  have hout : lexMax (lowA ++ [b] ++ lowBoth) = lexMax lowA + {b.toKey} :=
    lexMax_low_append_peak_low hpreB hsufB
  let U := lexMax tail
  let B := belowPart a U
  let O := removeBelow U a.toKey
  have hpart : B + O = U := belowPart_add_removeBelow a U
  refine ⟨O + {b.toKey}, B + lexMax lowA, {a.toKey}, by simp, ?_, ?_, ?_⟩
  · change U + lexMax (lowA ++ [b] ++ lowBoth) =
      (O + {b.toKey}) + (B + lexMax lowA)
    rw [hout, ← hpart]
    ac_rfl
  · change ({a.toKey} + O) + {b.toKey} = (O + {b.toKey}) + {a.toKey}
    ac_rfl
  · intro y hy
    simp only [Multiset.mem_add] at hy
    rcases hy with hyB | hyLow
    · exact ⟨a.toKey, by simp, (Multiset.mem_filter.mp hyB).2⟩
    · obtain ⟨c, hc, rfl⟩ := mem_lexMax_source hyLow
      exact ⟨a.toKey, by simp, levelLabel_toKey_lt_iff.mpr (hA c hc)⟩

/-- **Lemma 3.6, left route-R2 specialization.** The peeled left input label is
strictly removed from the recursive subpeak. -/
theorem local_left_subpeak_strict
    {a b : LevelLabel} {tail lowA opt lowBoth : List LevelLabel}
    (hA : AllBelow a lowA)
    (hopt : opt = [] ∨ opt = [b])
    (hBoth : AllBelowEither a b lowBoth) :
    PeakMeasureLt (tail, lowA ++ opt ++ lowBoth) (a :: tail, [b]) := by
  rcases hopt with rfl | rfl
  · simpa using strict_subpeak_of_allBelowEither
      (tail := tail) (allBelowEither_low_append hA hBoth)
  · by_cases hba : LevelLabelLt b a
    · exact strict_subpeak_of_allBelowEither
        (tail := tail) (allBelowEither_low_peak_low_of_peak_lt hA hBoth hba)
    · exact strict_subpeak_of_surviving_peak hA hBoth hba

/-- **Lemma 3.6, right mirror.** -/
theorem local_right_subpeak_strict
    {a b : LevelLabel} {tail lowB opt lowBoth : List LevelLabel}
    (hB : AllBelow b lowB)
    (hopt : opt = [] ∨ opt = [a])
    (hBoth : AllBelowEither a b lowBoth) :
    PeakMeasureLt (lowB ++ opt ++ lowBoth, tail) ([a], b :: tail) := by
  have h := local_left_subpeak_strict
    (a := b) (b := a) (tail := tail) (lowA := lowB)
    (opt := opt) (lowBoth := lowBoth) hB hopt (by
      intro c hc
      rcases hBoth c hc with hca | hcb
      · exact Or.inr hca
      · exact Or.inl hcb)
  -- `PeakMeasureLt` is an `InvImage`, so state both sides as the underlying
  -- Dershowitz-Manna comparison before commuting the two summands.
  have h' : Multiset.IsDershowitzMannaLT
      (lexMax tail + lexMax (lowB ++ opt ++ lowBoth))
      (lexMax (b :: tail) + lexMax [a]) := h
  show Multiset.IsDershowitzMannaLT
    (lexMax (lowB ++ opt ++ lowBoth) + lexMax tail)
    (lexMax [a] + lexMax (b :: tail))
  simpa [add_comm] using h'

/-- Local measured join enriched with the two strict recursive-subpeak edges
needed by the global well-founded induction. -/
structure InductiveLocalJoin (step : LabelledStep State LevelLabel)
    (peak : LocalPeak step) extends
    MeasuredJoin step [peak.leftLabel] [peak.rightLabel] peak.left peak.right where
  leftStrict : ∀ tail : List LevelLabel,
    PeakMeasureLt (tail, toMeasuredJoin.leftOutput)
      (peak.leftLabel :: tail, [peak.rightLabel])
  rightStrict : ∀ tail : List LevelLabel,
    PeakMeasureLt (toMeasuredJoin.rightOutput, tail)
      ([peak.leftLabel], peak.rightLabel :: tail)

/-- Every exact decreasing local peak constructs the enriched induction object. -/
theorem LocalPeak.inductiveLocalJoin_of_decreasing
    {step : LabelledStep State LevelLabel} (peak : LocalPeak step)
    (hdec : peak.Decreasing LevelLabelLt) :
    Nonempty (InductiveLocalJoin step peak) := by
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
  let leftOut := lowA ++ optB ++ lowBothL
  let rightOut := lowB ++ optA ++ lowBothR
  refine ⟨{
    toMeasuredJoin := {
      join := valley.join
      leftOutput := leftOut
      rightOutput := rightOut
      leftPath := by
        simpa [leftOut, List.append_assoc] using hLowA.trans (hOptB.trans hBothL)
      rightPath := by
        simpa [rightOut, List.append_assoc] using hLowB.trans (hOptA.trans hBothR)
      leftMeasure := by
        simpa [leftOut] using local_left_measure_bound hAllA hOptBshape hAllBothL
      rightMeasure := by
        simpa [rightOut] using local_right_measure_bound hAllB hOptAshape hAllBothR
    }
    leftStrict := fun tail => by
      simpa [leftOut] using local_left_subpeak_strict
        (tail := tail) hAllA hOptBshape hAllBothL
    rightStrict := fun tail => by
      simpa [rightOut] using local_right_subpeak_strict
        (tail := tail) hAllB hOptAshape hAllBothR
  }⟩

end OperatorKO7.Meta.UniqueNormalization

#check @OperatorKO7.Meta.UniqueNormalization.belowPart
#check @OperatorKO7.Meta.UniqueNormalization.belowPart_add_removeBelow
#check @OperatorKO7.Meta.UniqueNormalization.removeBelow_lexMax_eq_zero_of_allBelow
#check @OperatorKO7.Meta.UniqueNormalization.lexMax_low_append_peak_low
#check @OperatorKO7.Meta.UniqueNormalization.allBelowEither_low_append
#check @OperatorKO7.Meta.UniqueNormalization.allBelowEither_low_peak_low_of_peak_lt
#check @OperatorKO7.Meta.UniqueNormalization.allBelow_b_of_not_below
#check @OperatorKO7.Meta.UniqueNormalization.strict_subpeak_of_allBelowEither
#check @OperatorKO7.Meta.UniqueNormalization.strict_subpeak_of_surviving_peak
#check @OperatorKO7.Meta.UniqueNormalization.local_left_subpeak_strict
#check @OperatorKO7.Meta.UniqueNormalization.local_right_subpeak_strict
#check @OperatorKO7.Meta.UniqueNormalization.InductiveLocalJoin
#check @OperatorKO7.Meta.UniqueNormalization.InductiveLocalJoin.mk
#check @OperatorKO7.Meta.UniqueNormalization.InductiveLocalJoin.toMeasuredJoin
#check @OperatorKO7.Meta.UniqueNormalization.InductiveLocalJoin.leftStrict
#check @OperatorKO7.Meta.UniqueNormalization.InductiveLocalJoin.rightStrict
#check @OperatorKO7.Meta.UniqueNormalization.LocalPeak.inductiveLocalJoin_of_decreasing

#print axioms OperatorKO7.Meta.UniqueNormalization.belowPart
#print axioms OperatorKO7.Meta.UniqueNormalization.belowPart_add_removeBelow
#print axioms OperatorKO7.Meta.UniqueNormalization.removeBelow_lexMax_eq_zero_of_allBelow
#print axioms OperatorKO7.Meta.UniqueNormalization.lexMax_low_append_peak_low
#print axioms OperatorKO7.Meta.UniqueNormalization.allBelowEither_low_append
#print axioms OperatorKO7.Meta.UniqueNormalization.allBelowEither_low_peak_low_of_peak_lt
#print axioms OperatorKO7.Meta.UniqueNormalization.allBelow_b_of_not_below
#print axioms OperatorKO7.Meta.UniqueNormalization.strict_subpeak_of_allBelowEither
#print axioms OperatorKO7.Meta.UniqueNormalization.strict_subpeak_of_surviving_peak
#print axioms OperatorKO7.Meta.UniqueNormalization.local_left_subpeak_strict
#print axioms OperatorKO7.Meta.UniqueNormalization.local_right_subpeak_strict
#print axioms OperatorKO7.Meta.UniqueNormalization.InductiveLocalJoin
#print axioms OperatorKO7.Meta.UniqueNormalization.InductiveLocalJoin.mk
#print axioms OperatorKO7.Meta.UniqueNormalization.InductiveLocalJoin.toMeasuredJoin
#print axioms OperatorKO7.Meta.UniqueNormalization.InductiveLocalJoin.leftStrict
#print axioms OperatorKO7.Meta.UniqueNormalization.InductiveLocalJoin.rightStrict
#print axioms OperatorKO7.Meta.UniqueNormalization.LocalPeak.inductiveLocalJoin_of_decreasing
