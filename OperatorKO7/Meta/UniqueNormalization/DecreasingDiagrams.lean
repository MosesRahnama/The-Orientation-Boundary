import OperatorKO7.Meta.UniqueNormalization.DecreasingPasting

/-!
# RTA #79 route R2: global decreasing diagrams

This module closes the generic metatheorem needed by route R2.  It is the Lean
specialization of van Oostrom's decreasing-diagrams theorem to the already
mechanized route-R2 label order.

The proof follows Zankl's formal Theorem 3.7.  Arbitrary finite labelled peaks
are ordered by the well-founded `PeakMeasureLt`.  For a nontrivial peak, the
first two steps form a local peak; local decreasingness produces a measured
local diagram.  Lemma 3.6 makes the first recursive peak strictly smaller,
Lemma 3.5 pastes the first recursive diagram, the mirrored Lemma 3.6 makes the
second recursive peak strictly smaller, and a mirrored paste closes the full
peak.  Empty arms are handled by trivial measured diagrams.

The final theorem forgets labels and concludes confluence of the unlabelled
relation.

Trust: kernel checked. No external certificate or new axiom.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniqueNormalization

universe u

variable {State : Type u}

/-- Mirror a measured joining diagram. -/
def MeasuredJoin.mirror
    {step : LabelledStep State LevelLabel}
    {tau sigma : List LevelLabel} {x y : State}
    (D : MeasuredJoin step tau sigma x y) :
    MeasuredJoin step sigma tau y x := {
  join := D.join
  leftOutput := D.rightOutput
  rightOutput := D.leftOutput
  leftPath := D.rightPath
  rightPath := D.leftPath
  leftMeasure := by simpa [peakMeasure, add_comm] using D.rightMeasure
  rightMeasure := by simpa [peakMeasure, add_comm] using D.leftMeasure
}

/-- Trivial measured diagram when the left input path is reflexive. -/
def MeasuredJoin.of_left_refl
    {step : LabelledStep State LevelLabel}
    {sigma : List LevelLabel} {x y : State}
    (h : LPath step x y sigma) :
    MeasuredJoin step [] sigma x y := {
  join := y
  leftOutput := sigma
  rightOutput := []
  leftPath := h
  rightPath := LPath.refl y
  leftMeasure := by
    simpa [peakMeasure] using DMLe.refl (lexMax sigma)
  rightMeasure := by
    simpa [peakMeasure] using DMLe.refl (lexMax sigma)
}

/-- Trivial measured diagram when the right input path is reflexive. -/
def MeasuredJoin.of_right_refl
    {step : LabelledStep State LevelLabel}
    {tau : List LevelLabel} {x y : State}
    (h : LPath step x y tau) :
    MeasuredJoin step tau [] y x :=
  (MeasuredJoin.of_left_refl h).mirror

/-- The strict first recursive peak obtained from a one-step local diagram stays
strictly below the original peak after restoring the untouched right suffix. -/
theorem peakMeasureLt_restore_right_suffix
    {a b : LevelLabel} {as bs out : List LevelLabel}
    (h : PeakMeasureLt (as, out) (a :: as, [b])) :
    PeakMeasureLt (as, out) (a :: as, b :: bs) := by
  have hright : DMLe (lexMax [b]) (lexMax (b :: bs)) := by
    apply dmLe_of_multiset_le
    rw [lexMax_singleton, lexMax_cons]
    exact Multiset.le_add_right _ _
  have hctx : DMLe
      (lexMax (a :: as) + lexMax [b])
      (lexMax (a :: as) + lexMax (b :: bs)) :=
    DMLe.add_left (lexMax (a :: as)) hright
  change Multiset.IsDershowitzMannaLT
    (peakMeasure (as, out)) (peakMeasure (a :: as, b :: bs))
  change Multiset.IsDershowitzMannaLT
    (peakMeasure (as, out)) (peakMeasure (a :: as, [b])) at h
  have hs := dmLt_trans_dmLe h hctx
  simpa [peakMeasure] using hs

/-- **Theorem 3.7, measured form.** Every finite labelled peak has a measured
joining diagram when every local peak is decreasing. -/
theorem allPeaksMeasured
    {step : LabelledStep State LevelLabel}
    (hdec : AllLocalPeaksDecreasing step LevelLabelLt) :
    ∀ {source left right : State} {as bs : List LevelLabel},
      LPath step source left as →
      LPath step source right bs →
      Nonempty (MeasuredJoin step as bs left right) := by
  have main : ∀ p : List LevelLabel × List LevelLabel,
      ∀ {source left right : State},
        LPath step source left p.1 →
        LPath step source right p.2 →
        Nonempty (MeasuredJoin step p.1 p.2 left right) := by
    intro p
    induction p using peakMeasureLt_wellFounded.induction with
    | _ p ih =>
        rcases p with ⟨as, bs⟩
        intro source left right ha hb
        cases ha with
        | refl =>
            exact ⟨MeasuredJoin.of_left_refl hb⟩
        | @cons a source s left as hA hAs =>
            cases hb with
            | refl =>
                exact ⟨MeasuredJoin.of_right_refl (LPath.cons hA hAs)⟩
            | @cons b _ u right bs hB hBs =>
                let peak : LocalPeak step := {
                  source := source
                  left := s
                  right := u
                  leftLabel := a
                  rightLabel := b
                  leftStep := hA
                  rightStep := hB
                }
                obtain ⟨Dlocal⟩ := peak.measuredJoin_of_decreasing (hdec peak)

                have hsmall1base : PeakMeasureLt
                    (as, Dlocal.leftOutput) (a :: as, [b]) := by
                  simpa using Dlocal.hypothesisDecreaseLeft (by simp) as
                have hsmall1 : PeakMeasureLt
                    (as, Dlocal.leftOutput) (a :: as, b :: bs) :=
                  peakMeasureLt_restore_right_suffix hsmall1base
                obtain ⟨D1⟩ :=
                  ih (as, Dlocal.leftOutput) hsmall1 hAs Dlocal.leftPath

                let Dp : MeasuredJoin step (a :: as) [b] left u := by
                  simpa using Dlocal.paste D1

                have hsmall2 : PeakMeasureLt
                    (Dp.rightOutput, bs) (a :: as, b :: bs) := by
                  have h := Dp.hypothesisDecreaseRight (by simp) bs
                  simpa using h
                obtain ⟨D2⟩ :=
                  ih (Dp.rightOutput, bs) hsmall2 Dp.rightPath hBs

                let finalD := Dp.mirror.paste D2.mirror
                exact ⟨by
                  simpa using finalD.mirror⟩
  intro source left right as bs ha hb
  exact main (as, bs) ha hb

/-- Confluence of the unlabelled relation. -/
def UnlabelledConfluent (step : LabelledStep State LevelLabel) : Prop :=
  ∀ {source left right : State},
    Relation.ReflTransGen (Unlabelled step) source left →
    Relation.ReflTransGen (Unlabelled step) source right →
    Relation.Join (Relation.ReflTransGen (Unlabelled step)) left right

/-- **van Oostrom decreasing-diagrams theorem, route-R2 specialization.** If all
local peaks are decreasing for the well-founded `LevelLabelLt` order, the
unlabelled relation is confluent. -/
theorem allLocalPeaksDecreasing_confluent
    {step : LabelledStep State LevelLabel}
    (hdec : AllLocalPeaksDecreasing step LevelLabelLt) :
    UnlabelledConfluent step := by
  intro source left right hleft hright
  obtain ⟨as, ha⟩ := exists_lPath_of_star hleft
  obtain ⟨bs, hb⟩ := exists_lPath_of_star hright
  obtain ⟨D⟩ := allPeaksMeasured hdec ha hb
  exact ⟨D.join, D.leftPath.toStar, D.rightPath.toStar⟩

end OperatorKO7.Meta.UniqueNormalization

#check @OperatorKO7.Meta.UniqueNormalization.MeasuredJoin.mirror
#check @OperatorKO7.Meta.UniqueNormalization.MeasuredJoin.of_left_refl
#check @OperatorKO7.Meta.UniqueNormalization.MeasuredJoin.of_right_refl
#check @OperatorKO7.Meta.UniqueNormalization.peakMeasureLt_restore_right_suffix
#check @OperatorKO7.Meta.UniqueNormalization.allPeaksMeasured
#check @OperatorKO7.Meta.UniqueNormalization.UnlabelledConfluent
#check @OperatorKO7.Meta.UniqueNormalization.allLocalPeaksDecreasing_confluent

#print axioms OperatorKO7.Meta.UniqueNormalization.MeasuredJoin.mirror
#print axioms OperatorKO7.Meta.UniqueNormalization.MeasuredJoin.of_left_refl
#print axioms OperatorKO7.Meta.UniqueNormalization.MeasuredJoin.of_right_refl
#print axioms OperatorKO7.Meta.UniqueNormalization.peakMeasureLt_restore_right_suffix
#print axioms OperatorKO7.Meta.UniqueNormalization.allPeaksMeasured
#print axioms OperatorKO7.Meta.UniqueNormalization.allLocalPeaksDecreasing_confluent
