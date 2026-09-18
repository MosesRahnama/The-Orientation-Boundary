import OperatorKO7.Meta.UniqueNormalization.DecreasingPastingAlgebra

/-!
# RTA #79 route R2: measured-diagram pasting

This module proves the measured-diagram pasting theorem corresponding to
Lemma 3.5 in the formal decreasing-diagrams development.

If `D1` joins a peak with input labels `(tau, sigma)`, and `D2` joins the new
peak formed by an additional left reduction `ups` against `D1.leftOutput`, then
the two diagrams paste into a measured join with inputs `(tau ++ ups, sigma)`.
The new left output is `D2.leftOutput`; the new right output is the concatenation
`D1.rightOutput ++ D2.rightOutput`.

The left measure is direct residual composition. The right measure follows the
formal source proof: split the second residual at the downset of `tau`, absorb
the dominated part into `D1.rightResidual`, and bound the surviving part using
the enlarged-downset consequence of `D1.leftMeasure` together with
`D2.rightResidual`.

Trust: kernel checked. No external certificate or new axiom.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniqueNormalization

/-- DM comparison preserves strict downsets. -/
theorem DMLe.belowMultiset_mono {M N : Multiset LevelKey}
    (hMN : DMLe M N) {x : LevelKey} (hx : BelowMultiset M x) :
    BelowMultiset N x := by
  rcases dmLe_iff_eq_or_lt.mp hMN with hEq | hlt
  · subst N
    exact hx
  · rcases hlt with ⟨X, Y, Z, hZ, hM, hN, hYZ⟩
    rcases hx with ⟨m, hm, hxm⟩
    rw [hM] at hm
    rcases Multiset.mem_add.mp hm with hmX | hmY
    · refine ⟨m, ?_, hxm⟩
      rw [hN]
      exact Multiset.mem_add.mpr (Or.inl hmX)
    · obtain ⟨z, hzZ, hmz⟩ := hYZ m hmY
      refine ⟨z, ?_, hxm.trans hmz⟩
      rw [hN]
      exact Multiset.mem_add.mpr (Or.inr hzZ)

/-- The first diagram's left measured inequality implies that every key below
`tau ++ leftOutput` is already below `tau ++ sigma`. This is the `step3`
downset inclusion used in the formal Lemma 3.5 proof. -/
theorem MeasuredJoin.leftOutput_downset
    {State : Type*} {step : LabelledStep State LevelLabel}
    {tau sigma : List LevelLabel} {x y : State}
    (D : MeasuredJoin step tau sigma x y) {q : LevelKey}
    (hq : BelowList (tau ++ D.leftOutput) q) :
    BelowList (tau ++ sigma) q := by
  have hsource : BelowMultiset (lexMax (tau ++ D.leftOutput)) q :=
    (belowMultiset_lexMax_iff_belowList _ _).2 hq
  have htarget : BelowMultiset (peakMeasure (tau, sigma)) q :=
    D.leftMeasure.belowMultiset_mono hsource
  have hsum : BelowMultiset (lexMax tau + lexMax sigma) q := by
    simpa [peakMeasure] using htarget
  rcases (belowMultiset_add (lexMax tau) (lexMax sigma) q).1 hsum with ht | hs
  · exact (belowList_append tau sigma q).2
      (Or.inl ((belowMultiset_lexMax_iff_belowList tau q).1 ht))
  · exact (belowList_append tau sigma q).2
      (Or.inr ((belowMultiset_lexMax_iff_belowList sigma q).1 hs))

/-- **Lemma 3.5, measured-diagram pasting.** -/
noncomputable def MeasuredJoin.paste
    {State : Type*} {step : LabelledStep State LevelLabel}
    {tau sigma ups : List LevelLabel} {x y z : State}
    (D1 : MeasuredJoin step tau sigma x y)
    (D2 : MeasuredJoin step ups D1.leftOutput z D1.join) :
    MeasuredJoin step (tau ++ ups) sigma z y := by
  classical
  let M2 := lexMax D2.rightOutput
  let F := removeBelowList (lexMax D1.rightOutput) sigma
  let G := removeBelowList (removeBelowList M2 D1.rightOutput) sigma
  let Q := belowListPart G tau
  let H := removeBelowList G tau

  have hleftFiltered := D2.leftResidual.removeBelowList tau
  have hleftFiltered' : DMLe
      (removeBelowList (lexMax D2.leftOutput) (tau ++ ups))
      (removeBelowList (lexMax D1.leftOutput) tau) := by
    simpa [removeBelowList_removeBelowList] using hleftFiltered
  have hleftResidual : DMLe
      (removeBelowList (lexMax D2.leftOutput) (tau ++ ups))
      (lexMax sigma) :=
    DMLe.trans hleftFiltered' D1.leftResidual

  have hconcat :
      removeBelowList (lexMax (D1.rightOutput ++ D2.rightOutput)) sigma = F + G := by
    rw [lexMax_append, removeBelowList_add]

  have hpartition : Q + H = G := by
    simpa [Q, H] using belowListPart_add_removeBelowList G tau

  have hQcond : ∀ q ∈ Q,
      BelowMultiset (lexMax tau) q ∧ ¬ BelowMultiset F q := by
    intro q hqQ
    have hqQ' : q ∈ belowListPart G tau := by simpa [Q] using hqQ
    have hqData : q ∈ G ∧ BelowList tau q := by
      simpa [belowListPart] using (Multiset.mem_filter.mp (by simpa [belowListPart] using hqQ'))
    have hbelowTau : BelowMultiset (lexMax tau) q :=
      (belowMultiset_lexMax_iff_belowList tau q).2 hqData.2
    refine ⟨hbelowTau, ?_⟩
    intro hbelowF
    rcases hbelowF with ⟨w, hwF, hqw⟩
    have hwR : w ∈ lexMax D1.rightOutput := by
      have hwF' : w ∈ removeBelowList (lexMax D1.rightOutput) sigma := by
        simpa [F] using hwF
      have hwData : w ∈ lexMax D1.rightOutput ∧ ¬ BelowList sigma w := by
        simpa [removeBelowList] using hwF'
      exact hwData.1
    have hqBelowR : BelowList D1.rightOutput q :=
      (belowMultiset_lexMax_iff_belowList D1.rightOutput q).1 ⟨w, hwR, hqw⟩
    have hqG : q ∈ G := hqData.1
    have hqFlat :
        q ∈ M2 ∧ ¬ BelowList sigma q ∧ ¬ BelowList D1.rightOutput q := by
      simpa [G, removeBelowList] using hqG
    exact hqFlat.2.2 hqBelowR

  have hQF : DMLe (Q + F) (lexMax tau) :=
    D1.rightResidual.add_dominated hQcond

  have hGform : G = removeBelowList M2 (sigma ++ D1.rightOutput) := by
    simpa [G] using
      removeBelowList_removeBelowList M2 sigma D1.rightOutput
  have hHform : H =
      removeBelowList M2 (tau ++ (sigma ++ D1.rightOutput)) := by
    dsimp [H]
    rw [hGform]
    simpa using removeBelowList_removeBelowList M2 tau (sigma ++ D1.rightOutput)
  have hsmallForm :
      removeBelowList (removeBelowList M2 D1.leftOutput) tau =
        removeBelowList M2 (tau ++ D1.leftOutput) := by
    exact removeBelowList_removeBelowList M2 tau D1.leftOutput

  have hdownSub : ∀ q,
      BelowList (tau ++ D1.leftOutput) q →
        BelowList (tau ++ (sigma ++ D1.rightOutput)) q := by
    intro q hq
    have hts : BelowList (tau ++ sigma) q := D1.leftOutput_downset hq
    rcases (belowList_append tau sigma q).1 hts with ht | hs
    · exact (belowList_append tau (sigma ++ D1.rightOutput) q).2 (Or.inl ht)
    · exact (belowList_append tau (sigma ++ D1.rightOutput) q).2
        (Or.inr ((belowList_append sigma D1.rightOutput q).2 (Or.inl hs)))

  have hanti : DMLe H
      (removeBelowList (removeBelowList M2 D1.leftOutput) tau) := by
    have h := removeBelowList_anti M2 hdownSub
    rw [← hHform, ← hsmallForm] at h
    exact h

  have hD2rightFiltered := D2.rightResidual.removeBelowList tau
  have hD2rightFiltered' : DMLe
      (removeBelowList (removeBelowList M2 D1.leftOutput) tau)
      (removeBelowList (lexMax ups) tau) := by
    simpa [M2] using hD2rightFiltered
  have hH : DMLe H (removeBelowList (lexMax ups) tau) :=
    DMLe.trans hanti hD2rightFiltered'

  have hsum1 : DMLe ((Q + F) + H) (lexMax tau + H) :=
    hQF.add_right H
  have hsum2 : DMLe (lexMax tau + H)
      (lexMax tau + removeBelowList (lexMax ups) tau) :=
    DMLe.add_left (lexMax tau) hH
  have hsum : DMLe ((Q + F) + H)
      (lexMax tau + removeBelowList (lexMax ups) tau) :=
    DMLe.trans hsum1 hsum2

  have hrightResidual : DMLe
      (removeBelowList (lexMax (D1.rightOutput ++ D2.rightOutput)) sigma)
      (lexMax (tau ++ ups)) := by
    rw [hconcat, ← hpartition, lexMax_append]
    simpa [add_assoc, add_comm, add_left_comm] using hsum

  exact {
    join := D2.join
    leftOutput := D2.leftOutput
    rightOutput := D1.rightOutput ++ D2.rightOutput
    leftPath := D2.leftPath
    rightPath := D1.rightPath.trans D2.rightPath
    leftMeasure := measuredLeft_of_residual hleftResidual
    rightMeasure := measuredRight_of_residual hrightResidual
  }

end OperatorKO7.Meta.UniqueNormalization

#check @OperatorKO7.Meta.UniqueNormalization.DMLe.belowMultiset_mono
#check @OperatorKO7.Meta.UniqueNormalization.MeasuredJoin.leftOutput_downset
#check @OperatorKO7.Meta.UniqueNormalization.MeasuredJoin.paste

#print axioms OperatorKO7.Meta.UniqueNormalization.DMLe.belowMultiset_mono
#print axioms OperatorKO7.Meta.UniqueNormalization.MeasuredJoin.leftOutput_downset
#print axioms OperatorKO7.Meta.UniqueNormalization.MeasuredJoin.paste
