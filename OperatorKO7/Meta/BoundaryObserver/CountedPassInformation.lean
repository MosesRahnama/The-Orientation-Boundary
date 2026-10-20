import OperatorKO7.Meta.BoundaryObserver.BoundaryPole
import OperatorKO7.Meta.BoundaryObserver.ObserverDegenerateCases

set_option autoImplicit false

/-!
# Information about finitely many counted passes

Manuscript: cor:three-laws and thm:boundary-theorem clause 12.
The target label ranges over any finite type. The initial record selects both
its content and its counter assignment. All probability laws are those of the
supplied protocol, and the proof derives zero local gain from their product form.
The collected theorem in `BoundaryTheorem.lean` imports this module for clause 12 and carries
the closing theorem `boundaryTheorem_all_carriers`.
-/

namespace OperatorKO7.Meta.BoundaryObserver.CountedPassInformation

universe u

open MergedPair RecursorDecidability BoundaryPole ProtocolResolution

/-- Content-determined rows have zero capacity about any finite family of counts. -/
theorem counted_rows_zero_capacity {T : Type u} {Z A Y : Type}
    [Fintype Z] [Fintype A] [Fintype Y]
    (R : T) (k : Z → ℕ) (p : FiniteProtocol Z A Y)
    (K : List (A × Y) → A → Reading (T × ℕ) Y)
    (hdet : ∀ h a, RecordDetermined (content (T := T)) (K h a))
    (hobs : ∀ h a z, p.observation h a z = K h a (R, k z)) :
    LocalCapacityBound p 0 := by
  have hread : ∀ h a z, p.observation h a z = K h a (R, 0) := by
    intro h a z
    exact (hobs h a z).trans (hdet h a (R, k z) (R, 0) rfl)
  intro h a hw _ _
  have hrow :
      (fun zy : Z × Y => posterior p h zy.1 * (p.observation h a zy.1).mass zy.2) =
      (fun zy : Z × Y => posterior p h zy.1 * (K h a (R, 0)).mass zy.2) := by
    funext zy
    rw [hread h a zy.1]
  have hgain : localGain p h a = 0 := by
    unfold localGain
    rw [hrow]
    exact jointMI_product_zero (posterior p h) (K h a (R, 0)).mass
      (posterior_total p h hw) (K h a (R, 0)).total
  simpa only [hgain, zero_mul] using (le_refl (0 : ℝ))

/-- The finite and limiting information vanish for any finite count label. -/
theorem counted_passes_zero_information {T : Type u} {Z A Y : Type}
    [Fintype Z] [Fintype A] [Fintype Y]
    (R : T) (k : Z → ℕ) (p : FiniteProtocol Z A Y)
    (K : List (A × Y) → A → Reading (T × ℕ) Y)
    (hdet : ∀ h a, RecordDetermined (content (T := T)) (K h a))
    (hobs : ∀ h a z, p.observation h a z = K h a (R, k z)) :
    (∀ n bank, HistoryBank n bank → terminalMI p n bank = 0) ∧
      informationLimit p = 0 := by
  have hc := counted_rows_zero_capacity R k p K hdet hobs
  refine ⟨?_, informationLimit_zero_capacity p hc⟩
  intro n bank hb
  have hu := terminalMI_le_expectedCost p 0 n bank hb hc
  exact le_antisymm (by simpa only [zero_mul] using hu)
    (terminalMI_nonnegative p n bank hb)

/-- Initial information is retained while subsequent content readings acquire zero
information about the finite count label. Zero-weight initial records impose no laws. -/
theorem counted_passes_conditional_zero_information {T : Type u} {H0 Z A Y : Type}
    [Fintype H0] [Fintype Z] [Fintype A] [Fintype Y]
    (R : H0 → T) (k : H0 → Z → ℕ) (p : ConditionalProtocol H0 Z A Y)
    (K : H0 → List (A × Y) → A → Reading (T × ℕ) Y)
    (hdet : ∀ v, 0 < p.initialRecord.mass v → ∀ h a,
      RecordDetermined (content (T := T)) (K v h a))
    (hobs : ∀ v, 0 < p.initialRecord.mass v → ∀ h a z,
      (p.given v).observation h a z = K v h a (R v, k v z)) :
    (∀ n bank, HistoryBank n bank → conditionalJointInfo p n bank = 0) ∧
      conditionalInformationLimit p = 0 := by
  have hc : ∀ v, 0 < p.initialRecord.mass v → LocalCapacityBound (p.given v) 0 := by
    intro v hv
    exact counted_rows_zero_capacity (R v) (k v) (p.given v) (K v)
      (hdet v hv) (hobs v hv)
  exact ⟨fun n bank hb => conditionalJointInfo_zero_capacity p n bank hb hc,
    conditionalInformationLimit_zero_capacity p hc⟩

/-- Full count-label information statement, with arbitrary finite labels and histories. -/
def FinitePassInformationGoal : Prop :=
  ∀ (T : Type u) (H0 Z A Y : Type)
    [Fintype H0] [Fintype Z] [Fintype A] [Fintype Y]
    (R : H0 → T) (k : H0 → Z → ℕ) (p : ConditionalProtocol H0 Z A Y)
    (K : H0 → List (A × Y) → A → Reading (T × ℕ) Y),
    (∀ v, 0 < p.initialRecord.mass v → ∀ h a,
      RecordDetermined (content (T := T)) (K v h a)) →
    (∀ v, 0 < p.initialRecord.mass v → ∀ h a z,
      (p.given v).observation h a z = K v h a (R v, k v z)) →
    (∀ n bank, HistoryBank n bank → conditionalJointInfo p n bank = 0) ∧
      conditionalInformationLimit p = 0

theorem finitePassInformationGoal : FinitePassInformationGoal.{u} := by
  intro T H0 Z A Y _ _ _ _ R k p K hdet hobs
  exact counted_passes_conditional_zero_information R k p K hdet hobs

/-- The orientation clause covers empty and inhabited content types. -/
def AllCarrierRecursionGoal : Prop :=
  ∀ T : Type u,
    WellFounded (fun y x : T × ℕ => Pass x y) ∧
      (Determines (content (T := T)) observed ↔ IsEmpty T) ∧
      ∀ M : T × ℕ → ℕ, (∀ x y, Pass x y → M y < M x) →
        (Determines content M ↔ IsEmpty T)

theorem allCarrierRecursionGoal : AllCarrierRecursionGoal.{u} := by
  intro T
  exact ⟨pass_wellFounded, ObserverDegenerateCases.content_determines_observed_iff_empty T,
    fun M hM => ObserverDegenerateCases.orienting_content_determined_iff_empty M hM⟩

/-- A reading of the counter violates the hypothesis that only content is read. -/
theorem counter_reading_not_content_determined {T : Type u} (R : T) :
    ¬ RecordDetermined (content (T := T))
      (booleanTestRow (fun x : T × ℕ => decide (x.2 = 0))) := by
  intro hdet
  have heq := hdet (R, 0) (R, 1) rfl
  have hm := congrArg (fun L : FiniteLaw Bool => L.mass true) heq
  norm_num [booleanTestRow, PairResolution.deterministicRow_mass] at hm

end OperatorKO7.Meta.BoundaryObserver.CountedPassInformation
