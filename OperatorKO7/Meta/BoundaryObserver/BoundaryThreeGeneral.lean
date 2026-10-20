import OperatorKO7.Meta.BoundaryObserver.Boundary

set_option autoImplicit false

/-!
# Three boundary descriptions without a finite record carrier

The indicator reading separates distinct records on the finite Boolean carrier.
The proof graph node is N1 in the Boundary Theorem math completion graph.
-/

namespace OperatorKO7.Meta.BoundaryObserver.BoundaryThreeGeneral

/-- A Boolean reading whose outcome is the point mass at the truth value of
equality between the current record and the record of the named state. -/
noncomputable def indicatorReading {X Q : Type} (q : X → Q) (x₀ : X) :
    BoundaryPole.Reading X Bool := by
  classical
  exact fun x => PairResolution.deterministicRow
    (fun z : X => decide (q z = q x₀)) x

/-- Every state with a common record has the same Boolean indicator law. -/
theorem indicatorReading_recordDetermined {X Q : Type} (q : X → Q) (x₀ : X) :
    BoundaryPole.RecordDetermined q (indicatorReading q x₀) := by
  classical
  intro x x' hq
  have hm : (indicatorReading q x₀ x).mass =
      (indicatorReading q x₀ x').mass := by
    funext b
    simp [indicatorReading, PairResolution.deterministicRow_mass, hq]
  have hext : ∀ (P R : ProtocolResolution.FiniteLaw Bool),
      P.mass = R.mass → P = R := by
    intro P R h
    cases P
    cases R
    cases h
    rfl
  exact hext _ _ hm

/-- Distinct records have Boolean indicator laws of triangular discrimination two. -/
theorem indicatorReading_discrimination_split {X Q : Type} (q : X → Q) {x₀ x₁ : X}
    (h : q x₀ ≠ q x₁) :
    BoundaryPole.readingDiscrimination (indicatorReading q x₀) x₀ x₁ = 2 := by
  classical
  have hd := BoundarySingularity.discrimination_deterministic
    (fun z : X => decide (q z = q x₀)) x₀ x₁
  change BoundaryPole.readingDiscrimination (indicatorReading q x₀) x₀ x₁ =
    (if decide (q x₀ = q x₀) = decide (q x₁ = q x₀) then (0 : ℝ) else 2) at hd
  simpa [h.symm] using hd

/-- A pair is a nontrivial record collision exactly if all record-determined
finite-output readings have discrimination zero, without a finite record type. -/
theorem boundaryZeroSet_general {X Q : Type} (q : X → Q) (x₀ x₁ : X) :
    MergedPair.IsMergedPair q x₀ x₁ ↔
      (x₀ ≠ x₁ ∧ ∀ (Y : Type) [Fintype Y] (K : BoundaryPole.Reading X Y),
        BoundaryPole.RecordDetermined q K →
          BoundaryPole.readingDiscrimination K x₀ x₁ = 0) := by
  constructor
  · intro hm
    refine ⟨hm.1, ?_⟩
    intro Y _ K hdet
    exact BoundaryPole.recordPoleGoal X Q Y q K x₀ x₁ hdet hm
  · rintro ⟨hne, hzero⟩
    refine ⟨hne, ?_⟩
    by_contra hsplit
    have hd := indicatorReading_discrimination_split q hsplit
    have hz := hzero Bool (indicatorReading q x₀)
      (indicatorReading_recordDetermined q x₀)
    have hcontr : (0 : ℝ) = 2 := hz.symm.trans hd
    norm_num at hcontr

/-- Every unequal pair lies on the boundary exactly if a record-preserving
permutation exchanges its states, and exactly if every record-determined finite
reading has discrimination zero, without any hypothesis on the record carrier. -/
theorem boundary_three_descriptions_general {X Q : Type} (q : X → Q) (x₀ x₁ : X)
    (hne : x₀ ≠ x₁) :
    (q x₀ = q x₁ ↔
      ∃ σ ∈ OperatorKO7.Meta.OperationalInexpressibility.LicenseStabilizer.licenseStabilizer q,
        σ x₀ = x₁) ∧
    (q x₀ = q x₁ ↔
      ∀ (Y : Type) [Fintype Y] (K : BoundaryPole.Reading X Y),
        BoundaryPole.RecordDetermined q K →
          BoundaryPole.readingDiscrimination K x₀ x₁ = 0) := by
  refine ⟨MergedPair.same_record_iff_orbit q x₀ x₁, ?_⟩
  constructor
  · intro hq
    exact ((boundaryZeroSet_general q x₀ x₁).mp ⟨hne, hq⟩).2
  · intro hz
    exact ((boundaryZeroSet_general q x₀ x₁).mpr ⟨hne, hz⟩).2

/-- The natural-number identity observer has an infinite record carrier,
and its Boolean indicator reading separates states zero and one by two. -/
theorem nat_identity_split_control :
    BoundaryPole.readingDiscrimination (indicatorReading (id : ℕ → ℕ) 0) 0 1 = 2 := by
  exact indicatorReading_discrimination_split (id : ℕ → ℕ)
    (x₀ := 0) (x₁ := 1) (by decide)

end OperatorKO7.Meta.BoundaryObserver.BoundaryThreeGeneral
