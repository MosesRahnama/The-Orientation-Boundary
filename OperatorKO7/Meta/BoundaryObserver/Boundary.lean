import OperatorKO7.Meta.BoundaryObserver.MergedPair
import OperatorKO7.Meta.BoundaryObserver.BoundaryPole

set_option autoImplicit false

/-!
# Three equivalent descriptions of a record boundary

The reading factorization is over the actual range of the record. This allows
every finite outcome carrier, including the empty carrier, without an extra
nonemptiness assumption on either the state or outcome type.
Graph: notes/universal-roadmap/UNIVERSAL-OBSERVATION-PROOF-GRAPH.md, V1_L4.
-/

namespace OperatorKO7.Meta.BoundaryObserver.Boundary

open OperatorKO7.Meta.BoundaryObserver.MergedPair
open OperatorKO7.Meta.BoundaryObserver.BoundaryPole

/-- A finite reading factors through the record, represented on the true
range of `q`. No value outside that range is artificially supplied. -/
def FactorsThroughRecordRange {X Q Y : Type} [Fintype Y]
    (q : X → Q) (K : BoundaryPole.Reading X Y) : Prop :=
  ∃ Kq : ↥(Set.range q) → ProtocolResolution.FiniteLaw Y,
    ∀ x : X, K x = Kq ⟨q x, ⟨x, rfl⟩⟩

/-- Every fiber-constant finite reading has an actual record factor, and
every such factor gives a fiber-constant reading. This includes empty types. -/
theorem recordDetermined_iff_range_factor {X Q Y : Type} [Fintype Y]
    (q : X → Q) (K : BoundaryPole.Reading X Y) :
    BoundaryPole.RecordDetermined q K ↔ FactorsThroughRecordRange q K := by
  classical
  constructor
  · intro hdet
    let select : ↥(Set.range q) → X := fun r => Classical.choose r.property
    have hs : ∀ r : ↥(Set.range q), q (select r) = r.val :=
      fun r => Classical.choose_spec r.property
    refine ⟨fun r => K (select r), ?_⟩
    intro x
    exact hdet x (select ⟨q x, ⟨x, rfl⟩⟩)
      (hs ⟨q x, ⟨x, rfl⟩⟩).symm
  · rintro ⟨Kq, hKq⟩ x x' hq
    calc
      K x = Kq ⟨q x, ⟨x, rfl⟩⟩ := hKq x
      _ = Kq ⟨q x', ⟨x', rfl⟩⟩ :=
        congrArg Kq (Subtype.ext hq)
      _ = K x' := (hKq x').symm

/-- The record boundary has the same three descriptions at the same
observer and the same explicit unequal pair: record equality, one orbit of
record-preserving permutations, and the common zero set of all finite readings
that actually factor through the record. The finite-record hypothesis is used
only in the zero-set converse, through its deterministic record reading. -/
theorem boundary_three_descriptions {X Q : Type} [Fintype Q] [DecidableEq Q]
    (q : X → Q) (x₀ x₁ : X) (hne : x₀ ≠ x₁) :
    (q x₀ = q x₁ ↔
      ∃ σ ∈ OperatorKO7.Meta.OperationalInexpressibility.LicenseStabilizer.licenseStabilizer q,
        σ x₀ = x₁) ∧
    (q x₀ = q x₁ ↔
      ∀ (Y : Type) [Fintype Y] (K : BoundaryPole.Reading X Y),
        FactorsThroughRecordRange q K →
          BoundaryPole.readingDiscrimination K x₀ x₁ = 0) := by
  refine ⟨MergedPair.same_record_iff_orbit q x₀ x₁, ?_⟩
  constructor
  · intro hq Y _ K hfactor
    exact BoundaryPole.recordPoleGoal X Q Y q K x₀ x₁
      ((recordDetermined_iff_range_factor q K).2 hfactor) ⟨hne, hq⟩
  · intro hzero
    have hz :
        ∀ (Y : Type) [Fintype Y] (K : BoundaryPole.Reading X Y),
          BoundaryPole.RecordDetermined q K →
            BoundaryPole.readingDiscrimination K x₀ x₁ = 0 := by
      intro Y _ K hdet
      exact hzero Y K ((recordDetermined_iff_range_factor q K).1 hdet)
    exact ((BoundaryPole.boundaryZeroSetGoal X Q q x₀ x₁).2 ⟨hne, hz⟩).2

/-- The constant record merges two distinct states, and every finite
record-factored reading has zero discrimination on this pair. -/
theorem same_record_nontrivial_control :
    (false : Bool) ≠ true ∧
    ((fun _ : Bool => ()) false = (fun _ : Bool => ()) true) ∧
    (∃ σ ∈ OperatorKO7.Meta.OperationalInexpressibility.LicenseStabilizer.licenseStabilizer
        (fun _ : Bool => ()), σ false = true) ∧
    (∀ (Y : Type) [Fintype Y] (K : BoundaryPole.Reading Bool Y),
      FactorsThroughRecordRange (fun _ : Bool => ()) K →
        BoundaryPole.readingDiscrimination K false true = 0) := by
  have h := boundary_three_descriptions (fun _ : Bool => ()) false true Bool.false_ne_true
  exact ⟨Bool.false_ne_true, rfl, h.1.mp rfl, h.2.mp rfl⟩

/-- The identity record on the two-point carrier has an actual finite
record-factored reading that separates the two unequal records by discrimination
two. This is the control for the reverse zero-set implication. -/
theorem unequal_record_separating_reading_control :
    (id : Bool → Bool) false ≠ (id : Bool → Bool) true ∧
    ∃ K : BoundaryPole.Reading Bool Bool,
      FactorsThroughRecordRange (id : Bool → Bool) K ∧
      BoundaryPole.readingDiscrimination K false true = 2 := by
  refine ⟨Bool.false_ne_true, ?_⟩
  let K : BoundaryPole.Reading Bool Bool :=
    fun x => PairResolution.deterministicRow (id : Bool → Bool) x
  refine ⟨K, ?_, ?_⟩
  · apply (recordDetermined_iff_range_factor (id : Bool → Bool) K).1
    intro x y hxy
    exact congrArg (fun z => PairResolution.deterministicRow (id : Bool → Bool) z) hxy
  · have hd := BoundarySingularity.discrimination_deterministic
      (id : Bool → Bool) false true
    change BoundarySingularity.discrimination
      (PairResolution.deterministicRow (id : Bool → Bool) false).mass
      (PairResolution.deterministicRow (id : Bool → Bool) true).mass =
      (if (id : Bool → Bool) false = (id : Bool → Bool) true then 0 else 2) at hd
    simpa only [BoundaryPole.readingDiscrimination, K, Bool.false_ne_true, if_false] using hd

end OperatorKO7.Meta.BoundaryObserver.Boundary
