/-!
This module proves a syntactic occurrence theorem for a minimal first-order RecordTerm language
with one generator constructor. Frame presence plus active-site presence yields two distinct
generator positions. Broader architectural transport requires a separate theorem.


















-/

namespace OperatorKO7.StepDuplicating
namespace StepDuplicatingSchema

/-- Carrier with the constructors displayed below. -/
inductive RecordCounter where
  | zero
  | succ : RecordCounter → RecordCounter
deriving DecidableEq, Repr

/-- Carrier with the constructors displayed below.
-/
inductive RecordGenerator where
  | gen
deriving DecidableEq, Repr

/-- Carrier with the constructors displayed below. -/
inductive RecordTerm where
  | base
  | frame : RecordGenerator → RecordTerm → RecordTerm
  | active : RecordTerm → RecordGenerator → RecordCounter → RecordTerm
deriving DecidableEq, Repr

namespace RecordTerm

/-- Carrier with the constructors displayed below. -/
inductive GeneratorPos where
  | frameHead
  | frameTail : GeneratorPos → GeneratorPos
  | activeGen
  | activeCarrier : GeneratorPos → GeneratorPos
deriving DecidableEq, Repr

/-- Enumeration of generator-occurrence positions. -/
def generatorPositions : RecordTerm → List GeneratorPos
  | .base => []
  | .frame .gen t => .frameHead :: (generatorPositions t).map .frameTail
  | .active t .gen _ => .activeGen :: (generatorPositions t).map .activeCarrier

/-- A right-hand side emits a new record frame iff it contains a `frame`
occurrence anywhere. -/
def emitsNewRecordFrame : RecordTerm → Prop
  | .base => False
  | .frame _ _ => True
  | .active t _ _ => emitsNewRecordFrame t

/-- Definition with formal content given by the displayed type and body.
-/
def preservesRecursiveGenerator : RecordTerm → Prop
  | .base => False
  | .frame _ t => preservesRecursiveGenerator t
  | .active _ _ _ => True

/-- Definition with formal content given by the displayed type and body.
-/
def GeneratorPos.isFrameGeneratorPos : GeneratorPos → Prop
  | .frameHead => True
  | .frameTail p => p.isFrameGeneratorPos
  | .activeGen => False
  | .activeCarrier p => p.isFrameGeneratorPos

/-- Definition with formal content given by the displayed type and body.
-/
def GeneratorPos.isActiveGeneratorPos : GeneratorPos → Prop
  | .frameHead => False
  | .frameTail p => p.isActiveGeneratorPos
  | .activeGen => True
  | .activeCarrier p => p.isActiveGeneratorPos

/-- A canonical frame-slot generator position, when one exists. -/
def firstFrameGeneratorPos : RecordTerm → Option GeneratorPos
  | .base => none
  | .frame .gen _ => some .frameHead
  | .active t .gen _ => (firstFrameGeneratorPos t).map .activeCarrier

/-- A canonical active-site generator position, when one exists. -/
def firstActiveGeneratorPos : RecordTerm → Option GeneratorPos
  | .base => none
  | .frame .gen t => (firstActiveGeneratorPos t).map .frameTail
  | .active _ .gen _ => some .activeGen

theorem firstFrameGeneratorPos_spec :
    ∀ {rhs p}, firstFrameGeneratorPos rhs = some p →
      p ∈ generatorPositions rhs ∧ p.isFrameGeneratorPos
  | .base, _, h => by cases h
  | .frame .gen _, _, h => by
      cases h
      simp [generatorPositions, GeneratorPos.isFrameGeneratorPos]
  | .active t .gen _, _, h => by
      cases hsub : firstFrameGeneratorPos t with
      | none =>
          simp [firstFrameGeneratorPos, hsub] at h
      | some p' =>
          simp [firstFrameGeneratorPos, hsub] at h
          cases h
          rcases firstFrameGeneratorPos_spec hsub with ⟨hp', hframe⟩
          exact ⟨by simp [generatorPositions, hp'], hframe⟩

theorem firstActiveGeneratorPos_spec :
    ∀ {rhs p}, firstActiveGeneratorPos rhs = some p →
      p ∈ generatorPositions rhs ∧ p.isActiveGeneratorPos
  | .base, _, h => by cases h
  | .frame .gen t, _, h => by
      cases hsub : firstActiveGeneratorPos t with
      | none =>
          simp [firstActiveGeneratorPos, hsub] at h
      | some p' =>
          simp [firstActiveGeneratorPos, hsub] at h
          cases h
          rcases firstActiveGeneratorPos_spec hsub with ⟨hp', hactive⟩
          exact ⟨by simp [generatorPositions, hp'], hactive⟩
  | .active _ .gen _, _, h => by
      cases h
      simp [generatorPositions, GeneratorPos.isActiveGeneratorPos]

theorem firstFrameGeneratorPos_exists :
    ∀ rhs : RecordTerm, emitsNewRecordFrame rhs →
      ∃ p, firstFrameGeneratorPos rhs = some p
  | .base, hframe => by
      cases hframe
  | .frame _ t, _ => by
      exact ⟨.frameHead, rfl⟩
  | .active t _ c, hframe => by
      have ht : emitsNewRecordFrame t := by
        simpa [emitsNewRecordFrame] using hframe
      rcases firstFrameGeneratorPos_exists t ht with ⟨p, hp⟩
      exact ⟨.activeCarrier p, by simp [firstFrameGeneratorPos, hp]⟩

theorem firstActiveGeneratorPos_exists :
    ∀ rhs : RecordTerm, preservesRecursiveGenerator rhs →
      ∃ p, firstActiveGeneratorPos rhs = some p
  | .base, hactive => by
      cases hactive
  | .frame _ t, hactive => by
      have ht : preservesRecursiveGenerator t := by
        simpa [preservesRecursiveGenerator] using hactive
      rcases firstActiveGeneratorPos_exists t ht with ⟨p, hp⟩
      exact ⟨.frameTail p, by simp [firstActiveGeneratorPos, hp]⟩
  | .active t _ c, _ => by
      exact ⟨.activeGen, rfl⟩

theorem frame_pos_ne_active_pos :
    ∀ p : GeneratorPos, p.isFrameGeneratorPos → ¬ p.isActiveGeneratorPos
  | .frameHead, hframe => by
      intro hactive
      exact hactive
  | .frameTail p, hframe => by
      intro hactive
      exact frame_pos_ne_active_pos p hframe hactive
  | .activeGen, hframe => by
      exact False.elim hframe
  | .activeCarrier p, hframe => by
      intro hactive
      exact frame_pos_ne_active_pos p hframe hactive

/- -/
/-- The displayed proposition follows from the stated hypotheses.


-/
theorem architectural_necessity_of_payload_duplication
    {rhs : RecordTerm}
    (hframe : emitsNewRecordFrame rhs)
    (hactive : preservesRecursiveGenerator rhs) :
    ∃ p q,
      p ≠ q ∧
      p ∈ generatorPositions rhs ∧
      q ∈ generatorPositions rhs ∧
      p.isFrameGeneratorPos ∧
      q.isActiveGeneratorPos := by
  rcases firstFrameGeneratorPos_exists rhs hframe with ⟨p, hpdef⟩
  rcases firstActiveGeneratorPos_exists rhs hactive with ⟨q, hqdef⟩
  rcases firstFrameGeneratorPos_spec hpdef with ⟨hp, hpf⟩
  rcases firstActiveGeneratorPos_spec hqdef with ⟨hq, hqa⟩
  refine ⟨p, q, ?_, hp, hq, hpf, hqa⟩
  intro hpq
  subst hpq
  exact frame_pos_ne_active_pos p hpf hqa

/-- The displayed proposition follows from the stated hypotheses.

-/
theorem no_record_without_duplication_or_generator_erasure
    {rhs : RecordTerm}
    (huniq :
      ∀ p q,
        p ∈ generatorPositions rhs →
        q ∈ generatorPositions rhs →
        p = q) :
    ¬ (emitsNewRecordFrame rhs ∧ preservesRecursiveGenerator rhs) := by
  intro hboth
  rcases architectural_necessity_of_payload_duplication hboth.1 hboth.2 with
    ⟨p, q, hpq, hp, hq, _, _⟩
  exact hpq (huniq p q hp hq)

/-- Definition with formal content given by the displayed type and body. -/
def primitiveDuplicatorRhs (n : RecordCounter) : RecordTerm :=
  .frame .gen (.active .base .gen n)

theorem primitiveDuplicatorRhs_emitsNewRecordFrame (n : RecordCounter) :
    emitsNewRecordFrame (primitiveDuplicatorRhs n) := by
  simp [primitiveDuplicatorRhs, emitsNewRecordFrame]

theorem primitiveDuplicatorRhs_preservesRecursiveGenerator (n : RecordCounter) :
    preservesRecursiveGenerator (primitiveDuplicatorRhs n) := by
  simp [primitiveDuplicatorRhs, preservesRecursiveGenerator]

theorem primitiveDuplicatorRhs_witnesses_duplication (n : RecordCounter) :
    ∃ p q,
      p ≠ q ∧
      p ∈ generatorPositions (primitiveDuplicatorRhs n) ∧
      q ∈ generatorPositions (primitiveDuplicatorRhs n) := by
  rcases architectural_necessity_of_payload_duplication
      (primitiveDuplicatorRhs_emitsNewRecordFrame n)
      (primitiveDuplicatorRhs_preservesRecursiveGenerator n) with
    ⟨p, q, hpq, hp, hq, _, _⟩
  exact ⟨p, q, hpq, hp, hq⟩

end RecordTerm

end StepDuplicatingSchema
end OperatorKO7.StepDuplicating
