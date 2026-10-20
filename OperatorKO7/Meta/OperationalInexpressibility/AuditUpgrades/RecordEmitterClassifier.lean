import OperatorKO7.Meta.RecordEmissionNecessity_BeyondFirstOrder

/-!
# The three-way classifier of record emitters

Proposition 9.8 states that a classifier places each record emitter in one of the single-sort,
many-sorted or externalized-trace regimes and in one only. Here a record emitter of any regime is
a value of the sum type `AnyRecordEmitter`, and `classify` sends it to its regime.

* `classify_places_each_emitter`: each emitter lies in one regime and in no other.
* `classify_surjective`: each of the three regimes holds an emitter.
* `regimeConclusion_holds`: for every emitter, the conclusion of its regime's theorem holds under
  the hypotheses of that theorem; the three regime theorems are reached through the classifier.

Trust: kernel-only. No `sorry`, no `admit`, no new `axiom`.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.OperationalInexpressibility.AuditUpgrades.RecordEmitterClassifier

open OperatorKO7.StepDuplicating.StepDuplicatingSchema

/-- A record emitter of one of the three regimes. -/
inductive AnyRecordEmitter : Type 1
  | singleSort (rhs : RecordTerm)
  | manySorted {n : Nat} (e : ManySortedRecordEmitter n)
  | externalized {Sys : BaseDuplicatingSystem} {b s : Sys.T}
      (E : BaseDuplicatingSystem.FaithfulRecordEmitter Sys b s)

/-- The regime of an emitter. -/
def classify : AnyRecordEmitter → RecordEmitterClass
  | .singleSort _ => .singleSortFirstOrder
  | .manySorted _ => .manySortedFirstOrder
  | .externalized _ => .externalizedTrace

/-- Membership of an emitter in a regime. -/
def InRegime (c : RecordEmitterClass) (e : AnyRecordEmitter) : Prop := classify e = c

/-- Each emitter lies in one regime and in no other. -/
theorem classify_places_each_emitter (e : AnyRecordEmitter) :
    ∃! c : RecordEmitterClass, InRegime c e :=
  ⟨classify e, rfl, fun _ h => h.symm⟩

/-- Each of the three regimes holds an emitter. -/
theorem classify_surjective : Function.Surjective classify := by
  intro c
  cases c with
  | singleSortFirstOrder => exact ⟨.singleSort RecordTerm.base, rfl⟩
  | manySortedFirstOrder =>
      exact ⟨.manySorted (n := 1) ⟨fun _ => RecordTerm.base⟩, rfl⟩
  | externalizedTrace => exact ⟨.externalized freeFaithfulRecordEmitter, rfl⟩

/-- Two distinct generator positions of a right-hand side, one in a frame slot and one at an
active site. -/
def TwoGeneratorPositions (rhs : RecordTerm) : Prop :=
  ∃ p q : RecordTerm.GeneratorPos,
    p ≠ q ∧ p ∈ RecordTerm.generatorPositions rhs ∧ q ∈ RecordTerm.generatorPositions rhs ∧
      p.isFrameGeneratorPos ∧ q.isActiveGeneratorPos

/-- The conclusion of the regime theorem of an emitter, under the hypotheses of that theorem. -/
def RegimeConclusion : AnyRecordEmitter → Prop
  | .singleSort rhs =>
      RecordTerm.emitsNewRecordFrame rhs → RecordTerm.preservesRecursiveGenerator rhs →
        TwoGeneratorPositions rhs
  | @AnyRecordEmitter.manySorted _ e =>
      ∀ σ, RecordTerm.emitsNewRecordFrame (e.sortTerm σ) →
        RecordTerm.preservesRecursiveGenerator (e.sortTerm σ) →
          TwoGeneratorPositions (e.sortTerm σ)
  | @AnyRecordEmitter.externalized Sys b s E =>
      ∀ (K : Nat) (i j : Fin (K + 1)), i ≠ j →
        E.recordObs (Sys.wrapChain s i.1 b) ≠ E.recordObs (Sys.wrapChain s j.1 b)

/-- For every emitter the conclusion of its regime's theorem holds. -/
theorem regimeConclusion_holds (e : AnyRecordEmitter) : RegimeConclusion e := by
  cases e with
  | singleSort rhs =>
      intro hframe hactive
      exact RecordTerm.architectural_necessity_of_payload_duplication hframe hactive
  | manySorted e =>
      intro σ hframe hactive
      exact record_emission_extension_to_many_sorted e σ hframe hactive
  | externalized E =>
      intro K i j hij
      exact BaseDuplicatingSystem.record_emission_extension_to_externalized_trace E i j hij

/-- The classifier and the regime theorems together: every emitter lies in one regime, every
regime holds an emitter, and the regime conclusion holds for every emitter. -/
theorem record_emitter_classification :
    (∀ e : AnyRecordEmitter, ∃! c : RecordEmitterClass, InRegime c e) ∧
      Function.Surjective classify ∧ (∀ e : AnyRecordEmitter, RegimeConclusion e) :=
  ⟨classify_places_each_emitter, classify_surjective, regimeConclusion_holds⟩

end OperatorKO7.Meta.OperationalInexpressibility.AuditUpgrades.RecordEmitterClassifier
