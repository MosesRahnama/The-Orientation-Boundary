import OperatorKO7.Meta.DistinctionBoundary.MinimalFork.Pointed
import OperatorKO7.Meta.DistinctionBoundary.MinimalFork.KO7LocalConeBridge
import OperatorKO7.Meta.OperationalInexpressibility.LicenseCriterion

/-!
# The observational diagonal fork

Relation: `MapConeStep`, a two-edge relation on three states, and its licensed subrelation
`MapConeLicensed`.
Closure: `Quantitative.Reach`.
Strategy: the complete root relation on the three-state carrier.
Trust: kernel-only; no `sorry`, `admit`, `axiom`, `native_decide`.

An observer that sees the same observation twice holds a diagonal input.  A system that may
answer that input either with a null record ("no new distinction") or with a non-null record
("a new state") is a marked non-joinable fork. This module builds that fork and proves an
exact raw relation isomorphism with the canonical `Fork3`, together with the corresponding
licensed one-edge repair. The separate KO7 local-cone modules identify `Fork3` with the
`eqW` diagonal cone; composing those maps is the correct route from `MapCone` to KO7. No
claim about evidence channels, priors, terminal weights, or overproduction gap follows from
the bare relation isomorphism alone. Below the raw and licensed MapCone presentations are
composed all the way to the existing KO7 local-cone isomorphisms, and their edges are shown
to be exactly live kernel `Step` and licensed `SafeStep` edges on the corresponding three
`Trace` states. The licensed relation refusing the novelty edge is confluent at the diagonal
with a unique verdict.

The observer extension below uses actual input pairs. A decoder decides their equality
from observations alone exactly when the observer is injective. An added channel must
separate every unequal pair identified by the observer. Restricting the raw edges to the
correct record gives a confluent relation for every input pair and recovers the original
licensed relation on actual diagonals.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.DistinctionBoundary.ObservationalDiagonalFork

open OperatorKO7.Meta.DistinctionBoundary.Quantitative
open OperatorKO7.Meta.DistinctionBoundary.MinimalFork

/-- The three states of an observational diagonal: the diagonal input, the null record, and
the novelty record. -/
inductive MapCone where
  | diagonal
  | stable
  | novel
  deriving DecidableEq, Fintype, Repr

/-- The raw relation admits both records from the diagonal. -/
inductive MapConeStep : MapCone → MapCone → Prop where
  | toStable : MapConeStep .diagonal .stable
  | toNovel : MapConeStep .diagonal .novel

theorem stable_normal : OperatorKO7.Meta.DistinctionBoundary.Quantitative.NormalForm MapConeStep .stable := by
  intro y h
  cases h

theorem novel_normal : OperatorKO7.Meta.DistinctionBoundary.Quantitative.NormalForm MapConeStep .novel := by
  intro y h
  cases h

/-- The two records are unjoinable. -/
theorem mapCone_verdicts_unjoinable : ¬ Joinable MapConeStep .stable .novel := by
  rintro ⟨z, hz1, hz2⟩
  have h1 : z = .stable := eq_of_normalForm_reach stable_normal hz1
  have h2 : z = .novel := eq_of_normalForm_reach novel_normal hz2
  exact MapCone.noConfusion (h1.symm.trans h2)

/-- The raw relation is not confluent at the diagonal. -/
theorem mapCone_not_confluentAt_diagonal : ¬ ConfluentAt MapConeStep .diagonal := by
  intro hconf
  exact mapCone_verdicts_unjoinable
    (hconf .stable .novel (reach_step MapConeStep.toStable) (reach_step MapConeStep.toNovel))

/-- The observational diagonal as a marked non-joinable fork. -/
def mapConePointed : PointedFork where
  Carrier := MapCone
  R := MapConeStep
  source := .diagonal
  equal := .stable
  different := .novel
  toEqual := MapConeStep.toStable
  toDifferent := MapConeStep.toNovel
  verdicts_unjoinable := mapCone_verdicts_unjoinable

/-- The carrier bijection with the canonical fork. -/
def fork3EquivMapCone : Fork3 ≃ MapCone where
  toFun
    | .source => .diagonal
    | .equal => .stable
    | .different => .novel
  invFun
    | .diagonal => .source
    | .stable => .equal
    | .novel => .different
  left_inv := by intro x; cases x <;> rfl
  right_inv := by intro x; cases x <;> rfl

/-- The bijection matches the two edge relations exactly. -/
theorem fork3Step_iff_mapConeStep {x y : Fork3} :
    Fork3Step x y ↔ MapConeStep (fork3EquivMapCone x) (fork3EquivMapCone y) := by
  constructor
  · intro h
    cases h with
    | toEqual => exact MapConeStep.toStable
    | toDifferent => exact MapConeStep.toNovel
  · intro h
    cases x <;> cases y <;> simp [fork3EquivMapCone] at h ⊢ <;>
      first
      | exact Fork3Step.toEqual
      | exact Fork3Step.toDifferent
      | cases h

/-- **The map cone is the eqW cone.** `Fork3` and the observational diagonal fork are
relation-isomorphic. -/
def fork3MapConeIso : OperatorKO7.Meta.DistinctionBoundary.MinimalFork.RelIso Fork3Step MapConeStep where
  toEquiv := fork3EquivMapCone
  map_rel_iff := fork3Step_iff_mapConeStep

/-- The canonical mark-forced map from `Fork3` into the map cone is a bijection. -/
theorem canonicalHom_mapCone_bijective :
    Function.Bijective (canonicalHom mapConePointed).toFun := by
  refine ⟨canonicalHom_injective mapConePointed, ?_⟩
  intro y
  cases y with
  | diagonal => exact ⟨.source, rfl⟩
  | stable => exact ⟨.equal, rfl⟩
  | novel => exact ⟨.different, rfl⟩

/-! ## The licensed relation refuses the novelty record -/

/-- Refusing the non-null record on a diagonal input leaves one edge. -/
inductive MapConeLicensed : MapCone → MapCone → Prop where
  | toStable : MapConeLicensed .diagonal .stable

/-- The licensed relation is a subrelation of the raw one. -/
theorem mapConeLicensed_sub {x y : MapCone} (h : MapConeLicensed x y) : MapConeStep x y := by
  cases h
  exact MapConeStep.toStable

/-- The one-edge canonical repair and the licensed MapCone relation agree exactly under the
same carrier equivalence as the raw fork. -/
theorem fork3LicensedStep_iff_mapConeLicensed {x y : Fork3} :
    Fork3LicensedStep x y ↔
      MapConeLicensed (fork3EquivMapCone x) (fork3EquivMapCone y) := by
  cases x <;> cases y <;> constructor <;> intro h <;> cases h <;>
    first | exact MapConeLicensed.toStable | exact Fork3LicensedStep.toEqual

/-- Licensed relation isomorphism from the canonical one-edge repair to the observational
MapCone repair. -/
def fork3MapConeLicensedIso : OperatorKO7.Meta.DistinctionBoundary.MinimalFork.RelIso Fork3LicensedStep MapConeLicensed where
  toEquiv := fork3EquivMapCone
  map_rel_iff := fork3LicensedStep_iff_mapConeLicensed

/-- **Raw MapCone is exactly the live KO7 diagonal cone.** This is composition of the proved
MapCone↔Fork3 and Fork3↔KO7 local relation isomorphisms. -/
noncomputable def mapConeLocalRawIso :
    OperatorKO7.Meta.DistinctionBoundary.MinimalFork.RelIso MapConeStep
      OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7LocalCone.LocalRaw :=
  fork3MapConeIso.symm.trans
    OperatorKO7.Meta.DistinctionBoundary.MinimalFork.KO7LocalConeBridge.fork3LocalRawIso

/-- **Licensed MapCone is exactly the live KO7 licensed cone.** -/
noncomputable def mapConeLocalLicensedIso :
    OperatorKO7.Meta.DistinctionBoundary.MinimalFork.RelIso MapConeLicensed
      OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7LocalCone.LocalLicensed :=
  fork3MapConeLicensedIso.symm.trans
    OperatorKO7.Meta.DistinctionBoundary.MinimalFork.KO7LocalConeBridge.fork3LocalLicensedIso

/-- The observational diagonal embedded into the three live KO7 `Trace` states. -/
def mapConeToTrace (x : MapCone) : OperatorKO7.Trace :=
  OperatorKO7.Meta.DistinctionBoundary.MinimalFork.KO7LocalConeBridge.fork3ToTrace
    (fork3EquivMapCone.symm x)

/-- Raw MapCone edges are exactly live kernel `Step` edges on the three-state image. -/
theorem mapConeStep_iff_ko7Step {x y : MapCone} :
    MapConeStep x y ↔ OperatorKO7.Step (mapConeToTrace x) (mapConeToTrace y) := by
  have hMap :=
    (fork3Step_iff_mapConeStep
      (x := fork3EquivMapCone.symm x) (y := fork3EquivMapCone.symm y)).symm
  have hKO7 :=
    OperatorKO7.Meta.DistinctionBoundary.MinimalFork.KO7LocalConeBridge.fork3Step_iff_ko7Step
      (x := fork3EquivMapCone.symm x) (y := fork3EquivMapCone.symm y)
  simpa [mapConeToTrace] using hMap.trans hKO7

/-- Licensed MapCone edges are exactly live `SafeStep` edges on the same three-state image. -/
theorem mapConeLicensed_iff_ko7SafeStep {x y : MapCone} :
    MapConeLicensed x y ↔
      MetaSN_KO7.SafeStep (mapConeToTrace x) (mapConeToTrace y) := by
  have hMap :=
    (fork3LicensedStep_iff_mapConeLicensed
      (x := fork3EquivMapCone.symm x) (y := fork3EquivMapCone.symm y)).symm
  have hKO7 :=
    OperatorKO7.Meta.DistinctionBoundary.MinimalFork.KO7LocalConeBridge.fork3LicensedStep_iff_safeStep
      (x := fork3EquivMapCone.symm x) (y := fork3EquivMapCone.symm y)
  simpa [mapConeToTrace] using hMap.trans hKO7

/-- The refused edge is inhabited: the license is a strict restriction. -/
theorem novelty_refused : MapConeStep .diagonal .novel ∧ ¬ MapConeLicensed .diagonal .novel :=
  ⟨MapConeStep.toNovel, fun h => by cases h⟩

/-- Every state reachable from the diagonal under the licensed relation is the diagonal or
the null record. -/
theorem licensed_reach_diagonal {y : MapCone} (h : Reach MapConeLicensed .diagonal y) :
    y = .diagonal ∨ y = .stable := by
  rcases h with ⟨n, hn⟩
  cases hn with
  | zero => exact Or.inl rfl
  | succ hstep hrest =>
      cases hstep
      cases hrest with
      | zero => exact Or.inr rfl
      | succ hstep' _ => cases hstep'

/-- The licensed relation is confluent at the diagonal: the null record is the unique verdict. -/
theorem licensed_confluentAt_diagonal : ConfluentAt MapConeLicensed .diagonal := by
  intro x y hx hy
  refine ⟨.stable, ?_, ?_⟩
  · rcases licensed_reach_diagonal hx with rfl | rfl
    · exact reach_step MapConeLicensed.toStable
    · exact reach_refl _
  · rcases licensed_reach_diagonal hy with rfl | rfl
    · exact reach_step MapConeLicensed.toStable
    · exact reach_refl _

/-- A non-null record on a diagonal input is available only in the raw relation: the licensed
relation reaches no novelty record from the diagonal. -/
theorem licensed_never_reaches_novel : ¬ Reach MapConeLicensed .diagonal .novel := by
  intro h
  rcases licensed_reach_diagonal h with h1 | h1 <;> cases h1

/-! ## Actual observations and equality records -/

universe u v w

/-- The observations available for a comparison of two source states. -/
def pairObservation {X : Type u} {Q : Type v} (q : X → Q) (p : X × X) : Q × Q :=
  (q p.1, q p.2)

/-- The stable record asserts equality; the novel record asserts disequality. -/
def RecordCorrect {X : Type u} (x y : X) (r : MapCone) : Prop :=
  (r = .stable ∧ x = y) ∨ (r = .novel ∧ x ≠ y)

theorem recordCorrect_stable_iff {X : Type u} (x y : X) :
    RecordCorrect x y .stable ↔ x = y := by simp [RecordCorrect]

theorem recordCorrect_novel_iff {X : Type u} (x y : X) :
    RecordCorrect x y .novel ↔ x ≠ y := by simp [RecordCorrect]

theorem recordCorrect_self_iff {X : Type u} (x : X) (r : MapCone) :
    RecordCorrect x x r ↔ r = .stable := by simp [RecordCorrect]

theorem RecordCorrect.unique {X : Type u} {x y : X} {r s : MapCone}
    (hr : RecordCorrect x y r) (hs : RecordCorrect x y s) : r = s := by
  rcases hr with ⟨rfl, heq⟩ | ⟨rfl, hne⟩
  · rcases hs with ⟨rfl, _⟩ | ⟨rfl, hne⟩
    · rfl
    · exact (hne heq).elim
  · rcases hs with ⟨rfl, heq⟩ | ⟨rfl, _⟩
    · exact (hne heq).elim
    · rfl

def intendedRecord {X : Type u} [DecidableEq X] (x y : X) : MapCone :=
  if x = y then .stable else .novel

theorem intendedRecord_correct {X : Type u} [DecidableEq X] (x y : X) :
    RecordCorrect x y (intendedRecord x y) := by
  by_cases h : x = y
  · exact Or.inl ⟨if_pos h, h⟩
  · exact Or.inr ⟨if_neg h, h⟩

theorem recordCorrect_iff_intended {X : Type u} [DecidableEq X]
    (x y : X) (r : MapCone) :
    RecordCorrect x y r ↔ r = intendedRecord x y := by
  constructor
  · exact fun h => h.unique (intendedRecord_correct x y)
  · rintro rfl
    exact intendedRecord_correct x y

/-- A decoder receives only the two observations, not the source states. -/
def ObservedDecoderCorrect {X : Type u} {Q : Type v}
    (q : X → Q) (decoder : Q × Q → MapCone) : Prop :=
  ∀ x y, RecordCorrect x y (decoder (q x, q y))

theorem ObservedDecoderCorrect.injective {X : Type u} {Q : Type v}
    {q : X → Q} {decoder : Q × Q → MapCone}
    (h : ObservedDecoderCorrect q decoder) : Function.Injective q := by
  intro x y hxy
  have hd := (recordCorrect_self_iff x _).mp (h x x)
  have hrec := h x y
  rw [← hxy, hd] at hrec
  exact (recordCorrect_stable_iff x y).mp hrec

/-- This decoder compares the received observations. -/
def observerDecoder {Q : Type v} [DecidableEq Q] (p : Q × Q) : MapCone :=
  intendedRecord p.1 p.2

theorem observerDecoder_correct_of_injective {X : Type u} {Q : Type v}
    [DecidableEq Q] (q : X → Q) (hq : Function.Injective q) :
    ObservedDecoderCorrect q observerDecoder := by
  intro x y
  by_cases h : q x = q y
  · exact Or.inl ⟨if_pos h, hq h⟩
  · exact Or.inr ⟨if_neg h, fun he => h (congrArg q he)⟩

/-- Arbitrary source and observation types, including empty types. -/
theorem observedDecoder_exists_iff_injective {X : Type u} {Q : Type v} (q : X → Q) :
    (∃ decoder, ObservedDecoderCorrect q decoder) ↔ Function.Injective q := by
  classical
  exact ⟨fun ⟨_, h⟩ => h.injective, fun h => ⟨observerDecoder, observerDecoder_correct_of_injective q h⟩⟩

/-- A fixed collapsed unequal pair prevents correctness on that pair and its
actual diagonal simultaneously. -/
theorem collapsed_pair_decoder_failure {X : Type u} {Q : Type v}
    (q : X → Q) (decoder : Q × Q → MapCone) {x y : X}
    (hq : q x = q y) (hne : x ≠ y) :
    ¬ (RecordCorrect x x (decoder (q x, q x)) ∧
      RecordCorrect x y (decoder (q x, q y))) := by
  rintro ⟨hdiag, hpair⟩
  have hd := (recordCorrect_self_iff x _).mp hdiag
  rw [← hq, hd] at hpair
  exact hne ((recordCorrect_stable_iff x y).mp hpair)

/-- Equality records factor through the paired observer exactly when the
observer preserves every source-state distinction. -/
theorem intendedRecord_licensed_iff_injective {X : Type u} {Q : Type v}
    [DecidableEq X] (q : X → Q) :
    OperatorKO7.Meta.OperationalInexpressibility.LicenseCriterion.Licensed
      (pairObservation q) (fun p : X × X => intendedRecord p.1 p.2) ↔
        Function.Injective q := by
  constructor
  · intro h x y hxy
    have he := h (x, x) (x, y) (Prod.ext rfl hxy)
    have hr : intendedRecord x y = .stable :=
      he.symm.trans (by simp [intendedRecord])
    have hc := intendedRecord_correct x y
    rw [hr] at hc
    exact (recordCorrect_stable_iff x y).mp hc
  · intro h p r hpr
    have hp : p.1 = r.1 := h (congrArg Prod.fst hpr)
    have hr : p.2 = r.2 := h (congrArg Prod.snd hpr)
    exact congrArg (fun t : X × X => intendedRecord t.1 t.2) (Prod.ext hp hr)

theorem joint_decoder_exists_iff_injective {X : Type u} {Q : Type v} {Z : Type w}
    (q : X → Q) (channel : X → Z) :
    (∃ decoder, ObservedDecoderCorrect (fun x => (q x, channel x)) decoder) ↔
      Function.Injective (fun x => (q x, channel x)) :=
  observedDecoder_exists_iff_injective _

/-- A channel supporting correct comparison must separate every unequal pair
already identified by the base observer. -/
theorem novelty_requires_exogenous_distinction
    {X : Type u} {Q : Type v} {Z : Type w}
    {q : X → Q} {channel : X → Z}
    {decoder : (Q × Z) × (Q × Z) → MapCone}
    (h : ObservedDecoderCorrect (fun x => (q x, channel x)) decoder)
    {x y : X} (hq : q x = q y) (hne : x ≠ y) : channel x ≠ channel y := by
  intro hc
  exact hne (h.injective (Prod.ext hq hc))

/-! ## The correct-record restriction on the same three states -/

def TruthLicensed {X : Type u} (x y : X) (a b : MapCone) : Prop :=
  MapConeStep a b ∧ RecordCorrect x y b

theorem RecordCorrect.raw_edge {X : Type u} {x y : X} {r : MapCone}
    (h : RecordCorrect x y r) : MapConeStep .diagonal r := by
  rcases h with ⟨rfl, _⟩ | ⟨rfl, _⟩
  · exact MapConeStep.toStable
  · exact MapConeStep.toNovel

theorem RecordCorrect.raw_normal {X : Type u} {x y : X} {r : MapCone}
    (h : RecordCorrect x y r) :
    OperatorKO7.Meta.DistinctionBoundary.Quantitative.NormalForm MapConeStep r := by
  rcases h with ⟨rfl, _⟩ | ⟨rfl, _⟩
  · exact stable_normal
  · exact novel_normal

theorem truthLicensed_deterministic {X : Type u} (x y : X)
    {a b c : MapCone} (hab : TruthLicensed x y a b) (hac : TruthLicensed x y a c) :
    b = c :=
  hab.2.unique hac.2

theorem truthLicensed_record_normal {X : Type u} {x y : X} {r : MapCone}
    (h : RecordCorrect x y r) :
    OperatorKO7.Meta.DistinctionBoundary.Quantitative.NormalForm (TruthLicensed x y) r := by
  intro z hz
  exact h.raw_normal z hz.1

theorem truthLicensed_reach_diagonal {X : Type u} (x y : X) {r : MapCone}
    (h : Reach (TruthLicensed x y) .diagonal r) :
    r = .diagonal ∨ RecordCorrect x y r := by
  rcases h with ⟨n, hn⟩
  cases hn with
  | zero => exact Or.inl rfl
  | succ hstep hrest =>
      have heq := eq_of_normalForm_reach
        (truthLicensed_record_normal hstep.2) ⟨_, hrest⟩
      exact Or.inr (heq.symm ▸ hstep.2)

theorem truthLicensed_confluentAt_diagonal {X : Type u} (x y : X) :
    ConfluentAt (TruthLicensed x y) .diagonal := by
  classical
  intro a b ha hb
  have hc := intendedRecord_correct x y
  refine ⟨intendedRecord x y, ?_, ?_⟩
  · rcases truthLicensed_reach_diagonal x y ha with rfl | hrec
    · exact reach_step ⟨hc.raw_edge, hc⟩
    · rw [hrec.unique hc]
      exact reach_refl _
  · rcases truthLicensed_reach_diagonal x y hb with rfl | hrec
    · exact reach_step ⟨hc.raw_edge, hc⟩
    · rw [hrec.unique hc]
      exact reach_refl _

/-- At an actual diagonal, the truth restriction is the original one-edge repair. -/
theorem truthLicensed_self_iff {X : Type u} (x : X) (a b : MapCone) :
    TruthLicensed x x a b ↔ MapConeLicensed a b := by
  constructor
  · rintro ⟨hraw, hcorrect⟩
    have hb := (recordCorrect_self_iff x b).mp hcorrect
    subst b
    cases hraw
    exact MapConeLicensed.toStable
  · intro h
    cases h
    exact ⟨MapConeStep.toStable, (recordCorrect_stable_iff x x).mpr rfl⟩

end OperatorKO7.Meta.DistinctionBoundary.ObservationalDiagonalFork
