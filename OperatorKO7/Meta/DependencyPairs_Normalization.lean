import OperatorKO7.Meta.DependencyPairs_Works
import OperatorKO7.Meta.FreeStepDuplicatingSyntax
import OperatorKO7.Meta.Rewriting.RankedNormalization

/-! # Determinism, confluence, normalization, and length of recursor pairs

The pair relation contracts only a successor at the head of the counter.
`RankedMachine` proves the normalization laws for any deterministic ranked relation;
the two instances below use free recursor syntax and the KO7 pair relation.
-/

namespace OperatorKO7.MetaDependencyPairs

open Trace
open OperatorKO7.Meta.Rewriting
open OperatorKO7.CompositionalImpossibility

def dpNext : Trace → Option Trace
  | .recΔ b s (.delta n) => some (.recΔ b s n)
  | _ => none

theorem dpNext_iff {a b : Trace} : dpNext a = some b ↔ DPPair a b := by
  constructor
  · intro h
    cases a <;> simp only [dpNext] at h
    all_goals try contradiction
    case recΔ base payload counter =>
      cases counter
      all_goals try contradiction
      case delta n =>
        cases Option.some.inj h
        exact DPPair.rec_succ base payload n
  · intro h
    cases h
    rfl

def dpMachine : RankedMachine Trace where
  next := dpNext
  rank := dpRank
  decreases := fun h => dpPair_decreases (dpNext_iff.mp h)

theorem dpMachine_step_iff {a b : Trace} : dpMachine.Step a b ↔ DPPair a b :=
  dpNext_iff

theorem dpPair_deterministic {a b c : Trace} (h : DPPair a b) (g : DPPair a c) : b = c :=
  dpMachine.deterministic (dpNext_iff.mpr h) (dpNext_iff.mpr g)

def dpNormalize : Trace → Trace := dpMachine.normalize
def dpLength : Trace → Nat := dpMachine.cost

theorem dpNormalize_reachable (a : Trace) :
    Relation.ReflTransGen DPPair a (dpNormalize a) := by
  have heq : dpMachine.Step = DPPair := by
    funext x y
    exact propext dpNext_iff
  simpa [dpNormalize, heq] using dpMachine.normalize_reachable a

theorem dpNormalize_normal (a : Trace) : ∀ b, ¬ DPPair (dpNormalize a) b := by
  intro b hb
  have h := dpNext_iff.mpr hb
  have hn := dpMachine.normalize_normal a
  simp only [dpNormalize, dpMachine] at h hn
  rw [hn] at h
  contradiction

theorem dpNormalize_step {a b : Trace} (h : DPPair a b) :
    dpNormalize a = dpNormalize b := dpMachine.normalize_step (dpNext_iff.mpr h)

theorem dpNormalize_star {a b : Trace} (h : Relation.ReflTransGen DPPair a b) :
    dpNormalize a = dpNormalize b := by
  induction h with
  | refl => rfl
  | tail _ hs ih => exact ih.trans (dpNormalize_step hs)

theorem dpPair_confluent {a b c : Trace}
    (h : Relation.ReflTransGen DPPair a b) (g : Relation.ReflTransGen DPPair a c) :
    ∃ d, Relation.ReflTransGen DPPair b d ∧ Relation.ReflTransGen DPPair c d := by
  refine ⟨dpNormalize a, ?_, ?_⟩
  · rw [dpNormalize_star h]; exact dpNormalize_reachable b
  · rw [dpNormalize_star g]; exact dpNormalize_reachable c

def deltaPrefix : Trace → Nat
  | .delta n => deltaPrefix n + 1
  | _ => 0

def stripDelta : Trace → Trace
  | .delta n => stripDelta n
  | t => t

theorem dpLength_rec (b s n : Trace) : dpLength (.recΔ b s n) = deltaPrefix n := by
  induction n with
  | delta n ih =>
    have h := dpMachine.cost_step (show dpMachine.Step (.recΔ b s (.delta n))
      (.recΔ b s n) from rfl)
    change dpLength (.recΔ b s (.delta n)) = dpLength (.recΔ b s n) + 1 at h
    simpa [deltaPrefix, ih] using h
  | _ => exact dpMachine.cost_terminal rfl

theorem dpNormalize_rec (b s n : Trace) :
    dpNormalize (.recΔ b s n) = .recΔ b s (stripDelta n) := by
  induction n with
  | delta n ih => exact (dpNormalize_step (DPPair.rec_succ b s n)).trans ih
  | _ => exact dpMachine.normalize_terminal rfl

theorem dpNormalize_idempotent (a : Trace) : dpNormalize (dpNormalize a) = dpNormalize a :=
  dpMachine.normalize_idempotent a

/-- Counter rank bounds length; a nested recursor need not expose a pair step. -/
theorem dpRank_not_dpLength :
    dpRank (.recΔ .void .void (.recΔ .void .void (.delta .void))) = 1 ∧
    dpLength (.recΔ .void .void (.recΔ .void .void (.delta .void))) = 0 := by
  constructor
  · rfl
  · exact dpMachine.cost_terminal rfl

theorem dpLength_counterEncoding (n : Nat) : dpLength (dpCounterEncoding n) = n := by
  rw [dpCounterEncoding, dpLength_rec]
  induction n with
  | zero => rfl
  | succ n ih => simpa [dpCounterTower, deltaPrefix] using ih

theorem dp_normalization_certificate (a : Trace) :
    Relation.ReflTransGen DPPair a (dpNormalize a) ∧
    (∀ b, ¬ DPPair (dpNormalize a) b) ∧
    dpMachine.Steps (dpLength a) a (dpNormalize a) ∧ dpLength a ≤ dpRank a :=
  ⟨dpNormalize_reachable a, dpNormalize_normal a,
    dpMachine.normalizing_steps a, dpMachine.cost_le_rank a⟩

end OperatorKO7.MetaDependencyPairs

namespace OperatorKO7.StepDuplicating.StepDuplicatingSchema

open OperatorKO7.Meta.Rewriting

/-- The transformed call decreases every schema projection by exactly one. -/
theorem projection_pair_rank {S : StepDuplicatingSchema} (R : ProjectionRank S)
    (b s n : S.T) :
    R.rank (S.recur b s (S.succ n)) = R.rank (S.recur b s n) + 1 := by
  rw [R.rank_recur, R.rank_recur, R.rank_succ]

/-- The free recursor's transformed call relation, before any KO7 instantiation. -/
inductive FreeDPPair : FreeTerm → FreeTerm → Prop
  | rec_succ (b s n : FreeTerm) : FreeDPPair (.recur b s (.succ n)) (.recur b s n)

def freeDPNext : FreeTerm → Option FreeTerm
  | .recur b s (.succ n) => some (.recur b s n)
  | _ => none

theorem freeDPNext_iff {a b : FreeTerm} : freeDPNext a = some b ↔ FreeDPPair a b := by
  constructor
  · intro h
    cases a <;> simp only [freeDPNext] at h
    all_goals try contradiction
    case recur baseTerm payload counter =>
      cases counter
      all_goals try contradiction
      case succ n =>
        cases Option.some.inj h
        exact FreeDPPair.rec_succ baseTerm payload n
  · intro h
    cases h
    rfl

def freeDPMachine : RankedMachine FreeTerm where
  next := freeDPNext
  rank := freeCounterDepth
  decreases := by
    intro a b h
    have hp := freeDPNext_iff.mp h
    cases hp
    simp [freeCounterDepth]

theorem freeDPPair_deterministic {a b c : FreeTerm}
    (h : FreeDPPair a b) (g : FreeDPPair a c) : b = c :=
  freeDPMachine.deterministic (freeDPNext_iff.mpr h) (freeDPNext_iff.mpr g)

theorem freeDPPair_reverse_wellFounded : WellFounded (fun a b => FreeDPPair b a) :=
  Subrelation.wf (fun h => freeDPMachine.decreases (freeDPNext_iff.mpr h))
    (measure freeCounterDepth).wf

theorem freeDPPair_confluent {a b c : FreeTerm}
    (h : Relation.ReflTransGen FreeDPPair a b)
    (g : Relation.ReflTransGen FreeDPPair a c) :
    ∃ d, Relation.ReflTransGen FreeDPPair b d ∧ Relation.ReflTransGen FreeDPPair c d := by
  have heq : freeDPMachine.Step = FreeDPPair := by
    funext a b
    exact propext freeDPNext_iff
  simpa [heq] using freeDPMachine.confluent (heq ▸ h) (heq ▸ g)

def freeSuccPrefix : FreeTerm → Nat
  | .succ n => freeSuccPrefix n + 1
  | _ => 0

def freeStripSucc : FreeTerm → FreeTerm
  | .succ n => freeStripSucc n
  | t => t

theorem freeDP_cost_recur (b s n : FreeTerm) :
    freeDPMachine.cost (.recur b s n) = freeSuccPrefix n := by
  induction n with
  | succ n ih =>
    rw [freeDPMachine.cost_step (show freeDPMachine.Step (.recur b s (.succ n))
      (.recur b s n) from rfl), ih]
    rfl
  | _ => exact freeDPMachine.cost_terminal rfl

theorem freeDP_normalize_recur (b s n : FreeTerm) :
    freeDPMachine.normalize (.recur b s n) = .recur b s (freeStripSucc n) := by
  induction n with
  | succ n ih =>
    exact (freeDPMachine.normalize_step (show freeDPMachine.Step (.recur b s (.succ n))
      (.recur b s n) from rfl)).trans ih
  | _ => exact freeDPMachine.normalize_terminal rfl

theorem freeDP_normalization_certificate (a : FreeTerm) :
    Relation.ReflTransGen FreeDPPair a (freeDPMachine.normalize a) ∧
    (∀ b, ¬ FreeDPPair (freeDPMachine.normalize a) b) ∧
    freeDPMachine.Steps (freeDPMachine.cost a) a (freeDPMachine.normalize a) := by
  have heq : freeDPMachine.Step = FreeDPPair := by
    funext a b
    exact propext freeDPNext_iff
  refine ⟨by simpa [heq] using freeDPMachine.normalize_reachable a, ?_,
    freeDPMachine.normalizing_steps a⟩
  intro b hb
  have h := freeDPNext_iff.mpr hb
  have hn := freeDPMachine.normalize_normal a
  change freeDPNext (freeDPMachine.normalize a) = none at hn
  rw [hn] at h
  contradiction

end OperatorKO7.StepDuplicating.StepDuplicatingSchema
