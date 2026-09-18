import OperatorKO7.Meta.Recursor.DPConfessionLicense
import OperatorKO7.Meta.Rewriting.RankedNormalization

/-!
# Free recursor root rules and transformed calls

The carrier is closed recursor syntax. The root relation has two rules; the
transformed-call relation has one. Neither relation uses the KO7 rule catalog.
Extraction retains the callee in the successor rule's right-hand side.
Root extensions are classified by their actual edges, including repeated rules.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel

open OperatorKO7.Meta.Recursor.DPConfessionLicense
open OperatorKO7.Meta.Rewriting

inductive FreeRecursorStep : RecursorTerm → RecursorTerm → Prop
  | zero (b s : RecursorTerm) : FreeRecursorStep (.recR b s .void) b
  | succ (b s n : RecursorTerm) :
      FreeRecursorStep (.recR b s (.delta n)) (.app s (.recR b s n))

inductive FreeRecursorDPPair : RecursorTerm → RecursorTerm → Prop
  | succ (b s n : RecursorTerm) :
      FreeRecursorDPPair (.recR b s (.delta n)) (.recR b s n)

def rootNext : RecursorTerm → Option RecursorTerm
  | .recR b _ .void => some b
  | .recR b s (.delta n) => some (.app s (.recR b s n))
  | _ => none

def dpNext : RecursorTerm → Option RecursorTerm
  | .recR b s (.delta n) => some (.recR b s n)
  | _ => none

theorem rootNext_iff {a b : RecursorTerm} :
    rootNext a = some b ↔ FreeRecursorStep a b := by
  constructor
  · intro h
    cases a <;> simp only [rootNext] at h
    all_goals try contradiction
    case recR base payload counter =>
      cases counter
      all_goals try contradiction
      case void =>
        cases Option.some.inj h
        exact .zero _ payload
      case delta n =>
        cases Option.some.inj h
        exact .succ base payload n
  · intro h
    cases h <;> rfl

theorem dpNext_iff {a c : RecursorTerm} :
    dpNext a = some c ↔ FreeRecursorDPPair a c := by
  constructor
  · intro h
    cases a <;> simp only [dpNext] at h
    all_goals try contradiction
    case recR base payload counter =>
      cases counter
      all_goals try contradiction
      case delta n =>
        cases Option.some.inj h
        exact .succ base payload n
  · intro h
    cases h
    rfl

/-- The extractor checks both the source and the emitted wrapper. -/
def extractCall (a rhs : RecursorTerm) : Option RecursorTerm :=
  match a with
  | .recR b s (.delta n) =>
      if rhs = .app s (.recR b s n) then some (.recR b s n) else none
  | _ => none

theorem extractCall_iff {a rhs c : RecursorTerm} :
    extractCall a rhs = some c ↔
      ∃ b s n, a = .recR b s (.delta n) ∧
        rhs = .app s (.recR b s n) ∧ c = .recR b s n := by
  constructor
  · intro h
    cases a <;> simp only [extractCall] at h
    all_goals try contradiction
    case recR base payload counter =>
      cases counter
      all_goals try contradiction
      case delta n =>
        change (if rhs = .app payload (.recR base payload n) then
          some (.recR base payload n) else none) = some c at h
        by_cases hrhs : rhs = .app payload (.recR base payload n)
        · rw [if_pos hrhs] at h
          exact ⟨base, payload, n, rfl, hrhs, (Option.some.inj h).symm⟩
        · rw [if_neg hrhs] at h
          cases h
  · rintro ⟨b, s, n, rfl, rfl, rfl⟩
    simp [extractCall]

theorem freeRecursor_extraction_sound {a rhs c : RecursorTerm}
    (h : extractCall a rhs = some c) :
    FreeRecursorStep a rhs ∧ FreeRecursorDPPair a c := by
  obtain ⟨b, s, n, rfl, rfl, rfl⟩ := extractCall_iff.mp h
  exact ⟨.succ b s n, .succ b s n⟩

theorem freeRecursor_extraction_complete {a rhs c : RecursorTerm}
    (h : FreeRecursorStep a rhs) :
    extractCall a rhs = some c ↔ FreeRecursorDPPair a c := by
  constructor
  · exact fun he => (freeRecursor_extraction_sound he).2
  · intro hd
    cases h with
    | zero b s => cases hd
    | succ b s n =>
        cases hd
        simp [extractCall]

def deltaPrefix : RecursorTerm → Nat
  | .delta n => deltaPrefix n + 1
  | _ => 0

def stripDelta : RecursorTerm → RecursorTerm
  | .delta n => stripDelta n
  | t => t

def dpRank : RecursorTerm → Nat
  | .recR _ _ n => deltaPrefix n
  | _ => 0

theorem freeRecursor_dp_rank_exact {a c : RecursorTerm}
    (h : FreeRecursorDPPair a c) : dpRank a = dpRank c + 1 := by
  cases h
  rfl

theorem freeRecursor_dp_rank_decreases {a c : RecursorTerm}
    (h : FreeRecursorDPPair a c) : dpRank c < dpRank a := by
  rw [freeRecursor_dp_rank_exact h]
  exact Nat.lt_succ_self _

def dpMachine : RankedMachine RecursorTerm where
  next := dpNext
  rank := dpRank
  decreases := fun h => freeRecursor_dp_rank_decreases (dpNext_iff.mp h)

theorem dpMachine_step_eq : dpMachine.Step = FreeRecursorDPPair := by
  funext a b
  exact propext dpNext_iff

theorem freeRecursor_dp_rev_wellFounded :
    WellFounded (fun a b => FreeRecursorDPPair b a) := by
  simpa only [dpMachine_step_eq] using dpMachine.reverse_wellFounded

theorem freeRecursor_dp_deterministic {a b c : RecursorTerm}
    (h : FreeRecursorDPPair a b) (g : FreeRecursorDPPair a c) : b = c :=
  dpMachine.deterministic (dpNext_iff.mpr h) (dpNext_iff.mpr g)

theorem freeRecursor_dp_confluent {a b c : RecursorTerm}
    (h : Relation.ReflTransGen FreeRecursorDPPair a b)
    (g : Relation.ReflTransGen FreeRecursorDPPair a c) :
    ∃ d, Relation.ReflTransGen FreeRecursorDPPair b d ∧
      Relation.ReflTransGen FreeRecursorDPPair c d := by
  simpa only [dpMachine_step_eq] using
    dpMachine.confluent (dpMachine_step_eq ▸ h) (dpMachine_step_eq ▸ g)

theorem freeRecursor_dp_length (b s n : RecursorTerm) :
    dpMachine.cost (.recR b s n) = deltaPrefix n := by
  induction n with
  | delta n ih =>
      rw [dpMachine.cost_step (show dpMachine.Step (.recR b s (.delta n))
        (.recR b s n) from rfl), ih]
      rfl
  | _ => exact dpMachine.cost_terminal rfl

theorem freeRecursor_dp_normalize (b s n : RecursorTerm) :
    dpMachine.normalize (.recR b s n) = .recR b s (stripDelta n) := by
  induction n with
  | delta n ih =>
      exact (dpMachine.normalize_step (show dpMachine.Step (.recR b s (.delta n))
        (.recR b s n) from rfl)).trans ih
  | _ => exact dpMachine.normalize_terminal rfl

/-- A counter-payload polynomial for the two root rules. -/
def rootWeight : RecursorTerm → Nat
  | .void => 0
  | .delta t | .integrate t => rootWeight t + 1
  | .merge a b | .app a b | .eqWit a b => rootWeight a + rootWeight b + 1
  | .recR b s n => rootWeight b + (rootWeight s + 2) * (rootWeight n + 1)

theorem rootWeight_decreases {a b : RecursorTerm} (h : FreeRecursorStep a b) :
    rootWeight b < rootWeight a := by
  cases h with
  | zero b s => simp [rootWeight]
  | succ b s n =>
      simp only [rootWeight]
      have heq : rootWeight b + (rootWeight s + 2) * (rootWeight n + 1 + 1) =
          rootWeight s + (rootWeight b + (rootWeight s + 2) * (rootWeight n + 1)) + 1 + 1 := by
        ring
      rw [heq]
      exact Nat.lt_succ_self _

def rootMachine : RankedMachine RecursorTerm where
  next := rootNext
  rank := rootWeight
  decreases := fun h => rootWeight_decreases (rootNext_iff.mp h)

theorem rootMachine_step_eq : rootMachine.Step = FreeRecursorStep := by
  funext a b
  exact propext rootNext_iff

theorem freeRecursor_root_deterministic {a b c : RecursorTerm}
    (h : FreeRecursorStep a b) (g : FreeRecursorStep a c) : b = c :=
  rootMachine.deterministic (rootNext_iff.mpr h) (rootNext_iff.mpr g)

/-- Root rewriting stops at the emitted application; it does not reduce its callee. -/
theorem freeRecursor_successor_root_cost (b s n : RecursorTerm) :
    rootMachine.cost (.recR b s (.delta n)) = 1 := by
  rw [rootMachine.cost_step (show rootMachine.Step (.recR b s (.delta n))
    (.app s (.recR b s n)) from rfl)]
  rw [rootMachine.cost_terminal (show rootMachine.next (.app s (.recR b s n)) = none
    from rfl)]

theorem freeRecursor_step_rev_wellFounded :
    WellFounded (fun a b => FreeRecursorStep b a) := by
  simpa only [rootMachine_step_eq] using rootMachine.reverse_wellFounded

theorem freeRecursor_root_confluent {a b c : RecursorTerm}
    (h : Relation.ReflTransGen FreeRecursorStep a b)
    (g : Relation.ReflTransGen FreeRecursorStep a c) :
    ∃ d, Relation.ReflTransGen FreeRecursorStep b d ∧
      Relation.ReflTransGen FreeRecursorStep c d := by
  simpa only [rootMachine_step_eq] using
    rootMachine.confluent (rootMachine_step_eq ▸ h) (rootMachine_step_eq ▸ g)

theorem freeRecursor_normalization_certificate (a : RecursorTerm) :
    Relation.ReflTransGen FreeRecursorStep a (rootMachine.normalize a) ∧
      (∀ b, ¬ FreeRecursorStep (rootMachine.normalize a) b) ∧
      rootMachine.Steps (rootMachine.cost a) a (rootMachine.normalize a) := by
  refine ⟨?_, ?_, rootMachine.normalizing_steps a⟩
  · simpa only [rootMachine_step_eq] using rootMachine.normalize_reachable a
  · intro b hb
    have hs := rootNext_iff.mpr hb
    have hn := rootMachine.normalize_normal a
    change rootNext (rootMachine.normalize a) = none at hn
    rw [hn] at hs
    contradiction

def ExtendedStep (extra : RecursorTerm → RecursorTerm → Prop) (a b : RecursorTerm) : Prop :=
  FreeRecursorStep a b ∨ extra a b

def ExtractionComplete (R : RecursorTerm → RecursorTerm → Prop) : Prop :=
  ∀ a rhs, R a rhs → ∀ c, FreeRecursorDPPair a c → extractCall a rhs = some c

def PairFree (extra : RecursorTerm → RecursorTerm → Prop) : Prop :=
  ∀ a rhs, extra a rhs → ∀ c, ¬ FreeRecursorDPPair a c

/-- Added edges may repeat a successor rule or have no transformed call. -/
def CompatibleExtra (extra : RecursorTerm → RecursorTerm → Prop) : Prop :=
  ∀ a rhs, extra a rhs →
    (∀ c, ¬ FreeRecursorDPPair a c) ∨
      ∃ b s n, a = .recR b s (.delta n) ∧ rhs = .app s (.recR b s n)

theorem rootExtension_extraction_complete_iff_compatible
    (extra : RecursorTerm → RecursorTerm → Prop) :
    ExtractionComplete (ExtendedStep extra) ↔ CompatibleExtra extra := by
  constructor
  · intro hc a rhs he
    cases hn : dpNext a with
    | some c =>
      have hd := dpNext_iff.mp hn
      obtain ⟨b, s, n, ha, hrhs, _⟩ := extractCall_iff.mp (hc a rhs (.inr he) c hd)
      exact .inr ⟨b, s, n, ha, hrhs⟩
    | none =>
      refine .inl (fun c hd => ?_)
      have heq := dpNext_iff.mpr hd
      rw [hn] at heq
      cases heq
  · intro hc a rhs he c hd
    rcases he with hroot | hextra
    · exact (freeRecursor_extraction_complete hroot).mpr hd
    · rcases hc a rhs hextra with hfree | ⟨b, s, n, rfl, rfl⟩
      · exact (hfree c hd).elim
      · exact (freeRecursor_extraction_complete (.succ b s n)).mpr hd

/-- For genuinely new edges, compatibility reduces exactly to pair-freeness. -/
theorem rootExtension_extraction_complete_iff_added_rules_pair_free
    (extra : RecursorTerm → RecursorTerm → Prop)
    (hnew : ∀ a b, extra a b → ¬ FreeRecursorStep a b) :
    ExtractionComplete (ExtendedStep extra) ↔ PairFree extra := by
  rw [rootExtension_extraction_complete_iff_compatible]
  constructor
  · intro hc a rhs he
    rcases hc a rhs he with hfree | ⟨b, s, n, rfl, rfl⟩
    · exact hfree
    · exact (hnew _ _ he (.succ b s n)).elim
  · intro hf a rhs he
    exact .inl (hf a rhs he)

theorem pair_free_extension_extraction_complete
    {extra : RecursorTerm → RecursorTerm → Prop} (h : PairFree extra) :
    ExtractionComplete (ExtendedStep extra) :=
  (rootExtension_extraction_complete_iff_compatible extra).mpr
    (fun a rhs he => .inl (h a rhs he))

/-- Remove edges already present in the two-rule root relation. -/
def newEdges (extra : RecursorTerm → RecursorTerm → Prop)
    (a rhs : RecursorTerm) : Prop := extra a rhs ∧ ¬ FreeRecursorStep a rhs

/-- Every extension is classified without an additional disjointness premise. -/
theorem rootExtension_extraction_complete_iff_new_edges_pair_free
    (extra : RecursorTerm → RecursorTerm → Prop) :
    ExtractionComplete (ExtendedStep extra) ↔ PairFree (newEdges extra) := by
  constructor
  · intro hc a rhs he c hd
    exact he.2 (freeRecursor_extraction_sound (hc a rhs (.inr he.1) c hd)).1
  · intro hf a rhs he c hd
    rcases he with hroot | hextra
    · exact (freeRecursor_extraction_complete hroot).mpr hd
    · by_cases hr : rootNext a = some rhs
      · exact (freeRecursor_extraction_complete (rootNext_iff.mp hr)).mpr hd
      · exact (hf a rhs ⟨hextra, fun hs => hr (rootNext_iff.mpr hs)⟩ c hd).elim

theorem wrong_rhs_extension_not_complete :
    ¬ ExtractionComplete (ExtendedStep (fun a rhs =>
      a = .recR .void .void (.delta .void) ∧ rhs = .void)) := by
  intro h
  have he := h _ _ (.inr ⟨rfl, rfl⟩) _ (FreeRecursorDPPair.succ .void .void .void)
  simp [extractCall] at he

theorem repeated_root_rules_preserve_extraction :
    ExtractionComplete (ExtendedStep FreeRecursorStep) ∧ ¬ PairFree FreeRecursorStep := by
  constructor
  · intro a rhs he c hd
    exact (freeRecursor_extraction_complete (he.elim id id)).mpr hd
  · intro h
    exact h _ _ (.succ .void .void .void) _ (.succ .void .void .void)

def spuriousEdge (a b : RecursorTerm) : Prop := a = .void ∧ b = .delta .void

theorem spurious_not_step : ¬ FreeRecursorStep .void (.delta .void) := by
  intro h
  cases h

theorem spurious_not_dp : ¬ FreeRecursorDPPair .void (.delta .void) := by
  intro h
  cases h

theorem spurious_extension_pair_free : PairFree spuriousEdge := by
  rintro a rhs ⟨rfl, rfl⟩ c h
  cases h

theorem freeRecursor_step_nonvacuous :
    FreeRecursorStep (.recR .void .void (.delta .void))
      (.app .void (.recR .void .void .void)) := .succ _ _ _

theorem freeRecursor_dp_nonvacuous :
    FreeRecursorDPPair (.recR .void .void (.delta .void))
      (.recR .void .void .void) := .succ _ _ _

theorem rootExtension_pair_free_criterion_needs_disjointness :
    ∃ extra : RecursorTerm → RecursorTerm → Prop,
      ExtractionComplete (ExtendedStep extra) ∧ ¬ PairFree extra :=
  ⟨FreeRecursorStep, repeated_root_rules_preserve_extraction⟩

end OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel
