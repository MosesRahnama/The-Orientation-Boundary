import OperatorKO7.Meta.Methods.OrientationClosure.SchemaCore

/-!
# Generic transport laws for the Orientation Boundary

Theorems in this module separate the properties that transport under relation
extension, faithful renaming, and substrate simulation.  In particular,
termination transport requires a positive target path for every source step;
reflexive zero-step simulation is insufficient.

The last section holds two deleted-premise controls of the transport table: a contextual relation
that misses the duplicating root step and is oriented by term size while the root relation is not
(the root-to-contextual barrier transfer without its inclusion premise), and a confluent four-state
relation whose identity embedding reflects steps and has a closed image but drops two steps, so the
target is not confluent (the confluence transfer without step preservation).
-/

set_option autoImplicit false

namespace OperatorKO7.Methods.OrientationClosure.TransportLaws

universe u v w

/-- A measure orients a relation when every forward source step maps to a strict
target comparison. -/
def OrientsRelation {A : Type u} {B : Type v}
    (R : A → A → Prop) (m : A → B) (lt : B → B → Prop) : Prop :=
  ∀ {a b}, R a b → lt (m b) (m a)

/-- A negative orientation result survives any rule/relation extension that
retains the obstructing source relation. -/
theorem no_orienter_of_subrelation
    {A : Type u} {B : Type v}
    {R S : A → A → Prop} {m : A → B} {lt : B → B → Prop}
    (hsub : ∀ {a b}, R a b → S a b)
    (hno : ¬ OrientsRelation R m lt) :
    ¬ OrientsRelation S m lt := by
  intro hS
  apply hno
  intro a b hR
  exact hS (hsub hR)

/-- Restricting a well-founded relation preserves well-foundedness. -/
theorem wellFounded_of_subrelation
    {A : Type u} {R S : A → A → Prop}
    (hsub : ∀ {a b}, R a b → S a b)
    (hS : WellFounded (fun y x => S x y)) :
    WellFounded (fun y x => R x y) := by
  exact Subrelation.wf (fun {_ _} h => hsub h) hS

/-! ## Faithful renaming -/

/-- Transport a relation through a bijective change of names. -/
def renamedRelation {A : Type u} {B : Type v}
    (e : A ≃ B) (R : A → A → Prop) (x y : B) : Prop :=
  R (e.symm x) (e.symm y)

/-- Bijective renaming preserves reverse well-foundedness. -/
theorem renamedRelation_wellFounded
    {A : Type u} {B : Type v} (e : A ≃ B) (R : A → A → Prop)
    (hR : WellFounded (fun y x => R x y)) :
    WellFounded (fun y x => renamedRelation e R x y) := by
  exact InvImage.wf e.symm hR

/-- The converse holds under the inverse renaming. -/
theorem originalRelation_wellFounded_of_renamed
    {A : Type u} {B : Type v} (e : A ≃ B) (R : A → A → Prop)
    (hB : WellFounded (fun y x => renamedRelation e R x y)) :
    WellFounded (fun y x => R x y) := by
  apply Subrelation.wf
    (r := InvImage (fun y x : B => renamedRelation e R x y) e)
  · intro y x h
    change renamedRelation e R (e x) (e y)
    simpa [renamedRelation] using h
  · exact InvImage.wf e hB

/-- Therefore faithful renaming preserves and reflects termination. -/
theorem renamedRelation_wellFounded_iff
    {A : Type u} {B : Type v} (e : A ≃ B) (R : A → A → Prop) :
    WellFounded (fun y x => renamedRelation e R x y) ↔
      WellFounded (fun y x => R x y) :=
  ⟨originalRelation_wellFounded_of_renamed e R,
    renamedRelation_wellFounded e R⟩

/-! ## Positive-path simulation -/

/-- Every source edge is simulated by a nonempty target path.  The target path
is stated in reverse-relation form so it feeds well-foundedness directly. -/
structure PositiveSimulation
    (A : Type u) (B : Type v)
    (Source : A → A → Prop) (Target : B → B → Prop) where
  encode : A → B
  forward : ∀ {a b}, Source a b →
    Relation.TransGen (fun y x => Target x y) (encode b) (encode a)

/-- Positive simulation into a terminating target proves source termination. -/
theorem source_wellFounded_of_positiveSimulation
    {A : Type u} {B : Type v}
    {Source : A → A → Prop} {Target : B → B → Prop}
    (S : PositiveSimulation A B Source Target)
    (hTarget : WellFounded (fun y x => Target x y)) :
    WellFounded (fun y x => Source x y) := by
  have hTargetPlus :
      WellFounded (Relation.TransGen (fun y x => Target x y)) := hTarget.transGen
  apply Subrelation.wf
    (r := InvImage (Relation.TransGen (fun y x => Target x y)) S.encode)
  · intro y x h
    exact S.forward h
  · exact InvImage.wf S.encode hTargetPlus

/-- Injectivity is not required for termination transport when every source
step makes positive target progress. -/
theorem positiveSimulation_injectivity_not_required
    {A : Type u} {B : Type v}
    {Source : A → A → Prop} {Target : B → B → Prop}
    (S : PositiveSimulation A B Source Target)
    (hTarget : WellFounded (fun y x => Target x y)) :
    WellFounded (fun y x => Source x y) :=
  source_wellFounded_of_positiveSimulation S hTarget

/-! ## Zero-step simulation is insufficient -/

/-- Reflexive simulation permits a source edge to disappear into zero target
steps. -/
structure ReflexiveSimulation
    (A : Type u) (B : Type v)
    (Source : A → A → Prop) (Target : B → B → Prop) where
  encode : A → B
  forward : ∀ {a b}, Source a b →
    Relation.ReflTransGen (fun y x => Target x y) (encode b) (encode a)

/-- One-state looping source. -/
def LoopSource (_ _ : Unit) : Prop := True

/-- Empty target relation. -/
def EmptyTarget (_ _ : Unit) : Prop := False

/-- Constant encoding gives a reflexive zero-step simulation of the looping
source into the empty target. -/
def zeroStepLoopSimulation :
    ReflexiveSimulation Unit Unit LoopSource EmptyTarget where
  encode := fun _ => ()
  forward := by
    intro a b h
    exact Relation.ReflTransGen.refl

/-- The empty target terminates. -/
theorem emptyTarget_wellFounded :
    WellFounded (fun y x : Unit => EmptyTarget x y) := by
  exact ⟨fun a => Acc.intro a (fun _ h => False.elim h)⟩

/-- The looping source does not terminate. -/
theorem loopSource_not_wellFounded :
    ¬ WellFounded (fun y x : Unit => LoopSource x y) := by
  intro hwf
  have hloop : LoopSource () () := trivial
  exact (hwf.asymmetric () () hloop) hloop

/-- Machine-checked falsifier for replacing positive-path simulation by a
reflexive simulation. -/
theorem reflexiveSimulation_does_not_transfer_termination :
    Nonempty (ReflexiveSimulation Unit Unit LoopSource EmptyTarget) ∧
      WellFounded (fun y x : Unit => EmptyTarget x y) ∧
      ¬ WellFounded (fun y x : Unit => LoopSource x y) :=
  ⟨⟨zeroStepLoopSimulation⟩, emptyTarget_wellFounded,
    loopSource_not_wellFounded⟩

/-! ## Row 1 control: a contextual relation that misses a root step -/

/-- Number of variable and constructor occurrences of a free term.
Proves: nothing; a definition.
Scope: free terms over every variable type. -/
def transportControlSize {ν : Type u} : SchemaCore.FreeTerm ν → Nat
  | .var _ => 1
  | .zero => 1
  | .succ t => transportControlSize t + 1
  | .wrap s t => transportControlSize s + transportControlSize t + 1
  | .recur b s n => transportControlSize b + transportControlSize s + transportControlSize n + 1

/-- Proves: plugging into a one-hole constructor context preserves strict decrease of
`transportControlSize`.
Does not prove: anything for other measures.
Relation: none; a measure inequality under contexts.
Closure: one-hole constructor contexts. Strategy: not applicable.
Trust: kernel only.
Scope: free terms over every variable type. -/
theorem transportControlSize_plug_lt {ν : Type u} (C : SchemaCore.FreeContext ν)
    {t u : SchemaCore.FreeTerm ν} (h : transportControlSize u < transportControlSize t) :
    transportControlSize (C.plug u) < transportControlSize (C.plug t) := by
  induction C with
  | hole => exact h
  | succ C ih =>
      simp only [SchemaCore.FreeContext.plug, transportControlSize]
      omega
  | wrapLeft C r ih =>
      simp only [SchemaCore.FreeContext.plug, transportControlSize]
      omega
  | wrapRight l C ih =>
      simp only [SchemaCore.FreeContext.plug, transportControlSize]
      omega
  | recurBase C s n ih =>
      simp only [SchemaCore.FreeContext.plug, transportControlSize]
      omega
  | recurStep b C n ih =>
      simp only [SchemaCore.FreeContext.plug, transportControlSize]
      omega
  | recurCounter b s C ih =>
      simp only [SchemaCore.FreeContext.plug, transportControlSize]
      omega

/-- One-hole contextual closure of the zero rule `recur b s zero → b` alone. -/
inductive ZeroRuleContextStep {ν : Type u} :
    SchemaCore.FreeTerm ν → SchemaCore.FreeTerm ν → Prop where
  | lift (C : SchemaCore.FreeContext ν) (b s : SchemaCore.FreeTerm ν) :
      ZeroRuleContextStep (C.plug (.recur b s .zero)) (C.plug b)

/-- Proves: every step of `ZeroRuleContextStep` is a step of the contextual relation
`SchemaCore.ContextStep`.
Does not prove: the converse; the duplicating rule is missing.
Relation: `ZeroRuleContextStep` against `ContextStep`.
Closure: one-hole constructor contexts. Strategy: full.
Trust: kernel only.
Scope: free terms over every variable type. -/
theorem zeroRuleContextStep_contextStep {ν : Type u} {t u : SchemaCore.FreeTerm ν}
    (h : ZeroRuleContextStep t u) : SchemaCore.ContextStep t u := by
  cases h with
  | lift C b s => exact SchemaCore.ContextStep.lift C (SchemaCore.RootStep.recurZero b s)

/-- Proves: `transportControlSize` strictly decreases along every step of `ZeroRuleContextStep`.
Does not prove: decrease along the duplicating rule.
Relation: `ZeroRuleContextStep`.
Closure: one-hole constructor contexts. Strategy: full.
Trust: kernel only.
Scope: free terms over every variable type. -/
theorem transportControlSize_orients_zeroRuleContextStep {ν : Type u} :
    OrientsRelation (ZeroRuleContextStep (ν := ν)) transportControlSize (· < ·) := by
  intro t u h
  cases h with
  | lift C b s =>
      apply transportControlSize_plug_lt C
      simp only [transportControlSize]
      omega

/-- Deleted-premise control of the transfer from a root barrier to a contextual barrier.
Proves: the free root relation has a step that `ZeroRuleContextStep` lacks; `ZeroRuleContextStep`
is contained in the contextual relation; `transportControlSize` fails to orient the root relation
and orients `ZeroRuleContextStep`. The transfer `no_orienter_of_subrelation` is therefore false
with its inclusion premise deleted.
Does not prove: that every contextual relation missing a root step loses the barrier.
Relation: `SchemaCore.RootStep` and `ZeroRuleContextStep` on closed free terms.
Closure: root for the barrier, one-hole contexts for the orienting relation. Strategy: full.
Trust: kernel only.
Scope: closed free terms, the measure `transportControlSize`. -/
theorem rootBarrier_transfer_fails_without_root_inclusion :
    (∃ t u : SchemaCore.FreeTerm Empty,
        SchemaCore.RootStep t u ∧ ¬ ZeroRuleContextStep t u) ∧
      (∀ {t u : SchemaCore.FreeTerm Empty}, ZeroRuleContextStep t u →
        SchemaCore.ContextStep t u) ∧
      ¬ OrientsRelation (SchemaCore.RootStep (ν := Empty)) transportControlSize (· < ·) ∧
      OrientsRelation (ZeroRuleContextStep (ν := Empty)) transportControlSize (· < ·) := by
  refine ⟨⟨.recur .zero .zero (.succ .zero), .wrap .zero (.recur .zero .zero .zero),
      SchemaCore.RootStep.recurSucc _ _ _, fun hz => ?_⟩,
    fun h => zeroRuleContextStep_contextStep h, fun horient => ?_,
    transportControlSize_orients_zeroRuleContextStep⟩
  · have hlt := transportControlSize_orients_zeroRuleContextStep hz
    simp only [transportControlSize] at hlt
    omega
  · have hlt := horient (SchemaCore.RootStep.recurSucc (.zero : SchemaCore.FreeTerm Empty)
      .zero .zero)
    simp only [transportControlSize] at hlt
    omega

/-! ## Row 8 control: step reflection without step preservation -/

/-- Four states for the confluence-transfer control. -/
inductive FourState where
  | x
  | a
  | b
  | z
  deriving DecidableEq

/-- A confluent source relation: two steps out of `x`, joined at `z`. -/
def forkJoinSource : FourState → FourState → Prop
  | .x, .a => True
  | .x, .b => True
  | .a, .z => True
  | .b, .z => True
  | _, _ => False

/-- The target relation keeps the two steps out of `x` and drops the two joining steps. -/
def forkOnlyTarget : FourState → FourState → Prop
  | .x, .a => True
  | .x, .b => True
  | _, _ => False

/-- Proves: every state reaches `z` in `forkJoinSource`.
Does not prove: anything about `forkOnlyTarget`.
Relation: the reflexive-transitive closure of `forkJoinSource`.
Closure: reflexive-transitive. Strategy: not applicable.
Trust: kernel only.
Scope: the four states. -/
theorem forkJoinSource_reaches_z (p : FourState) :
    Relation.ReflTransGen forkJoinSource p .z := by
  cases p
  · exact Relation.ReflTransGen.head (b := .a) (show forkJoinSource .x .a from trivial)
      (Relation.ReflTransGen.single (show forkJoinSource .a .z from trivial))
  · exact Relation.ReflTransGen.single (show forkJoinSource .a .z from trivial)
  · exact Relation.ReflTransGen.single (show forkJoinSource .b .z from trivial)
  · exact Relation.ReflTransGen.refl

/-- Proves: in `forkOnlyTarget`, the only state reachable from `a` is `a`, and the only state
reachable from `b` is `b`.
Does not prove: anything about the source relation.
Relation: the reflexive-transitive closure of `forkOnlyTarget`.
Closure: reflexive-transitive. Strategy: not applicable.
Trust: kernel only.
Scope: the four states. -/
theorem forkOnlyTarget_stuck (w : FourState) :
    (Relation.ReflTransGen forkOnlyTarget .a w → w = .a) ∧
      (Relation.ReflTransGen forkOnlyTarget .b w → w = .b) := by
  constructor
  · intro h
    rcases Relation.ReflTransGen.cases_head h with h1 | ⟨c, hc, _⟩
    · exact h1.symm
    · cases c <;> exact absurd hc (by simp [forkOnlyTarget])
  · intro h
    rcases Relation.ReflTransGen.cases_head h with h1 | ⟨c, hc, _⟩
    · exact h1.symm
    · cases c <;> exact absurd hc (by simp [forkOnlyTarget])

/-- Deleted-premise control of the confluence transfer along an embedding.
Proves: the identity map from `forkJoinSource` to `forkOnlyTarget` is injective, reflects every
target step to a source step, and has an image closed under target steps; the source is
confluent; step preservation fails at `a → z`; and the target fork at the image point `x` is not
joinable. Confluence transfer is therefore false with step preservation deleted.
Does not prove: failure of confluence transfer when step preservation holds.
Relation: `forkJoinSource` and `forkOnlyTarget` with their reflexive-transitive closures.
Closure: reflexive-transitive. Strategy: not applicable.
Trust: kernel only.
Scope: the four states and the identity map. -/
theorem reflection_without_preservation_breaks_confluence :
    Function.Injective (id : FourState → FourState) ∧
      (∀ u v : FourState, forkOnlyTarget (id u) (id v) → forkJoinSource u v) ∧
      (∀ u y : FourState, forkOnlyTarget (id u) y → ∃ w, id w = y) ∧
      (∀ s u v : FourState, Relation.ReflTransGen forkJoinSource s u →
        Relation.ReflTransGen forkJoinSource s v →
        ∃ w, Relation.ReflTransGen forkJoinSource u w ∧
          Relation.ReflTransGen forkJoinSource v w) ∧
      forkJoinSource .a .z ∧ ¬ forkOnlyTarget (id FourState.a) (id FourState.z) ∧
      Relation.ReflTransGen forkOnlyTarget (id FourState.x) .a ∧
      Relation.ReflTransGen forkOnlyTarget (id FourState.x) .b ∧
      ¬ ∃ w, Relation.ReflTransGen forkOnlyTarget .a w ∧
        Relation.ReflTransGen forkOnlyTarget .b w := by
  refine ⟨Function.injective_id, fun u v h => ?_, fun _ y _ => ⟨y, rfl⟩,
    fun _ u v _ _ => ⟨.z, forkJoinSource_reaches_z u, forkJoinSource_reaches_z v⟩,
    trivial, fun h => h, Relation.ReflTransGen.single (show forkOnlyTarget .x .a from trivial),
    Relation.ReflTransGen.single (show forkOnlyTarget .x .b from trivial), ?_⟩
  · cases u <;> cases v <;> simp_all [forkJoinSource, forkOnlyTarget]
  · rintro ⟨w, ha, hb⟩
    have h1 := (forkOnlyTarget_stuck w).1 ha
    have h2 := (forkOnlyTarget_stuck w).2 hb
    rw [h1] at h2
    cases h2

end OperatorKO7.Methods.OrientationClosure.TransportLaws
