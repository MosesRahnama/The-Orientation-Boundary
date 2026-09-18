import OperatorKO7.Meta.Methods.OrientationClosure.SchemaCore

/-!
# Generic transport laws for the Orientation Boundary

Theorems in this module separate the properties that transport under relation
extension, faithful renaming, and substrate simulation.  In particular,
termination transport requires a positive target path for every source step;
reflexive zero-step simulation is insufficient.
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

end OperatorKO7.Methods.OrientationClosure.TransportLaws
