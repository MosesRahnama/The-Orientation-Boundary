import OperatorKO7.Meta.UniqueNormalization.UNStatement
import Mathlib.Data.Prod.Lex

/-!
# Normal-form faithful transport

A map can transfer uniqueness of normal forms when it maps source reductions to target reductions,
maps source normal forms to target normal forms, and remains injective on source normal forms. The
same conditions also transport conversion-based uniqueness because mapped source steps induce mapped
conversions.

Relation: arbitrary binary relations and first-order TRS `Step`/`StepStar`/`conv`.
Property: unique reachable normal forms and unique normal forms under conversion.
Trust: kernel-only.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.OperationalInexpressibility.NormalFormFaithfulTransport

open OperatorKO7.Meta.Rewriting
open OperatorKO7.Meta.UniqueNormalization

universe u v u' v'

/-- Normality for an arbitrary binary relation. -/
def RelationNormal {A : Type u} (R : A → A → Prop) (a : A) : Prop :=
  ∀ b, ¬ R a b

/-- Every start state has at most one reachable normal endpoint. -/
def RelationUNred {A : Type u} (R : A → A → Prop) : Prop :=
  ∀ s t u, RelationNormal R t → RelationNormal R u →
    Relation.ReflTransGen R s t → Relation.ReflTransGen R s u → t = u

/-- A source step maps to a finite target reduction; equality is included by reflexivity. -/
def StepStarSimulation {A : Type u} {B : Type v}
    (R : A → A → Prop) (S : B → B → Prop) (f : A → B) : Prop :=
  ∀ {a b}, R a b → Relation.ReflTransGen S (f a) (f b)

/-- Step-star simulation extends from one step to every finite source reduction. -/
theorem map_reflTransGen
    {A : Type u} {B : Type v} {R : A → A → Prop} {S : B → B → Prop}
    {f : A → B} (hsim : StepStarSimulation R S f)
    {a b : A} (h : Relation.ReflTransGen R a b) :
    Relation.ReflTransGen S (f a) (f b) := by
  induction h with
  | refl => exact .refl
  | tail _ hlast ih => exact Relation.ReflTransGen.trans ih (hsim hlast)

/-- Arbitrary-relation uniqueness transfers through a normal-form faithful simulation. -/
theorem relationUNred_transfer
    {A : Type u} {B : Type v} {R : A → A → Prop} {S : B → B → Prop}
    {f : A → B}
    (hsim : StepStarSimulation R S f)
    (hnormal : ∀ {a}, RelationNormal R a → RelationNormal S (f a))
    (hinjective : ∀ {a b}, RelationNormal R a → RelationNormal R b → f a = f b → a = b)
    (htarget : RelationUNred S) : RelationUNred R := by
  intro s t u ht hu hst hsu
  apply hinjective ht hu
  exact htarget (f s) (f t) (f u) (hnormal ht) (hnormal hu)
    (map_reflTransGen (R := R) (S := S) (f := f) hsim hst)
    (map_reflTransGen (R := R) (S := S) (f := f) hsim hsu)

/-- A TRS step-star simulation maps every source conversion to a target conversion. -/
theorem conv_map_of_stepStarSimulation
    {sigma : Type u} {nu : Type v} {tau : Type u'} {mu : Type v'}
    {R : TRS sigma nu} {S : TRS tau mu}
    {f : Term sigma nu → Term tau mu}
    (hsim : ∀ {a b}, Step R a b → StepStar S (f a) (f b))
    {a b : Term sigma nu} (h : conv R a b) : conv S (f a) (f b) := by
  induction h with
  | refl => exact conv.refl S _
  | tail _ hlast ih =>
      rcases hlast with hstep | hstep
      · exact conv.trans ih (conv.of_stepStar (hsim hstep))
      · exact conv.trans ih (conv.symm (conv.of_stepStar (hsim hstep)))

/-- `UN→` transfers from a target TRS through a normal-form faithful reduction simulation. -/
theorem UNred_transfer
    {sigma : Type u} {nu : Type v} {tau : Type u'} {mu : Type v'}
    {R : TRS sigma nu} {S : TRS tau mu}
    {f : Term sigma nu → Term tau mu}
    (hsim : ∀ {a b}, Step R a b → StepStar S (f a) (f b))
    (hnormal : ∀ {a}, NormalForm R a → NormalForm S (f a))
    (hinjective : ∀ {a b}, NormalForm R a → NormalForm R b → f a = f b → a = b)
    (htarget : UNred S) : UNred R := by
  intro s t u ht hu hst hsu
  apply hinjective ht hu
  exact htarget (f s) (f t) (f u) (hnormal ht) (hnormal hu)
    (map_reflTransGen (R := Step R) (S := Step S) (f := f) hsim hst)
    (map_reflTransGen (R := Step R) (S := Step S) (f := f) hsim hsu)

/-- `UN=` transfers under the same simulation because source conversions map to target conversions. -/
theorem UNconv_transfer
    {sigma : Type u} {nu : Type v} {tau : Type u'} {mu : Type v'}
    {R : TRS sigma nu} {S : TRS tau mu}
    {f : Term sigma nu → Term tau mu}
    (hsim : ∀ {a b}, Step R a b → StepStar S (f a) (f b))
    (hnormal : ∀ {a}, NormalForm R a → NormalForm S (f a))
    (hinjective : ∀ {a b}, NormalForm R a → NormalForm R b → f a = f b → a = b)
    (htarget : UNconv S) : UNconv R := by
  intro s t hs ht hconv
  apply hinjective hs ht
  exact htarget (f s) (f t) (hnormal hs) (hnormal ht)
    (conv_map_of_stepStarSimulation hsim hconv)

/-- The collapsed target has one state and no steps. -/
def EmptyUnitStep (_ _ : Unit) : Prop := False

/-! ## Termination transport with explicit stuttering descent -/

/-- A source step either makes a nonempty target reduction or stutters at the
same target state while strictly decreasing an independent natural-number rank.
This is the exact extra datum needed when reflexive target simulations are
allowed to erase source steps. -/
structure StutteringSimulation {A : Type u} {B : Type v}
    (R : A → A → Prop) (S : B → B → Prop) where
  encode : A → B
  stutterRank : A → Nat
  forward : ∀ {a b}, R a b →
    Relation.TransGen (fun y x => S x y) (encode b) (encode a) ∨
      (encode b = encode a ∧ stutterRank b < stutterRank a)

/-- Target well-foundedness plus a strict rank on every erased source step
transfers well-foundedness to the source relation. The two coordinates are kept
separate by a lexicographic product: genuine target progress decreases the first
coordinate, while a target stutter must decrease the second. -/
theorem relation_wellFounded_of_stutteringSimulation
    {A : Type u} {B : Type v} {R : A → A → Prop} {S : B → B → Prop}
    (sim : StutteringSimulation R S)
    (hS : WellFounded (fun y x => S x y)) :
    WellFounded (fun y x => R x y) := by
  have hSplus : WellFounded (Relation.TransGen (fun y x => S x y)) := hS.transGen
  have hlex : WellFounded
      (Prod.Lex (Relation.TransGen (fun y x => S x y)) (fun a b : Nat => a < b)) :=
    WellFounded.prod_lex hSplus Nat.lt_wfRel.wf
  apply Subrelation.wf
    (r := InvImage
      (Prod.Lex (Relation.TransGen (fun y x => S x y)) (fun a b : Nat => a < b))
      (fun a => (sim.encode a, sim.stutterRank a)))
  · intro y x hxy
    rcases sim.forward hxy with hprogress | ⟨hstutter, hrank⟩
    · exact Prod.Lex.left _ _ hprogress
    · change Prod.Lex
        (Relation.TransGen (fun y x => S x y)) (fun a b : Nat => a < b)
        (sim.encode y, sim.stutterRank y) (sim.encode x, sim.stutterRank x)
      rw [hstutter]
      exact Prod.Lex.right _ hrank
  · exact InvImage.wf (fun a => (sim.encode a, sim.stutterRank a)) hlex

/-- A one-state source with a self-loop. -/
def LoopUnitStep (_ _ : Unit) : Prop := True

/-- Reflexive target simulation alone can erase the looping source completely. -/
theorem loopUnit_stepStar_simulates :
    StepStarSimulation LoopUnitStep EmptyUnitStep (id : Unit → Unit) := by
  intro a b _
  exact Relation.ReflTransGen.refl

/-- The empty one-state target relation is well founded. -/
theorem emptyUnit_wellFounded :
    WellFounded (fun y x : Unit => EmptyUnitStep x y) := by
  exact ⟨fun a => Acc.intro a (fun _ h => False.elim h)⟩

/-- The source self-loop is not well founded. -/
theorem loopUnit_not_wellFounded :
    ¬ WellFounded (fun y x : Unit => LoopUnitStep x y) := by
  intro hwf
  have hloop : LoopUnitStep () () := trivial
  exact (hwf.asymmetric () () hloop) hloop

/-- Machine-checked necessity control: target termination plus arbitrary
reflexive step-star simulation does not transfer source termination when silent
source steps are allowed without an independent descent certificate. -/
theorem stutter_descent_is_required_for_termination_transport :
    StepStarSimulation LoopUnitStep EmptyUnitStep (id : Unit → Unit) ∧
      WellFounded (fun y x : Unit => EmptyUnitStep x y) ∧
      ¬ WellFounded (fun y x : Unit => LoopUnitStep x y) :=
  ⟨loopUnit_stepStar_simulates, emptyUnit_wellFounded, loopUnit_not_wellFounded⟩

/-! ## Injectivity control -/

inductive ForkState where
  | source
  | left
  | right
  deriving DecidableEq

inductive ForkStep : ForkState → ForkState → Prop where
  | toLeft : ForkStep .source .left
  | toRight : ForkStep .source .right

/-- Collapse all source states to the one target state. -/
def collapseFork (_ : ForkState) : Unit := ()

/-- Every fork step maps to a reflexive target reduction. -/
theorem collapseFork_simulates : StepStarSimulation ForkStep EmptyUnitStep collapseFork := by
  intro a b _
  exact Relation.ReflTransGen.refl

/-- Every collapsed image is target-normal. -/
theorem collapseFork_preserves_normal
    {a : ForkState} (_ : RelationNormal ForkStep a) :
    RelationNormal EmptyUnitStep (collapseFork a) := by
  intro b h
  exact h

/-- The one-state empty target relation has unique reachable normal forms. -/
theorem emptyUnit_relationUNred : RelationUNred EmptyUnitStep := by
  intro s t u _ _ _ _
  exact Subsingleton.elim t u

/-- The left fork endpoint is source-normal. -/
theorem fork_left_normal : RelationNormal ForkStep .left := by
  intro b h
  cases h

/-- The right fork endpoint is source-normal. -/
theorem fork_right_normal : RelationNormal ForkStep .right := by
  intro b h
  cases h

/-- The source fork does not have unique reachable normal forms. -/
theorem fork_not_relationUNred : ¬ RelationUNred ForkStep := by
  intro h
  have heq : ForkState.left = ForkState.right :=
    h .source .left .right fork_left_normal fork_right_normal
      (Relation.ReflTransGen.single .toLeft)
      (Relation.ReflTransGen.single .toRight)
  cases heq

/-- Step simulation, normal-form preservation, and target uniqueness can all hold while source
uniqueness fails when the map collapses distinct source normal forms. -/
theorem normalForm_injectivity_is_required :
    StepStarSimulation ForkStep EmptyUnitStep collapseFork ∧
      (∀ {a}, RelationNormal ForkStep a → RelationNormal EmptyUnitStep (collapseFork a)) ∧
      RelationUNred EmptyUnitStep ∧ ¬ RelationUNred ForkStep :=
  ⟨collapseFork_simulates, collapseFork_preserves_normal,
    emptyUnit_relationUNred, fork_not_relationUNred⟩

end OperatorKO7.Meta.OperationalInexpressibility.NormalFormFaithfulTransport
