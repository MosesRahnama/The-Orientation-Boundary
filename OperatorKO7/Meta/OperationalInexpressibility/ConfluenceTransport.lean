import OperatorKO7.Meta.OperationalInexpressibility.NormalFormFaithfulTransport
import Mathlib.Tactic.FinCases

/-!
# Confluence transport

A terminating relation with unique reachable normal forms is confluent: every state reaches a
normal form, and two reducts of one state reach normal forms that coincide. Conversely a confluent
relation has unique reachable normal forms, so for terminating relations the two properties are
equivalent. For a first-order term rewriting system the same holds with uniqueness of normal forms
under conversion.

Combined with the two transport theorems of `NormalFormFaithfulTransport`, this gives source
confluence from two simulations: a stuttering simulation into a terminating target supplies
termination, and a normal-form faithful simulation into a target with unique reachable normal
forms supplies uniqueness. A three-state instance maps onto a two-state target by a
non-injective map with one stuttering step.

Target uniqueness is an input of the transport theorem. The theorem does not establish uniqueness
of normal forms for a target; in particular it does not address the open problem on
non-ω-overlapping systems of the Distinction Boundary program.

Relation: arbitrary binary relations; first-order TRS `Step` and `StepStar`.
Property: confluence, termination, and uniqueness of normal forms.
Trust: kernel only; the normal-form existence argument uses classical case analysis.
Scope: arbitrary carriers and relations; arbitrary first-order signatures and variable types.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.OperationalInexpressibility.ConfluenceTransport

open OperatorKO7.Meta.Rewriting
open OperatorKO7.Meta.UniqueNormalization
open OperatorKO7.Meta.OperationalInexpressibility.NormalFormFaithfulTransport

universe u v w u' v'

/-- Confluence of an arbitrary relation: two reduction sequences out of one state can be joined. -/
def RelationConfluent {A : Type u} (R : A → A → Prop) : Prop :=
  ∀ a b c, Relation.ReflTransGen R a b → Relation.ReflTransGen R a c →
    ∃ d, Relation.ReflTransGen R b d ∧ Relation.ReflTransGen R c d

/-- A reduction sequence out of a normal state is trivial. -/
theorem eq_of_relationNormal_of_reflTransGen {A : Type u} {R : A → A → Prop} {t d : A}
    (ht : RelationNormal R t) (h : Relation.ReflTransGen R t d) : t = d := by
  rcases h.cases_head with heq | ⟨c, hstep, _⟩
  · exact heq
  · exact absurd hstep (ht c)

/-- Every state of a terminating relation reaches a normal state. -/
theorem exists_relationNormal_of_wellFounded {A : Type u} {R : A → A → Prop}
    (hwf : WellFounded (fun y x => R x y)) (a : A) :
    ∃ n, Relation.ReflTransGen R a n ∧ RelationNormal R n := by
  induction a using hwf.induction with
  | _ a ih =>
    by_cases hnormal : RelationNormal R a
    · exact ⟨a, Relation.ReflTransGen.refl, hnormal⟩
    · simp only [RelationNormal, not_forall, not_not] at hnormal
      obtain ⟨b, hab⟩ := hnormal
      obtain ⟨n, hbn, hn⟩ := ih b hab
      exact ⟨n, Relation.ReflTransGen.head hab hbn, hn⟩

/-- **(i) Termination and unique reachable normal forms give confluence.** -/
theorem confluent_of_wellFounded_and_relationUNred {A : Type u} {R : A → A → Prop}
    (hwf : WellFounded (fun y x => R x y)) (hun : RelationUNred R) : RelationConfluent R := by
  intro a b c hab hac
  obtain ⟨nb, hbnb, hnb⟩ := exists_relationNormal_of_wellFounded hwf b
  obtain ⟨nc, hcnc, hnc⟩ := exists_relationNormal_of_wellFounded hwf c
  have heq : nb = nc := hun a nb nc hnb hnc (hab.trans hbnb) (hac.trans hcnc)
  refine ⟨nb, hbnb, ?_⟩
  rw [heq]
  exact hcnc

/-- A confluent relation has unique reachable normal forms. -/
theorem relationUNred_of_relationConfluent {A : Type u} {R : A → A → Prop}
    (h : RelationConfluent R) : RelationUNred R := by
  intro s t u ht hu hst hsu
  obtain ⟨d, htd, hud⟩ := h s t u hst hsu
  rw [eq_of_relationNormal_of_reflTransGen ht htd, eq_of_relationNormal_of_reflTransGen hu hud]

/-- For a terminating relation, confluence is uniqueness of reachable normal forms. -/
theorem relationConfluent_iff_relationUNred_of_wellFounded {A : Type u} {R : A → A → Prop}
    (hwf : WellFounded (fun y x => R x y)) : RelationConfluent R ↔ RelationUNred R :=
  ⟨relationUNred_of_relationConfluent, confluent_of_wellFounded_and_relationUNred hwf⟩

/-- **(ii) Confluence from two transports.** A stuttering simulation into a terminating target and
a normal-form faithful simulation into a target with unique reachable normal forms give source
confluence. -/
theorem confluent_of_transports {A : Type u} {B : Type v} {C : Type w}
    {R : A → A → Prop} {S : B → B → Prop} {T : C → C → Prop}
    (sim : StutteringSimulation R S) (hS : WellFounded (fun y x => S x y))
    {f : A → C} (hsim : StepStarSimulation R T f)
    (hnormal : ∀ {a}, RelationNormal R a → RelationNormal T (f a))
    (hinjective : ∀ {a b}, RelationNormal R a → RelationNormal R b → f a = f b → a = b)
    (hT : RelationUNred T) : RelationConfluent R :=
  confluent_of_wellFounded_and_relationUNred
    (relation_wellFounded_of_stutteringSimulation sim hS)
    (relationUNred_transfer hsim hnormal hinjective hT)

/-! ## First-order term rewriting systems -/

/-- **(iii) TRS form.** A terminating first-order TRS with unique normal forms under conversion is
confluent. -/
theorem confluent_of_wellFounded_and_UNconv {sigma : Type u} {nu : Type v} {R : TRS sigma nu}
    (hwf : WellFounded (fun y x => Step R x y)) (hun : UNconv R) : confluent R := by
  have hrel : RelationConfluent (Step R) :=
    confluent_of_wellFounded_and_relationUNred hwf
      (fun s t u ht hu hst hsu => UNred_of_UNconv hun s t u ht hu hst hsu)
  intro s t₁ t₂ h₁ h₂
  exact hrel s t₁ t₂ h₁ h₂

/-- For a terminating TRS, confluence is uniqueness of normal forms under conversion. -/
theorem terminating_confluent_iff_UNconv {sigma : Type u} {nu : Type v} {R : TRS sigma nu}
    (hwf : WellFounded (fun y x => Step R x y)) : confluent R ↔ UNconv R :=
  ⟨UNconv_of_confluent, confluent_of_wellFounded_and_UNconv hwf⟩

/-- For a terminating TRS, confluence is uniqueness of reachable normal forms. -/
theorem terminating_confluent_iff_UNred {sigma : Type u} {nu : Type v} {R : TRS sigma nu}
    (hwf : WellFounded (fun y x => Step R x y)) : confluent R ↔ UNred R := by
  constructor
  · exact fun h => UNred_of_UNconv (UNconv_of_confluent h)
  · intro hun
    have hrel : RelationConfluent (Step R) :=
      confluent_of_wellFounded_and_relationUNred hwf
        (fun s t u ht hu hst hsu => hun s t u ht hu hst hsu)
    intro s t₁ t₂ h₁ h₂
    exact hrel s t₁ t₂ h₁ h₂

/-- **TRS confluence from two transports.** A stuttering simulation of `Step R` into a terminating
relation and a normal-form faithful reduction simulation into a TRS with unique normal forms under
conversion give confluence of `R`. -/
theorem confluent_of_TRS_transports {sigma : Type u} {nu : Type v} {tau : Type u'} {mu : Type v'}
    {B : Type w} {R : TRS sigma nu} {S : B → B → Prop} {T : TRS tau mu}
    (sim : StutteringSimulation (Step R) S) (hS : WellFounded (fun y x => S x y))
    {f : Term sigma nu → Term tau mu}
    (hsim : ∀ {a b}, Step R a b → StepStar T (f a) (f b))
    (hnormal : ∀ {a}, NormalForm R a → NormalForm T (f a))
    (hinjective : ∀ {a b}, NormalForm R a → NormalForm R b → f a = f b → a = b)
    (hT : UNconv T) : confluent R :=
  confluent_of_wellFounded_and_UNconv
    (relation_wellFounded_of_stutteringSimulation sim hS)
    (UNconv_transfer hsim hnormal hinjective hT)

/-! ## A non-isomorphic instance -/

/-- Three states with steps `2 → 1`, `1 → 0`, and `2 → 0`. -/
inductive TriStep : Fin 3 → Fin 3 → Prop
  | twoOne : TriStep 2 1
  | oneZero : TriStep 1 0
  | twoZero : TriStep 2 0

/-- Two states with the step `1 → 0`. -/
inductive DuoStep : Fin 2 → Fin 2 → Prop
  | oneZero : DuoStep 1 0

/-- The map sending `0` to `0` and both other states to `1`. -/
def triToDuo (i : Fin 3) : Fin 2 :=
  if i = 0 then 0 else 1

/-- The only normal state of the source is `0`. -/
theorem triStep_normal_iff (a : Fin 3) : RelationNormal TriStep a ↔ a = 0 := by
  constructor
  · intro h
    by_contra hne
    fin_cases a
    · exact hne rfl
    · exact h 0 TriStep.oneZero
    · exact h 0 TriStep.twoZero
  · rintro rfl b hb
    cases hb

/-- The only normal state of the target is `0`. -/
theorem duoStep_normal_iff (b : Fin 2) : RelationNormal DuoStep b ↔ b = 0 := by
  constructor
  · intro h
    by_contra hne
    fin_cases b
    · exact hne rfl
    · exact h 0 DuoStep.oneZero
  · rintro rfl c hc
    cases hc

/-- The target relation terminates. -/
theorem duoStep_wellFounded : WellFounded (fun y x => DuoStep x y) := by
  apply Subrelation.wf (r := fun y x : Fin 2 => y < x) _ (InvImage.wf (fun i : Fin 2 => i.val)
    Nat.lt_wfRel.wf)
  intro y x h
  cases h
  decide

/-- The target relation has unique reachable normal forms. -/
theorem duoStep_relationUNred : RelationUNred DuoStep := by
  intro s t u ht hu _ _
  rw [(duoStep_normal_iff t).1 ht, (duoStep_normal_iff u).1 hu]

/-- The collapsing map is a stuttering simulation, with rank the state index. -/
def triToDuoStuttering : StutteringSimulation TriStep DuoStep where
  encode := triToDuo
  stutterRank := fun i => i.val
  forward := by
    intro a b h
    cases h with
    | twoOne => exact Or.inr ⟨by decide, by decide⟩
    | oneZero => exact Or.inl (Relation.TransGen.single (by
        show DuoStep (triToDuo 1) (triToDuo 0)
        exact DuoStep.oneZero))
    | twoZero => exact Or.inl (Relation.TransGen.single (by
        show DuoStep (triToDuo 2) (triToDuo 0)
        exact DuoStep.oneZero))

/-- The collapsing map sends every source step to a target reduction. -/
theorem triToDuo_stepStarSimulation : StepStarSimulation TriStep DuoStep triToDuo := by
  intro a b h
  cases h with
  | twoOne => exact Relation.ReflTransGen.refl
  | oneZero => exact Relation.ReflTransGen.single DuoStep.oneZero
  | twoZero => exact Relation.ReflTransGen.single DuoStep.oneZero

/-- **Non-isomorphic instance.** The three-state source is confluent by transport along a
non-injective map onto a two-state target. -/
theorem triStep_confluent_by_transport :
    RelationConfluent TriStep ∧ ¬ Function.Injective triToDuo := by
  refine ⟨confluent_of_transports triToDuoStuttering duoStep_wellFounded
    triToDuo_stepStarSimulation ?_ ?_ duoStep_relationUNred, ?_⟩
  · intro a ha
    rw [(triStep_normal_iff a).1 ha]
    exact (duoStep_normal_iff _).2 rfl
  · intro a b ha hb _
    rw [(triStep_normal_iff a).1 ha, (triStep_normal_iff b).1 hb]
  · intro h
    have h12 : (1 : Fin 3) = 2 := h (by decide)
    exact absurd h12 (by decide)

/-! ## Necessity of uniqueness -/

/-- The fork terminates. -/
theorem forkStep_wellFounded : WellFounded (fun y x => ForkStep x y) := by
  refine ⟨fun a => ?_⟩
  cases a with
  | left => exact Acc.intro _ fun y h => by cases h
  | right => exact Acc.intro _ fun y h => by cases h
  | source =>
      exact Acc.intro _ fun y h => by
        cases h with
        | toLeft => exact Acc.intro _ fun z hz => by cases hz
        | toRight => exact Acc.intro _ fun z hz => by cases hz

/-- **Uniqueness is required.** The fork terminates and is not confluent. -/
theorem uniqueness_is_required_for_confluence :
    WellFounded (fun y x => ForkStep x y) ∧ ¬ RelationConfluent ForkStep := by
  refine ⟨forkStep_wellFounded, fun h => fork_not_relationUNred ?_⟩
  exact relationUNred_of_relationConfluent h

end OperatorKO7.Meta.OperationalInexpressibility.ConfluenceTransport
