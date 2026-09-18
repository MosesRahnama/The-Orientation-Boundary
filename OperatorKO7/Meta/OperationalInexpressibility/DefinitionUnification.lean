import OperatorKO7.Meta.OperationalInexpressibility.LicenseCore

/-!
# One definition with two faces

Operational inexpressibility is stated at two levels. The language level is the paper's
definition: a named dimension is present, and no derivable statement both depends on that
dimension and constrains the target. The observer level is the license criterion: two worlds that
the observer cannot tell apart carry different target verdicts. This module proves that the two
levels define one notion.

Three hypotheses connect them. Soundness: every derivable denotation is constant on observer
fibers. Completeness: some derivable statement separates any two distinct observations. Dimension
visibility: some pair of worlds in one outside context changes both the dimension and the
observation. Under all three, the language-level definition holds exactly when the dimension is
present and the observer collides with the target inside an outside context. Soundness alone gives
the implication from the observer level to the language level. Each of the three hypotheses is
necessary; the fixtures at the end drop one hypothesis at a time and exhibit the failure.

A second statement gives the license form of the definition. When dependence on the dimension
means failure of the license of an observer that forgets the dimension, the second clause of the
definition says exactly that every derivable statement constraining the target is licensed by that
forgetful observer.

Relation: equality of observer outputs inside an arbitrary context relation.
Property: equivalence of the language-level and observer-level definitions.
Trust: kernel only; the converse directions use classical case analysis.
Scope: arbitrary world, statement, observation, dimension, and verdict types in independent
universes; arbitrary context relation. No finiteness, decidability, or inhabitance assumption.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.OperationalInexpressibility.DefinitionUnification

open OperatorKO7.Meta.OperationalInexpressibility.ObserverKernel
open OperatorKO7.Meta.OperationalInexpressibility.DirectGrammarBoundary
open OperatorKO7.Meta.OperationalInexpressibility.LicenseCriterion

universe uW uS uO uD uV

/-- A proof language read semantically. Statements denote verdict-valued functions of worlds,
derivability is a formation judgment, and each world carries an observation, a value of the named
dimension, a target verdict, and an outside-context relation. No witness pair is stored. -/
structure ObservedLanguage where
  World : Type uW
  Statement : Type uS
  Observation : Type uO
  Dimension : Type uD
  Verdict : Type uV
  denotes : Statement → World → Verdict
  derivable : Statement → Prop
  observe : World → Observation
  dimension : World → Dimension
  target : World → Verdict
  sameContext : World → World → Prop

namespace ObservedLanguage

variable (L : ObservedLanguage.{uW, uS, uO, uD, uV})

/-- Clause (i) of the definition: two worlds in one outside context carry distinct values of the
named dimension. -/
def DimensionPresent : Prop :=
  ∃ x y : L.World, L.sameContext x y ∧ L.dimension x ≠ L.dimension y

/-- A statement depends on the dimension when its denotation changes across a pair of worlds in
one outside context whose dimension values differ. -/
def DependsOnDimension (ψ : L.Statement) : Prop :=
  ∃ x y : L.World, L.sameContext x y ∧ L.dimension x ≠ L.dimension y ∧
    L.denotes ψ x ≠ L.denotes ψ y

/-- A statement constrains the target when, inside one outside context, equal denotations force
equal target verdicts. -/
def ConstrainsTarget (ψ : L.Statement) : Prop :=
  ∀ {x y : L.World}, L.sameContext x y → L.denotes ψ x = L.denotes ψ y → L.target x = L.target y

/-- The language level of the definition: the dimension is present and no derivable statement
both depends on it and constrains the target. -/
def LanguageInexpressible : Prop :=
  L.DimensionPresent ∧ ∀ ψ, L.derivable ψ → ¬ (L.DependsOnDimension ψ ∧ L.ConstrainsTarget ψ)

/-- Two worlds of one outside context share the observation and carry distinct target verdicts. -/
def ContextCollision : Prop :=
  ∃ x y : L.World, L.sameContext x y ∧ L.observe x = L.observe y ∧ L.target x ≠ L.target y

/-- The target is licensed inside every outside context: equal observations inside one context
force equal target verdicts. -/
def LicensedInContext : Prop :=
  ∀ x y : L.World, L.sameContext x y → L.observe x = L.observe y → L.target x = L.target y

/-- The observer level of the definition: the dimension is present and the observer collides with
the target inside an outside context. -/
def ObserverInexpressible : Prop :=
  L.DimensionPresent ∧ L.ContextCollision

/-- Soundness of the language for its observer: every derivable denotation is constant on
observer fibers. -/
def Sound : Prop :=
  ∀ ψ, L.derivable ψ → FactorsThrough L.observe (L.denotes ψ)

/-- Completeness of the language for its observer: some derivable statement separates any two
worlds with distinct observations. -/
def Complete : Prop :=
  ∃ ψ, L.derivable ψ ∧ ∀ x y : L.World, L.denotes ψ x = L.denotes ψ y → L.observe x = L.observe y

/-- Dimension visibility: some pair of worlds in one outside context changes both the dimension
and the observation. -/
def ObserverSeesDimension : Prop :=
  ∃ x y : L.World, L.sameContext x y ∧ L.dimension x ≠ L.dimension y ∧ L.observe x ≠ L.observe y

variable {L}

/-- A context collision is exactly the failure of the context-relative license. -/
theorem contextCollision_iff_not_licensedInContext :
    L.ContextCollision ↔ ¬ L.LicensedInContext := by
  constructor
  · rintro ⟨x, y, hctx, hobs, htarget⟩ hlic
    exact htarget (hlic x y hctx hobs)
  · intro hnot
    by_contra hnone
    apply hnot
    intro x y hctx hobs
    by_contra htarget
    exact hnone ⟨x, y, hctx, hobs, htarget⟩

/-- With the total context relation, the context-relative license is the license criterion. -/
theorem licensedInContext_iff_licensed_of_total (htotal : ∀ x y : L.World, L.sameContext x y) :
    L.LicensedInContext ↔ Licensed L.observe L.target := by
  constructor
  · intro h x y hobs
    exact h x y (htotal x y) hobs
  · intro h x y _ hobs
    exact h x y hobs

/-- With the total context relation, a context collision is exactly an unlicensed target. -/
theorem contextCollision_iff_unlicensed_of_total (htotal : ∀ x y : L.World, L.sameContext x y) :
    L.ContextCollision ↔ ¬ Licensed L.observe L.target := by
  rw [contextCollision_iff_not_licensedInContext, licensedInContext_iff_licensed_of_total htotal]

/-- A sound language contains no derivable statement that constrains the target across a context
collision. -/
theorem not_constrainsTarget_of_contextCollision (hsound : L.Sound)
    (hcoll : L.ContextCollision) {ψ : L.Statement} (hψ : L.derivable ψ) :
    ¬ L.ConstrainsTarget ψ := by
  obtain ⟨x, y, hctx, hobs, htarget⟩ := hcoll
  intro hcon
  exact htarget (hcon hctx (hsound ψ hψ hobs))

/-- For every sound language, the observer level of the definition implies the language level. -/
theorem languageInexpressible_of_observerInexpressible (hsound : L.Sound)
    (h : L.ObserverInexpressible) : L.LanguageInexpressible :=
  ⟨h.1, fun _ψ hψ hboth => not_constrainsTarget_of_contextCollision hsound h.2 hψ hboth.2⟩

/-- A complete language whose observer sees the dimension, and which has no context collision,
contains a derivable statement that depends on the dimension and constrains the target. -/
theorem exists_incorporating_statement_of_not_contextCollision (hcomplete : L.Complete)
    (hsees : L.ObserverSeesDimension) (hnone : ¬ L.ContextCollision) :
    ∃ ψ, L.derivable ψ ∧ L.DependsOnDimension ψ ∧ L.ConstrainsTarget ψ := by
  obtain ⟨ψ, hψ, hsep⟩ := hcomplete
  refine ⟨ψ, hψ, ?_, ?_⟩
  · obtain ⟨x, y, hctx, hdim, hobs⟩ := hsees
    exact ⟨x, y, hctx, hdim, fun hden => hobs (hsep x y hden)⟩
  · intro x y hctx hden
    by_contra htarget
    exact hnone ⟨x, y, hctx, hsep x y hden, htarget⟩

/-- For a complete language whose observer sees the dimension, the language level of the
definition implies the observer level. -/
theorem observerInexpressible_of_languageInexpressible (hcomplete : L.Complete)
    (hsees : L.ObserverSeesDimension) (h : L.LanguageInexpressible) : L.ObserverInexpressible := by
  refine ⟨h.1, ?_⟩
  by_contra hnone
  obtain ⟨ψ, hψ, hdep, hcon⟩ :=
    exists_incorporating_statement_of_not_contextCollision hcomplete hsees hnone
  exact h.2 ψ hψ ⟨hdep, hcon⟩

/-- **One definition with two faces.** For a sound and complete language whose observer sees the
dimension, the language-level definition of operational inexpressibility holds exactly when the
dimension is present and the observer collides with the target inside an outside context. -/
theorem operationalInexpressibility_language_iff_observer (hsound : L.Sound)
    (hcomplete : L.Complete) (hsees : L.ObserverSeesDimension) :
    L.LanguageInexpressible ↔ L.ObserverInexpressible :=
  ⟨observerInexpressible_of_languageInexpressible hcomplete hsees,
    languageInexpressible_of_observerInexpressible hsound⟩

/-- With the total context relation, the language-level definition is the conjunction of
dimension presence and failure of the license criterion. -/
theorem languageInexpressible_iff_unlicensed_of_total (hsound : L.Sound) (hcomplete : L.Complete)
    (hsees : L.ObserverSeesDimension) (htotal : ∀ x y : L.World, L.sameContext x y) :
    L.LanguageInexpressible ↔ L.DimensionPresent ∧ ¬ Licensed L.observe L.target := by
  rw [operationalInexpressibility_language_iff_observer hsound hcomplete hsees]
  exact and_congr Iff.rfl (contextCollision_iff_unlicensed_of_total htotal)

end ObservedLanguage

/-! ## The license form of the second clause -/

/-- **License form of the definition.** When dependence on the dimension is failure of the
license of an observer that forgets the dimension, the second clause of the definition says
exactly that every derivable statement constraining the target is licensed by that observer. -/
theorem noIncorporation_iff_constraining_licensed_by_forgetful
    {S : Type uS} {W : Type uW} {K : Type uO} {V : Type uV}
    (derivable dependsOn constrains : S → Prop) (denote : S → W → V) (forget : W → K)
    (hdep : ∀ ψ, dependsOn ψ ↔ ¬ Licensed forget (denote ψ)) :
    (∀ ψ, derivable ψ → ¬ (dependsOn ψ ∧ constrains ψ)) ↔
      ∀ ψ, derivable ψ → constrains ψ → Licensed forget (denote ψ) := by
  constructor
  · intro h ψ hψ hcon
    by_contra hnot
    exact h ψ hψ ⟨(hdep ψ).2 hnot, hcon⟩
  · rintro h ψ hψ ⟨hdepψ, hcon⟩
    exact (hdep ψ).1 hdepψ (h ψ hψ hcon)

/-! ## Necessity of the three hypotheses

Each fixture below satisfies two of the three hypotheses of
`operationalInexpressibility_language_iff_observer` and violates the equivalence. -/

/-- An observer that sees nothing: one constant statement, a constant observation, a Boolean
dimension, and a constant target. -/
def blindObserverLanguage : ObservedLanguage.{0, 0, 0, 0, 0} where
  World := Bool
  Statement := Unit
  Observation := Unit
  Dimension := Bool
  Verdict := Unit
  denotes := fun _ _ => ()
  derivable := fun _ => True
  observe := fun _ => ()
  dimension := id
  target := fun _ => ()
  sameContext := fun _ _ => True

/-- Dimension visibility is necessary: the blind-observer language is sound and complete, its
language level holds, and its observer level fails. -/
theorem observerSeesDimension_is_required :
    blindObserverLanguage.Sound ∧ blindObserverLanguage.Complete ∧
      ¬ blindObserverLanguage.ObserverSeesDimension ∧
      blindObserverLanguage.LanguageInexpressible ∧
      ¬ blindObserverLanguage.ObserverInexpressible := by
  refine ⟨fun _ _ _ _ _ => rfl, ⟨(), trivial, fun _ _ _ => rfl⟩, ?_, ?_, ?_⟩
  · rintro ⟨_, _, _, _, hobs⟩
    exact hobs rfl
  · refine ⟨⟨false, true, trivial, show (false : Bool) ≠ true by decide⟩, ?_⟩
    rintro _ _ ⟨⟨_, _, _, _, hden⟩, _⟩
    exact hden rfl
  · rintro ⟨_, _, _, _, _, htarget⟩
    exact htarget rfl

/-- A language with one constant statement over an injective observer. -/
def constantStatementLanguage : ObservedLanguage.{0, 0, 0, 0, 0} where
  World := Bool
  Statement := Unit
  Observation := Bool
  Dimension := Bool
  Verdict := Bool
  denotes := fun _ _ => false
  derivable := fun _ => True
  observe := id
  dimension := id
  target := id
  sameContext := fun _ _ => True

/-- Completeness is necessary: the constant-statement language is sound and its observer sees the
dimension, its language level holds, and its observer level fails. -/
theorem complete_is_required :
    constantStatementLanguage.Sound ∧ ¬ constantStatementLanguage.Complete ∧
      constantStatementLanguage.ObserverSeesDimension ∧
      constantStatementLanguage.LanguageInexpressible ∧
      ¬ constantStatementLanguage.ObserverInexpressible := by
  refine ⟨fun _ _ _ _ _ => rfl, ?_,
    ⟨false, true, trivial, show (false : Bool) ≠ true by decide,
      show (false : Bool) ≠ true by decide⟩, ?_, ?_⟩
  · rintro ⟨_, _, hsep⟩
    have hbad : (false : Bool) = true := hsep false true rfl
    cases hbad
  · refine ⟨⟨false, true, trivial, show (false : Bool) ≠ true by decide⟩, ?_⟩
    rintro _ _ ⟨⟨_, _, _, _, hden⟩, _⟩
    exact hden rfl
  · rintro ⟨_, ⟨x, y, _, hobs, htarget⟩⟩
    exact htarget hobs

/-- A language whose one statement reads the whole world while the observer reads only the first
coordinate. -/
def unsoundStatementLanguage : ObservedLanguage.{0, 0, 0, 0, 0} where
  World := Bool × Bool
  Statement := Unit
  Observation := Bool
  Dimension := Bool
  Verdict := Bool × Bool
  denotes := fun _ w => w
  derivable := fun _ => True
  observe := Prod.fst
  dimension := Prod.snd
  target := id
  sameContext := fun _ _ => True

/-- Soundness is necessary: the unsound-statement language is complete and its observer sees the
dimension, its observer level holds, and its language level fails. -/
theorem sound_is_required :
    ¬ unsoundStatementLanguage.Sound ∧ unsoundStatementLanguage.Complete ∧
      unsoundStatementLanguage.ObserverSeesDimension ∧
      unsoundStatementLanguage.ObserverInexpressible ∧
      ¬ unsoundStatementLanguage.LanguageInexpressible := by
  have hff_tt : (false : Bool) ≠ true := by decide
  have hpair : ((false, false) : Bool × Bool) ≠ (false, true) := by decide
  refine ⟨?_, ⟨(), trivial, fun x y h => congrArg Prod.fst h⟩,
    ⟨(false, false), (true, true), trivial, hff_tt, hff_tt⟩,
    ⟨⟨(false, false), (false, true), trivial, hff_tt⟩,
      ⟨(false, false), (false, true), trivial, rfl, hpair⟩⟩, ?_⟩
  · intro hsound
    have hfac : FactorsThrough unsoundStatementLanguage.observe
        (unsoundStatementLanguage.denotes ()) := hsound () trivial
    exact hpair (@hfac (false, false) (false, true) rfl)
  · rintro ⟨_, hall⟩
    apply hall () trivial
    refine ⟨⟨(false, false), (false, true), trivial, hff_tt, hpair⟩, ?_⟩
    intro x y _ hden
    exact hden

end OperatorKO7.Meta.OperationalInexpressibility.DefinitionUnification
