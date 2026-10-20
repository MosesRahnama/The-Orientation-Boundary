/-
Copyright (c) 2026 Moses Rahnama. All rights reserved.
Source-available; see the file LICENSE. Free for individual research;
departmental academic use and commercial use require a paid license.
Authors: Moses Rahnama
-/
import OperatorKO7.Meta.DistinctionBoundary.DynamicDiagonalGradeTransport
import OperatorKO7.Meta.DistinctionBoundary.DiagonalGradeReverseSeparations
import OperatorKO7.Meta.DistinctionBoundary.GradeRefinementTower
import OperatorKO7.Meta.DistinctionBoundary.DiagonalLevels
import OperatorKO7.Meta.LicensedBoundaryCalculus.LicensingProductQuotient
import OperatorKO7.Meta.LicensedBoundaryCalculus.LicensingCompletionRule

/-!
# Stratification at the declared structural and dynamic tags

Intent: close the Diagonal Grades stratification conjecture on precisely the
seven declared tags

* structural: `C0`, `C1`, `C2`;
* dynamic: `D0`, `D1s`, `D1p`, `D2`.

The obstruction object is proof carrying. At each tag it contains either a
witness of the semantic realization or a proof that the realization is empty.
The uniform transport table records the hypotheses that move or reflect each
dynamic grade. Two finite fixtures show that simulation alone does not move
`D1p` forward and lifting alone does not reflect `D2`. Seven adjacent reverse
separations and the four computation-rule families are included in the same
compiled package.

Nothing is claimed about tags outside this finite declaration.

Relation: generic `R` and `S` for the dynamic tags.
Closure: reflexive-transitive inside `D1p` and `D2At`.
Strategy: unrestricted, with the transport hypothesis stated per direction.
External trust: Mathlib baseline only.
Non-vacuity witnesses: the structural `C0` and `C1` realizations on `Trace`,
the dynamic `D0` realization, the seven reverse witnesses, and both negative
transport fixtures are explicit.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.DistinctionBoundary.DiagonalGradeStratification

open OperatorKO7
open OperatorKO7.Meta.DistinctionBoundary.DynamicDiagonalGrade
open OperatorKO7.Meta.DistinctionBoundary.DynamicDiagonalGradeTransport
open OperatorKO7.Meta.DistinctionBoundary.DiagonalGradeReverseSeparations
open OperatorKO7.Meta.DistinctionBoundary.IndexedDiagonalGrade
open OperatorKO7.Meta.DistinctionBoundary.DiagonalLevels
open OperatorKO7.Meta.DistinctionBoundary.RoleErasureInstance
open OperatorKO7.Meta.DistinctionBoundary.ObserverExpressivity
open OperatorKO7.Meta.DistinctionBoundary.PersistentLicense
open OperatorKO7.Meta.LicensedBoundaryCalculus.LicensingDatumCategory
open OperatorKO7.Meta.LicensedBoundaryCalculus.LicensingProductQuotient
open OperatorKO7.Meta.LicensedBoundaryCalculus.LicensingCompletionRule
open OperatorKO7.Meta.LicensedBoundaryCalculus.MetricDynamicLicense
open OperatorKO7.Analysis.UniformSeparation

/-! ## Tags and semantic realizations -/

/-- The four declared dynamic tags. -/
inductive DynTag
  | d0
  | d1s
  | d1p
  | d2
deriving DecidableEq, Repr

/-- The three declared structural tags. -/
inductive StructTag
  | c0
  | c1
  | c2
deriving DecidableEq, Repr

/-- The complete declared tag type. -/
inductive GradeTag
  | structural : StructTag → GradeTag
  | dynamic : DynTag → GradeTag
deriving DecidableEq, Repr

/-- Semantic realization of a dynamic tag on its declared relation, observer,
and point pair. -/
def dynRealization {α β : Type} (tag : DynTag)
    (Represented : (α → α → Prop) → Prop) (R : α → α → Prop)
    (q : α → β) (x y : α) : Prop :=
  match tag with
  | .d0 => D0 q x y
  | .d1s => D1s q x y
  | .d1p => D1p R q x y
  | .d2 => D2At Represented R q x y

/-- Semantic realization of a structural tag on the declared `Trace` carrier.
The C2 realization is the existence of a self-evaluation datum internal to the
seven-constructor signature, which the existing no-go refutes. -/
def structRealization : StructTag → Prop
  | .c0 => Nonempty (CopyDiagonal Trace)
  | .c1 => Nonempty (ComparisonDiagonal Trace)
  | .c2 => ∃ D : SelfEvaluationDiagonal.{0,0} Trace, Nonempty (InternalToSignature D)

/-- Semantic realization of any declared tag. Structural tags use their frozen
`Trace` carrier; dynamic tags use the supplied relation-level data. -/
def gradeRealization {α β : Type} (tag : GradeTag)
    (Represented : (α → α → Prop) → Prop) (R : α → α → Prop)
    (q : α → β) (x y : α) : Prop :=
  match tag with
  | .structural s => structRealization s
  | .dynamic d => dynRealization d Represented R q x y

/-- A proof-carrying witness or refusal at one proposition. -/
inductive Verdict (P : Prop)
  | realized : P → Verdict P
  | refused : (¬ P) → Verdict P

namespace Verdict

/-- The obstruction is trivial precisely when it contains a realization
witness. -/
def IsRealized {P : Prop} : Verdict P → Prop
  | .realized _ => True
  | .refused _ => False

end Verdict

/-- The canonical obstruction decision at a proposition. -/
noncomputable def obstructionAt (P : Prop) : Verdict P := by
  classical
  exact if h : P then .realized h else .refused h

/-- The canonical obstruction is trivial if and only if the proposition is
realized. -/
theorem obstruction_trivial_iff_realized (P : Prop) :
    (obstructionAt P).IsRealized ↔ P := by
  classical
  by_cases h : P
  · simp [obstructionAt, h, Verdict.IsRealized]
  · simp [obstructionAt, h, Verdict.IsRealized]

/-- The obstruction assigned to a declared grade tag. -/
noncomputable def gradeObstruction {α β : Type} (tag : GradeTag)
    (Represented : (α → α → Prop) → Prop) (R : α → α → Prop)
    (q : α → β) (x y : α) : Verdict (gradeRealization tag Represented R q x y) :=
  obstructionAt (gradeRealization tag Represented R q x y)

/-- Clause (i) of stratification: at every declared tag the obstruction is
trivial exactly when the semantic realization is inhabited. -/
theorem grade_obstruction_trivial_iff_realized {α β : Type}
    (tag : GradeTag) (Represented : (α → α → Prop) → Prop)
    (R : α → α → Prop) (q : α → β) (x y : α) :
    (gradeObstruction tag Represented R q x y).IsRealized ↔
      gradeRealization tag Represented R q x y :=
  obstruction_trivial_iff_realized _

/-! ## Uniform positive transport table -/

/-- Clause (ii), as one uniform positive table. Static distinction moves and
reflects through observer factorization. Persistent distinction moves forward
under step lifting and reflects backward under step simulation. Represented
persistent distinction moves between code languages under denotation
preservation. -/
theorem dyn_transport_table
    {α β γ δ Code₁ Code₂ : Type}
    {f : α → β} {R : α → α → Prop} {S : β → β → Prop}
    {q : α → γ} {q' : β → γ} {x y : α}
    {T : δ → δ → Prop} {r : δ → γ} {z w : δ}
    {denote₁ : Code₁ → δ → δ → Prop}
    {denote₂ : Code₂ → δ → δ → Prop}
    (mapCode : Code₁ → Code₂)
    (hobs : ObserverFactorsThrough f q q') :
    (D1s q x y → D1s q' (f x) (f y)) ∧
    (D1s q' (f x) (f y) → D1s q x y) ∧
    (StepLifting f R S → D1p R q x y → D1p S q' (f x) (f y)) ∧
    (StepSimulation f R S → D1p S q' (f x) (f y) → D1p R q x y) ∧
    (CodeDenotationPreserving mapCode denote₁ denote₂ →
      D2At (RepresentedBy Code₁ denote₁) T r z w →
      D2At (RepresentedBy Code₂ denote₂) T r z w) := by
  refine ⟨d1s_transport_of_observerFactor hobs,
    d1s_reflect_of_observerFactor hobs, ?_, ?_, ?_⟩
  · intro hlift hD1
    exact d1p_transport_of_stepLifting hobs hlift hD1
  · intro hsim hD1
    exact d1p_reflect_of_stepSimulation hobs hsim hD1
  · intro hcode hD2
    exact d2At_transport_codeDenotation mapCode hcode hD2

/-! ## Two negative transport fixtures -/

/-- Empty one-step dynamics on `Bool`. -/
def noStepBool (_ _ : Bool) : Prop := False

/-- One directed step, from `true` to `false`. -/
def collapseStepBool (x y : Bool) : Prop := x = true ∧ y = false

/-- Reachability in the empty relation is equality. -/
theorem noStepBool_star_iff_eq (x y : Bool) :
    Relation.ReflTransGen noStepBool x y ↔ x = y := by
  constructor
  · intro h
    induction h with
    | refl => rfl
    | tail _ hstep _ => exact hstep.elim
  · intro h
    subst y
    exact Relation.ReflTransGen.refl

/-- The pair `(true,false)` is persistently distinguished under the empty
relation. -/
theorem noStepBool_d1p : D1p noStepBool id true false := by
  intro x' y' hx hy
  have hxt : true = x' := (noStepBool_star_iff_eq true x').1 hx
  have hyf : false = y' := (noStepBool_star_iff_eq false y').1 hy
  subst x'
  subst y'
  decide

/-- The same pair is not persistently distinguished after adding the collapse
step. -/
theorem collapseStepBool_not_d1p : ¬ D1p collapseStepBool id true false := by
  intro h
  have hbad := h false false
    (Relation.ReflTransGen.single ⟨rfl, rfl⟩)
    Relation.ReflTransGen.refl
  exact hbad rfl

/-- Forward transport of D1p cannot be obtained from simulation alone. The
source relation is empty, so the identity map simulates it into the target;
source D1p holds and target D1p fails. -/
theorem d1p_not_transport_of_simulation_alone :
    ObserverFactorsThrough id (id : Bool → Bool) id ∧
    StepSimulation id noStepBool collapseStepBool ∧
    D1p noStepBool id true false ∧
    ¬ D1p collapseStepBool id true false := by
  refine ⟨fun _ => rfl, ?_, noStepBool_d1p, collapseStepBool_not_d1p⟩
  intro _ _ h
  exact h.elim

/-- Empty represented language. -/
def EmptyRepresentation (_ : Bool → Bool → Prop) : Prop := False

/-- A represented language containing exactly Boolean disequality. -/
def DisequalityRepresentation (cmp : Bool → Bool → Prop) : Prop :=
  cmp = fun a b => a ≠ b

/-- The identity map lifts the empty relation into itself. -/
theorem noStepBool_id_lifting : StepLifting id noStepBool noStepBool := by
  intro _ _ h
  exact h.elim

/-- D2 is realized in the disequality representation language. -/
theorem disequalityRepresentation_d2 :
    D2At DisequalityRepresentation noStepBool id true false := by
  refine ⟨noStepBool_d1p, ?_⟩
  refine ⟨fun a b => a ≠ b, rfl, ?_⟩
  intro a b
  rfl

/-- D2 is impossible in the empty representation language. -/
theorem emptyRepresentation_not_d2 :
    ¬ D2At EmptyRepresentation noStepBool id true false := by
  rintro ⟨_, cmp, hcmp, _⟩
  exact hcmp

/-- Lifting alone does not reflect D2 across a change of represented language.
The dynamics and observer are identical, the target language represents
Boolean disequality, and the source language represents nothing. -/
theorem d2_not_reflect_of_lifting_alone :
    ObserverFactorsThrough id (id : Bool → Bool) id ∧
    StepLifting id noStepBool noStepBool ∧
    D2At DisequalityRepresentation noStepBool id true false ∧
    ¬ D2At EmptyRepresentation noStepBool id true false :=
  ⟨fun _ => rfl, noStepBool_id_lifting,
    disequalityRepresentation_d2, emptyRepresentation_not_d2⟩

/-! ## Clause (iii): all adjacent reverse separations -/

/-- The seven adjacent reverse certificates of the interface-refinement tower. -/
structure AdjacentReverseSeparations where
  substQuote : ¬ Refines gradeSubst gradeQuote
  diagSubst : ¬ Refines gradeDiagSyntax gradeSubst
  selfDiag : SelfEvaluationLaw lossyQuote lossyEval lossyDiag ∧
    ¬ FaithfulQuote lossyQuote
  universalSelf : UniversalEvaluation AllUnitBool separatedUniversalEval ∧
    ¬ CodeArgumentIdentification Bool Unit
  representationUniversal : RepresentationClosed AllBoolEndomaps ∧
    ¬ ∃ eval, UniversalEvaluation (Code := Unit) (Arg := Bool) (Val := Bool)
      AllBoolEndomaps eval
  booleanRepresentation : BooleanEqualityComparator boolEqualityTest ∧
    ¬ RepresentationClosed NegationOnly
  truthBoolean : ¬ Refines gradeSemanticTruth gradeBoolCompare

/-- Every adjacent missing reverse implication carries a concrete
carrier-and-interface witness. -/
theorem adjacent_reverse_separations_complete :
    Nonempty AdjacentReverseSeparations :=
  ⟨{
    substQuote := subst_not_refines_quote
    diagSubst := diag_not_refines_subst
    selfDiag := selfEvaluation_without_faithfulDiagonalSyntax
    universalSelf := universalEvaluation_without_selfEvaluationCarrier
    representationUniversal := representationClosure_without_universalEvaluation
    booleanRepresentation := booleanComparison_without_representationClosure
    truthBoolean := truth_not_refines_bool
  }⟩

/-! ## Clause (iv): computation rules -/

/-- The four declared computation-rule families, kept at the live universe-zero
interfaces used by `Box`, D1p, and D2At. -/
structure DeclaredComputationRules where
  productClosure :
    ∀ {A B : Type} {R : A → A → Prop} {S : B → B → Prop}
      {a a' : A} {b b' : B},
      Relation.ReflTransGen (ProductStep R S) (a, b) (a', b') ↔
        Relation.ReflTransGen R a a' ∧ Relation.ReflTransGen S b b'
  productPersistence :
    ∀ {A B : Type} {R : A → A → Prop} {S : B → B → Prop}
      {P : A → Prop} {Q : B → Prop} (a : A) (b : B),
      Box (ProductStep R S) (fun p : A × B => P p.1 ∧ Q p.2) (a, b) ↔
        Box R P a ∧ Box S Q b
  quotientObstruction :
    ∀ {Y : Type} (y₀ _y : Y) (t : Occ Y → Occ Y → Occ Y),
      NaturalUnder roleCollapse t →
        ¬ IsDiscriminator ((y₀, Role.active) : Occ Y) t
  licensedSubrelation :
    ∀ {α β : Type} {R : α → α → Prop} (q : α → β) (x y : α),
      Box (PairLift R) (fun p : α × α => q p.1 ≠ q p.2) (x, y) ↔
        D1p R q x y
  completion :
    ∀ {α β : Type} (R : α → α → Prop) (P : α → Prop)
      (q : α → β) (x y : α) (D : LicensingDatum.{0,0,0})
      (d : D.Carrier) (F : ℕ → ℂ → ℂ) (U : Set ℂ),
      (Box (Relation.ReflTransGen R) P x ↔ Box R P x) ∧
      (D1p (Relation.ReflTransGen R) q x y ↔ D1p R q x y) ∧
      (Box (completeDatum D).dynamics D.license d ↔
        Box D.dynamics D.license d) ∧
      (MetricPersistentLicense F U ↔
        ∀ K ⊆ U, IsCompact K →
          ∃ ε, 0 < ε ∧ ∃ N,
            Box shiftStep (fun n => ∀ z ∈ K, ε ≤ ‖F n z‖) N)

/-- The product, quotient, licensed-subrelation, and dynamic-completion rules
are all inhabited by the compiled modules. -/
def declaredComputationRules : DeclaredComputationRules where
  productClosure := fun {_ _ _ _ _ _ _ _} => productStep_star_iff
  productPersistence := fun {_ _ _ _ _ _} a b => box_product_iff a b
  quotientObstruction := fun y₀ y t hnat =>
    roleErasure_quotient_no_discriminator y₀ y t hnat
  licensedSubrelation := fun q x y => licensedPairSubrelation_box_iff_d1p q x y
  completion := fun R P q x y D d F U =>
    completion_rules_complete R P q x y D d F U

/-! ## The finite stratification package -/

/-- One proof-carrying package for clauses (i)--(iv) at the declared tags. -/
structure DeclaredStratification where
  obstructionClassification :
    ∀ {α β : Type} (tag : GradeTag)
      (Represented : (α → α → Prop) → Prop)
      (R : α → α → Prop) (q : α → β) (x y : α),
      (gradeObstruction tag Represented R q x y).IsRealized ↔
        gradeRealization tag Represented R q x y
  d1sForward :
    ∀ {α β γ : Type} {f : α → β} {q : α → γ} {q' : β → γ}
      {x y : α},
      ObserverFactorsThrough f q q' →
        D1s q x y → D1s q' (f x) (f y)
  d1sReflect :
    ∀ {α β γ : Type} {f : α → β} {q : α → γ} {q' : β → γ}
      {x y : α},
      ObserverFactorsThrough f q q' →
        D1s q' (f x) (f y) → D1s q x y
  d1pForward :
    ∀ {α β γ : Type} {f : α → β}
      {R : α → α → Prop} {S : β → β → Prop}
      {q : α → γ} {q' : β → γ} {x y : α},
      ObserverFactorsThrough f q q' → StepLifting f R S →
        D1p R q x y → D1p S q' (f x) (f y)
  d1pReflect :
    ∀ {α β γ : Type} {f : α → β}
      {R : α → α → Prop} {S : β → β → Prop}
      {q : α → γ} {q' : β → γ} {x y : α},
      ObserverFactorsThrough f q q' → StepSimulation f R S →
        D1p S q' (f x) (f y) → D1p R q x y
  d2CodeForward :
    ∀ {α γ Code₁ Code₂ : Type}
      {denote₁ : Code₁ → α → α → Prop}
      {denote₂ : Code₂ → α → α → Prop}
      (mapCode : Code₁ → Code₂),
      CodeDenotationPreserving mapCode denote₁ denote₂ →
        ∀ {R : α → α → Prop} {q : α → γ} {x y : α},
          D2At (RepresentedBy Code₁ denote₁) R q x y →
            D2At (RepresentedBy Code₂ denote₂) R q x y
  d1pSimulationOnlyCounterexample :
    ObserverFactorsThrough id (id : Bool → Bool) id ∧
    StepSimulation id noStepBool collapseStepBool ∧
    D1p noStepBool id true false ∧
    ¬ D1p collapseStepBool id true false
  d2LiftingOnlyCounterexample :
    ObserverFactorsThrough id (id : Bool → Bool) id ∧
    StepLifting id noStepBool noStepBool ∧
    D2At DisequalityRepresentation noStepBool id true false ∧
    ¬ D2At EmptyRepresentation noStepBool id true false
  reverseSeparations : AdjacentReverseSeparations
  computationRules : DeclaredComputationRules

/-- Clauses (i)--(iv) of the manuscript's stratification conjecture are
mechanized on the three structural and four dynamic tags, and on no wider tag
universe. -/
theorem stratification_theorem_at_declared_tags :
    Nonempty DeclaredStratification :=
  ⟨{
    obstructionClassification := grade_obstruction_trivial_iff_realized
    d1sForward := d1s_transport_of_observerFactor
    d1sReflect := d1s_reflect_of_observerFactor
    d1pForward := d1p_transport_of_stepLifting
    d1pReflect := d1p_reflect_of_stepSimulation
    d2CodeForward := d2At_transport_codeDenotation
    d1pSimulationOnlyCounterexample := d1p_not_transport_of_simulation_alone
    d2LiftingOnlyCounterexample := d2_not_reflect_of_lifting_alone
    reverseSeparations := Classical.choice adjacent_reverse_separations_complete
    computationRules := declaredComputationRules
  }⟩

end OperatorKO7.Meta.DistinctionBoundary.DiagonalGradeStratification



