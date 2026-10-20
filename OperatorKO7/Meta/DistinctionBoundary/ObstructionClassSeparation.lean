import OperatorKO7.Meta.DistinctionBoundary.DiagonalLevels
import OperatorKO7.Meta.DistinctionBoundary.SharedRoot
import OperatorKO7.Meta.DominancePremiseSharpness

/-!
# Obstruction-class separation

Diagonal self-evaluation obstruction is stable under every carrier-preserving
extension that remains closed under a fixed-point-free diagonal shift.  Direct
polynomial orientation obstruction is not stable: the counter-uncoupled
language is obstructed for every step-duplicating schema, while the full
polynomial language contains a cross-coupled orienter on the free schema.

The two obstruction systems therefore admit no equivalence preserving both
language extension and obstruction truth.  The final section separately
packages the constant-collapse witnesses as nondefinability certificates.

Relation: the root duplicating step on the orientation side; evaluator
representation on the diagonal side.  Closure: root and carrier-preserving
language extension.  Trust: kernel and Mathlib only.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.DistinctionBoundary.ObstructionClassSeparation

open OperatorKO7
open OperatorKO7.Meta.DistinctionBoundary.DiagonalLevels
open OperatorKO7.Meta.DistinctionBoundary.SharedRoot
open OperatorKO7.StepDuplicating
open OperatorKO7.StepDuplicating.StepDuplicatingSchema

universe u v w

/-! ## Generic diagonal-closed languages -/

/-- A unary/binary function language closed under the shifted diagonal of each
admitted binary evaluator. -/
structure DiagonalClosedLanguage (A : Type u) (Y : Type v) (shift : Y → Y) where
  unary : (A → Y) → Prop
  binary : (A → A → Y) → Prop
  diagonal_closed : ∀ {E : A → A → Y}, binary E → unary (fun a => shift (E a a))

/-- One evaluator represents every admitted unary function. -/
def IsUniversalEvaluator {A : Type u} {Y : Type v} {shift : Y → Y}
    (L : DiagonalClosedLanguage A Y shift) (E : A → A → Y) : Prop :=
  L.binary E ∧ ∀ f : A → Y, L.unary f → ∃ c : A, ∀ x : A, E c x = f x

/-- The language has no admitted universal evaluator. -/
def SelfEvaluationObstructed {A : Type u} {Y : Type v} {shift : Y → Y}
    (L : DiagonalClosedLanguage A Y shift) : Prop :=
  ¬ ∃ E : A → A → Y, IsUniversalEvaluator L E

/-- Inclusion of the unary and binary classes on fixed carriers and a fixed
diagonal shift. -/
structure DiagonalClosedLanguage.Extends {A : Type u} {Y : Type v}
    {shift : Y → Y} (L₀ L₁ : DiagonalClosedLanguage A Y shift) : Prop where
  unary_mono : ∀ {f : A → Y}, L₀.unary f → L₁.unary f
  binary_mono : ∀ {E : A → A → Y}, L₀.binary E → L₁.binary E

/-- Lawvere's diagonal argument for an arbitrary code carrier, value carrier,
language, and fixed-point-free shift. -/
theorem no_universal_evaluator_of_diagonal_closure
    {A : Type u} {Y : Type v} {shift : Y → Y}
    (hshift : ∀ y : Y, shift y ≠ y)
    (L : DiagonalClosedLanguage A Y shift) :
    SelfEvaluationObstructed L := by
  rintro ⟨E, hE, huniversal⟩
  obtain ⟨c, hc⟩ := huniversal (fun a => shift (E a a)) (L.diagonal_closed hE)
  exact hshift (E c c) (hc c).symm

/-- Every diagonal-closed language over a fixed-point-free shift is obstructed,
without a finiteness, decidability, or nonemptiness premise. -/
theorem every_diagonalClosedLanguage_obstructed
    {A : Type u} {Y : Type v} {shift : Y → Y}
    (hshift : ∀ y : Y, shift y ≠ y) :
    ∀ L : DiagonalClosedLanguage A Y shift, SelfEvaluationObstructed L :=
  fun L => no_universal_evaluator_of_diagonal_closure hshift L

/-- The diagonal obstruction survives every carrier-preserving language
extension that retains diagonal closure under the same shift. -/
theorem diagonal_obstruction_stable_under_extension
    {A : Type u} {Y : Type v} {shift : Y → Y}
    (hshift : ∀ y : Y, shift y ≠ y)
    {L₀ L₁ : DiagonalClosedLanguage A Y shift}
    (_ : L₀.Extends L₁) (_ : SelfEvaluationObstructed L₀) :
    SelfEvaluationObstructed L₁ :=
  no_universal_evaluator_of_diagonal_closure hshift L₁

/-! ## The kernel Sigma language as a specialization -/

/-- The unary and binary Sigma-definable functions on `Trace`, closed under
the `delta`-shifted diagonal. -/
def traceSigmaLanguage : DiagonalClosedLanguage Trace Trace Trace.delta where
  unary := SigmaDefinableUnary
  binary := SigmaDefinableBinary
  diagonal_closed := sigmaDefinableUnary_delta_diagonal

/-- The generic diagonal theorem specializes definitionally to the compiled
Sigma-language no-universal-evaluator theorem. -/
theorem traceSigmaLanguage_obstructed :
    SelfEvaluationObstructed traceSigmaLanguage := by
  simpa [SelfEvaluationObstructed, IsUniversalEvaluator, traceSigmaLanguage] using
    no_sigmaDefinable_universal_evaluator

/-- The Trace result is one instance of the arbitrary-carrier theorem. -/
theorem traceSigmaLanguage_obstructed_via_generic :
    SelfEvaluationObstructed traceSigmaLanguage :=
  no_universal_evaluator_of_diagonal_closure delta_ne_self traceSigmaLanguage

/-! ## Polynomial orientation languages -/

/-- Strict root orientation of every instance of the duplicating schema rule. -/
def OrientsDuplicatingStep {S : StepDuplicatingSchema}
    (M : BoundedPolynomialMeasure S) : Prop :=
  ∀ b s n : S.T,
    M.eval (S.wrap s (S.recur b s n)) < M.eval (S.recur b s (S.succ n))

/-- A language selects a class of polynomial interpretations on one schema. -/
structure PolynomialMeasureLanguage (S : StepDuplicatingSchema) where
  admits : BoundedPolynomialMeasure S → Prop

/-- Inclusion of polynomial interpretation languages. -/
def PolynomialMeasureLanguage.Extends {S : StepDuplicatingSchema}
    (L₀ L₁ : PolynomialMeasureLanguage S) : Prop :=
  ∀ M, L₀.admits M → L₁.admits M

/-- Every admitted interpretation fails to orient the duplicating step. -/
def PolynomialOrientationObstructed {S : StepDuplicatingSchema}
    (L : PolynomialMeasureLanguage S) : Prop :=
  ∀ M, L.admits M → ¬ OrientsDuplicatingStep M

/-- The counter-uncoupled polynomial language. -/
def counterUncoupledPolynomialLanguage (S : StepDuplicatingSchema) :
    PolynomialMeasureLanguage S where
  admits := NoCounterExponent

/-- The full bounded-polynomial language. -/
def fullPolynomialLanguage (S : StepDuplicatingSchema) :
    PolynomialMeasureLanguage S where
  admits := fun _ => True

/-- Counter-uncoupled polynomial interpretations form a sublanguage of the
full polynomial language on every schema. -/
theorem counterUncoupled_extends_full (S : StepDuplicatingSchema) :
    (counterUncoupledPolynomialLanguage S).Extends (fullPolynomialLanguage S) := by
  intro M hM
  trivial

/-- Counter-uncoupled polynomial orientation is obstructed on every
step-duplicating schema. -/
theorem counterUncoupledPolynomial_obstructed (S : StepDuplicatingSchema) :
    PolynomialOrientationObstructed (counterUncoupledPolynomialLanguage S) := by
  intro M hM
  exact no_polynomial_orients_dup_step_of_no_counter_exponent M hM

/-- The full polynomial language is not obstructed on the free schema: the
compiled cross-coupled polynomial orients every duplicating-step instance. -/
theorem fullPolynomial_not_obstructed_freeSchema :
    ¬ PolynomialOrientationObstructed (fullPolynomialLanguage freeSchema) := by
  intro h
  exact h crossCoupledPolynomial trivial crossCoupledWeight_strictly_orients

/-- One carrier-preserving polynomial-language extension removes the direct
orientation obstruction. -/
theorem polynomial_extension_dissolves_obstruction :
    (counterUncoupledPolynomialLanguage freeSchema).Extends
        (fullPolynomialLanguage freeSchema) ∧
      PolynomialOrientationObstructed
        (counterUncoupledPolynomialLanguage freeSchema) ∧
      ¬ PolynomialOrientationObstructed (fullPolynomialLanguage freeSchema) :=
  ⟨counterUncoupled_extends_full freeSchema,
    counterUncoupledPolynomial_obstructed freeSchema,
    fullPolynomial_not_obstructed_freeSchema⟩

/-! ## Exact separation of obstruction systems -/

/-- A class of objects equipped with extension and obstruction predicates. -/
structure ObstructionSystem where
  Object : Type u
  extension : Object → Object → Prop
  obstructed : Object → Prop

/-- An isomorphism of obstruction systems preserves both extension and
obstruction truth. -/
structure ObstructionSystemEquiv (S : ObstructionSystem.{u})
    (T : ObstructionSystem.{v}) where
  objects : S.Object ≃ T.Object
  extension_iff : ∀ x y, S.extension x y ↔ T.extension (objects x) (objects y)
  obstructed_iff : ∀ x, S.obstructed x ↔ T.obstructed (objects x)

/-- A map between obstruction systems that preserves and reflects obstruction
truth, without an injectivity or extension premise. -/
structure ObstructionTruthMap (S : ObstructionSystem.{u})
    (T : ObstructionSystem.{v}) where
  toFun : S.Object → T.Object
  obstructed_iff : ∀ x, S.obstructed x ↔ T.obstructed (toFun x)

/-- Every obstruction survives every extension in a system. -/
def ObstructionSystem.ExtensionStable (S : ObstructionSystem.{u}) : Prop :=
  ∀ x y, S.extension x y → S.obstructed x → S.obstructed y

/-- Reverse an obstruction-system isomorphism. -/
def ObstructionSystemEquiv.symm
    {S : ObstructionSystem.{u}} {T : ObstructionSystem.{v}}
    (E : ObstructionSystemEquiv S T) : ObstructionSystemEquiv T S where
  objects := E.objects.symm
  extension_iff := by
    intro x y
    simpa using
      (E.extension_iff (E.objects.symm x) (E.objects.symm y)).symm
  obstructed_iff := by
    intro x
    simpa using (E.obstructed_iff (E.objects.symm x)).symm

/-- Extension stability transports across every obstruction-system
isomorphism. -/
theorem extensionStable_map
    {S : ObstructionSystem.{u}} {T : ObstructionSystem.{v}}
    (E : ObstructionSystemEquiv S T) (hS : S.ExtensionStable) :
    T.ExtensionStable := by
  intro x y hxy hx
  have hsxy : S.extension (E.objects.symm x) (E.objects.symm y) := by
    apply (E.extension_iff (E.objects.symm x) (E.objects.symm y)).2
    simpa using hxy
  have hsx : S.obstructed (E.objects.symm x) := by
    apply (E.obstructed_iff (E.objects.symm x)).2
    simpa using hx
  have hsy := hS _ _ hsxy hsx
  have hTy := (E.obstructed_iff (E.objects.symm y)).1 hsy
  simpa using hTy

/-- Extension stability is invariant under obstruction-system isomorphism. -/
theorem extensionStable_iff
    {S : ObstructionSystem.{u}} {T : ObstructionSystem.{v}}
    (E : ObstructionSystemEquiv S T) :
    S.ExtensionStable ↔ T.ExtensionStable :=
  ⟨extensionStable_map E, extensionStable_map E.symm⟩

/-- The obstruction system of diagonal-closed languages on arbitrary carriers
under a fixed shift. -/
def diagonalObstructionSystem
    (A : Type u) (Y : Type v) (shift : Y → Y) : ObstructionSystem where
  Object := DiagonalClosedLanguage A Y shift
  extension := DiagonalClosedLanguage.Extends
  obstructed := SelfEvaluationObstructed

/-- The obstruction system of bounded-polynomial languages on the free
step-duplicating schema. -/
def freePolynomialOrientationSystem : ObstructionSystem where
  Object := PolynomialMeasureLanguage freeSchema
  extension := PolynomialMeasureLanguage.Extends
  obstructed := PolynomialOrientationObstructed

/-- Every diagonal-language obstruction over a fixed-point-free shift survives
extension, for arbitrary code and value carriers. -/
theorem diagonalObstructionSystem_extensionStable
    {A : Type u} {Y : Type v} {shift : Y → Y}
    (hshift : ∀ y : Y, shift y ≠ y) :
    (diagonalObstructionSystem A Y shift).ExtensionStable := by
  intro L₀ L₁ hExt hObs
  exact diagonal_obstruction_stable_under_extension hshift hExt hObs

/-- The Trace Sigma obstruction system is the kernel specialization of the
arbitrary-carrier extension-stability theorem. -/
theorem traceDiagonalObstructionSystem_extensionStable :
    (diagonalObstructionSystem Trace Trace Trace.delta).ExtensionStable :=
  diagonalObstructionSystem_extensionStable delta_ne_self

/-- Polynomial orientation obstruction on the free schema is not stable under
language extension. -/
theorem freePolynomialOrientationSystem_not_extensionStable :
    ¬ freePolynomialOrientationSystem.ExtensionStable := by
  intro hstable
  exact fullPolynomial_not_obstructed_freeSchema
    (hstable (counterUncoupledPolynomialLanguage freeSchema)
      (fullPolynomialLanguage freeSchema)
      (counterUncoupled_extends_full freeSchema)
      (counterUncoupledPolynomial_obstructed freeSchema))

/-- For every fixed-point-free shift, its diagonal-language obstruction system
and the free polynomial-orientation system admit no isomorphism preserving
extension and obstruction truth. -/
theorem diagonal_and_orientation_obstructions_not_equivalent_generic
    {A : Type u} {Y : Type v} {shift : Y → Y}
    (hshift : ∀ y : Y, shift y ≠ y) :
    ¬ Nonempty
      (ObstructionSystemEquiv (diagonalObstructionSystem A Y shift)
        freePolynomialOrientationSystem) := by
  rintro ⟨E⟩
  have hStable : freePolynomialOrientationSystem.ExtensionStable :=
    extensionStable_map E (diagonalObstructionSystem_extensionStable hshift)
  exact freePolynomialOrientationSystem_not_extensionStable hStable

/-- The Trace Sigma and free-polynomial systems are a specialization of the
arbitrary-carrier nonisomorphism theorem. -/
theorem diagonal_and_orientation_obstructions_not_equivalent :
    ¬ Nonempty
      (ObstructionSystemEquiv
        (diagonalObstructionSystem Trace Trace Trace.delta)
        freePolynomialOrientationSystem) :=
  diagonal_and_orientation_obstructions_not_equivalent_generic delta_ne_self

/-- No obstruction-truth-preserving map from a diagonal system with a
fixed-point-free shift onto the free polynomial-orientation system is
surjective.  This is strictly stronger than the nonisomorphism theorem and
does not assume preservation of the extension relation. -/
theorem no_surjective_obstructionTruthMap_diagonal_to_orientation
    {A : Type u} {Y : Type v} {shift : Y → Y}
    (hshift : ∀ y : Y, shift y ≠ y)
    (F : ObstructionTruthMap (diagonalObstructionSystem A Y shift)
      freePolynomialOrientationSystem) :
    ¬ Function.Surjective F.toFun := by
  intro hsurjective
  obtain ⟨L, hL⟩ := hsurjective (fullPolynomialLanguage freeSchema)
  have hSource : SelfEvaluationObstructed L :=
    no_universal_evaluator_of_diagonal_closure hshift L
  have hTarget : PolynomialOrientationObstructed (F.toFun L) :=
    (F.obstructed_iff L).1 hSource
  rw [hL] at hTarget
  exact fullPolynomial_not_obstructed_freeSchema hTarget

/-! ## Constant-collapse nondefinability witnesses -/

/-- A target observable is definable from a source observable when it factors
through one decoder. -/
def DefinableFrom {X : Type u} {C : Type v} {L : Type w}
    (source : X → C) (target : X → L) : Prop :=
  ∃ decode : C → L, ∀ x, decode (source x) = target x

/-- Any same-source, different-target pair refutes definability, over arbitrary
universe levels and without finiteness or decidable equality. -/
theorem collision_not_definable
    {X : Type u} {C : Type v} {L : Type w}
    {source : X → C} {target : X → L} {x y : X}
    (hsame : source x = source y) (hdifferent : target x ≠ target y) :
    ¬ DefinableFrom source target := by
  rintro ⟨decode, hdecode⟩
  apply hdifferent
  calc
    target x = decode (source x) := (hdecode x).symm
    _ = decode (source y) := congrArg decode hsame
    _ = target y := hdecode y

/-- Every substitution-invariance obstruction is a nondefinability witness:
the license cannot be recovered from the collapse observation. -/
theorem substitutionObstruction_not_definable
    {Term : Type} {Lic : Type}
    (O : SubstitutionInvariantObstruction Term Lic) :
    ¬ DefinableFrom O.collapse O.license :=
  collision_not_definable O.collapse_identifies O.license_separates

/-- The distinction-axis constant-collapse witness is a concrete
nondefinability certificate. -/
theorem distinction_license_not_definable_from_collapse :
    ¬ DefinableFrom distinctionObstruction.collapse distinctionObstruction.license :=
  substitutionObstruction_not_definable distinctionObstruction

/-- The orientation-axis constant-collapse witness is a concrete
nondefinability certificate. -/
theorem orientation_license_not_definable_from_collapse :
    ¬ DefinableFrom orientationObstruction.collapse orientationObstruction.license :=
  substitutionObstruction_not_definable orientationObstruction

/-- The complete separation package: diagonal obstruction is extension-stable,
polynomial orientation obstruction is not, no obstruction-system isomorphism
identifies them, and both constant-collapse examples carry exact
nondefinability certificates. -/
theorem obstruction_class_separation_complete :
    (diagonalObstructionSystem Trace Trace Trace.delta).ExtensionStable ∧
      ¬ freePolynomialOrientationSystem.ExtensionStable ∧
      ¬ Nonempty
        (ObstructionSystemEquiv
          (diagonalObstructionSystem Trace Trace Trace.delta)
          freePolynomialOrientationSystem) ∧
      (¬ DefinableFrom distinctionObstruction.collapse
        distinctionObstruction.license) ∧
      ¬ DefinableFrom orientationObstruction.collapse
        orientationObstruction.license :=
  ⟨traceDiagonalObstructionSystem_extensionStable,
    freePolynomialOrientationSystem_not_extensionStable,
    diagonal_and_orientation_obstructions_not_equivalent,
    distinction_license_not_definable_from_collapse,
    orientation_license_not_definable_from_collapse⟩

end OperatorKO7.Meta.DistinctionBoundary.ObstructionClassSeparation
