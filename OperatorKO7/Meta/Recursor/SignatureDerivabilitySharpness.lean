/-!
# Sharpness of the signature non-derivability hypothesis

The non-derivability theorem for the dependency-pair projection is quantified over
`Σ`-algebras whose recursor slot is constant in its third argument. Read without that
restriction the surrounding prose says the metatheoretic license is mathematically
required; read with it, the theorem says that algebras already blind to the third argument
stay blind to it.

This module pins the hypothesis as exactly right rather than as an artefact of the
statement. `constantThirdArgument_identifies_witnessPair` is the theorem's content, and
`counterHeightAlgebra_separates_witnessPair` exhibits a `Σ`-algebra that reads the third
argument and does separate the witness pair, so the hypothesis is load bearing and the
conclusion is scoped to the class it names.

The consequence for the manuscript is that the non-derivability is relative to the
direct whole-term class, which is the class the barrier package targets, rather than
absolute.

Relation: `Σ`-algebras over the recursor fragment of the companion signature.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only. No `sorry`, no `admit`, no new `axiom`, no native reduction.
-/

set_option autoImplicit false

universe u

namespace OperatorKO7.Meta.Recursor.SignatureDerivabilitySharpness

/-- The recursor fragment of the companion signature: a leaf, a successor-style wrapper,
and the ternary recursor. -/
inductive RecTerm : Type
  | void : RecTerm
  | delta : RecTerm → RecTerm
  | recDelta : RecTerm → RecTerm → RecTerm → RecTerm
deriving DecidableEq, Repr

/-- A `Σ`-algebra over that fragment. -/
structure RecAlgebra (Carrier : Type u) where
  /-- Interpretation of the leaf. -/
  void : Carrier
  /-- Interpretation of the wrapper. -/
  delta : Carrier → Carrier
  /-- Interpretation of the recursor. -/
  recDelta : Carrier → Carrier → Carrier → Carrier

/-- The canonical fold out of the free algebra. -/
def fold {Carrier : Type u} (S : RecAlgebra Carrier) : RecTerm → Carrier
  | .void => S.void
  | .delta t => S.delta (fold S t)
  | .recDelta x y z => S.recDelta (fold S x) (fold S y) (fold S z)

/-- The witness pair of the non-derivability theorem: two recursor terms differing only in
the third argument. -/
def witnessLeft : RecTerm := .recDelta .void .void .void

/-- The right half of the witness pair. -/
def witnessRight : RecTerm := .recDelta .void .void (.delta .void)

/-- The two witness terms are distinct in the free algebra. -/
theorem witnessPair_distinct : witnessLeft ≠ witnessRight := by
  intro h
  exact RecTerm.noConfusion (RecTerm.recDelta.inj h).2.2

/-! ### The theorem's content -/

/--
Proves: every algebra whose recursor slot ignores its third argument identifies the witness
pair, so the projection's distinguishing function escapes every such evaluator.
-/
theorem constantThirdArgument_identifies_witnessPair
    {Carrier : Type u} (S : RecAlgebra Carrier)
    (hconst : ∀ x y z z' : Carrier, S.recDelta x y z = S.recDelta x y z') :
    fold S witnessLeft = fold S witnessRight := by
  simp only [witnessLeft, witnessRight, fold]
  exact hconst _ _ _ _

/-! ### The hypothesis is load bearing -/

/-- The counter-height algebra, which reads the third argument. -/
def counterHeightAlgebra : RecAlgebra Nat where
  void := 0
  delta := fun n => n + 1
  recDelta := fun _ _ z => z

/--
Intent: **the sharpness witness**. A `Σ`-algebra that reads the third argument separates the
witness pair, so the constant-third-argument hypothesis carries the theorem and the
non-derivability is relative to that class rather than absolute.

Trust: kernel-only.
Gate R5 non-vacuity witness for the hypothesis.
-/
theorem counterHeightAlgebra_separates_witnessPair :
    fold counterHeightAlgebra witnessLeft ≠ fold counterHeightAlgebra witnessRight := by
  intro h
  simp only [witnessLeft, witnessRight, fold, counterHeightAlgebra] at h
  omega

/--
Proves: the counter-height algebra fails the constant-third-argument hypothesis, which is
the precise reason it escapes the theorem.
-/
theorem counterHeightAlgebra_reads_third_argument :
    ¬ (∀ x y z z' : Nat,
        counterHeightAlgebra.recDelta x y z = counterHeightAlgebra.recDelta x y z') := by
  intro hconst
  have := hconst 0 0 0 1
  simp only [counterHeightAlgebra] at this
  omega

/--
Proves: the two facts together, which is the scoped form the manuscript needs. The
projection's distinguishing function lies outside every constant-third-argument evaluator,
and inside at least one evaluator that reads the third argument.
-/
theorem signature_nonDerivability_is_relative_to_the_constant_class :
    (∀ (Carrier : Type) (S : RecAlgebra Carrier),
        (∀ x y z z' : Carrier, S.recDelta x y z = S.recDelta x y z') →
        fold S witnessLeft = fold S witnessRight)
      ∧ (∃ S : RecAlgebra Nat, fold S witnessLeft ≠ fold S witnessRight) :=
  ⟨fun _ S hconst => constantThirdArgument_identifies_witnessPair S hconst,
   ⟨counterHeightAlgebra, counterHeightAlgebra_separates_witnessPair⟩⟩

end OperatorKO7.Meta.Recursor.SignatureDerivabilitySharpness
