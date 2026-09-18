import OperatorKO7.Meta.UniqueNormalization.ConstructorCompatibility
import OperatorKO7.Meta.UniqueNormalization.ConstructorTranslation
import OperatorKO7.Meta.UniqueNormalization.Theorem69

/-!
# Reach test: the reduction of RTA #79 to constructor compatibility

Campaign: `Roadmaps\klop\ROADMAP.md`, WP-K2c reframed.

This check imports every module it names. It asserts that the reduction chain
elaborates verbatim and exercises each link: constructor compatibility gives
consistency (Lemma 28), the constructor translation carries consistency back
(Corollary 16), and Theorem 69's reduction turns consistency of the extensions
into unique normal forms.

The final example preserves the older constructor-compatibility reduction
interface. The source-faithful summit now continues through `Summit.lean` and
`SignatureExtension.lean`; this gate audits the reduction as an intermediate
theorem rather than calling it the whole remaining campaign obligation.
-/

set_option autoImplicit false

namespace UN79ReductionReach

open OperatorKO7.Meta.Rewriting
open OperatorKO7.Meta.UniqueNormalization

#check @ConTopped
#check @ConTopped.var
#check @ConTopped.app
#check @ConstructorCompatible
#check @Consistent_of_constructorCompatible
#check @Consistent_of_translation_constructorCompatible
#check @UNconv_of_translation_constructorCompatible
#check @UNred_of_translation_constructorCompatible
#check @forall₂_conv_refl
#check @constructorCompatible_of_conv_eq
#check @constructorCompatible_nil
#check @conv_nil_eq
#check @not_step_nil

#print axioms OperatorKO7.Meta.UniqueNormalization.ConTopped
#print axioms OperatorKO7.Meta.UniqueNormalization.ConTopped.var
#print axioms OperatorKO7.Meta.UniqueNormalization.ConTopped.app
#print axioms OperatorKO7.Meta.UniqueNormalization.ConstructorCompatible
#print axioms OperatorKO7.Meta.UniqueNormalization.Consistent_of_constructorCompatible
#print axioms OperatorKO7.Meta.UniqueNormalization.Consistent_of_translation_constructorCompatible
#print axioms OperatorKO7.Meta.UniqueNormalization.UNconv_of_translation_constructorCompatible
#print axioms OperatorKO7.Meta.UniqueNormalization.UNred_of_translation_constructorCompatible
#print axioms OperatorKO7.Meta.UniqueNormalization.forall₂_conv_refl
#print axioms OperatorKO7.Meta.UniqueNormalization.constructorCompatible_of_conv_eq
#print axioms OperatorKO7.Meta.UniqueNormalization.not_step_nil
#print axioms OperatorKO7.Meta.UniqueNormalization.conv_nil_eq
#print axioms OperatorKO7.Meta.UniqueNormalization.constructorCompatible_nil

/-- Lemma 28: constructor compatibility gives consistency. -/
example {sigma nu : Type} {R : TRS (sigma ⊕ sigma) nu}
    (h : ConstructorCompatible (conv R)) : Consistent R :=
  Consistent_of_constructorCompatible h

/-- Lemma 28 composed with Corollary 16: constructor compatibility of the
translation gives consistency of the system itself. -/
example {sigma nu : Type} (R : TRS sigma nu)
    (h : ConstructorCompatible (conv (constructorTranslation R))) : Consistent R :=
  Consistent_of_translation_constructorCompatible R h

/-- **The older constructor-compatibility reduction, in one type.** Given
constructor compatibility over every system of the class, and membership of each
same-signature Theorem 69 extension in that class, the system has unique normal
forms with respect to conversion and with respect to reduction.

Both hypotheses are statements about systems other than `R`, which is what the
2026-09-01 strength audit corrected: the earlier shape drew its conclusion from a
hypothesis refuted elsewhere in the same development. -/
example {sigma nu : Type} {R : TRS sigma nu} {x y : nu} (hxy : x ≠ y)
    (hCC : ∀ S : TRS sigma nu, NonOmegaOverlapping S → TRS.RhsDetermined S →
      ConstructorCompatible (conv (constructorTranslation S)))
    (hclass : ∀ t u : Term sigma nu, NormalForm R t → NormalForm R u →
      conv R t u → t ≠ u →
      ∃ F : sigma, NonOmegaOverlapping (extendedTRS R F t u x y) ∧
        TRS.RhsDetermined (extendedTRS R F t u x y)) :
    UNconv R ∧ UNred R :=
  ⟨UNconv_of_translation_constructorCompatible hxy hCC hclass,
    UNred_of_translation_constructorCompatible hxy hCC hclass⟩

/-- The hypothesis class is inhabited: the empty system's translation has
constructor-compatible conversion. -/
example : ConstructorCompatible (conv (constructorTranslation ([] : TRS Nat Nat))) :=
  constructorCompatible_nil

end UN79ReductionReach
