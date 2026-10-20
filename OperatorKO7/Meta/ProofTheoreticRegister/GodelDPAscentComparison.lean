import OperatorKO7.Meta.GodelSideAscentProfile
import OperatorKO7.Meta.LCELComparisonDegeneracy

set_option autoImplicit false

/-!
# What the Gödel and dependency-pair ascents share, and where they part

The operational-inexpressibility paper reads the dependency-pair confession and the Gödel
reflection ascent through one six-step licensed-ascent shape. Two facts are needed to state that
reading as a theorem instead of an analogy.

First, both sides realize the shape, and the Gödel side does so on compiled arithmetic rather than
a synthetic all-`True` profile: `godelCompiledAscentProfile` carries a provable formula, the failure
of the Gödel sentence to be its own truth predicate, unprovability of `ConQ`, a model of Q, the
failure of `ConQ` in that model, and unprovability of the negation. `structural_identity` carries
the dependency-pair side.

Second, the comparison at that layer is a classification and transports no witness. Any two
realized profiles of the same family compare, the comparison hom-sets are subsingletons, and the
same holds slot for slot on the LCEL side. The witness layer separates the two boundaries the shape
identifies: the Gödel checker ascent maps into the quotation ascent, while the orientation and
quotation ascents admit no morphism in either direction.

`shape_transports_witness_does_not` states both halves together. Nothing here claims that the
Gödel construction and the duplicating recursor are one object.
-/

namespace OperatorKO7.Meta.ProofTheoreticRegister.GodelDPAscentComparison

open OperatorKO7.ProofTheoreticRegister
open OperatorKO7.ClassicalAscentProfile
open OperatorKO7.StructuralIdentityComparison
open OperatorKO7.Meta.SafeStep.AscentProfileDegeneracy
open OperatorKO7.Meta.GodelSideAscentProfile
open OperatorKO7.Meta.LicensedBoundaryCalculus.LicensedAscent
open OperatorKO7.Meta.LicensedBoundaryCalculus.LicensedAscentTransport

/-- **Both sides realize the six-step shape.** The dependency-pair profile realizes it by
`structural_identity`; the Gödel profile realizes it on compiled arithmetic, with no stage
stipulated as `True`. -/
theorem dp_and_godel_realize_six_step_shape :
    RealizesSixStepShape dpSixStepStructuralProfile
      ∧ RealizesSixStepShape godelCompiledAscentProfile.shape :=
  ⟨structural_identity, godelCompiledAscentProfile_realizes⟩

/-- **The comparison at the shape layer is a classification.** Membership is six true stages plus
the reflection tag; any two realized profiles of the same family compare in both directions; and
the hom-sets are subsingletons, so a comparison carries no data beyond the classification. The
same degeneracy holds slot for slot for the LCEL comparison. -/
theorem six_step_comparison_degenerate :
    (∀ C : AscentProfile,
        CompatibleWithDp C ↔
          (RealizesSixStepShape C.shape ∧ C.family = AscentFamily.reflection))
      ∧ (∀ P Q : AscentProfile, Subsingleton (ComparisonWitness P Q))
      ∧ Nonempty (ComparisonWitness godelCompiledAscentProfile dpAsClassicalAscentProfile)
      ∧ Nonempty (ComparisonWitness contentlessProfile godelCompiledAscentProfile)
      ∧ (∀ L₁ L₂ : OperatorKO7.LCELSchema.FormalLCELInstance,
          Subsingleton (OperatorKO7.LCELStructuralIdentity.LCELQuasiFunctor L₁ L₂)) :=
  ⟨compatibleWithDp_iff_realizes,
   comparisonWitness_subsingleton,
   ⟨comparisonOfRealized godelCompiledAscentProfile_realizes
      (by simpa [dpAsClassicalAscentProfile] using structural_identity) rfl⟩,
   ⟨comparisonOfRealized ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
      godelCompiledAscentProfile_realizes rfl⟩,
   OperatorKO7.LCELComparisonDegeneracy.lcelQuasiFunctor_subsingleton⟩

/-- **The shape transports; the witnesses do not.** The Gödel checker ascent maps into the
quotation ascent at the witness layer, and the orientation and quotation ascents admit no morphism
in either direction, while all three carry the same six-step truth profile. The identification at
the shape layer therefore says nothing about carrier-level structure. -/
theorem shape_transports_witness_does_not :
    Nonempty (AscentHom godelCheckerAscent quotationAscent)
      ∧ IsEmpty (AscentHom orientationAscent quotationAscent)
      ∧ IsEmpty (AscentHom quotationAscent orientationAscent)
      ∧ RealizesSixStepShape (toAscentProfile godelCheckerAscent).shape
      ∧ RealizesSixStepShape (toAscentProfile orientationAscent).shape
      ∧ RealizesSixStepShape (toAscentProfile quotationAscent).shape :=
  ⟨godel_transports_to_quotation,
   no_ascentHom_orientation_quotation,
   no_ascentHom_quotation_orientation,
   godelCheckerAscent_realizes,
   toAscentProfile_realizes orientationAscent,
   toAscentProfile_realizes quotationAscent⟩

/-- The three ascents are pairwise comparison-equivalent at the shape layer, which is what makes
the separation of `shape_transports_witness_does_not` informative. -/
theorem three_ascents_compare_at_shape_layer :
    Nonempty (ComparisonWitness (toAscentProfile godelCheckerAscent)
        (toAscentProfile orientationAscent))
      ∧ Nonempty (ComparisonWitness (toAscentProfile orientationAscent)
        (toAscentProfile quotationAscent))
      ∧ Nonempty (ComparisonWitness (toAscentProfile quotationAscent)
        (toAscentProfile godelCheckerAscent)) :=
  ⟨⟨comparisonOfRealized godelCheckerAscent_realizes
      (toAscentProfile_realizes orientationAscent) rfl⟩,
   ⟨comparisonOfRealized (toAscentProfile_realizes orientationAscent)
      (toAscentProfile_realizes quotationAscent) rfl⟩,
   ⟨comparisonOfRealized (toAscentProfile_realizes quotationAscent)
      godelCheckerAscent_realizes rfl⟩⟩

end OperatorKO7.Meta.ProofTheoreticRegister.GodelDPAscentComparison
