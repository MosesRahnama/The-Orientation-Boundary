import OperatorKO7.Meta.UniversalFirstOrderInterpretationMethod
import OperatorKO7.Meta.ConstructionMethodClassification
import OperatorKO7.Meta.TransformedCallClassification

/-!
# Constructor maps for the universal first-order method carrier

Seven functions inject a natural-number tag into a correspondingly named constructor of
`UniversalFirstOrderInterpretationMethod`. Two functions map finite W1 and W2 class tags to natural
numbers before constructing a carrier value. A final function constructs the externally certified
tag. The verdict lemmas unfold these constructors and prove their assigned verdicts by reflexivity.

The source-family semantics are not represented in the domains of the seven `Nat`-based functions,
so this module proves neither behavior preservation nor a semantic embedding from those source
families. The coverage theorem case-splits on the carrier itself. In its W1 and W2 cases it uses
direct constructor witnesses, not the finite-class maps, because the carrier accepts arbitrary
natural-number tags.
-/

namespace OperatorKO7.UniversalFirstOrderEmbeddings

open OperatorKO7.UniversalFirstOrderInterpretationMethod

/-! ## Constructor maps -/

/-- Construct a direct-schema-barrier carrier value from an unrestricted natural-number tag. -/
def embedDirectSchemaBarrier (idx : Nat) :
    UniversalFirstOrderInterpretationMethod :=
  .directSchemaBarrier idx

/-- Construct a transparent-nonlinear carrier value from a natural-number tag. -/
def embedTransparentNonlinear (idx : Nat) :
    UniversalFirstOrderInterpretationMethod :=
  .transparentNonlinearMember idx

/-- Construct an unconstrained-nonlinear carrier value from a natural-number tag. -/
def embedUnconstrainedNonlinear (idx : Nat) :
    UniversalFirstOrderInterpretationMethod :=
  .unconstrainedNonlinearMember idx

/-- Construct an FBI-generic carrier value from a natural-number tag. -/
def embedFBIGeneric (idx : Nat) :
    UniversalFirstOrderInterpretationMethod :=
  .fbiGenericMember idx

/-- Construct a matrix-unrestricted carrier value from a natural-number tag. -/
def embedMatrixUnrestricted (idx : Nat) :
    UniversalFirstOrderInterpretationMethod :=
  .matrixUnrestrictedMember idx

/-- Construct a generic-DP carrier value from a natural-number tag. -/
def embedGenericDP (idx : Nat) :
    UniversalFirstOrderInterpretationMethod :=
  .genericDPMember idx

/-- Construct a semantic-method carrier value from a natural-number tag. -/
def embedSemantic (idx : Nat) :
    UniversalFirstOrderInterpretationMethod :=
  .semanticMember idx

/-- Encode the four `W1ImportClass` constructors by natural numbers from zero through three. -/
def w1ImportClassIndex :
    OperatorKO7.ConstructionMethodClassification.W1ImportClass → Nat
  | .precedence                => 0
  | .globalPolynomial          => 1
  | .importedWholeWitness      => 2
  | .transparencyEssentiality  => 3

/-- Map a `W1ImportClass` tag to its encoded `w1LicensedEscape` carrier value. -/
def embedW1Licensed
    (cls : OperatorKO7.ConstructionMethodClassification.W1ImportClass) :
    UniversalFirstOrderInterpretationMethod :=
  .w1LicensedEscape (w1ImportClassIndex cls)

/-- Encode the two `W2TransformClass` constructors by zero and one. -/
def w2TransformClassIndex :
    OperatorKO7.TransformedCallClassification.W2TransformClass → Nat
  | .ko7DPProjection                 => 0
  | .benchmarkFamilyTransformedCall  => 1

/-- Map a `W2TransformClass` tag to its encoded `w2LicensedEscape` carrier value. -/
def embedW2Licensed
    (cls : OperatorKO7.TransformedCallClassification.W2TransformClass) :
    UniversalFirstOrderInterpretationMethod :=
  .w2LicensedEscape (w2TransformClassIndex cls)

/-- Construct an externally certified carrier value from an unrestricted natural-number tag. No
certificate evidence is an argument of this function. -/
def embedKO7CertifiedExternal (idx : Nat) :
    UniversalFirstOrderInterpretationMethod :=
  .ko7CertifiedExternal idx

/-! ## Verdicts assigned by the carrier constructors -/

theorem embedDirectSchemaBarrier_isW0Blocked (idx : Nat) :
    isW0Blocked (embedDirectSchemaBarrier idx) := by
  unfold isW0Blocked embedDirectSchemaBarrier
  rfl

theorem embedTransparentNonlinear_isW0Blocked (idx : Nat) :
    isW0Blocked (embedTransparentNonlinear idx) := by
  unfold isW0Blocked embedTransparentNonlinear
  rfl

theorem embedUnconstrainedNonlinear_isW0Blocked (idx : Nat) :
    isW0Blocked (embedUnconstrainedNonlinear idx) := by
  unfold isW0Blocked embedUnconstrainedNonlinear
  rfl

theorem embedFBIGeneric_isW0Blocked (idx : Nat) :
    isW0Blocked (embedFBIGeneric idx) := by
  unfold isW0Blocked embedFBIGeneric
  rfl

theorem embedMatrixUnrestricted_isW0Blocked (idx : Nat) :
    isW0Blocked (embedMatrixUnrestricted idx) := by
  unfold isW0Blocked embedMatrixUnrestricted
  rfl

theorem embedGenericDP_isW0Blocked (idx : Nat) :
    isW0Blocked (embedGenericDP idx) := by
  unfold isW0Blocked embedGenericDP
  rfl

theorem embedSemantic_isW0Blocked (idx : Nat) :
    isW0Blocked (embedSemantic idx) := by
  unfold isW0Blocked embedSemantic
  rfl

theorem embedW1Licensed_verdict_w1
    (cls : OperatorKO7.ConstructionMethodClassification.W1ImportClass) :
    universalMethodVerdict (embedW1Licensed cls)
      = UniversalMethodVerdict.w1_licensed := by
  unfold embedW1Licensed
  rfl

theorem embedW2Licensed_verdict_w2
    (cls : OperatorKO7.TransformedCallClassification.W2TransformClass) :
    universalMethodVerdict (embedW2Licensed cls)
      = UniversalMethodVerdict.w2_licensed := by
  unfold embedW2Licensed
  rfl

theorem embedKO7CertifiedExternal_verdict_externally_certified (idx : Nat) :
    universalMethodVerdict (embedKO7CertifiedExternal idx)
      = UniversalMethodVerdict.externally_certified := by
  unfold embedKO7CertifiedExternal
  rfl

/-! ## Carrier-constructor coverage -/

/-- Every carrier value has a witness for its constructor family. The W1 and W2 disjuncts use the
carrier constructors directly and therefore cover natural-number tags outside the images of
`embedW1Licensed` and `embedW2Licensed`. -/
theorem universal_first_order_method_embedding_coverage
    (m : UniversalFirstOrderInterpretationMethod) :
    (∃ idx, m = embedDirectSchemaBarrier idx) ∨
    (∃ idx, m = embedTransparentNonlinear idx) ∨
    (∃ idx, m = embedUnconstrainedNonlinear idx) ∨
    (∃ idx, m = embedFBIGeneric idx) ∨
    (∃ idx, m = embedMatrixUnrestricted idx) ∨
    (∃ idx, m = embedGenericDP idx) ∨
    (∃ idx, m = embedSemantic idx) ∨
    (∃ idx, m = .w1LicensedEscape idx) ∨
    (∃ idx, m = .w2LicensedEscape idx) ∨
    (∃ idx, m = embedKO7CertifiedExternal idx) := by
  cases m
  · exact Or.inl ⟨_, rfl⟩
  · exact Or.inr (Or.inl ⟨_, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨_, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl⟩))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl⟩)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl⟩))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨_, rfl⟩))))))))

end OperatorKO7.UniversalFirstOrderEmbeddings
