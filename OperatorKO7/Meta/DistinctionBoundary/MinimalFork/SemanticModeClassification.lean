import OperatorKO7.Meta.DistinctionBoundary.MinimalForkQuantitative
import OperatorKO7.Meta.DistinctionBoundary.SemanticsPreservingMaximality

/-!
# Semantic equality-mode certificate

The legacy equality-mode table stores a proposition-valued enum label. This
module adds a proof-bearing canonical local surface: the unguarded totalized mode
carries the two-edge `Fork3Step`; every non-raw mode carries the one-edge
licensed local surface. Fork presence is then defined by an actual injective
relation-preserving embedding, not by the enum label itself.

Scope: canonical three-state local equality-mode surfaces only.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.DistinctionBoundary.MinimalFork

open OperatorKO7.Meta.DistinctionBoundary

/-- Canonical local reduction surface associated with each equality mode. -/
def CanonicalModeRel (m : EqualityMode) : Fork3 → Fork3 → Prop :=
  if m = EqualityMode.unguardedTotalizedRewrite then Fork3Step
  else Fork3LicensedStep

/-- Proof-bearing local relation surface for an equality mode. -/
structure ModeSurface (m : EqualityMode) where
  R : Fork3 → Fork3 → Prop
  exact_relation : R = CanonicalModeRel m

/-- Canonical local surface used by the semantic classifier. -/
def canonicalModeSurface (m : EqualityMode) : ModeSurface m where
  R := CanonicalModeRel m
  exact_relation := rfl

/-- A real fork embedding into a canonical equality-mode surface. -/
structure ForkEmbedding (m : EqualityMode) where
  toFun : Fork3 → Fork3
  injective : Function.Injective toFun
  map_rel : ∀ {x y}, Fork3Step x y → CanonicalModeRel m (toFun x) (toFun y)

/-- Semantic fork presence means a proof-bearing embedding exists. -/
def ContainsCanonicalFork (m : EqualityMode) : Prop := Nonempty (ForkEmbedding m)

/-- Roadmap-stable semantic predicate name. -/
def SemanticCanFork := ContainsCanonicalFork

/-- A mode certificate carries an actual local surface plus either a Fork3
embedding or a proof that no such embedding exists. -/
inductive ForkDisposition (m : EqualityMode) : Type
  | contains (e : ForkEmbedding m)
  | excludes (h : ¬ ContainsCanonicalFork m)

/-- Proof-bearing semantic mode certificate. -/
structure ModeCertificate (m : EqualityMode) where
  surface : ModeSurface m
  disposition : ForkDisposition m

/-- Identity embedding in the raw unguarded totalized mode. -/
def rawCanonicalForkEmbedding :
    ForkEmbedding EqualityMode.unguardedTotalizedRewrite where
  toFun := id
  injective := Function.injective_id
  map_rel := by
    intro x y h
    simpa [CanonicalModeRel] using h

/-- Raw mode semantically contains the canonical fork. -/
theorem raw_mode_contains_canonicalFork :
    ContainsCanonicalFork EqualityMode.unguardedTotalizedRewrite :=
  ⟨rawCanonicalForkEmbedding⟩

/-- Every edge of the licensed surface has the unique equal verdict target. -/
theorem fork3LicensedStep_target_equal {x y : Fork3}
    (h : Fork3LicensedStep x y) : y = .equal := by
  cases h
  rfl

/-- No injective copy of the two-edge fork fits into the one-edge licensed surface. -/
theorem noForkEmbedding_into_licensed :
    ¬ Nonempty
      {f : Fork3 → Fork3 //
        Function.Injective f ∧
        ∀ {x y}, Fork3Step x y → Fork3LicensedStep (f x) (f y)} := by
  rintro ⟨⟨f, hinj, hmap⟩⟩
  have heq : f .equal = .equal :=
    fork3LicensedStep_target_equal (hmap Fork3Step.toEqual)
  have hdiff : f .different = .equal :=
    fork3LicensedStep_target_equal (hmap Fork3Step.toDifferent)
  have hcollapsed : f .equal = f .different := heq.trans hdiff.symm
  exact Fork3.noConfusion (hinj hcollapsed)

/-- Every non-raw equality mode semantically excludes the canonical two-edge fork. -/
theorem nonraw_mode_excludes_canonicalFork
    (m : EqualityMode) (hne : m ≠ EqualityMode.unguardedTotalizedRewrite) :
    ¬ ContainsCanonicalFork m := by
  rintro ⟨e⟩
  have hmap : ∀ {x y}, Fork3Step x y → Fork3LicensedStep (e.toFun x) (e.toFun y) := by
    intro x y h
    have := e.map_rel h
    simpa [CanonicalModeRel, hne] using this
  exact noForkEmbedding_into_licensed
    ⟨⟨e.toFun, e.injective, hmap⟩⟩

/-- Semantic classification theorem: a real canonical `Fork3` embedding exists
exactly in the unguarded totalized rewrite mode. -/
theorem containsCanonicalFork_iff_raw (m : EqualityMode) :
    ContainsCanonicalFork m ↔ m = EqualityMode.unguardedTotalizedRewrite := by
  constructor
  · intro h
    by_contra hne
    exact nonraw_mode_excludes_canonicalFork m hne h
  · intro h
    subst m
    exact raw_mode_contains_canonicalFork

/-- Semantic fork presence is definitionally proof-bearing Fork3 containment. -/
theorem semanticCanFork_iff_containsFork3 (m : EqualityMode) :
    SemanticCanFork m ↔ ContainsCanonicalFork m := Iff.rfl

/-- Roadmap-stable semantic classification theorem. -/
theorem semanticCanFork_iff_unguardedTotalizedRewrite (m : EqualityMode) :
    SemanticCanFork m ↔ m = EqualityMode.unguardedTotalizedRewrite :=
  containsCanonicalFork_iff_raw m

/-- The semantic classification agrees extensionally with the legacy enum label,
but is independently witnessed by embeddings/non-embeddings. -/
theorem semanticFork_iff_legacyLabel (m : EqualityMode) :
    ContainsCanonicalFork m ↔ EqualityMode.CanDiagonalFork m := by
  rw [containsCanonicalFork_iff_raw,
    equalityMode_canDiagonalFork_iff]

/-- No non-raw canonical surface can contain a two-exit nonjoinable fork. -/
theorem relational_mode_noFork : ¬ ContainsCanonicalFork EqualityMode.relational :=
  nonraw_mode_excludes_canonicalFork _ (by intro h; cases h)

theorem typed_mode_noFork : ¬ ContainsCanonicalFork EqualityMode.typed :=
  nonraw_mode_excludes_canonicalFork _ (by intro h; cases h)

theorem structural_mode_noFork : ¬ ContainsCanonicalFork EqualityMode.structural :=
  nonraw_mode_excludes_canonicalFork _ (by intro h; cases h)

theorem guarded_mode_noFork : ¬ ContainsCanonicalFork EqualityMode.guardedRewrite :=
  nonraw_mode_excludes_canonicalFork _ (by intro h; cases h)

theorem delete_mode_noFork : ¬ ContainsCanonicalFork EqualityMode.deleteRewrite :=
  nonraw_mode_excludes_canonicalFork _ (by intro h; cases h)

theorem quotient_mode_noFork : ¬ ContainsCanonicalFork EqualityMode.quotientRewrite :=
  nonraw_mode_excludes_canonicalFork _ (by intro h; cases h)

/-- Naming repair for the historical inert/relational mismatch. -/
theorem relational_certificate_naming_repair :
    ¬ ContainsCanonicalFork EqualityMode.relational :=
  relational_mode_noFork

/-- Raw mode has an explicit real fork embedding. -/
theorem raw_mode_containsFork3 :
    ContainsCanonicalFork EqualityMode.unguardedTotalizedRewrite :=
  raw_mode_contains_canonicalFork

/-- Proof-bearing certificates for every listed mode. -/
def rawModeCertificate : ModeCertificate EqualityMode.unguardedTotalizedRewrite where
  surface := canonicalModeSurface _
  disposition := ForkDisposition.contains rawCanonicalForkEmbedding

def relationalModeCertificate : ModeCertificate EqualityMode.relational where
  surface := canonicalModeSurface _
  disposition := ForkDisposition.excludes relational_mode_noFork

def typedModeCertificate : ModeCertificate EqualityMode.typed where
  surface := canonicalModeSurface _
  disposition := ForkDisposition.excludes typed_mode_noFork

def structuralModeCertificate : ModeCertificate EqualityMode.structural where
  surface := canonicalModeSurface _
  disposition := ForkDisposition.excludes structural_mode_noFork

def guardedModeCertificate : ModeCertificate EqualityMode.guardedRewrite where
  surface := canonicalModeSurface _
  disposition := ForkDisposition.excludes guarded_mode_noFork

def deleteModeCertificate : ModeCertificate EqualityMode.deleteRewrite where
  surface := canonicalModeSurface _
  disposition := ForkDisposition.excludes delete_mode_noFork

def quotientModeCertificate : ModeCertificate EqualityMode.quotientRewrite where
  surface := canonicalModeSurface _
  disposition := ForkDisposition.excludes quotient_mode_noFork

/-- Complete non-raw exclusion bundle. -/
theorem all_nonraw_modes_noFork :
    (¬ ContainsCanonicalFork EqualityMode.relational) ∧
    (¬ ContainsCanonicalFork EqualityMode.typed) ∧
    (¬ ContainsCanonicalFork EqualityMode.structural) ∧
    (¬ ContainsCanonicalFork EqualityMode.guardedRewrite) ∧
    (¬ ContainsCanonicalFork EqualityMode.deleteRewrite) ∧
    (¬ ContainsCanonicalFork EqualityMode.quotientRewrite) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact nonraw_mode_excludes_canonicalFork _ (by intro h; cases h)
  · exact nonraw_mode_excludes_canonicalFork _ (by intro h; cases h)
  · exact nonraw_mode_excludes_canonicalFork _ (by intro h; cases h)
  · exact nonraw_mode_excludes_canonicalFork _ (by intro h; cases h)
  · exact nonraw_mode_excludes_canonicalFork _ (by intro h; cases h)
  · exact nonraw_mode_excludes_canonicalFork _ (by intro h; cases h)

end OperatorKO7.Meta.DistinctionBoundary.MinimalFork
