import OperatorKO7.Meta.LCELAnnotatedReimport
import OperatorKO7.Meta.LCELTypedDPInstance

set_option autoImplicit false

/-!
# Canonical inhabited LCEL annotated-reimport instances

This module places both manuscript fixtures outside the defining clause module.
Each record has an inhabited boundary/reimport overlap and routes extension
proofs into the proof-carrying annotated layer.  The final refuter states that
the same overlap cannot inhabit the old plain-base conservativity clauses.

Relation: typed derivability objects and their annotated reimport.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-checked Lean terms; no external tool boundary.
-/

namespace OperatorKO7.Meta.LCELCanonicalInstances

open OperatorKO7.Meta.LCELBoundaryReimportRepair
open OperatorKO7.Meta.LCELTypedDerivations
open OperatorKO7.Meta.LCELAnnotatedReimport
open OperatorKO7.Meta.LCELDPInstance

/-! ## Proof-carrying Gödel-shaped fixture -/

/-- Three sentences make the fixture nonconstant: a base theorem, a licensed
boundary theorem, and a negative control whose non-derivability is proved
below. -/
inductive GodelCanonicalSentence where
  | basic
  | boundary
  | unlicensed
deriving DecidableEq, Repr

/-- The base theory proves exactly `basic`. -/
def godelCanonicalBaseDerivation : GodelCanonicalSentence -> Type
  | .basic => PUnit
  | .boundary => PEmpty
  | .unlicensed => PEmpty

/-- The licensed extension adds exactly the boundary theorem. -/
def godelCanonicalExtensionDerivation : GodelCanonicalSentence -> Type
  | .basic => PUnit
  | .boundary => PUnit
  | .unlicensed => PEmpty

def godelCanonicalBaseTheory : TypedTheory where
  Sentence := GodelCanonicalSentence
  Derivation := godelCanonicalBaseDerivation

def godelCanonicalExtensionTheory : TypedTheory where
  Sentence := GodelCanonicalSentence
  Derivation := godelCanonicalExtensionDerivation

/-- Exact base-layer derivability: the base theory proves precisely `basic`. -/
theorem godelCanonical_base_derivable_iff
    (phi : GodelCanonicalSentence) :
    Nonempty (godelCanonicalBaseTheory.Derivation phi) ↔
      phi = GodelCanonicalSentence.basic := by
  cases phi with
  | basic =>
      constructor
      · intro _
        rfl
      · intro _
        exact ⟨PUnit.unit⟩
  | boundary =>
      constructor
      · rintro ⟨d⟩
        exact PEmpty.elim d
      · intro h
        cases h
  | unlicensed =>
      constructor
      · rintro ⟨d⟩
        exact PEmpty.elim d
      · intro h
        cases h

/-- Exact licensed-layer derivability: the extension proves precisely `basic`
and `boundary`, and it still does not prove the negative control. -/
theorem godelCanonical_extension_derivable_iff
    (phi : GodelCanonicalSentence) :
    Nonempty (godelCanonicalExtensionTheory.Derivation phi) ↔
      phi = GodelCanonicalSentence.basic ∨
        phi = GodelCanonicalSentence.boundary := by
  cases phi with
  | basic =>
      constructor
      · intro _
        exact Or.inl rfl
      · intro _
        exact ⟨PUnit.unit⟩
  | boundary =>
      constructor
      · intro _
        exact Or.inr rfl
      · intro _
        exact ⟨PUnit.unit⟩
  | unlicensed =>
      constructor
      · rintro ⟨d⟩
        exact PEmpty.elim d
      · intro h
        rcases h with h | h <;> cases h

/-- Inclusion of the genuine base proof object into the licensed theory. -/
def godelCanonicalTheoryExtension :
    TheoryExtension godelCanonicalBaseTheory
      godelCanonicalExtensionTheory where
  onSentence := fun phi => phi
  sentence_injective := by
    intro left right h
    exact h
  onDerivation := fun {phi} d =>
    match phi with
    | .basic => PUnit.unit
    | .boundary => nomatch d
    | .unlicensed => nomatch d
  derivation_injective := by
    intro phi left right _
    cases phi with
    | basic =>
        cases left
        cases right
        rfl
    | boundary => exact PEmpty.elim left
    | unlicensed => exact PEmpty.elim left

/-- The external annotation carried by the boundary proof. -/
inductive GodelReflectionLicense where
  | reflection
deriving DecidableEq, Repr

def godelCanonicalBoundary : GodelCanonicalSentence -> Prop
  | .boundary => True
  | _ => False

def godelCanonicalReimport : GodelCanonicalSentence -> Prop
  | .basic => True
  | .boundary => True
  | .unlicensed => False

/-- Gödel-shaped canonical clauses whose annotated predicate is an actual
`AnnotatedDerivation` type, not a constant proposition. -/
def godelCanonicalAnnotatedClauses :
    LCELAnnotatedClauses GodelCanonicalSentence where
  provesBase := fun phi =>
    Nonempty (godelCanonicalBaseTheory.Derivation phi)
  provesExt := fun phi =>
    Nonempty (godelCanonicalExtensionTheory.Derivation phi)
  annotatedProvesBase := fun phi =>
    Nonempty
      (AnnotatedDerivation godelCanonicalBaseTheory
        godelCanonicalExtensionTheory godelCanonicalTheoryExtension
        GodelReflectionLicense phi)
  boundary := godelCanonicalBoundary
  reimport := godelCanonicalReimport
  boundary_underivable_in_base := by
    intro phi hboundary
    cases phi <;>
      simp [godelCanonicalBoundary, godelCanonicalBaseTheory,
        godelCanonicalBaseDerivation] at hboundary ⊢
  boundary_derivable_in_extension := by
    intro phi hboundary
    cases phi with
    | basic => exact False.elim hboundary
    | boundary => exact ⟨PUnit.unit⟩
    | unlicensed => exact False.elim hboundary
  base_derivations_are_annotated := by
    intro phi hbase
    rcases hbase with ⟨d⟩
    exact ⟨annotateBase d⟩
  reimport_returns_annotated := by
    intro phi _ hext
    exact extension_derivation_reimports_annotated
      GodelReflectionLicense.reflection hext

/-- The canonical Gödel-shaped instance has a genuine boundary/reimport
overlap. -/
theorem godelCanonical_boundary_reimport_overlap :
    godelCanonicalAnnotatedClauses.boundary
        GodelCanonicalSentence.boundary ∧
      godelCanonicalAnnotatedClauses.reimport
        GodelCanonicalSentence.boundary :=
  ⟨trivial, trivial⟩

/-- The boundary extension proof is a concrete proof object. -/
def godelCanonicalBoundaryExtensionProof :
    godelCanonicalExtensionTheory.Derivation
      GodelCanonicalSentence.boundary :=
  PUnit.unit

/-- The concrete boundary proof reimports with its reflection annotation. -/
def godelCanonicalBoundaryAnnotatedProof :
    AnnotatedDerivation godelCanonicalBaseTheory
      godelCanonicalExtensionTheory godelCanonicalTheoryExtension
      GodelReflectionLicense GodelCanonicalSentence.boundary :=
  reimportAnnotated GodelReflectionLicense.reflection
    godelCanonicalBoundaryExtensionProof

/-- Exact annotated-layer derivability: annotations preserve the two extension
theorems and manufacture no proof of the negative control. -/
theorem godelCanonical_annotated_derivable_iff
    (phi : GodelCanonicalSentence) :
    godelCanonicalAnnotatedClauses.annotatedProvesBase phi ↔
      phi = GodelCanonicalSentence.basic ∨
        phi = GodelCanonicalSentence.boundary := by
  constructor
  · rintro ⟨d⟩
    cases d with
    | base baseProof =>
        exact Or.inl
          ((godelCanonical_base_derivable_iff phi).mp ⟨baseProof⟩)
    | licensed _ extensionProof =>
        exact (godelCanonical_extension_derivable_iff phi).mp
          ⟨extensionProof⟩
  · intro h
    rcases h with hbasic | hboundary
    · subst phi
      exact ⟨annotateBase PUnit.unit⟩
    · subst phi
      exact ⟨godelCanonicalBoundaryAnnotatedProof⟩

/-- The negative control has no derivation in the base theory. -/
theorem godelCanonical_unlicensed_not_base :
    ¬ Nonempty
      (godelCanonicalBaseTheory.Derivation
        GodelCanonicalSentence.unlicensed) := by
  rintro ⟨d⟩
  exact PEmpty.elim d

/-- The negative control remains underivable in the licensed extension. -/
theorem godelCanonical_unlicensed_not_extension :
    ¬ Nonempty
      (godelCanonicalExtensionTheory.Derivation
        GodelCanonicalSentence.unlicensed) := by
  rintro ⟨d⟩
  exact PEmpty.elim d

/-- The negative control is also underivable in the proof-carrying annotated
union of the two layers. -/
theorem godelCanonical_unlicensed_not_annotated :
    ¬ godelCanonicalAnnotatedClauses.annotatedProvesBase
      GodelCanonicalSentence.unlicensed := by
  intro h
  rcases (godelCanonical_annotated_derivable_iff
      GodelCanonicalSentence.unlicensed).mp h with h | h <;> cases h

/-- Paper-facing metatheorem: the third sentence is not an unfinished proof.
Its non-derivability is proved separately in the base theory, licensed
extension, and annotated union. -/
theorem godelCanonical_unlicensed_nonderivability :
    (¬ Nonempty
      (godelCanonicalBaseTheory.Derivation
        GodelCanonicalSentence.unlicensed)) ∧
    (¬ Nonempty
      (godelCanonicalExtensionTheory.Derivation
        GodelCanonicalSentence.unlicensed)) ∧
    (¬ godelCanonicalAnnotatedClauses.annotatedProvesBase
      GodelCanonicalSentence.unlicensed) :=
  ⟨godelCanonical_unlicensed_not_base,
    godelCanonical_unlicensed_not_extension,
    godelCanonical_unlicensed_not_annotated⟩

/-- Boundary reimport preserves its payload and cannot erase to a base proof. -/
theorem godelCanonical_boundary_reimport_receipt :
    licensedPayload? godelCanonicalBoundaryAnnotatedProof =
        some (GodelReflectionLicense.reflection,
          godelCanonicalBoundaryExtensionProof) ∧
      eraseToBase? godelCanonicalBoundaryAnnotatedProof = none :=
  ⟨rfl, rfl⟩

/-- Exact boundary predicate for the concrete typed dependency-pair fixture. -/
def dpCanonicalBoundary (phi : DPSentence) : Prop :=
  phi = DPSentence.sourceTermination

/-- The source-termination conclusion is the concrete reimport class. -/
def dpCanonicalReimport (phi : DPSentence) : Prop :=
  phi = DPSentence.sourceTermination

/-- Full proof-carrying annotated-clause record for the concrete typed DP
fixture.  It does not assert a generic dependency-pair soundness theorem: its
license is the explicitly documented certificate-consuming fixed-KO7
construction. -/
def dpCanonicalAnnotatedClauses : LCELAnnotatedClauses DPSentence where
  provesBase := fun phi => Nonempty (dpBaseTheory.Derivation phi)
  provesExt := fun phi => Nonempty (dpExtensionTheory.Derivation phi)
  annotatedProvesBase := fun phi =>
    Nonempty
      (AnnotatedDerivation dpBaseTheory dpExtensionTheory dpTheoryExtension
        KO7FixedSystemLicense phi)
  boundary := dpCanonicalBoundary
  reimport := dpCanonicalReimport
  boundary_underivable_in_base := by
    intro phi hphi
    subst phi
    exact sourceTermination_is_boundary
  boundary_derivable_in_extension := by
    intro phi hphi
    subst phi
    exact ⟨ko7LicensedSourceTermination⟩
  base_derivations_are_annotated := by
    intro phi hbase
    rcases hbase with ⟨d⟩
    exact ⟨AnnotatedDerivation.base d⟩
  reimport_returns_annotated := by
    intro phi hreimport hext
    subst phi
    rcases hext with ⟨d⟩
    exact ⟨reimportAnnotated ko7DPCertificateConsumingLicense d⟩

/-- The concrete DP annotated instance has the intended nonempty
boundary/reimport overlap. -/
theorem dpCanonical_boundary_reimport_overlap :
    dpCanonicalAnnotatedClauses.boundary DPSentence.sourceTermination ∧
      dpCanonicalAnnotatedClauses.reimport DPSentence.sourceTermination :=
  ⟨rfl, rfl⟩

/-- Both canonical annotated-clause types are inhabited outside their defining
modules. -/
theorem canonicalAnnotatedClauseInstances_inhabited :
    Nonempty (LCELAnnotatedClauses GodelCanonicalSentence) ∧
      Nonempty (LCELAnnotatedClauses DPSentence) :=
  ⟨⟨godelCanonicalAnnotatedClauses⟩, ⟨dpCanonicalAnnotatedClauses⟩⟩

/-- The old plain-base conservativity clauses cannot carry the same concrete
DP boundary/reimport overlap. -/
theorem dpCanonical_plainBase_reimport_impossible
    (L : LCELClauses DPSentence)
    (hboundary : L.boundary = dpCanonicalBoundary)
    (hreimport : L.reimport = dpCanonicalReimport) : False :=
  boundary_and_reimport_overlap_is_impossible L
    DPSentence.sourceTermination
    (by rw [hboundary]; rfl)
    (by rw [hreimport]; rfl)

section AuditChecks

#check @godelCanonicalAnnotatedClauses
#check @godelCanonical_base_derivable_iff
#check @godelCanonical_extension_derivable_iff
#check @godelCanonical_boundary_reimport_overlap
#check @godelCanonicalBoundaryAnnotatedProof
#check @godelCanonical_annotated_derivable_iff
#check @godelCanonical_unlicensed_not_base
#check @godelCanonical_unlicensed_not_extension
#check @godelCanonical_unlicensed_not_annotated
#check @godelCanonical_unlicensed_nonderivability
#check @godelCanonical_boundary_reimport_receipt
#check @dpCanonicalAnnotatedClauses
#check @dpCanonical_boundary_reimport_overlap
#check @canonicalAnnotatedClauseInstances_inhabited
#check @dpCanonical_plainBase_reimport_impossible

#print axioms godelCanonical_boundary_reimport_overlap
#print axioms godelCanonical_base_derivable_iff
#print axioms godelCanonical_extension_derivable_iff
#print axioms godelCanonical_annotated_derivable_iff
#print axioms godelCanonical_unlicensed_not_base
#print axioms godelCanonical_unlicensed_not_extension
#print axioms godelCanonical_unlicensed_not_annotated
#print axioms godelCanonical_unlicensed_nonderivability
#print axioms godelCanonical_boundary_reimport_receipt
#print axioms dpCanonical_boundary_reimport_overlap
#print axioms canonicalAnnotatedClauseInstances_inhabited
#print axioms dpCanonical_plainBase_reimport_impossible

end AuditChecks

end OperatorKO7.Meta.LCELCanonicalInstances
