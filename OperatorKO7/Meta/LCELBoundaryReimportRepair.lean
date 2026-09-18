/-!
# The LCEL boundary/reimport collision, and the repair that both canonical instances need

The layer-crossing-under-external-license schema carries three clauses that interact:

* clause 2 (boundary): every boundary statement is underivable in the base system `T`;
* clause 4 (licensed extension): every boundary statement is derivable in `T⁺ = T + Σ`;
* clause 5 (reimport class): `T⁺` is `Γ'`-conservative over `T`.

`boundary_and_reimport_overlap_is_impossible` shows the three clauses force
`Π ∩ Γ' = ∅`. Both canonical instances of the manuscript violate that:

* the Gödel instance takes `Γ' = Π₁` while its boundary sentence `Con(T)` is itself `Π₁`,
  so clause 5 would return `T ⊢ Con(T)`;
* the dependency-pair instance takes `Γ' = {termination of R}` while the same
  termination statement is the boundary the base language fails to derive.

`godelShaped` below is a two-sentence model of that configuration, and
`godelShaped_violates_conservativity_clause` proves no `LCELClauses` structure carries it.

The repair is `LCELAnnotatedClauses`: replace conservativity by the annotation map the
schema already carries as clause 6. A `Γ'`-conclusion returns to the base layer *carrying
its license annotation*, rather than becoming base-derivable outright. That is what both
instances actually do (accepting `G_PA` as externally true; declaring the wrapper inert
under Arts and Giesl), it permits `Π ∩ Γ'` to be inhabited, and
`godelShaped_satisfies_annotated_clauses` exhibits the Gödel configuration inside it.

Relation: an abstract derivability predicate; no arithmetic is formalized here.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only. No `sorry`, no `admit`, no new `axiom`, no native reduction.
-/

set_option autoImplicit false

universe u

namespace OperatorKO7.Meta.LCELBoundaryReimportRepair

/-! ### The clause set as the manuscript states it -/

/--
Intent: clauses 2, 4 and 5 of the layer-crossing schema over an abstract sentence type.

`provesBase` is `T ⊢ ·`, `provesExt` is `T⁺ ⊢ ·`, `boundary` is `Π`, `reimport` is `Γ'`.
The three fields are the manuscript's three clauses verbatim.
-/
structure LCELClauses (Sentence : Type u) where
  /-- `T ⊢ ·`. -/
  provesBase : Sentence → Prop
  /-- `T⁺ ⊢ ·`, for `T⁺ = T + Σ`. -/
  provesExt : Sentence → Prop
  /-- The boundary `Π`. -/
  boundary : Sentence → Prop
  /-- The reimport class `Γ'`. -/
  reimport : Sentence → Prop
  /-- Clause 2: boundary statements are underivable in the base system. -/
  boundary_underivable_in_base : ∀ φ, boundary φ → ¬ provesBase φ
  /-- Clause 4: the licensed extension derives every boundary statement. -/
  boundary_derivable_in_extension : ∀ φ, boundary φ → provesExt φ
  /-- Clause 5: the licensed extension is `Γ'`-conservative over the base system. -/
  reimport_conservative : ∀ ψ, reimport ψ → provesExt ψ → provesBase ψ

/--
Intent: **the collision theorem**. Clauses 2, 4 and 5 jointly forbid any sentence from
lying in both the boundary and the reimport class.

Proves: no sentence is simultaneously a boundary statement and a reimport-class statement.
Does not prove: that the clause set is unsatisfiable outright. It is satisfiable exactly
when the boundary and the reimport class are disjoint.
Trust: kernel-only.
-/
theorem boundary_and_reimport_overlap_is_impossible
    {Sentence : Type u} (L : LCELClauses Sentence) (φ : Sentence)
    (hboundary : L.boundary φ) (hreimport : L.reimport φ) : False :=
  L.boundary_underivable_in_base φ hboundary
    (L.reimport_conservative φ hreimport (L.boundary_derivable_in_extension φ hboundary))

/--
Proves: the schema as stated entails that the boundary and the reimport class are
disjoint, so disjointness is a derived obligation on every instance rather than an
optional side condition.
-/
theorem boundary_reimport_disjoint_of_clauses
    {Sentence : Type u} (L : LCELClauses Sentence) (φ : Sentence) :
    L.boundary φ → ¬ L.reimport φ :=
  fun hb hr => boundary_and_reimport_overlap_is_impossible L φ hb hr

/-! ### The configuration both canonical instances actually supply -/

/-- Two sentences: one the base system proves, one it fails to prove. The second models
`Con(T)` on the Gödel side and the duplicator's termination statement on the
dependency-pair side. -/
inductive GodelShapedSentence : Type
  | basic
  | boundarySentence
deriving DecidableEq, Repr

open GodelShapedSentence

/-- Base derivability in the two-sentence model. -/
def godelShapedProvesBase : GodelShapedSentence → Prop
  | basic => True
  | boundarySentence => False

/-- Licensed-extension derivability in the two-sentence model. -/
def godelShapedProvesExt : GodelShapedSentence → Prop
  | _ => True

/-- The boundary in the two-sentence model. -/
def godelShapedBoundary : GodelShapedSentence → Prop
  | basic => False
  | boundarySentence => True

/-- The reimport class in the two-sentence model. This is the `Γ' = Π₁` choice: the class
is a complexity class, so it contains the boundary sentence too. -/
def godelShapedReimport : GodelShapedSentence → Prop
  | _ => True

/--
Proves: in the configuration the manuscript supplies, the conservativity clause fails
outright, exhibited on the boundary sentence.
-/
theorem godelShaped_conservativity_fails_on_boundarySentence :
    godelShapedReimport boundarySentence
      ∧ godelShapedProvesExt boundarySentence
      ∧ ¬ godelShapedProvesBase boundarySentence :=
  ⟨trivial, trivial, fun h => h⟩

/--
Intent: **no `LCELClauses` structure carries the manuscript's Gödel-side data**. Supplying
`Γ'` as a complexity class that contains the boundary sentence is inconsistent with
clauses 2, 4 and 5 taken together.

Trust: kernel-only.
-/
theorem godelShaped_violates_conservativity_clause
    (L : LCELClauses GodelShapedSentence)
    (hbase : L.boundary = godelShapedBoundary)
    (hreimport : L.reimport = godelShapedReimport) : False := by
  refine boundary_and_reimport_overlap_is_impossible L boundarySentence ?_ ?_
  · rw [hbase]; exact trivial
  · rw [hreimport]; exact trivial

/-! ### The repair: annotated reimport in place of conservativity -/

/--
Intent: the repaired clause set. Clause 5 is replaced by the annotation map the schema
already carries as clause 6: a reimport-class conclusion of `T⁺` returns to the base layer
as an *annotated* base conclusion, recording the site at which `Σ` was invoked.

`annotatedProvesBase` is the derivability predicate of the base layer extended by
license annotations. Base derivations remain annotated derivations
(`base_derivations_are_annotated`), and reimport-class conclusions of the extension
become annotated base conclusions (`reimport_returns_annotated`).
-/
structure LCELAnnotatedClauses (Sentence : Type u) where
  /-- `T ⊢ ·`. -/
  provesBase : Sentence → Prop
  /-- `T⁺ ⊢ ·`. -/
  provesExt : Sentence → Prop
  /-- Base derivability extended by license annotations. -/
  annotatedProvesBase : Sentence → Prop
  /-- The boundary `Π`. -/
  boundary : Sentence → Prop
  /-- The reimport class `Γ'`. -/
  reimport : Sentence → Prop
  /-- Clause 2, unchanged. -/
  boundary_underivable_in_base : ∀ φ, boundary φ → ¬ provesBase φ
  /-- Clause 4, unchanged. -/
  boundary_derivable_in_extension : ∀ φ, boundary φ → provesExt φ
  /-- Every base derivation is an annotated derivation. -/
  base_derivations_are_annotated : ∀ ψ, provesBase ψ → annotatedProvesBase ψ
  /-- Clause 5, repaired: reimport-class conclusions return annotated. -/
  reimport_returns_annotated : ∀ ψ, reimport ψ → provesExt ψ → annotatedProvesBase ψ

/--
Proves: the repaired clause set permits the boundary and the reimport class to overlap,
exhibited on the configuration both canonical instances supply.
Non-vacuity witness for the repaired schema (Gate R5).
-/
def godelShapedAnnotated : LCELAnnotatedClauses GodelShapedSentence where
  provesBase := godelShapedProvesBase
  provesExt := godelShapedProvesExt
  annotatedProvesBase := fun _ => True
  boundary := godelShapedBoundary
  reimport := godelShapedReimport
  boundary_underivable_in_base := by
    intro φ hφ
    cases φ with
    | basic => exact absurd hφ (fun h => h)
    | boundarySentence => exact fun h => h
  boundary_derivable_in_extension := by
    intro φ _
    cases φ <;> exact trivial
  base_derivations_are_annotated := by
    intro _ _
    exact trivial
  reimport_returns_annotated := by
    intro _ _ _
    exact trivial

/--
Proves: the repaired schema carries the very configuration that refutes the original,
namely a sentence lying in both the boundary and the reimport class.
-/
theorem godelShaped_satisfies_annotated_clauses :
    godelShapedAnnotated.boundary boundarySentence
      ∧ godelShapedAnnotated.reimport boundarySentence :=
  ⟨trivial, trivial⟩

/--
Proves: the repair keeps the license substantive. The annotated base layer proves a
sentence the plain base layer does not, so replacing conservativity by annotation leaves
the ascent nontrivial rather than collapsing it.
-/
theorem godelShapedAnnotated_license_is_strict :
    ∃ φ : GodelShapedSentence,
      godelShapedAnnotated.annotatedProvesBase φ
        ∧ ¬ godelShapedAnnotated.provesBase φ :=
  ⟨boundarySentence, trivial, fun h => h⟩

/--
Proves: the repaired schema is strictly more permissive than the original, in the precise
sense that every `LCELClauses` structure induces an `LCELAnnotatedClauses` structure by
taking the annotated layer to be the base layer itself.

Trust: kernel-only.
-/
def LCELClauses.toAnnotated {Sentence : Type u} (L : LCELClauses Sentence) :
    LCELAnnotatedClauses Sentence where
  provesBase := L.provesBase
  provesExt := L.provesExt
  annotatedProvesBase := L.provesBase
  boundary := L.boundary
  reimport := L.reimport
  boundary_underivable_in_base := L.boundary_underivable_in_base
  boundary_derivable_in_extension := L.boundary_derivable_in_extension
  base_derivations_are_annotated := fun _ h => h
  reimport_returns_annotated := L.reimport_conservative

/--
Proves: the converse fails. There is an `LCELAnnotatedClauses` structure that no
`LCELClauses` structure with the same boundary and reimport data can carry, so the repair
is a genuine weakening rather than a restatement.
-/
theorem annotated_clauses_strictly_weaker_than_conservativity :
    ∃ A : LCELAnnotatedClauses GodelShapedSentence,
      (∃ φ, A.boundary φ ∧ A.reimport φ)
        ∧ ∀ L : LCELClauses GodelShapedSentence,
            L.boundary = A.boundary → L.reimport = A.reimport → False := by
  refine ⟨godelShapedAnnotated, ⟨boundarySentence, trivial, trivial⟩, ?_⟩
  intro L hb hr
  exact godelShaped_violates_conservativity_clause L hb hr

end OperatorKO7.Meta.LCELBoundaryReimportRepair
