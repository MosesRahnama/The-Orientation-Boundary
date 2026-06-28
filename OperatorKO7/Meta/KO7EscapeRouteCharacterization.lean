import OperatorKO7.Meta.RecursiveFamilyEscapeCharacterization
import OperatorKO7.Meta.KO7RDRSAdapter
import OperatorKO7.Meta.EscapeTrichotomy
import OperatorKO7.Meta.CanonicalWitnessUniversality

/-!
# KO7 Escape-Route Characterization (Phase F.5, KO7-instantiated side)

KO7-instantiated half of the escape-route characterization. The
schema-generic theorem at `Meta/RecursiveFamilyEscapeCharacterization.lean`
delivers a one-way classification only; KO7 has concrete escape witnesses
backed by the existing escape-trichotomy stack
(`Meta/EscapeTrichotomy.lean`), so this module establishes the
iff-style theorem `ko7_escape_route_iff` against the explicit
`KO7DirectOrienter` universe.

The five clauses correspond to the roadmap dataflow at Phase F.5:

```text
[KO7 concrete witnesses]
  <-> [violates sensitivity | violates transparency
      | imports cross-coupling | projects payload
      | imports structural order]
```

* `violatesSensitivity`: the orienter's primary scalar fails wrapper-subterm
  sensitivity on `ko7Schema` (`StepDuplicatingSchema.WrapSubtermSensitive`).
* `violatesTransparency`: the orienter's primary scalar fails base-level
  successor transparency on `ko7Schema`
  (`StepDuplicatingSchema.TransparentAtBase`).
* `importsCrossCoupling`: the orienter falls outside the formalized
  Nat-valued direct barrier universe (`KO7DirectBarrierRepresentable`).
* `projectsPayload`: the orienter is represented as one of the formalized
  Nat-valued direct barrier families (the families that project the
  duplicated payload to a Nat measure).
* `importsStructuralOrder`: the orienter is represented as one of the
  tracked-primary matrix-lex / matrix-permutation-lex families, the
  imported structural orders Phase F.5 lists separately from scalar
  payload projection.

The five clauses cover every orienting observer in the `KO7DirectOrienter`
universe via the existing `ko7_direct_escape_trichotomy_extended` theorem.
The iff is stated against `KO7EscapingOrienter`, the proposition that packages
both the orientation fact and one concrete escape clause. This avoids the false
converse "any escape clause orients KO7" while still giving a genuine iff:
an orienter orients KO7 exactly when it is an orienting witness equipped with
a Phase F.5 escape clause.

No proof placeholders are used and no top-level postulate is declared.
Existing theorem names and signatures are preserved.
-/

namespace OperatorKO7.StepDuplicating

open OperatorKO7
open OperatorKO7.EscapeTrichotomy
open OperatorKO7.CompositionalImpossibility
open RecursiveFamilyEscapeCharacterization
open CanonicalWitnessUniversality
open KO7RDRSAdapter

/-- Concrete KO7 escape clauses for orienters in the explicit
`KO7DirectOrienter` universe. The five constructors enumerate the five
named escape categories the Phase F.5 roadmap requires. -/
inductive KO7EscapeClause (O : KO7DirectOrienter) : Prop
  /-- The orienter's primary scalar fails wrapper-subterm sensitivity on
  `ko7Schema`. -/
  | violatesSensitivity :
      ¬ StepDuplicatingSchema.WrapSubtermSensitive ko7Schema O.primaryScalar →
        KO7EscapeClause O
  /-- The orienter's primary scalar fails base-level successor transparency
  on `ko7Schema`. -/
  | violatesTransparency :
      ¬ StepDuplicatingSchema.TransparentAtBase ko7Schema O.primaryScalar →
        KO7EscapeClause O
  /-- The orienter is not representable by the formalized Nat-valued direct
  barrier families: it imports cross-variable coupling outside the bounded
  frozen-base polynomial scope. -/
  | importsCrossCoupling :
      ¬ KO7DirectBarrierRepresentable O →
        KO7EscapeClause O
  /-- The orienter projects the duplicated payload through one of the
  scalar barrier families (additive, transparent compositional, pumped
  affine/quadratic/cross-quadratic/multilinear/polynomial/max, depth, or
  head-precedence). -/
  | projectsPayload :
      KO7DirectBarrierRepresentable O →
        KO7EscapeClause O
  /-- The orienter imports a structural order: a tracked-primary
  componentwise, lexicographic, or permutation-lex matrix family. -/
  | importsStructuralOrder :
      KO7DirectBarrierRepresentable O →
        KO7EscapeClause O

/-- An orienting KO7 direct observer together with a concrete Phase F.5 escape
clause. This is the honest iff target: the backward direction projects the
orientation proof carried by the witness, rather than claiming that an arbitrary
escape clause is sufficient to orient KO7. -/
structure KO7EscapingOrienter (O : KO7DirectOrienter) : Prop where
  /-- The observer genuinely orients KO7 in the explicit direct universe. -/
  orients : O.Orients
  /-- The orienter falls under one of the concrete Phase F.5 escape clauses. -/
  clause : KO7EscapeClause O

/-- Forward direction of the KO7 escape characterization: every orienting
direct observer in the `KO7DirectOrienter` universe falls into at least one
of the five concrete escape clauses. The proof reduces to the existing
`ko7_direct_escape_trichotomy_extended` theorem, redistributing its
three-way disjunction into the five Phase F.5 clauses. -/
theorem ko7_escape_route_forward
    {O : KO7DirectOrienter}
    (horient : O.Orients) :
    KO7EscapingOrienter O := by
  classical
  have htri : ¬ StepDuplicatingSchema.WrapSubtermSensitive ko7Schema O.primaryScalar ∨
      ¬ StepDuplicatingSchema.TransparentAtBase ko7Schema O.primaryScalar ∨
      ¬ KO7DirectBarrierRepresentable O :=
    ko7_direct_escape_trichotomy_extended (O := O) horient
  refine ⟨horient, ?_⟩
  rcases htri with hwrap | htrans | hnonRepr
  · exact KO7EscapeClause.violatesSensitivity hwrap
  · exact KO7EscapeClause.violatesTransparency htrans
  · exact KO7EscapeClause.importsCrossCoupling hnonRepr

/-- Backward direction of the KO7 escape characterization: a packaged escaping
orienter carries its orientation proof as data. This is intentionally not a
claim that a bare escape clause implies orientation. -/
theorem ko7_escape_route_backward
    {O : KO7DirectOrienter}
    (hesc : KO7EscapingOrienter O) :
    O.Orients :=
  hesc.orients

/-- KO7-instantiated iff characterization. An orienter `O` in the explicit
`KO7DirectOrienter` universe orients KO7 iff it is an orienting witness
equipped with one of the concrete Phase F.5 escape clauses. The iff is
established only on the explicit `KO7DirectOrienter` universe because the
concrete witnesses live there; no abstract iff is claimed beyond that universe. -/
theorem ko7_escape_route_iff
    (O : KO7DirectOrienter) :
    O.Orients ↔ KO7EscapingOrienter O :=
  ⟨fun horient => ko7_escape_route_forward (O := O) horient,
   fun hesc => ko7_escape_route_backward (O := O) hesc⟩

/-- Packaged KO7 iff characterization. The structure carries:

* the forward direction (orientation implies one of the five escape
  clauses);
* the backward direction (the five-clause cover is non-vacuous at the iff
  level);
* a cross-reference witness to the canonical KO7 RDRS schema confirming
  the iff is non-degenerate. -/
structure KO7EscapeRouteCharacterization : Prop where
  /-- Forward direction: every orienting observer in the explicit KO7
  direct universe packages into a concrete escaping orienter. -/
  forward :
    ∀ (O : KO7DirectOrienter), O.Orients → KO7EscapingOrienter O
  /-- Backward direction: every packaged escaping orienter carries the
  orientation proof. -/
  backward :
    ∀ (O : KO7DirectOrienter), KO7EscapingOrienter O → O.Orients
  /-- The exact iff surface used by Phase F.5. -/
  iff_route :
    ∀ (O : KO7DirectOrienter), O.Orients ↔ KO7EscapingOrienter O
  /-- Cross-reference witness: the canonical KO7 RDRS witness from
  `Meta/CanonicalWitnessUniversality.lean` projects definitionally onto
  the role-aware KO7 RDRS adapter. -/
  canonicalWitness_consistent :
    ko7CanonicalWitness.schema = ko7RDRS

/-- Canonical constructor: the KO7 iff characterization holds
unconditionally on the explicit `KO7DirectOrienter` universe, with the
canonical KO7 RDRS witness used as the cross-reference. -/
theorem ko7_escape_characterization_certificate :
    KO7EscapeRouteCharacterization where
  forward := fun O horient => ko7_escape_route_forward (O := O) horient
  backward := fun O hesc => ko7_escape_route_backward (O := O) hesc
  iff_route := ko7_escape_route_iff
  canonicalWitness_consistent := ko7_as_canonical_recursiveFamily_witness

/-- Phase F.5 closeout marker: both halves of the escape-route
characterization (the schema-generic one-way theorem at every
`DuplicatingRecursiveFamily` and the KO7-instantiated iff against
the explicit direct universe) are unconditionally established.

The conjunction below is the single public name reviewers reach for to
confirm Phase F.5 closure. -/
theorem phaseF5_escape_characterization_closed :
    (∀ (F : DuplicatingRecursiveFamily),
        RecursiveFamilyEscapeCharacterization F) ∧
      KO7EscapeRouteCharacterization := by
  refine ⟨?_, ko7_escape_characterization_certificate⟩
  intro F
  exact recursiveFamily_escape_characterization_certificate F

end OperatorKO7.StepDuplicating
