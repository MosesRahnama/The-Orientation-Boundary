import OperatorKO7.Meta.DistinctionBoundary.ObserverExpressivity

set_option autoImplicit false

/-!
# Role erasure: the clone no-go instantiated at the duplicating recursor

Manuscript anchors: the definability-boundary section of
`Rahnama_The_Distinction_Boundary`, and the dependency-pair externality weld of
`ROADMAP-09-six-welds-boundary-object.md` (Weld 2).

## What this module proves

The duplicating recursor produces two occurrences of the same value that differ
only in role: one is the frame copy, one is the live (active) copy. This module
carries that situation as an explicit carrier `Occ Y := Y × Role` with the role
erasure endomorphism `roleCollapse`, and proves four statements about it.

* `roleCollapse_merges` — role collapse identifies the two occurrences of every
  value while the occurrences themselves are distinct. This is the R5
  non-vacuity witness for the merging hypothesis of T-E.
* `isActive_not_value_factored` — activity does not factor through value: no
  `g : Y → Bool` computes the role coordinate from the value coordinate. This is
  the direct route and needs no naturality.
* `no_roleBlind_discriminator` — T-E
  (`not_discriminator_of_natural_under_noninjective`) instantiated: no binary
  operation on occurrences that is natural under role collapse is a sound and
  complete disequality discriminator for an active-role collapse point.
* `dp_license_is_exogenous_separator` — any channel that decodes to activity
  separates the two occurrences that value observation identifies, and therefore
  (`dp_license_not_value_factored`) does not factor through value erasure. This
  is the precise sense in which the dependency-pair license is external: external
  relative to the value-only interface, internal once the role coordinate is
  adjoined.

## The load-carrying hypothesis detail

T-E requires a collapse point `nil` with the reflection property
`h z = nil → z = nil`. Here the collapse point is pinned on the **active** side,
`nil := (y₀, Role.active)`. The image of `roleCollapse` is frame-only
(`roleCollapse_never_active`), so the reflection hypothesis holds vacuously.
With a frame-role collapse point the reflection hypothesis is false, and the
instantiation would not go through. The choice is not cosmetic and is recorded
here because it is the first thing a refuter checks.

## Claim boundaries

* The no-go is about the occurrence carrier `Occ Y`, not about `Y`. On `Bool`
  a disequality discriminator exists (`valueDiscriminator_isDiscriminator`), and
  `roleBlind_obstruction_is_about_occurrences` states both facts together.
* As in T-E, the statement bounds one binary operation, that is, a single term
  operation of a clone. Multi-term programs and external decision procedures lie
  outside its scope.
* `isActive` is `Prop`-valued. The non-factorization statement quantifies over
  `Bool`-valued value functions, so it rules out a decision procedure reading
  values alone, not merely a propositional coincidence.

Relation: not applicable (carrier-level observations). Closure: not applicable.
Strategy: not applicable. Trust: kernel only, Mathlib baseline.
-/

namespace OperatorKO7.Meta.DistinctionBoundary.RoleErasureInstance

open OperatorKO7.Meta.DistinctionBoundary.ObserverExpressivity

/-! ## 1. The occurrence carrier and role erasure -/

/-- The role coordinate of an occurrence: the frame copy or the live copy. -/
inductive Role
  | frame
  | active
  deriving DecidableEq, Repr

/-- An occurrence is a value together with a role. -/
abbrev Occ (Y : Type*) := Y × Role

/-- Role erasure as an endomorphism of the occurrence carrier: keep the value,
forget the role by sending every occurrence to its frame copy. -/
def roleCollapse {Y : Type*} : Occ Y → Occ Y := fun o => (o.1, Role.frame)

/-- The predicate a dependency-pair license must decide: is this occurrence the
live one? -/
def isActive {Y : Type*} (o : Occ Y) : Prop := o.2 = Role.active

/-- Role collapse never returns an active occurrence. This is what makes the
reflection hypothesis of T-E vacuously true at an active-role collapse point. -/
theorem roleCollapse_never_active {Y : Type*} (y₀ : Y) (z : Occ Y) :
    roleCollapse z ≠ (y₀, Role.active) := by
  intro hz
  have hrole : Role.frame = Role.active := congrArg Prod.snd hz
  exact Role.noConfusion hrole

/-- The two occurrences of a value are distinct. -/
theorem occ_frame_ne_active {Y : Type*} (y : Y) :
    ((y, Role.frame) : Occ Y) ≠ (y, Role.active) := by
  intro h
  exact Role.noConfusion (congrArg Prod.snd h)

/-- **R5 witness.** Role collapse merges the two occurrences of every value,
and those occurrences are distinct. The merging hypothesis of T-E is therefore
inhabited at this carrier, for every value. -/
theorem roleCollapse_merges {Y : Type*} (y : Y) :
    roleCollapse ((y, Role.frame) : Occ Y) = roleCollapse ((y, Role.active) : Occ Y) ∧
      ((y, Role.frame) : Occ Y) ≠ (y, Role.active) :=
  ⟨rfl, occ_frame_ne_active y⟩

/-! ## 2. Activity does not factor through value -/

/-- **Direct non-factorization.** No value-only function computes activity: the
two occurrences of `y` carry the same value and different activity. No
naturality hypothesis is used. -/
theorem isActive_not_value_factored {Y : Type*} (y : Y) :
    ¬ ∃ g : Y → Bool, ∀ o : Occ Y, (isActive o ↔ g o.1 = true) := by
  rintro ⟨g, hg⟩
  have hact : g y = true := (hg ((y, Role.active) : Occ Y)).mp rfl
  have hfrm : isActive ((y, Role.frame) : Occ Y) := (hg ((y, Role.frame) : Occ Y)).mpr hact
  exact Role.noConfusion hfrm

/-! ## 3. T-E instantiated at role erasure -/

/-- The naturality class of T-E is inhabited at this carrier: the first
projection operation is natural under role collapse. Without this the
instantiated no-go could be vacuous through its naturality premise. -/
theorem naturalUnder_roleCollapse_nonvacuous (Y : Type*) :
    ∃ t : Occ Y → Occ Y → Occ Y, NaturalUnder roleCollapse t :=
  ⟨fun x _ => x, fun _ _ => rfl⟩

/-- **T-E instantiated.** No binary operation on occurrences that is natural
under role collapse is a sound and complete disequality discriminator for an
active-role collapse point.

The collapse point must sit on the active side: `roleCollapse` never outputs an
active occurrence, so the reflection hypothesis of T-E holds vacuously. -/
theorem no_roleBlind_discriminator {Y : Type*} (y₀ y : Y)
    (t : Occ Y → Occ Y → Occ Y) (hnat : NaturalUnder roleCollapse t) :
    ¬ IsDiscriminator ((y₀, Role.active) : Occ Y) t :=
  not_discriminator_of_natural_under_noninjective
    ((y₀, Role.active) : Occ Y) roleCollapse t
    (fun z hz => absurd hz (roleCollapse_never_active y₀ z))
    ((y, Role.frame) : Occ Y) ((y, Role.active) : Occ Y)
    (occ_frame_ne_active y) rfl hnat

/-! ## 4. The dependency-pair license as an exogenous separator -/

/-- **Separator necessity.** Any channel whose decoding agrees with activity
separates the two occurrences that value observation identifies. -/
theorem dp_license_is_exogenous_separator {Y C : Type*} (y : Y)
    (c : Occ Y → C) (decode : C → Prop)
    (hdec : ∀ o : Occ Y, decode (c o) ↔ isActive o) :
    c ((y, Role.frame) : Occ Y) ≠ c ((y, Role.active) : Occ Y) := by
  intro hEq
  have hact : decode (c ((y, Role.active) : Occ Y)) :=
    (hdec ((y, Role.active) : Occ Y)).mpr rfl
  rw [← hEq] at hact
  exact Role.noConfusion ((hdec ((y, Role.frame) : Occ Y)).mp hact)

/-- **The externality statement.** A channel that decodes to activity does not
factor through role erasure. This is the dependency-pair license read at the
right altitude: external relative to the value-only interface. -/
theorem dp_license_not_value_factored {Y C : Type*} (y : Y)
    (c : Occ Y → C) (decode : C → Prop)
    (hdec : ∀ o : Occ Y, decode (c o) ↔ isActive o) :
    ¬ ∃ g : Y → C, ∀ o : Occ Y, c o = g o.1 := by
  rintro ⟨g, hg⟩
  refine dp_license_is_exogenous_separator y c decode hdec ?_
  rw [hg ((y, Role.frame) : Occ Y), hg ((y, Role.active) : Occ Y)]

/-! ## 5. The obstruction is about occurrences, not about values -/

/-- A disequality discriminator on `Bool` with collapse point `false`. -/
def valueDiscriminator (a b : Bool) : Bool := decide (a ≠ b)

/-- The value carrier does carry a discriminator. -/
theorem valueDiscriminator_isDiscriminator :
    IsDiscriminator false valueDiscriminator := by
  intro a b
  cases a <;> cases b <;> simp [valueDiscriminator]

/-- **Non-triviality.** On the value carrier `Bool` a sound and complete
disequality discriminator exists, while on the occurrence carrier `Occ Bool` no
role-blind one does. The obstruction is created by adjoining the role
coordinate, not by the values. -/
theorem roleBlind_obstruction_is_about_occurrences :
    IsDiscriminator false valueDiscriminator ∧
      ∀ t : Occ Bool → Occ Bool → Occ Bool, NaturalUnder roleCollapse t →
        ¬ IsDiscriminator ((false, Role.active) : Occ Bool) t :=
  ⟨valueDiscriminator_isDiscriminator,
    fun t hnat => no_roleBlind_discriminator false false t hnat⟩

end OperatorKO7.Meta.DistinctionBoundary.RoleErasureInstance
