import OperatorKO7.Meta.DistinctionBoundary.GateTheorem
import OperatorKO7.Meta.DistinctionBoundary.ObserverExpressivity

/-!
# Gate observer uniqueness

This module upgrades the Gate's existence theorem to a characterization over a
declared observer class. A value-natural observer is invariant under every map
of the `Trace` value coordinate while the frame/active role is held fixed. Such
an observer factors through the role projection, and the factor is unique.
Consequently it separates the duplicated-generator pair exactly when its role
factor separates `frame` from `active`.

The scope is exact. No uniqueness is claimed for observers that can inspect a
chosen non-natural property of the value coordinate, and no dependency-pair
soundness theorem is added here. The capstone carries the complete existing
`gate_derives_dp_license` package together with the new characterization.

Relation: carrier-level observation plus the existing Gate package.
Closure: not applicable to the new observer classification.
Trust: kernel checked, Mathlib baseline only.
-/

set_option autoImplicit false

open OperatorKO7 Trace
open OperatorKO7.MetaDependencyPairs
open OperatorKO7.Meta.DistinctionBoundary.ObserverExpressivity
open OperatorKO7.Meta.DistinctionBoundary.RoleErasureInstance
open OperatorKO7.Meta.DistinctionBoundary.DPChannelInstance
open OperatorKO7.Meta.DistinctionBoundary.GateTheorem
open OperatorKO7.Meta.DistinctionBoundary.Quantitative
open OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7LocalCone
open OperatorKO7.Meta.SafeStep.BranchEntropyGeneral
open OperatorKO7.Meta.SafeStep.GaugeFixingGuard
open OperatorKO7.Meta.BoundaryGeneral.DistinctionRecord

namespace OperatorKO7.Meta.DistinctionBoundary.GateObserverUniqueness

universe u

/-- A value-natural observer is invariant under every endomorphism of the
`Trace` value coordinate while preserving the role coordinate. -/
def ValueNatural {β : Type u} (q : Occ Trace → β) : Prop :=
  ∀ (h : Trace → Trace) (o : Occ Trace), q (h o.1, o.2) = q o

/-- The canonical role factor of an occurrence observer, obtained by evaluating
it at `void` in each role. -/
def roleFactor {β : Type u} (q : Occ Trace → β) : Role → β :=
  fun r => q (void, r)

/-- Lift an observer on roles to an occurrence observer. -/
def roleObserverLift {β : Type u} (g : Role → β) : Occ Trace → β :=
  fun o => g o.2

/-- The role projection is value-natural. -/
theorem roleProj_valueNatural :
    ValueNatural (fun o : Occ Trace => o.2) := by
  intro h o
  rfl

/-- Every lifted role observer is value-natural. -/
theorem roleObserverLift_valueNatural {β : Type u} (g : Role → β) :
    ValueNatural (roleObserverLift g) := by
  intro h o
  rfl

/-- Every value-natural observer factors through the role projection. The
factor is the canonical `roleFactor`. -/
theorem valueNatural_factors_through_role {β : Type u}
    (q : Occ Trace → β) (hq : ValueNatural q) :
    ∃ g : Role → β, ∀ o : Occ Trace, q o = g o.2 := by
  refine ⟨roleFactor q, ?_⟩
  intro o
  exact (hq (fun _ => void) o).symm

/-- Any observer that factors through role is value-natural. -/
theorem valueNatural_of_factors_through_role {β : Type u}
    (q : Occ Trace → β) (g : Role → β)
    (hfactor : ∀ o : Occ Trace, q o = g o.2) : ValueNatural q := by
  intro h o
  calc
    q (h o.1, o.2) = g o.2 := hfactor (h o.1, o.2)
    _ = q o := (hfactor o).symm

/-- The role factor of an occurrence observer is unique. -/
theorem valueNatural_role_factor_unique {β : Type u}
    (q : Occ Trace → β) {g₁ g₂ : Role → β}
    (h₁ : ∀ o : Occ Trace, q o = g₁ o.2)
    (h₂ : ∀ o : Occ Trace, q o = g₂ o.2) : g₁ = g₂ := by
  funext r
  calc
    g₁ r = q (void, r) := (h₁ (void, r)).symm
    _ = g₂ r := h₂ (void, r)

/-- Exact classification: value-natural occurrence observers are precisely the
observers with a unique role factor. -/
theorem valueNatural_iff_existsUnique_role_factor {β : Type u}
    (q : Occ Trace → β) :
    ValueNatural q ↔ ∃! g : Role → β, ∀ o : Occ Trace, q o = g o.2 := by
  constructor
  · intro hq
    rcases valueNatural_factors_through_role q hq with ⟨g, hg⟩
    refine ⟨g, hg, ?_⟩
    intro g' hg'
    exact valueNatural_role_factor_unique q hg' hg
  · rintro ⟨g, hg, _⟩
    exact valueNatural_of_factors_through_role q g hg

/-- The observer class itself is equivalent to the type of role observers. -/
def valueNaturalObserverEquiv (β : Type u) :
    {q : Occ Trace → β // ValueNatural q} ≃ (Role → β) where
  toFun q := roleFactor q.1
  invFun g := ⟨roleObserverLift g, roleObserverLift_valueNatural g⟩
  left_inv q := by
    apply Subtype.ext
    funext o
    exact q.2 (fun _ => void) o
  right_inv g := by
    funext r
    rfl

/-- The role projection separates the duplicated-generator pair. -/
theorem roleProj_separates_generator (s : Trace) :
    (generatorFrame s).2 ≠ (generatorActive s).2 := by
  exact occ_frame_ne_active s ∘ Prod.ext rfl

/-- A separating value-natural observer is a role observer whose two role
values are distinct. -/
theorem separating_valueNatural_is_role {β : Type u}
    (q : Occ Trace → β) (hq : ValueNatural q) (s : Trace)
    (hsep : q (generatorFrame s) ≠ q (generatorActive s)) :
    ∃ g : Role → β,
      (∀ o : Occ Trace, q o = g o.2) ∧ g Role.frame ≠ g Role.active := by
  rcases valueNatural_factors_through_role q hq with ⟨g, hg⟩
  refine ⟨g, hg, ?_⟩
  intro hroles
  apply hsep
  calc
    q (generatorFrame s) = g Role.frame := hg (generatorFrame s)
    _ = g Role.active := hroles
    _ = q (generatorActive s) := (hg (generatorActive s)).symm

/-- A value-only observable sees the generator pair on the value diagonal. -/
theorem value_observable_never_separates {β : Type u}
    (v : Trace → β) (s : Trace) :
    v (generatorFrame s).1 = v (generatorActive s).1 := by
  rfl

/-- Exact separation criterion for a value-natural observer. -/
theorem valueNatural_separating_iff_role_distinct {β : Type u}
    (q : Occ Trace → β) (hq : ValueNatural q) (s : Trace) :
    (q (generatorFrame s) ≠ q (generatorActive s)) ↔
      ∃ g : Role → β,
        (∀ o : Occ Trace, q o = g o.2) ∧ g Role.frame ≠ g Role.active := by
  constructor
  · exact separating_valueNatural_is_role q hq s
  · rintro ⟨g, hg, hroles⟩ hEq
    apply hroles
    calc
      g Role.frame = q (generatorFrame s) := (hg (generatorFrame s)).symm
      _ = q (generatorActive s) := hEq
      _ = g Role.active := hg (generatorActive s)

/-- On the two-constructor role carrier, separating the two role values is
exactly injectivity of the role encoding. -/
theorem roleMap_injective_iff_distinct {β : Type u} (g : Role → β) :
    Function.Injective g ↔ g Role.frame ≠ g Role.active := by
  constructor
  · intro hinj hEq
    exact Role.noConfusion (hinj hEq)
  · intro hne r₁ r₂ hEq
    cases r₁ <;> cases r₂
    · rfl
    · exact absurd hEq hne
    · exact absurd hEq hne.symm
    · rfl

/-- A separating value-natural observer is exactly an injective encoding of the
role coordinate followed by the role projection. -/
theorem separating_valueNatural_is_role_embedding {β : Type u}
    (q : Occ Trace → β) (hq : ValueNatural q) (s : Trace)
    (hsep : q (generatorFrame s) ≠ q (generatorActive s)) :
    ∃ g : Role → β,
      Function.Injective g ∧ ∀ o : Occ Trace, q o = g o.2 := by
  rcases separating_valueNatural_is_role q hq s hsep with ⟨g, hg, hne⟩
  exact ⟨g, (roleMap_injective_iff_distinct g).2 hne, hg⟩

/-- Gate characterization. The complete existing Gate license package is
carried unchanged, and the new conjunct proves uniqueness up to an injective
encoding of role over the declared value-natural observer class. -/
theorem gate_characterization (b s n : Trace) :
    ((¬ HasNonNullRecord (ko7RecordSurface Trace) s s) ∧
    HasNonNullRecord (ko7RecordSurface Role) Role.frame Role.active ∧
    (¬ ∃ g : Trace → Bool, ∀ o : Occ Trace,
      (isActive o ↔ g o.1 = true)) ∧
    actualDPChannel b s n (((), Role.frame) : Occ Unit) ≠
      actualDPChannel b s n (((), Role.active) : Occ Unit) ∧
    Step (recΔ b s (delta n)) (app s (extractRecSuccDP b s n)) ∧
    DPPair (recΔ b s (delta n)) (extractRecSuccDP b s n) ∧
    (¬ ∃ g : Unit → Bool, ∀ o : Occ Unit,
      actualDPChannel b s n o = g o.1) ∧
    (¬ DistinctionLicense s s) ∧
    (branchEntropy (terminalMultiplicity LocalRaw .source) -
        branchEntropy (terminalMultiplicity LocalLicensed .source) =
      branchEntropy 2) ∧
    structuralHartleyCollapse LocalRaw LocalLicensed .source = 1) ∧
    (∀ q : Occ Trace → Bool, ValueNatural q →
      (q (generatorFrame s) ≠ q (generatorActive s) ↔
        ∃ g : Role → Bool,
          (∀ o : Occ Trace, q o = g o.2) ∧
            g Role.frame ≠ g Role.active)) := by
  refine ⟨gate_derives_dp_license b s n, ?_⟩
  intro q hq
  exact valueNatural_separating_iff_role_distinct q hq s

end OperatorKO7.Meta.DistinctionBoundary.GateObserverUniqueness
